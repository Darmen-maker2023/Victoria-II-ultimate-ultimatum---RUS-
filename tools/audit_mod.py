"""Offline Victoria II data audit. Does not launch the game or access saved games."""
from __future__ import annotations
import argparse
import csv
from collections import Counter, defaultdict
from dataclasses import dataclass
from decimal import Decimal, InvalidOperation
import json
from pathlib import Path
import re
import sys

LEX = re.compile(rb'#[^\r\n]*|"[^"\r\n]*(?:\r?\n[^"\r\n]*)*"|[{}=<>]|[^\s{}=<>"#]+')


@dataclass
class Node:
    key: str | None
    value: str | list
    line: int


def parse(raw):
    tokens = []
    line, last = 1, 0
    for m in LEX.finditer(raw):
        gap = raw[last:m.start()]
        if b'"' in gap:
            raise ValueError(f'Unterminated quoted text near line {line}')
        line += gap.count(b'\n')
        text = m.group().decode('latin1')
        if not text.startswith('#'):
            tokens.append((text.strip('"'), line, text.startswith('"')))
        line += m.group().count(b'\n')
        last = m.end()
    if b'"' in raw[last:]:
        raise ValueError(f'Unterminated quoted text near line {line}')
    index = 0
    def sequence(nested=False):
        nonlocal index
        result = []
        while index < len(tokens):
            text, ln, quoted = tokens[index]
            if text == '{' and not quoted:
                index += 1
                result.append(Node(None,sequence(True),ln))
                continue
            if text == '}' and not quoted:
                if not nested:
                    raise ValueError(f'Unexpected closing brace on line {ln}')
                index += 1
                return result
            if text in ['{', '=', '<', '>'] and not quoted:
                raise ValueError(f'Unexpected token {text!r} on line {ln}')
            index += 1
            if index < len(tokens) and tokens[index][0] in ['=','<','>'] and not tokens[index][2]:
                index += 1
                if index < len(tokens) and tokens[index][0] == '=' and not tokens[index][2]:
                    index += 1
                if index >= len(tokens):
                    raise ValueError(f'Missing value for {text} on line {ln}')
                val, value_line, value_quoted = tokens[index]
                index += 1
                if val == '{' and not value_quoted:
                    value = sequence(True)
                elif val in ['}','=','<','>'] and not value_quoted:
                    raise ValueError(f'Missing value for {text} on line {ln}')
                else:
                    value = val
                result.append(Node(text, value, ln))
            else:
                result.append(Node(None, text, ln))
        if nested:
            raise ValueError(f'Unclosed block near line {line}')
        return result
    return sequence()


def walk(nodes, ancestors=()):
    for node in nodes:
        yield node, ancestors
        if isinstance(node.value,list):
            yield from walk(node.value, ancestors+(node.key,))


def field(node, name):
    return next((x.value for x in node.value if x.key == name), None) if isinstance(node.value,list) else None


def audit(mod, base=None, historical=False):
    findings = []
    def issue(kind,path,line,message,severity='warning'):
        findings.append({'kind':kind,'path':path.as_posix() if isinstance(path,Path) else path,'line':line,'message':message,'severity':severity})
    scripts = {}
    documents = []
    extensions = {'.txt','.gui','.gfx','.map'}
    for folder in ['common','decisions','events','history','interface','inventions','map','poptypes','technologies','units']:
        for path in sorted((mod/folder).rglob('*')):
            if not path.is_file() or path.suffix.lower() not in extensions:
                continue
            rel = path.relative_to(mod)
            if rel.as_posix() in ['interface/credits.txt','history/units/v2dd2.txt']:
                documents.append(rel.as_posix())
                continue
            raw = path.read_bytes()
            if raw.startswith(b'\xef\xbb\xbf'):
                issue('utf8_bom',rel,1,'UTF-8 BOM in script','error')
                raw = raw[3:]
            try:
                scripts[rel] = parse(raw)
                if rel.parts[:2] == ('history','countries'):
                    for node in scripts[rel]:
                        if node.key is None and isinstance(node.value,str) and re.fullmatch(r'\d+\.\d+\.\d+',node.value):
                            issue('history_date_assignment',rel,node.line,f'Missing = after date {node.value}','error')
            except (ValueError,RecursionError) as exc:
                issue('syntax',rel,0,str(exc),'error')
    get = lambda name: scripts.get(Path(name),[])
    definitions = lambda folder: {n.key:(p,n) for p,nodes in scripts.items() if p.parts[0] == folder for n in nodes if n.key and isinstance(n.value,list)}
    techs = definitions('technologies')
    inventions = definitions('inventions')
    units = definitions('units')
    modifiers = {n.key for file in ['event_modifiers.txt','static_modifiers.txt','triggered_modifiers.txt'] for n in get('common/'+file) if n.key}
    governments = {n.key for n in get('common/governments.txt') if n.key}
    rebel_types = {n.key for n in get('common/rebel_types.txt') if n.key}
    ideologies = {n.key:field(n,'date') for group in get('common/ideologies.txt') if isinstance(group.value,list) for n in group.value if n.key and isinstance(n.value,list)}
    vanilla_techs = set()
    if base:
        for p in (base/'technologies').glob('*.txt'):
            vanilla_techs.update(n.key for n in parse(p.read_bytes()) if n.key)
    legacy_techs = vanilla_techs - techs.keys()
    folders_node = next((n for n in get('common/technology.txt') if n.key == 'folders'),None)
    folders = {n.key:[v.value for v in n.value if v.key is None] for n in folders_node.value} if folders_node else {}
    areas = {a for values in folders.values() for a in values}
    area_counts = Counter()
    for key,(p,n) in techs.items():
        area, year = field(n,'area'),field(n,'year')
        if area not in areas:
            issue('technology_area',p,n.line,f'{key}: undefined area {area}','error')
        if not year or not str(year).isdigit():
            issue('technology_year',p,n.line,f'{key}: invalid year {year}','error')
        area_counts[area] += 1
    countries = {}
    for n in get('common/countries.txt'):
        if not n.key or not re.fullmatch('[A-Z0-9]{3}',n.key) or not isinstance(n.value,str):
            continue
        if n.key in countries:
            issue('duplicate_country','common/countries.txt',n.line,n.key,'error')
        path = Path('common')/n.value
        countries[n.key] = path
        if not (mod/path).is_file():
            issue('missing_country','common/countries.txt',n.line,f'{n.key}: {path}','error')
    parties = defaultdict(set)
    party_count = 0
    for tag,path in countries.items():
        for party in get(path.as_posix()):
            if party.key != 'party':
                continue
            party_count += 1
            name, ideology = field(party,'name'),field(party,'ideology')
            parties[tag].add(name)
            if not name:
                issue('party_name',path,party.line,tag,'error')
            if ideology not in ideologies:
                issue('party_ideology',path,party.line,f'{tag} {name}: {ideology}','error')
            for key in ['start_date','end_date']:
                val = field(party,key)
                if not val or not re.fullmatch(r'\d+\.\d+\.\d+',val):
                    issue('party_date',path,party.line,f'{tag} {name}: {key}={val}','error')
            if historical and ideology in ideologies and ideologies[ideology]:
                start=field(party,'start_date')
                if start and tuple(map(int,start.split('.'))) < tuple(map(int,ideologies[ideology].split('.'))):
                    issue('party_before_ideology',path,party.line,f'{name}: {start} before {ideologies[ideology]}','error')
    all_parties = set().union(*parties.values()) if parties else set()
    event_ids = defaultdict(list)
    decision_ids = defaultdict(list)
    for path,nodes in scripts.items():
        if path.parts[0] == 'events':
            for node in nodes:
                if node.key in ['country_event','province_event'] and isinstance(node.value,list):
                    event_ids[field(node,'id')].append((path,node.line))
                    if not any(n.key == 'option' for n in node.value):
                        issue('event_without_option',path,node.line,str(field(node,'id')),'error')
                    for child, ancestors in walk(node.value):
                        if child.key in ['option','mean_time_to_happen'] and ancestors:
                            issue('nested_event_metadata',path,child.line,f'{child.key} inside {ancestors}','error')
                        if not ancestors and child.key in ['ai_chance','prestige','release','any_pop','tag','is_triggered_only_once','fires_only_once','mayor']:
                            issue('misplaced_event_field',path,child.line,str(child.key),'error')
                else:
                    issue('orphan_event_field',path,node.line,str(node.key),'error')
        if path.parts[0] == 'decisions':
            for group in nodes:
                if group.key == 'political_decisions' and isinstance(group.value,list):
                    for node in group.value:
                        if node.key:
                            decision_ids[node.key].append((path,node.line))
                        if not isinstance(node.value,list) or node.key in ['ai_will_do','potential','allow','effect'] or field(node,'potential') is None or field(node,'effect') is None:
                            issue('invalid_decision_structure',path,node.line,str(node.key),'error')
                        elif isinstance(node.value,list):
                            for child,ancestors in walk(node.value):
                                if child.key in ['potential','allow','effect','ai_will_do'] and ancestors:
                                    issue('nested_decision_metadata',path,child.line,f'{child.key} inside {ancestors}','error')
                            for condition in ['potential','allow']:
                                block=next((n for n in node.value if n.key==condition),None)
                                if block:
                                    for child,_ in walk(block.value):
                                        if child.key in ['change_tag','set_country_flag','set_global_flag','country_event','province_event','secede_province','inherit','annex_to']:
                                            issue('effect_in_decision_condition',path,child.line,str(child.key),'error')
                else:
                    issue('missing_decision_container',path,group.line,str(group.key),'error')
    for kind,table in [('duplicate_event',event_ids),('duplicate_decision',decision_ids)]:
        for key,locations in table.items():
            if len(locations)>1 or key is None:
                issue(kind,locations[0][0],locations[0][1],f'{key}: '+', '.join(f'{p}:{ln}' for p,ln in locations),'error')
    loc = defaultdict(list)
    csv_rows = 0
    for path in sorted((mod/'localisation').glob('*.csv')):
        rel = path.relative_to(mod)
        for i,raw in enumerate(path.read_bytes().splitlines(),1):
            if not raw.strip() or raw.lstrip().startswith(b'#'):
                continue
            try:
                cells = [v.encode('latin1') for v in next(csv.reader([raw.decode('latin1')],delimiter=';',strict=True))]
            except csv.Error as exc:
                issue('localisation_quoting',rel,i,str(exc),'error')
                continue
            if len(cells)<2 or not cells[0].strip():
                issue('localisation_unparsed',rel,i,'Non-record line or empty key')
                continue
            csv_rows += 1
            # Identifiers must match script bytes, including original Latin keys.
            key = cells[0].decode('latin1')
            text = cells[1].decode('cp1251',errors='replace')
            loc[key].append((text,rel,i))
            if len(cells)<=14 or cells[14].strip()!=b'x':
                issue('localisation_columns',rel,i,f'{key}: missing x marker in column 14')
            if key in ['ARMY_NAME','NAVY_NAME','REGIMENT_NAME'] or any(key == r+suffix for r in rebel_types for suffix in ['_name','_army']):
                if '"' in text or len(cells[1])>=180 or text.count('$')%2 or '\\$' in text:
                    issue('unsafe_name_template',rel,i,key,'error')
    for path,nodes in scripts.items():
        for node,parents in walk(nodes):
            key,value = node.key,node.value
            if not key:
                continue
            if key == 'limit' and any(x in parents for x in ['allow','potential','trigger']) and not any(x in parents for x in ['effect','immediate','option']):
                issue('trigger_limit',path,node.line,'Effect-only limit wrapper inside trigger')
            if key == 'random_neighbor' or (key=='claim' and path.parts[0]=='decisions'):
                issue('unknown_effect',path,node.line,key,'error')
            if key in ['has_country_flags','set_country_flags','remove_country_flags']:
                issue('unknown_flag_command',path,node.line,key,'error')
            if path.parts[0]=='decisions' and 'ai_will_do' in parents and key in ['country_event','province_event','treasury','set_country_flag']:
                issue('effect_inside_ai_weight',path,node.line,key,'error')
            if key in ['add_country_modifier','add_province_modifier'] and isinstance(value,list):
                ref = field(node,'name')
                if ref and ref not in modifiers:
                    issue('missing_modifier',path,node.line,f'{key}: {ref}')
            if key in ['has_country_modifier','has_province_modifier','remove_country_modifier','remove_province_modifier'] and isinstance(value,str) and value not in modifiers:
                issue('missing_modifier',path,node.line,f'{key}: {value}')
            if key == 'activate_technology' and isinstance(value,str) and value not in techs:
                issue('missing_technology',path,node.line,f'{key}: {value}','error')
            if key in legacy_techs:
                issue('legacy_technology',path,node.line,key)
            if key == 'activate_invention' and isinstance(value,str) and value not in inventions:
                issue('missing_invention',path,node.line,value,'error')
            if key == 'ruling_party' and isinstance(value,str):
                tag = path.name[:3] if path.parts[:2] == ('history','countries') else None
                if tag and tag not in countries:
                    issue('unregistered_country_history',path,node.line,f'{tag}: history is not loaded by the country index')
                    continue
                known = parties.get(tag,all_parties)
                if value not in known and not value.isdigit():
                    issue('missing_party',path,node.line,f'{tag or "event"}: {value}','error')
            if key == 'government' and isinstance(value,str) and value not in governments:
                issue('missing_government',path,node.line,value,'error')
            if key == 'upper_house' and isinstance(value,list) and path.parts[:2] == ('history','countries'):
                try:
                    shares = [Decimal(n.value) for n in value]
                    if not shares or any(not v.is_finite() or v < 0 for v in shares):
                        issue('invalid_upper_house_share',path,node.line,'Shares must be finite and nonnegative','error')
                    elif abs(sum(shares)-Decimal(100)) > Decimal('0.00001'):
                        issue('upper_house_total',path,node.line,f'Shares total {sum(shares)}, expected 100','error')
                except (InvalidOperation, TypeError, ValueError):
                    issue('invalid_upper_house_share',path,node.line,'Nonnumeric upper-house share','error')
            if key in ['enable_ideology','is_ideology_enabled','ruling_party_ideology'] and isinstance(value,str) and value not in ideologies:
                issue('missing_ideology',path,node.line,value,'error')
            if key in ['country_event','province_event'] and isinstance(value,list) and path.parts[0] in ['events','decisions','common'] and len(parents)>0:
                ref = field(node,'id')
                if ref and ref not in event_ids:
                    issue('missing_event',path,node.line,ref,'error')
            if key in ['country_event','province_event'] and isinstance(value,str) and value.isdigit() and value not in event_ids:
                issue('missing_event',path,node.line,value,'error')
            if key=='type' and isinstance(value,str) and any(p in parents for p in ['regiment','ship']) and value not in units:
                issue('missing_unit_type',path,node.line,value,'error')
            if key=='oob' and isinstance(value,str):
                resource=value.lstrip('/\\')
                # Missing armies are incomplete scenario data, not syntax failures.
                # The public descriptor replaces history, so no vanilla fallback.
                if not (mod/'history/units'/resource).is_file():
                    issue('missing_oob',path,node.line,value)
            if key in ['tag','change_tag','secede_province','add_core','remove_core','is_core','release'] and isinstance(value,str) and re.fullmatch('[A-Z][A-Z0-9]{2}',value) and value not in countries:
                issue('missing_tag',path,node.line,f'{key}: {value}')
    for group,keys in [('technology',techs.keys()),('party',all_parties),('ideology',ideologies.keys())]:
        for key in sorted(keys):
            if key not in loc:
                issue('missing_localisation','localisation',0,f'{group}: {key}')
    total_party_count = sum(n.key=='party' for p,nodes in scripts.items() if p.parts[:2]==('common','countries') for n in nodes)
    stats = {'scripts_parsed':len(scripts),'ignored_documents':documents,'localisation_files':len(list((mod/'localisation').glob('*.csv'))),'localisation_rows':csv_rows,
             'localisation_keys':len(loc),'countries':len(countries),'parties':party_count,'party_records_including_unregistered_countries':total_party_count,'ideologies':len(ideologies),
             'technologies':len(techs),'technology_folders':len(folders),'technology_areas':len(areas),
             'technologies_per_area':dict(sorted(area_counts.items())),'events':sum(map(len,event_ids.values())),
             'decisions':sum(map(len,decision_ids.values())),'counts_by_kind':dict(Counter(x['kind'] for x in findings)),
             'errors':sum(x['severity']=='error' for x in findings)}
    return {'stats':stats,'findings':findings}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('mod',type=Path)
    ap.add_argument('--base',type=Path)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--historical',action='store_true',help='Check party starts against ideology dates for the public edition')
    args=ap.parse_args()
    result=audit(args.mod,args.base,historical=args.historical)
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps(result['stats'],ensure_ascii=False,indent=2))
    for x in result['findings']:
        if x['severity']=='error':
            print(f"ERROR {x['kind']} {x['path']}:{x['line']} {x['message']}")
    return 1 if result['stats']['errors'] else 0


if __name__=='__main__':
    sys.stdout.reconfigure(encoding='utf-8')
    sys.exit(main())
