"""RAM-12 native state observations from fully certified historical MathCan proofs.

Input: fixed 76 RAM-11F old-source scripts. All native theorem bodies are
replaced by their proof scripts; read-only ram12_observe precedes each tactic.
Each complete instrumented source is compiled independently twice.
This produces old TRAIN proof-state labels, never new PEF or RAM-10 scores.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys
import time

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'ram11f'))
from native_replay import (OLD_SOURCE, WORKLIST_HASH, validate_worklist,
                          verify_checkout, render_source, compile_once, sha)

LABEL='RAM12_STATE_JSON:'
SALT='RAM12-FRESH-STATE-20261115/'
EXPECTED_SCRIPTS=76
EXPECTED_OCCURRENCES=282
EXPECTED_UNIQUE_ACTIONS=230
EXPECTED_PREFIXES=176
EXPECTED_ROOTS=22

def split(root:str,theorem:str)->str:
    value=int(hashlib.sha256((SALT+root+':'+theorem).encode()).hexdigest(),16)%6
    return 'dev' if value==0 else 'holdback' if value==1 else 'train'

def instrument(actions:list[str], proof_id:str)->list[str]:
    output=[]
    for i,action in enumerate(actions):
        if '\n' in action or '\r' in action or ';' in action:
            raise ValueError('unexpected compound proof action')
        output.extend([f'ram12_observe "{proof_id}:{i:02d}"',action])
    return output

def read_markers(raw:str, proof_id:str, actions:list[str])->list[dict]:
    states=[]
    for line in raw.splitlines():
        if LABEL not in line:continue
        try: row=json.loads(line.split(LABEL,1)[1].strip())
        except Exception as error:raise ValueError('invalid or wrapped Lean JSON state marker') from error
        if set(row)!={'id','goals','definitions'}:
            raise ValueError('changed Lean marker keys')
        if not isinstance(row['goals'],list) or not all(isinstance(g,str) for g in row['goals']):
            raise ValueError('invalid printed Lean goal list')
        if not isinstance(row['definitions'],list) or not all(isinstance(x,str) for x in row['definitions']):
            raise ValueError('invalid printed context definitions')
        states.append(row)
    expected=[f'{proof_id}:{i:02d}' for i in range(len(actions))]
    if [r['id'] for r in states]!=expected:
        raise ValueError(f'Lean trace sequence incomplete for {proof_id}: {len(states)}/{len(expected)}')
    if any(not row['goals'] for row in states):
        raise ValueError('a supposed next action followed a completed Lean proof')
    return states

def source_for_case(original:bytes,theorem:str,actions:list[str],proof_id:str)->bytes:
    src=render_source(original.decode('utf8'),theorem,instrument(actions,proof_id))
    result=('import RAM12.Trace\n'+src).encode('utf8')
    if re.search(r'^\s*(?:sorry|admit)\s*$',src,re.M):
        raise AssertionError('instrumentation inserted an admitted proof')
    return result

def read_expected(worklist:Path)->list[dict]:
    if sha(worklist.read_bytes())!=WORKLIST_HASH:
        raise AssertionError('RAM-11F source worklist changed')
    cases=validate_worklist(worklist)
    if len(cases)!=EXPECTED_SCRIPTS:raise AssertionError('original script count changed')
    roots={(r['source_file'],r['theorem']) for r in cases}
    steps=sum(len(r['proposed_new_actions']) for r in cases)
    if len(roots)!=EXPECTED_ROOTS or steps!=EXPECTED_OCCURRENCES:
        raise AssertionError('native script/root inventory differs')
    seen={(r['source_file'],r['theorem'],tuple(r['proposed_new_actions'][:i]),r['proposed_new_actions'][i])
          for r in cases for i in range(len(r['proposed_new_actions']))}
    prefixes={(f,t,p) for f,t,p,a in seen}
    if len(seen)!=EXPECTED_UNIQUE_ACTIONS or len(prefixes)!=EXPECTED_PREFIXES:
        raise AssertionError('prefix/action data do not match RAM-11F independent audit')
    return cases

def aggregate(rows:list[dict])->tuple[list[dict],dict]:
    states={}
    steps={}
    for row in rows:
        key=(row['source_file'],row['theorem'],tuple(row['prefix_actions']))
        value=(row['goals'],row['definitions'])
        if key in states and states[key]!=value:
            raise AssertionError('same original theorem + exact tactic prefix has conflicting Lean states')
        states[key]=value
        label=(key,row['next_action'])
        if label in steps:
            other=steps[label]
            if (other['goals'],other['definitions'])!=value:
                raise AssertionError('same original prefix/action has conflicting Lean states')
            other['supporting_proof_ids'].add(row['proof_id'])
        else:
            copy={k:v for k,v in row.items() if k!='proof_id'}
            copy['supporting_proof_ids']={row['proof_id']}
            steps[label]=copy
    roots={(f,t) for f,t,p in states}
    if (len(rows),len(steps),len(states),len(roots))!=(282,230,176,22):
        raise AssertionError('incomplete RAM-12 state-label coverage')
    result=[]
    for row in steps.values():
        row['supporting_proof_ids']=sorted(row['supporting_proof_ids'])
        row['label']='positive_from_twice_compiled_complete_original_Lean_source'
        row['full_source_compiles']=2
        result.append(row)
    result.sort(key=lambda r:(r['source_file'],r['theorem'],r['prefix_actions'],r['next_action']))
    rootcounts=Counter(split(f,t) for f,t in roots)
    if dict(rootcounts)!={'train':14,'dev':3,'holdback':5}:
        raise AssertionError('registered source-family hash split changed')
    return result,dict(raw_action_occurrences=len(rows),unique_prefix_actions=len(steps),
                       exact_prefix_states=len(states),roots=len(roots),
                       split_roots=dict(rootcounts),
                       historical_original_train_only=True,
                       unknown_as_failed=0,
                       original_pef_theorem_scores=0,ram10_heldout_theorem_scores=0)

def run(mathcan:Path,worklist:Path,out:Path)->dict:
    if out.exists():raise FileExistsError('source-only artifact output exists already')
    cases=read_expected(worklist)
    version=verify_checkout(mathcan)
    if '4.35.0' not in version:raise ValueError('unexpected Lean version')
    out.mkdir(parents=True)
    result=dict(schema='RAM12-v1-native-source-goal-observations',
                source_commit=OLD_SOURCE,worklist_sha256=WORKLIST_HASH,
                original_pef_scores=0,ram10_heldout_scores=0,
                compiler=version,status='running',cases=[])
    (out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    allrows=[]
    for i,case in enumerate(cases):
        base=out/'cases'/f'{i:03d}'
        actions=case['proposed_new_actions']
        ident=f'RAM11F-{i:03d}'
        row=dict(index=i,proof_id=ident,source_file=case['source_file'],theorem=case['theorem'],
                 actions=actions,status='not_started')
        start=time.perf_counter()
        try:
            raw=(mathcan/case['source_file']).read_bytes()
            if sha(raw)!=case['original_source_sha256']:
                raise ValueError('old MathCan source byte hash mismatch')
            script=source_for_case(raw,case['theorem'],actions,ident)
            row['instrumented_source_sha256']=sha(script)
            first=compile_once(mathcan,script,base/'first',25)
            row['first']=first
            if first['status']!='accepted':
                raise RuntimeError('first native full-source compilation failed: '+first['status'])
            a=read_markers((base/'first.log').read_text(encoding='utf8'),ident,actions)
            second=compile_once(mathcan,script,base/'second',25)
            row['second']=second
            if second['status']!='accepted':
                raise RuntimeError('second native full-source compilation failed: '+second['status'])
            b=read_markers((base/'second.log').read_text(encoding='utf8'),ident,actions)
            if a!=b or first['source_sha256']!=second['source_sha256'] or first['axioms']!=second['axioms']:
                raise AssertionError('independent native source/state/axiom replay differs')
            if time.perf_counter()-start>60:
                raise TimeoutError('per-theorem instrumented replay exceeded ceiling')
            for j,(act,state) in enumerate(zip(actions,a)):
                allrows.append(dict(proof_id=ident,source_file=case['source_file'],
                    theorem=case['theorem'],split=split(case['source_file'],case['theorem']),
                    prefix_actions=actions[:j],next_action=act,
                    goals=state['goals'],definitions=state['definitions'],
                    original_source_sha256=case['original_source_sha256'],
                    instrumented_source_sha256=sha(script),
                    original_lean_toolchain='leanprover/lean4:v4.35.0'))
            row['state_markers']=len(a)
            row['status']='two_complete_source_compiles_agree'
        except BaseException as error:
            row['status']='aborted_unscored'
            row['error']=repr(error)
            result['status']='aborted'
        row['seconds']=round(time.perf_counter()-start,4)
        result['cases'].append(row)
        (out/'receipt.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf8')
        print('RAM12_SOURCE',i,ident,row['status'],flush=True)
        if result['status']=='aborted':break
    if result['status']!='aborted':
        labels,stats=aggregate(allrows)
        path=out/'certified_state_action_labels.jsonl'
        path.write_text(''.join(json.dumps(r,sort_keys=True,ensure_ascii=False)+'\n' for r in labels),encoding='utf8')
        result.update(status='complete',**stats,processed=len(result['cases']),
                      full_source_compilations=152,labels_sha256=sha(path.read_bytes()))
        (out/'receipt.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf8')
    return result

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mathcan',type=Path,required=True)
    parser.add_argument('--worklist',type=Path,default=Path(__file__).resolve().parents[1]/'ram11f/locked_worklist.jsonl')
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    answer=run(args.mathcan,args.worklist,args.out)
    print('RAM12_RESULT',json.dumps({k:v for k,v in answer.items() if k!='cases'},sort_keys=True))
    if answer['status']!='complete':raise SystemExit(1)
