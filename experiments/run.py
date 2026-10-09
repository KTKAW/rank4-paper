"""Reproducible paired benchmarks. All generated inputs are saved, including capped runs."""
from pathlib import Path
from dataclasses import asdict
import sys,json,random,platform,subprocess,hashlib,datetime
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from algorithm.classifier import *

def sysctl(key):
    try:return subprocess.check_output(['/usr/sbin/sysctl','-n',key],text=True,stderr=subprocess.DEVNULL).strip()
    except Exception:return None

def main():
    rng=random.Random(20261009)
    fixed=[('acyclic',(1,1,1,2,1,1)),('zero',(0,)*6),('disconnected_MA',(2,-3,0,2,0,0)),('disconnected_NMA',(2,-2,0,2,0,0)),('double_box',(-2,0,2,-2,0,-2)),('finite_orbit',(-2,1,1,-1,-1,-1)),('seed_1',(-2,-1,-1,1,-1,1)),('seed_3',(-2,1,-1,1,1,1)),('five_MA',(0,-3,2,-2,-1,-6)),('five_NMA',(0,-3,2,-2,-1,-5)),('product',(-1,-8,3,4,-1,0)),('quadratic',(-3,-6,2,-3,1,-3)),('scalar_gap',(0,0,2,-3,1,-1)),('BFS_positive',(-2,-1,1,-1,2,-1))]
    fixed += [('line_'+str(t),line(t)) for t in (-5,0,1,2,3,4,10,11,32,33,128,129,1000,1001)]
    inputs=[{'id':name,'group':'named','tuple':q,'max_states':100000,'timeout':3.0} for name,q in fixed]
    for i in range(24):inputs.append({'id':f'uniform_{i:02}','group':'uniform','tuple':tuple(rng.randint(-3,3) for _ in range(6)),'max_states':25000,'timeout':1.0})
    for i in range(12):
        seed=tuple(rng.randint(0,2) for _ in range(6));w=[rng.randrange(4) for _ in range(6)]
        inputs.append({'id':f'planted_{i:02}','group':'planted','tuple':apply_word(seed,w),'generating_seed':seed,'generating_word':w,'max_states':25000,'timeout':1.0})
    (ROOT/'experiments/inputs.json').write_text(json.dumps(inputs,indent=2)+'\n')
    meta={'date_local':'2026-10-09','timezone':'Europe/London','utc_started':datetime.datetime.now(datetime.timezone.utc).isoformat(),'python':sys.version,'platform':platform.platform(),'machine':platform.machine(),'processor':sysctl('machdep.cpu.brand_string'),'cpu_count':sysctl('hw.ncpu'),'memory_bytes':sysctl('hw.memsize'),'seed':20261009,'repetitions':3,'warmup':'one acyclic call before timings; no result cache','sampling':'24 iid uniform labelled six-tuples in [-3,3]; 12 iid acyclic nonnegative tuples in [0,2]^6, each mutated by six iid uniform vertices; all draws kept','limits':'named 100000 discovered states / 3s; generated 25000 states / 1s; cooperative timeout checked once per expansion','classifier_sha256':hashlib.sha256((ROOT/'algorithm/classifier.py').read_bytes()).hexdigest(),'timing':'perf_counter inside analyze_tuple; includes bound calculation, shortcuts, search and independent MA witness replay; excludes import/JSON I/O','counter_scope':'mutation_evaluations counts candidate mutations in search/descent/line reduction; witness_check_mutations separately counts independent verification; fixed-word guards construct words without mutation; states_discovered/expanded and max_frontier count BFS only; finite-orbit certificate is verified at module import, outside timings'}
    (ROOT/'experiments/environment.json').write_text(json.dumps(meta,indent=2)+'\n')
    analyze_tuple((0,)*6)
    with (ROOT/'experiments/raw.jsonl').open('w') as f:
        for inp in inputs:
            for rep in range(3):
                # Alternate order to reduce consistent order bias.
                for method in (('hybrid','search') if rep%2==0 else ('search','hybrid')):
                    r=analyze_tuple(tuple(inp['tuple']),shortcuts=method=='hybrid',max_states=inp['max_states'],timeout=inp['timeout'])
                    if inp['group']=='planted':assert r.label!='NMA'
                    row={'id':inp['id'],'group':inp['group'],'method':method,'repetition':rep,**asdict(r)}
                    f.write(json.dumps(row)+'\n');f.flush()
            print(inp['id'],flush=True)
if __name__=='__main__':main()
