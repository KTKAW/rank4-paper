"""Exhaustive bounded census, independent of imported labels or height coverage."""
import json,sys
from pathlib import Path
from itertools import product
from collections import Counter,deque
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from algorithm.classifier import *

def positive(q):
    todo=deque([(q,())]);seen={q}
    while todo:
        s,w=todo.popleft()
        if acyclic(s):return w
        if len(w)==3:continue
        for k in range(4):
            t=mutate(s,k)
            if height(t)<=2 and t not in seen:seen.add(t);todo.append((t,w+(k,)))
    return None

def triangle_path(q):
    todo=deque([(q,())]);seen={q}
    while todo:
        state,w=todo.popleft();tri=triangle_obstruction(state)
        if tri:return w,tri
        if len(w)<3:
            for k in range(4):
                t=mutate(state,k)
                if t not in seen:seen.add(t);todo.append((t,w+(k,)))
    return None

def main():
    reps=sorted({canonical(q) for q in product(range(-2,3),repeat=6)})
    records=[];counts=Counter();breakdown=Counter()
    finite_can={canonical(q) for q in FINITE_ORBIT}
    for q in reps:
        c=connected(q);w=positive(q)
        rec={'tuple':q,'connected':c,'witness':w}
        if w is not None:
            assert verify_witness(q,w);rec.update(label='MA',certificate='bounded_word')
        else:
            tri=triangle_path(q)
            if tri:rec.update(label='NMA',certificate='rank_three',triangle_word=tri[0],vertices=tri[1])
            elif canonical(q) in finite_can:rec.update(label='NMA',certificate='finite_closed_class')
            else:
                obstruction=proper_obstruction(q,depth=4)
                if obstruction:rec.update(label='NMA',certificate='proper_order',proper_certificate=obstruction)
                else:rec.update(label='UNRESOLVED',certificate=None)
            breakdown[(c,rec['certificate'])]+=1
        counts[(c,rec['label'])]+=1;records.append(rec)
    out={'labelled_inputs':5**6,'equivalence':'vertex relabelling only (S4); neither mutation nor arrow reversal is quotiented out','representatives':len(reps),'counts':{str(k):v for k,v in counts.items()},'negative_breakdown':{str(k):v for k,v in breakdown.items()},'records':records}
    path=ROOT/'experiments/census.json';path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='records'},indent=2),flush=True)
    assert counts[(True,'MA')]==534 and counts[(False,'MA')]==27
    assert counts[(True,'NMA')]==133 and counts[(False,'NMA')]==1
    assert not any(r['label']=='UNRESOLVED' for r in records)
if __name__=='__main__':main()
