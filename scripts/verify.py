"""Independent finite certificate replay and regression checks (standard library).
The matrix mutation, acyclicity, relabelling, proper-order and transport routines
below do not call the production implementation. Finite/range checks are not
substitutes for the universal mathematical lemmas in the paper.
"""
import itertools as it
import json,sys,random,hashlib
from pathlib import Path
from collections import Counter
ROOT=Path(__file__).resolve().parents[1]
PERMS=list(it.permutations(range(4))); ORD=[p for p in PERMS if p[0]==0]
PAIRS=list(it.combinations(range(4),2))
def dense(q):
 b=[[0]*4 for _ in range(4)]
 for (i,j),v in zip(PAIRS,q):b[i][j]=v;b[j][i]=-v
 return b
def six(b):return tuple(b[i][j] for i,j in PAIRS)
def mut(q,k):
 b=dense(q)
 return six([[-b[i][j] if i==k or j==k else b[i][j]+(abs(b[i][k])*b[k][j]+b[i][k]*abs(b[k][j]))//2 for j in range(4)] for i in range(4)])
def word(q,w):
 for k in w:q=mut(q,k)
 return q
def rel(q,p):
 b=dense(q);return tuple(b[p[i]][p[j]] for i,j in PAIRS)
def canon(q):return min(rel(q,p) for p in PERMS)
def acyclic(q):return any(all(x>=0 for x in rel(q,p)) for p in PERMS)
def connected(q):
 b=dense(q);reach={0}
 for _ in range(3):reach|={j for i in list(reach) for j in range(4) if b[i][j]}
 return len(reach)==4
def pf(q):a,b,c,d,e,f=q;return a*f-b*e+c*d
def sc(q):a,b,c,d,e,f=q;return a*a+b*b+c*c+d*d+e*e+f*f+a*b*d+a*c*e+b*c*f+d*e*f+a*c*d*f
def norm(s):i=s.index(0);return tuple(s[i:]+s[:i])
def proper(q,s,k):
 b=dense(q);cycle=s+s
 start=s.index(k);after=cycle[start+1:start+4]
 return all(after.index(j)<after.index(i) for i in after for j in after if b[i][k]>0 and b[k][j]>0)
def classes(q):
 b=dense(q);parts=[{s} for s in ORD]
 for s in ORD:
  for i in range(4):
   j=(i+1)%4
   if b[s[i]][s[j]]==0:
    t=list(s);t[i],t[j]=t[j],t[i];t=norm(t)
    left=next(c for c in parts if s in c);right=next(c for c in parts if t in c)
    if left is not right:left.update(right);parts.remove(right)
 return {frozenset(c) for c in parts}
def isproper(q,c):return all(any(proper(q,s,k) for s in c) for k in range(4))
def pcl(q):return {c for c in classes(q) if isproper(q,c)}
def transport(q,c,k):
 b=dense(q);targets=set();new=mut(q,k);parts=classes(new)
 for s in c:
  if not proper(q,s,k):continue
  n=s.index(k);remaining=s[n+1:]+s[:n]
  for cut in range(4):
   if all(b[k][v]>=0 for v in remaining[:cut]) and all(b[k][v]<=0 for v in remaining[cut:]):
    t=norm(remaining[:cut]+(k,)+remaining[cut:]);targets.add(next(p for p in parts if t in p))
 assert len(targets)==1,(q,c,k,targets)
 return new,targets.pop()
def triangle(q,vs):
 b=dense(q);i,j,k=vs;x,y,z=b[i][j],b[j][k],b[k][i]
 return min(x,y,z)>=2 and x*x+y*y+z*z-x*y*z<=4 or max(x,y,z)<=-2 and x*x+y*y+z*z+x*y*z<=4
def negative_proper(q,cert):
 initials=pcl(q)
 if cert['reason']=='no_proper_class':assert not initials;return
 assert {frozenset(tuple(s) for s in x['initial_class']) for x in cert['classes']}==initials
 for x in cert['classes']:
  state=q;c=frozenset(tuple(s) for s in x['initial_class'])
  for k in x['word']:assert isproper(state,c);state,c=transport(state,c,k)
  assert state==tuple(x['endpoint']);m=sc(rel(state,min(c)));p=abs(pf(state));assert m==x['scalar']
  why=x['reason']
  if why=='improper_transport':assert not isproper(state,c)
  elif why=='endpoint_inequality':assert m<0 or m<2*p or connected(state) and (m<3 or m<=2*p)
  elif why=='finite_endpoint_exclusion':assert (m,p*p) in ((11,16),(18,49))
  else:raise AssertionError(why)
def orbit(seed):
 states={seed};todo=[seed]
 while todo:
  q=todo.pop()
  for k in range(4):
   r=mut(q,k)
   if r not in states:states.add(r);todo.append(r)
  assert len(states)<=24
 assert len(states)==24 and not any(map(acyclic,states))
 return states

def main():
 report={};census=json.loads((ROOT/'experiments/census.json').read_text());records=census['records']
 reps={canon(q) for q in it.product(range(-2,3),repeat=6)}
 assert len(reps)==695 and reps=={tuple(r['tuple']) for r in records}
 orb=orbit((-2,1,1,-1,-1,-1));orbcan={canon(q) for q in orb}
 counts=Counter();breakdown=Counter();lengths=Counter()
 for r in records:
  q=tuple(r['tuple']);assert connected(q)==r['connected'];counts[(r['connected'],r['label'])]+=1
  if r['label']=='MA':
   w=r['witness'];assert len(w)<=3 and acyclic(word(q,w));lengths[len(w)]+=1
   assert all(max(map(abs,word(q,w[:i])))<=2 for i in range(len(w)+1))
  else:
   assert r['label']=='NMA';breakdown[(r['connected'],r['certificate'])]+=1
   if r['certificate']=='rank_three':assert triangle(word(q,r['triangle_word']),r['vertices'])
   elif r['certificate']=='finite_closed_class':assert canon(q) in orbcan
   elif r['certificate']=='proper_order':negative_proper(q,r['proper_certificate'])
   else:raise AssertionError(r)
 assert dict(counts)=={(True,'MA'):534,(True,'NMA'):133,(False,'MA'):27,(False,'NMA'):1}
 report['census']={'counts':{str(k):v for k,v in counts.items()},'negative_partition':{str(k):v for k,v in breakdown.items()},'positive_lengths':dict(lengths),'all_695_certificates_replayed':True}
 for m,d in ((11,16),(18,49)):
  n=int(m**.5)+1;assert not any(sc(q)==m and pf(q)**2==d for q in it.product(range(n),repeat=6))
 report['finite_exclusions']={'11_16':4**6,'18_49':5**6}
 K=[(-2,0,1,0,-1,-1),(-1,-1,0,-1,1,-1),(-1,-1,0,0,-1,1),(-2,0,0,0,0,-1)]
 table=[[(0,1,'1023'),(0,1,'1023'),(0,-1,'1023'),(1,-1,'2031')],[(1,-1,'0213'),(0,-1,'1302'),(1,-1,'1023'),(2,1,'0123')],[(2,-1,'0213'),(1,-1,'2301'),(2,1,'1302'),(1,1,'0123')],[(3,-1,'0132'),(3,-1,'0132'),(3,1,'0132'),(3,1,'0132')]]
 for i in range(4):
  for k,(j,s,p) in enumerate(table[i]):assert mut(K[i],k)==tuple(s*x for x in rel(K[j],tuple(map(int,p)))),(i,k)
 core={tuple(s*x for x in rel(q,p)) for q in K for s in (-1,1) for p in PERMS}
 endpoints=[q for q in it.product(range(3),repeat=6) if sc(q)==5 and pf(q)**2==4]
 assert all(q in core for q in endpoints)
 report['equal_wall_core']={'topological_inputs_checked':3**6,'matching_endpoints':len(endpoints),'signed_labelled_core_states':len(core),'printed_transitions_checked':16}
 s1=(-2,-1,-1,1,-1,1);s3=(-2,1,-1,1,1,1)
 assert not pcl(s1) and not pcl(s3)
 report['proper_seed_table']={str(s):[[k for k in range(4) if proper(q,s,k)] for q in (s1,s3)] for s in ORD}
 box=(-2,0,2,-2,0,-2);child=mut(box,0);assert len(pcl(child))==1 and all(sc(rel(child,s))==0 for c in pcl(child) for s in c)
 line=lambda t:(-2,t+2,t,-t,2-t,0)
 for t in range(-100,501):
  if t<0:assert acyclic(line(t))
  else:assert word(line(t),(0,1))==line(t+4)
  if t>=0 and t%2==0:assert acyclic(word(line(t),[1,0]*(t//4)+([1] if t%4 else [])))
 assert word(s1,(0,1))==line(1) and word(line(3),(1,0))==s3
 for x,y,z,u,v in it.product(range(1,5),repeat=5):
  q=(0,-x,y,-z,-u,-v);assert len(pcl(q))==1
  if x*y<=v:assert acyclic(mut(q,0))
  else:
   child,c=transport(q,next(iter(pcl(q))),0);assert c==frozenset({(0,2,1,3)}) and not isproper(child,c)
 rng=random.Random(20261009)
 for _ in range(2000):
  q=(rng.choice((-1,1)),)+tuple(rng.randint(-20,20) for _ in range(5))
  assert word(q,(0,1,0,1,0))==rel(q,(1,0,2,3))
 # All printed A and I trajectory identities, including their endpoint frames.
 for F in range(4,25):
  for c in range(1,F):
   q=(1,-2,c,1,0,F-2*c)
   words=['0','01','012','0120','01202','1','10','102']
   tuples=[(-1,2,-c,-1,0,F),(1,1,-c,1,0,F),(1,-1,F-c,-1,F,-F),(-1,1,c-F,-2,F,-c),(1,-1,c-F,2,F-2*c,c),(-1,-1,c,-1,0,F-2*c),(1,1,-c,-1,c,F-c),(2,-1,F-2*c,1,c,c-F)]
   for w,target in zip(words,tuples):assert word(q,map(int,w))==target
   assert word(q,(1,0,2))==rel(word(q,(0,1,2,0,2)),(1,2,0,3))
  for t,u in it.product(range(1,F),repeat=2):
   q=(1,-1,-t,2,t-F,F-u);end=(1,-2,F-u,1,u,t-F)
   assert rel(word(q,(0,1,2)),(1,2,0,3))==end
   if t==u:continue
   w=(1,0,2,1,2) if t>u else (2,0,2,1,0)
   assert word(q,w)==end
   assert all(max(map(abs,word(q,w[:i])))<F for i in range(6))
 # Exact root-cell and equal-wall transition formulas, checked on a stated range.
 for t in range(2,8):
  for F in range(t*t+5,t*t+10):
   q=F-t;C0=(1,-1,-t,2,-q,q);C1=(-1,1,t,1,-F,q)
   assert mut(C0,0)==C1
   for k in (1,2):assert mut(C0,k)==rel(C0,(0,2,1,3))
   assert mut(C1,1)==tuple(-x for x in rel(C1,(2,1,0,3)))
   assert mut(C1,2)==tuple(-x for x in rel(C1,(1,0,2,3)))
   R0=(q,-t,-q,1+t*q,q*q-2,1);R1=(F,-q,-t,F*q-1,t*F-1,1)
   assert mut(C0,3)==rel(R0,(2,3,1,0)) and mut(C1,3)==tuple(-x for x in rel(R1,(3,1,2,0)))
 for A,D,E in it.product(range(2,5),repeat=3):
  for B in range(max(A,D)+1,max(A,D)+4):
   for C in range(max(A,E)+1,max(A,E)+4):
    R=(A,-D,-E,B,C,1);h=B*D-A;j=C*E-A;l=B*(D+E)+C*E-A
    W=(-h,D,-E,-B,B+C,-1);U=(-l,D,E,C,-B-C,1);Up=(-l,-D,D+E,-C,-B,-1);Wp=(-j,E,-D-E,-C,B,1)
    for state,k,target in [(R,2,W),(W,3,U),(U,2,Up),(Up,3,Wp),(Wp,2,rel(R,(0,1,3,2)))]:assert mut(state,k)==target
    newroots=[(A,-B,-C,A*B-D,A*C-E,1),(l,-D,-E,l*D+C,l*E-B-C,1),(l,-C,-B,D+l*C,l*B-D-E,1)]
    assert mut(R,1)==rel(newroots[0],(1,0,2,3))
    assert mut(U,0)==newroots[1]
    assert mut(Up,1)==tuple(-x for x in rel(newroots[2],(1,0,2,3)))
    for q in newroots:
     aa,dd,ee,bb,cc,ff=q
     assert min(aa,-dd,-ee)>=2 and bb>max(aa,-dd) and cc>max(aa,-ee) and ff==1
    for state,k,sgn,p in [(W,0,1,'0213'),(W,1,-1,'1203'),(U,1,-1,'1320'),(Up,0,1,'0321'),(Wp,0,1,'0213'),(Wp,1,-1,'1203')]:
     a,b,c,d,e,f=(sgn*x for x in rel(mut(state,k),tuple(map(int,p))))
     assert min(-a,b,c,f)>=2 and -d>max(-a,b) and -e>max(-a,c)
 report['identity_ranges']={'line':[-100,500],'five_parameter_each':[1,4],'pentagon_random_cases':2000,'A_I_F':[4,24],'root_A_D_E':[2,4],'root_B_C_offsets':[1,3],'scope':'regression evidence only; not universal proof'}
 # Production API and saved experimental witnesses; use imports only after certificates.
 sys.path.insert(0,str(ROOT));from algorithm import classifier as impl
 for q in it.product(range(-1,2),repeat=6):
  for k in range(4):assert impl.mutate(q,k)==mut(q,k) and pf(mut(q,k))==-pf(q)
  assert impl.acyclic(q)==acyclic(q)
 for bad in ([[0]*4]*3,[[1]*4]*4,[[False]*4]*4,[[0.,0,0,0]]*4):
  try:impl.classify(bad);raise AssertionError('invalid input accepted')
  except ValueError:pass
 limit=impl.analyze_tuple(s1,shortcuts=False,max_states=1);assert limit.label=='UNKNOWN'
 try:impl.classify(impl.adjacency(s1),shortcuts=False,max_states=1);raise AssertionError('cap not raised')
 except impl.ResourceLimit:pass
 raw=[json.loads(l) for l in (ROOT/'experiments/raw.jsonl').read_text().splitlines()];inputs={r['id']:r for r in json.loads((ROOT/'experiments/inputs.json').read_text())}
 assert len(raw)==384
 labels={}
 for r in raw:
  q=tuple(inputs[r['id']]['tuple']);assert r['H']==sum(map(abs,q))+sum(abs(sc(rel(q,s))) for s in ORD)
  assert r['state_bound']==(2*r['H']+1)**6
  if r['label']=='MA':assert acyclic(word(q,r['witness']))
  if r['label']!='UNKNOWN':labels.setdefault(r['id'],set()).add(r['label'])
 assert all(len(v)==1 for v in labels.values())
 report['benchmark']={'rows':len(raw),'all_MA_witnesses_replayed':True,'completed_labels_agree':True,'production_sha256':hashlib.sha256((ROOT/'algorithm/classifier.py').read_bytes()).hexdigest()}
 report['status']='PASS';(ROOT/'docs/checks/python_verification.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
