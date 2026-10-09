"""Exact four-vertex quiver classification. Python is independently tested, not extracted Lean.

Input adjacency: nonnegative integer 4x4, zero diagonal, no directed 2-cycles.
Signed API: analyze_tuple((b01,b02,b03,b12,b13,b23)). Positive bij means i -> j.
A resource cap raises ResourceLimit (simple API), or returns UNKNOWN (diagnostic API).
"""
from collections import deque
from dataclasses import dataclass, asdict
from itertools import permutations, combinations, product
from math import isqrt
import argparse
import json
import time

PAIRS = ((0,1),(0,2),(0,3),(1,2),(1,3),(2,3))
ORDERS = tuple((0,)+p for p in permutations((1,2,3)))
PERMS = tuple(permutations(range(4)))

def validate_tuple(q):
    if not isinstance(q,(tuple,list)) or len(q)!=6 or any(type(x) is not int for x in q):
        raise ValueError('Expected six exact Python integers; floats and booleans are rejected.')
    return tuple(q)

def matrix(q):
    b = [[0]*4 for _ in range(4)]
    for (i,j),x in zip(PAIRS,q): b[i][j],b[j][i]=x,-x
    return b

def from_adjacency(a):
    if not isinstance(a,(list,tuple)) or len(a)!=4 or any(not isinstance(r,(list,tuple)) or len(r)!=4 for r in a):
        raise ValueError('Expected a 4 by 4 directed adjacency matrix.')
    if any(type(x) is not int or x<0 for r in a for x in r):
        raise ValueError('Adjacency entries must be nonnegative exact integers.')
    if any(a[i][i]!=0 for i in range(4)) or any(a[i][j] and a[j][i] for i,j in PAIRS):
        raise ValueError('Loops and directed 2-cycles are not permitted.')
    return tuple(a[i][j]-a[j][i] for i,j in PAIRS)

def from_exchange(b):
    if not isinstance(b,(list,tuple)) or len(b)!=4 or any(not isinstance(r,(list,tuple)) or len(r)!=4 for r in b):
        raise ValueError('Expected a 4 by 4 exchange matrix.')
    if any(type(x) is not int for r in b for x in r) or any(b[i][j]!=-b[j][i] for i in range(4) for j in range(4)):
        raise ValueError('Exchange matrix must be integral and skew-symmetric.')
    return tuple(b[i][j] for i,j in PAIRS)

def adjacency(q):
    b=matrix(q)
    return [[max(x,0) for x in row] for row in b]

def mutate(q,k):
    b=matrix(q)
    return tuple(-b[i][j] if k in (i,j) else b[i][j]+max(b[i][k],0)*max(b[k][j],0)-max(-b[i][k],0)*max(-b[k][j],0) for i,j in PAIRS)

def apply_word(q,w):
    for k in w: q=mutate(q,k)
    return q

def topological_order(q):
    b=matrix(q); remaining=set(range(4)); order=[]
    while remaining:
        v=next((v for v in sorted(remaining) if all(b[u][v]<=0 for u in remaining)),None)
        if v is None: return None
        remaining.remove(v);order.append(v)
    return tuple(order)

def acyclic(q): return topological_order(q) is not None

def connected(q):
    b=matrix(q);seen={0};todo=[0]
    while todo:
        i=todo.pop()
        for j in range(4):
            if b[i][j] and j not in seen: seen.add(j);todo.append(j)
    return len(seen)==4

def relabel(q,p):
    b=matrix(q);return tuple(b[p[i]][p[j]] for i,j in PAIRS)

def canonical(q): return min(relabel(q,p) for p in PERMS)
def pfaffian(q):
    a,b,c,d,e,f=q;return a*f-b*e+c*d

def scalar(q):
    a,b,c,d,e,f=q
    return sum(x*x for x in q)+a*b*d+a*c*e+b*c*f+d*e*f+a*c*d*f

def height(q): return max(map(abs,q))
def height_bound(q): return sum(map(abs,q))+sum(abs(scalar(relabel(q,s))) for s in ORDERS)
def line(t): return (-2,t+2,t,-t,2-t,0)

def triangle_nma(x,y,z):
    return (min(x,y,z)>=2 and x*x+y*y+z*z-x*y*z<=4) or (max(x,y,z)<=-2 and x*x+y*y+z*z+x*y*z<=4)

def triangle_obstruction(q):
    b=matrix(q)
    return next((ijk for ijk in combinations(range(4),3) if triangle_nma(b[ijk[0]][ijk[1]],b[ijk[1]][ijk[2]],b[ijk[2]][ijk[0]])),None)

def normalize_order(p):
    i=p.index(0);return tuple(p[i:]+p[:i])

def proper_vertices(q,s):
    b=matrix(q);pos={v:i for i,v in enumerate(s)}
    return frozenset(k for k in range(4) if all((pos[k]-pos[i])%4<(pos[j]-pos[i])%4 for i in range(4) for j in range(4) if b[i][k]>0 and b[k][j]>0))

def wiggle_classes(q):
    b=matrix(q);left=set(ORDERS);classes=[]
    while left:
        seed=min(left);left.remove(seed);component={seed};todo=[seed]
        while todo:
            s=todo.pop()
            for i in range(4):
                j=(i+1)%4
                if b[s[i]][s[j]]==0:
                    t=list(s);t[i],t[j]=t[j],t[i];t=normalize_order(t)
                    if t not in component:
                        component.add(t);left.discard(t);todo.append(t)
        classes.append(tuple(sorted(component)))
    return tuple(classes)

def proper_classes(q):
    return tuple(c for c in wiggle_classes(q) if set().union(*(proper_vertices(q,s) for s in c))==set(range(4)))

def proper_mutate(q,cl,k):
    """Move k clockwise past all old outgoing neighbours, before incoming ones."""
    b=matrix(q)
    for s in cl:
        if k not in proper_vertices(q,s): continue
        n=s.index(k);rest=list(s[n+1:]+s[:n])
        for cut in range(4):
            if all((b[k][v]<=0 if i>=cut else b[k][v]>=0) for i,v in enumerate(rest)):
                t=normalize_order(rest[:cut]+[k]+rest[cut:])
                new=mutate(q,k)
                target=next(c for c in wiggle_classes(new) if t in c)
                return new,target
    raise ValueError('Mutation requires a proper vertex in the supplied class.')

def scalar_rejection(q,cl):
    m=scalar(relabel(q,cl[0]));p=abs(pfaffian(q))
    if m<0 or m<2*p or (connected(q) and (m<3 or m<=2*p)): return 'endpoint_inequality'
    if (m,p*p) in ((11,16),(18,49)): return 'finite_endpoint_exclusion'
    return None

def proper_obstruction(q,depth=1):
    """Sound partial test: reject every candidate total-proper class by a finite path."""
    classes=proper_classes(q)
    if not classes:return {'reason':'no_proper_class','classes':[]}
    cert=[]
    for cl in classes:
        todo=deque([(q,cl,())]);seen={(q,cl)};failure=None
        while todo and failure is None:
            state,c,w=todo.popleft();why=scalar_rejection(state,c)
            if c not in proper_classes(state): why='improper_transport'
            if why:
                failure={'initial_class':cl,'word':w,'reason':why,'endpoint':state,'scalar':scalar(relabel(state,c[0]))};break
            if len(w)>=depth: continue
            for k in range(4):
                new,nc=proper_mutate(state,c,k)
                if (new,nc) not in seen:seen.add((new,nc));todo.append((new,nc,w+(k,)))
        if failure is None:return None
        cert.append(failure)
    return {'reason':'all_proper_classes_excluded','classes':cert}

def verify_witness(q,w):
    """Independent dense-matrix mutation formula and independent topological test."""
    b=matrix(validate_tuple(q))
    for k in w:
        if type(k) is not int or k not in range(4):return False
        old=[r[:] for r in b]
        for i in range(4):
            for j in range(4):
                b[i][j]=-old[i][j] if k in (i,j) else old[i][j]+(abs(old[i][k])*old[k][j]+old[i][k]*abs(old[k][j]))//2
    return any(all(b[p[i]][p[j]]>=0 for i,j in PAIRS) for p in PERMS)

@dataclass
class Result:
    label: str
    branch: str
    witness: object
    certificate: object
    elapsed_seconds: float
    states_discovered: int
    states_expanded: int
    mutation_evaluations: int
    witness_check_mutations: int
    H: int
    state_bound: int
    max_frontier: int

class ResourceLimit(RuntimeError):
    def __init__(self,result):
        super().__init__('Resource limit reached; classification is UNKNOWN, never NMA.')
        self.result=result

def analyze_tuple(q, *, shortcuts=True, max_states=None, timeout=None):
    q=validate_tuple(q)
    if max_states is not None and (type(max_states) is not int or max_states<1):raise ValueError('max_states must be a positive integer or None')
    if timeout is not None and (isinstance(timeout,bool) or not isinstance(timeout,(int,float)) or timeout<=0):raise ValueError('timeout must be positive or None')
    start=time.perf_counter();H=height_bound(q);N=(2*H+1)**6
    stats={'discovered':0,'expanded':0,'mutations':0,'frontier':0}
    def expired():return timeout is not None and time.perf_counter()-start>=timeout
    def mut(s,k):stats['mutations']+=1;return mutate(s,k)
    def finish(label,branch,w=None,cert=None):
        checked=0
        if label=='MA':
            if w is None or not verify_witness(q,w):raise AssertionError('Independent witness check failed')
            checked=len(w)
        return Result(label,branch,w,cert,time.perf_counter()-start,stats['discovered'],stats['expanded'],stats['mutations'],checked,H,N,stats['frontier'])
    if acyclic(q):return finish('MA','acyclic',[])
    if shortcuts:
        tri=triangle_obstruction(q)
        if tri:return finish('NMA','triangle',cert={'vertices':tri})
        if not connected(q):
            state=q;w=[]
            while not acyclic(state):
                if expired():return finish('UNKNOWN','timeout')
                candidates=[mut(state,k) for k in range(4)]
                k=min(range(4),key=lambda k:sum(map(abs,candidates[k])))
                if sum(map(abs,candidates[k]))>=sum(map(abs,state)):raise AssertionError('Rank-three descent stalled')
                state=candidates[k];w.append(k)
            return finish('MA','disconnected',w)
        if q==(-2,0,2,-2,0,-2):
            child=mut(q,0);cert=proper_obstruction(child,depth=0)
            assert cert is not None
            return finish('NMA','double_arrow_box',cert={'word':[0],'endpoint_certificate':cert})
        t=q[2]
        if q==line(t):
            if t%2:return finish('NMA','alternating_line',cert={'parameter':t})
            w=[];state=q
            for _ in range(t//4):
                if expired():return finish('UNKNOWN','timeout')
                for k in (1,0):state=mut(state,k);w.append(k)
            if t%4==2:state=mut(state,1);w.append(1)
            return finish('MA','alternating_line',w)
        a,b,c,d,e,f=q
        if a==0 and b<0 and c>0 and d<0 and e<0 and f<0:
            if (-b)*c<=-f:return finish('MA','five_parameter',[0])
            return finish('NMA','five_parameter',cert={'xy':(-b)*c,'v':-f})
        if a==-1 and b<=0 and c>=1 and d>=1 and e==-1 and f==0 and d*(c-1)<=-b:
            return finish('MA','product_cone',[1,3])
        if a<0 and c>0 and e>0 and f<0 and b<=c*f and d<=e*f:
            return finish('MA','quadratic_cone',[3])
        # The closed orbit certificate is verified by scripts/verify.py.
        if q in FINITE_ORBIT:return finish('NMA','finite_orbit',cert={'orbit_size':len(FINITE_ORBIT)})
        # Counter records exclude mutations used internally by proper_obstruction:
        # use a zero-depth scalar test here, so production counts remain exact.
        obstruction=proper_obstruction(q,depth=0)
        if obstruction:return finish('NMA','proper_order',cert=obstruction)
    # Deduplicated labelled BFS. Only states within the ORIGINAL height box enter.
    parents={q:None};todo=deque([q]);stats['discovered']=1;stats['frontier']=1
    while todo:
        if expired():return finish('UNKNOWN','timeout')
        state=todo.popleft();stats['expanded']+=1
        for k in range(4):
            child=mut(state,k)
            if height(child)>H or child in parents:continue
            if max_states is not None and len(parents)>=max_states:return finish('UNKNOWN','state_limit')
            parents[child]=(state,k);stats['discovered']+=1
            if acyclic(child):
                w=[];s=child
                while parents[s] is not None:s,k=parents[s];w.append(k)
                return finish('MA','bounded_bfs',list(reversed(w)))
            todo.append(child);stats['frontier']=max(stats['frontier'],len(todo))
    return finish('NMA','bounded_bfs',cert={'exhausted':True,'H':H,'reachable_states':len(parents)})

def classify(adjacency_matrix, **limits):
    r=analyze_tuple(from_adjacency(adjacency_matrix),**limits)
    if r.label=='UNKNOWN':raise ResourceLimit(r)
    return r.label

def analyze(adjacency_matrix,**options):return analyze_tuple(from_adjacency(adjacency_matrix),**options)

# Deterministically construct, then check, the independent finite mutation class.
def _finite_orbit():
    seed=(-2,1,1,-1,-1,-1);seen={seed};todo=[seed]
    while todo:
        q=todo.pop()
        if acyclic(q):raise AssertionError('Finite negative certificate contains acyclic state')
        for k in range(4):
            c=mutate(q,k)
            if c not in seen:seen.add(c);todo.append(c)
        if len(seen)>24:raise AssertionError('Finite certificate not closed in 24 states')
    assert len(seen)==24
    return frozenset(seen)
FINITE_ORBIT=_finite_orbit()

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('input',help='JSON matrix, or six-tuple with --format tuple')
    p.add_argument('--format',choices=['adjacency','exchange','tuple'],default='adjacency')
    p.add_argument('--max-states',type=int)
    p.add_argument('--timeout',type=float)
    p.add_argument('--no-shortcuts',action='store_true')
    a=p.parse_args();x=json.loads(a.input)
    q={'adjacency':from_adjacency,'exchange':from_exchange,'tuple':validate_tuple}[a.format](x)
    r=analyze_tuple(q,shortcuts=not a.no_shortcuts,max_states=a.max_states,timeout=a.timeout)
    print(json.dumps(asdict(r),indent=2))
    return 2 if r.label=='UNKNOWN' else 0
if __name__=='__main__':raise SystemExit(main())
