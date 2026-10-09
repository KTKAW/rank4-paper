"""Independent Python checks of the explicit computations in main.pdf (8 Oct 2026 draft).
Run: python3 -I review_checks_main.py   (about 5 minutes; the disconnected scan is the slow part).
Box searches use the height budget H(B) of Theorem 7.1 as the search radius, so NMA verdicts
from box_search rely on that theorem; everything else is elementary arithmetic.
"""
import itertools, sys, time
from fractions import Fraction
sys.setrecursionlimit(10000)
# upper coords (b01,b02,b03,b12,b13,b23)
IDX=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
def mat(q):
    B=[[0]*4 for _ in range(4)]
    for (i,j),v in zip(IDX,q):
        B[i][j]=v; B[j][i]=-v
    return B
def up(B): return tuple(B[i][j] for i,j in IDX)
def pp(x): return max(x,0)
def mutate(B,k):
    C=[[0]*4 for _ in range(4)]
    for i in range(4):
        for j in range(4):
            if i==k or j==k: C[i][j]=-B[i][j]
            else: C[i][j]=B[i][j]+pp(B[i][k])*pp(B[k][j])-pp(-B[i][k])*pp(-B[k][j])
    return C
def word(q,w):
    B=mat(q)
    for k in w: B=mutate(B,k)
    return up(B)
def acyclic(q):
    B=mat(q)
    indeg=[0]*4
    for i in range(4):
        for j in range(4):
            if B[i][j]>0: indeg[j]+=1
    S=[v for v in range(4) if indeg[v]==0]; seen=0
    while S:
        v=S.pop(); seen+=1
        for j in range(4):
            if B[v][j]>0:
                indeg[j]-=1
                if indeg[j]==0: S.append(j)
    return seen==4
def rank_ok(q,r):
    B=mat(q)
    return all(not(B[i][j]>0) or r[i]<r[j] for i in range(4) for j in range(4))
def topo_ok(q,order):
    # order = sequence of vertices; need b_ij>0 => i before j
    pos={v:n for n,v in enumerate(order)}
    return rank_ok(q,[pos[v] for v in range(4)])
def markov(q):
    a,b,c,d,e,f=q
    return a*a+b*b+c*c+d*d+e*e+f*f+a*b*d+a*c*e+b*c*f+d*e*f+a*c*d*f
def pf(q):
    a,b,c,d,e,f=q
    return a*f-b*e+c*d
ORDERS=[(0,1,2,3),(0,1,3,2),(0,2,1,3),(0,2,3,1),(0,3,1,2),(0,3,2,1)]
def relabel(q,s):
    B=mat(q)
    return tuple(B[s[i]][s[j]] for i,j in IDX)
def Ms(q,s): return markov(relabel(q,s))
def H(q): return sum(abs(x) for x in q)+sum(abs(Ms(q,s)) for s in ORDERS)
def height(q): return max(abs(x) for x in q)
def box_search(q,T=None,cap=5_000_000):
    """BFS inside height<=T (default H(q)) on labeled states. Returns (label, nstates, witness or None)."""
    if T is None: T=H(q)
    start=tuple(q); seen={start:None}; frontier=[start]
    if acyclic(start): return ('MA',1,[])
    while frontier:
        nxt=[]
        for s in frontier:
            for k in range(4):
                t=up(mutate(mat(s),k))
                if t in seen or height(t)>T: continue
                seen[t]=(s,k)
                if acyclic(t):
                    w=[]; cur=t
                    while seen[cur] is not None:
                        p,kk=seen[cur]; w.append(kk); cur=p
                    return ('MA',len(seen),w[::-1])
                nxt.append(t)
                if len(seen)>cap: return ('UNKNOWN',len(seen),None)
        frontier=nxt
    return ('NMA',len(seen),None)
def min_word_len(q,maxlen=12):
    # BFS on labeled states without height restriction up to depth maxlen
    start=tuple(q)
    if acyclic(start): return 0
    seen={start}; frontier=[start]
    for d in range(1,maxlen+1):
        nxt=[]
        for s in frontier:
            for k in range(4):
                t=up(mutate(mat(s),k))
                if t in seen: continue
                seen.add(t)
                if acyclic(t): return d
                nxt.append(t)
        frontier=nxt
    return None
def connected(q):
    B=mat(q); seen={0}; st=[0]
    while st:
        v=st.pop()
        for j in range(4):
            if B[v][j]!=0 and j not in seen: seen.add(j); st.append(j)
    return len(seen)==4
def proper_vertex(q,s,v):
    B=mat(q); pos={x:n for n,x in enumerate(s)}
    for u in range(4):
        for w in range(4):
            if u!=v and w!=v and u!=w and B[u][v]>0 and B[v][w]>0:
                # (u,v,w) must be cyclically ordered in s: going from u, v comes before w
                du=(pos[v]-pos[u])%4; dw=(pos[w]-pos[u])%4
                if not (du<dw): return False
    return True
def wiggle_class(q,s):
    B=mat(q); cls={s}; st=[s]
    while st:
        o=st.pop()
        for i in range(4):
            a,b=o[i],o[(i+1)%4]
            if B[a][b]==0:
                lst=list(o); lst[i],lst[(i+1)%4]=b,a
                # normalize rotation so starts with 0
                t=tuple(lst); r=t.index(0); t=t[r:]+t[:r]
                if t not in cls: cls.add(t); st.append(t)
    return frozenset(cls)
def proper_classes(q):
    res=set()
    for s in ORDERS:
        cls=wiggle_class(q,s)
        if all(any(proper_vertex(q,o,v) for o in cls) for v in range(4)):
            res.add(cls)
    return res


def qline(t): return (-2,t+2,t,-t,2-t,0)
print("=== Lemma 3.1: mu[0,1] q(t) = q(t+4) for t>=0")
print("violations t in 0..60:",[t for t in range(0,61) if word(qline(t),[0,1])!=qline(t+4)])
print("mu0 q(t), t=0..4:",[word(qline(t),[0]) for t in range(5)]," paper: (2,-t-2,-t,t+4,t+2,0)")
print("t<0 recurrence holds?",[(t, word(qline(t),[0,1])==qline(t+4)) for t in range(-6,0)])
print("=== Lemma 3.3")
print("q(0)",qline(0),"acyclic",acyclic(qline(0)),"ranks(1,0,2,2)",rank_ok(qline(0),(1,0,2,2)))
m=word(qline(2),[1]); print("mu1 q(2)=",m,"acyclic",acyclic(m),"ranks(0,1,2,1)",rank_ok(m,(0,1,2,1)))
s1=(-2,-1,-1,1,-1,1); s3=(-2,1,-1,1,1,1)
for name,s in [("s1",s1),("s3",s3)]:
    words=[w for L in range(4) for w in itertools.product(range(4),repeat=L)]
    print(name,"#words<=3:",len(words),"acyclic endpoint within 3?",any(acyclic(word(s,w)) for w in words))
    print(name,"proper classes:",proper_classes(s))
print("mu[0,1] s1 =",word(s1,[0,1]),"== q(1):",word(s1,[0,1])==qline(1))
print("mu[1,0] q(3)=",word(qline(3),[1,0]),"== s3:",word(qline(3),[1,0])==s3)
print("=== Theorem 3.4 negative t")
print("t<=-2 ranks (2,0,1,1):",all(rank_ok(qline(t),(2,0,1,1)) for t in range(-40,-1)))
print("t=-1 ranks (2,0,3,1):",rank_ok(qline(-1),(2,0,3,1)))
print("connected t in -5..20:",all(connected(qline(t)) for t in range(-5,21)))
print("min acyclicizing length q(4n) n=0..5 (depth<=12):",[min_word_len(qline(4*n),12) for n in range(6)])
print("min acyclicizing length q(4n+2) n=0..5:",[min_word_len(qline(4*n+2),12) for n in range(6)])
sys.stdout.flush()
for name,q in [("s1",s1),("s3",s3),("q(1)",qline(1)),("q(3)",qline(3))]:
    t0=time.time(); r=box_search(q,cap=3_000_000); print(name,"box search within H=",H(q),":",r[:2],"time",round(time.time()-t0,1)); sys.stdout.flush()

print("=== Prop 5.1 disconnected criterion vs independent box search, entries in [-3,3], disconnected only")
def T(x,y,z):
    return (x>=2 and y>=2 and z>=2 and x*x+y*y+z*z-x*y*z<=4) or (-x>=2 and -y>=2 and -z>=2 and x*x+y*y+z*z+x*y*z<=4)
def T4(q):
    a,b,c,d,e,f=q
    return T(a,d,-b) or T(a,e,-c) or T(b,f,-c) or T(d,f,-e)
cnt=0; bad=[]
rng=range(-3,4)
for q in itertools.product(rng,repeat=6):
    if connected(q): continue
    cnt+=1
    lab=box_search(q,cap=200000)[0]
    if lab=='UNKNOWN': bad.append((q,'unknown')); continue
    if (lab=='NMA')!=T4(q): bad.append((q,lab,T4(q)))
print("disconnected inputs checked:",cnt,"mismatches:",bad[:10],len(bad))
print("example (-2,1,1,-1,-1,-1): connected?",connected((-2,1,1,-1,-1,-1)),"T4:",T4((-2,1,1,-1,-1,-1)),"box:",box_search((-2,1,1,-1,-1,-1))[:2])
# closed set of 24 states?
q0=(-2,1,1,-1,-1,-1); seen={q0}; st=[q0]
while st:
    s=st.pop()
    for k in range(4):
        t=up(mutate(mat(s),k))
        if t not in seen: seen.add(t); st.append(t)
    if len(seen)>1000: break
print("  full labeled mutation class size (if finite):",len(seen),"all cyclic:",all(not acyclic(s) for s in seen))
sys.stdout.flush()
print("=== Prop 5.2: MA(0,-x,y,-z,-u,-v) <=> xy<=v, x,y,z,u,v in 1..4")
bad=[];n=0
for x,y,z,u,v in itertools.product(range(1,5),repeat=5):
    q=(0,-x,y,-z,-u,-v); n+=1
    r=box_search(q,cap=400000); lab=r[0]
    if lab=='UNKNOWN': bad.append((q,'unknown')); continue
    if (lab=='MA')!=(x*y<=v): bad.append((q,lab,x*y<=v))
print("checked",n,"mismatches",bad[:10],len(bad))
m=word((0,-2,1,-1,-1,-3),[0]); print("mu0 (0,-2,1,-1,-1,-3) =",m,"paper formula (0,x,-y,-z,-u,xy-v)=",(0,2,-1,-1,-1,2-3))
print("topological order (3,0,2,1) valid when xy<=v? sample:",all(topo_ok(word((0,-x,y,-z,-u,-v),[0]),(3,0,2,1)) for x,y,z,u,v in itertools.product(range(1,5),repeat=5) if x*y<=v))
sys.stdout.flush()
print("=== Prop 5.3")


# symbolic check via sampling (sign conditions): b>=0,c,d>=1,d(c-1)<=b
bad=[]
for bb in range(0,8):
    for cc in range(1,6):
        for dd in range(1,6):
            if dd*(cc-1)<=bb:
                q=(-1,-bb,cc,dd,-1,0); r=word(q,[1,3]); exp=(1,dd*(cc-1)-bb,1-cc,0,-1,dd)
                if r!=exp or not topo_ok(r,(2,3,0,1)) or acyclic(q): bad.append((q,r,exp,topo_ok(r,(2,3,0,1)),acyclic(q)))
print("Prop 5.3 mismatches:",bad[:5],len(bad))
print("=== Prop 5.4")
bad=[];n=0
for a,bb,cc,dd,ee,ff in itertools.product(range(-4,5),repeat=6):
    if a<0 and cc>0 and ee>0 and ff<0 and bb-cc*ff<=0 and dd-ee*ff<=0:
        n+=1; q=(a,bb,cc,dd,ee,ff); r=word(q,[3]); exp=(a,bb-cc*ff,-cc,dd-ee*ff,-ee,-ff)
        if r!=exp or not topo_ok(r,(2,3,1,0)): bad.append((q,r,exp))
print("Prop 5.4 checked",n,"mismatches",bad[:5],len(bad))
print("=== Remark 6.1")
q=(0,-1,0,1,0,0); print("M=",markov(q),"mu2=",word(q,[2]),"M(mu2)=",markov(word(q,[2])))
print("=== Prop 6.2 example (0,0,2,-3,1,-1)")
q=(0,0,2,-3,1,-1); print("connected",connected(q),"P=",pf(q),"2|P|=",2*abs(pf(q)),"Ms=",[Ms(q,s) for s in ORDERS],"proper classes:",[sorted(c) for c in proper_classes(q)])
print("  M for proper orders:",[(sorted(c),[Ms(q,s) for s in sorted(c)]) for c in proper_classes(q)])
print("  box search:",box_search(q,cap=2000000)[:2])
print("=== 6.2 endpoint exclusions (M,P^2)=(11,16),(18,49): scan nonneg endpoints with entries<=floor(sqrt(m))")
for m,p2 in [(11,16),(18,49)]:
    r=int(m**0.5); found=[]
    for q in itertools.product(range(0,r+1),repeat=6):
        if markov(q)==m and pf(q)**2==p2: found.append(q)
    print(f"  (M,P^2)=({m},{p2}): endpoints found:",found)
print("  sanity: can M=m with some coordinate > floor(sqrt(m))? all terms nonneg for nonneg q:",all(markov(q)>=max(q)**2 for q in itertools.product(range(0,5),repeat=6)))
print("=== Prop 6.3")
for q in [(1,1,1,2,1,1),(-2,1,1,-1,-1,-1)]: print(q,"P=",pf(q),"acyclic:",acyclic(q))
print("=== 6.1 endpoint inequality: brute check over nonneg q in [0,4]^6: 2|P|<=M, and M>2|P| when connected")
viol=[q for q in itertools.product(range(0,5),repeat=6) if not (2*abs(pf(q))<=markov(q)) or (connected(q) and not markov(q)>2*abs(pf(q)))]
print("violations:",viol[:5],len(viol))
print("=== 7.1 example (-2,-1,1,-1,2,-1): mu2 =",word((-2,-1,1,-1,2,-1),[2]),"acyclic:",acyclic(word((-2,-1,1,-1,2,-1),[2])))
print("=== Section 7 H and N for examples:",[(q,H(q)) for q in [(0,0,0,0,0,0),(-1,0,1,-1,0,-1),(-2,1,1,-1,-1,-1)]])
