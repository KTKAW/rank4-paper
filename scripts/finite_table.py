"""Print a finite closed-class certificate using the independent matrix routines."""
from pathlib import Path
from verify import orbit,mut
ROOT=Path(__file__).resolve().parents[1]
states=sorted(orbit((-2,1,1,-1,-1,-1)));indices={q:i for i,q in enumerate(states)}
s=r'''\section{A finite negative certificate}\label{app:finite}
The following 24 labelled six-tuples form a closed mutation class. Row $i$ gives the four destination row indices under mutation at $0,1,2,3$. Each row has a directed cycle (equivalently, none of its 24 vertex permutations is entrywise nonnegative). Thus closure proves that every row is NMA, independently of the height theorem. In particular row '''+str(indices[(-2,1,1,-1,-1,-1)])+r''' is the determinant-$4$ example used in Proposition~\ref{prop:invariant}.
\begin{center}\small
\begin{tabular}{r rrrrrr rrrr}\toprule
& $a$&$b$&$c$&$d$&$e$&$f$&$\mu_0$&$\mu_1$&$\mu_2$&$\mu_3$\\\midrule
'''
for i,q in enumerate(states):s+=' & '.join(map(str,(i,)+q+tuple(indices[mut(q,k)] for k in range(4))))+r' \\'+'\n'
s+=r'''\bottomrule\end{tabular}\end{center}
There are only $24\cdot4=96$ mutation identities and $24\cdot24=576$ topological-order tests to replay. The independent checker regenerates this orbit from the seed and verifies both claims. Vertex relabelling identifies all of these states into the one finite negative class in the bounded census; the algorithm itself stores labelled states.
'''
(ROOT/'paper/finite.tex').write_text(s)
