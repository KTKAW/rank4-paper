# Appendix calculations

This file accompanies the paper *Mutation-acyclicity in rank four is decidable but not semialgebraic*
by Armstrong-Williams, Hirst, Jackson and Lee. It reproduces the hand calculations behind
Appendices A and B of the paper, as they were written out in full in an earlier version of the
paper, and attaches to each step the labels of the claims in `proof_claims.py` that verify it.
The labels are the ones cited in the paper. This file is meant for reading. The verification is
done by `check_proofs.py`, which checks every claim exactly and for all integer values of its
parameters; nothing below is needed for that check.

Notes on reading this file.

* **Setup.** The earlier version assumed $T\ge H(Q_*)$, where $H$ was the maximum of the height
  and of $|M_\omega|$ over all six cyclic orderings. The calculations only use
  $3\le m\le T$ and $2|p|<m$ for the Markov invariant $m=m(Q_*)$ of the totally proper class,
  so they apply verbatim to the current setup $T\ge m(Q_*)$, $F=T+1$.
* **Numbering.** Section numbers follow the current paper: A.1, A.2 and A.3 prove Lemmas 4.2, 4.3
  and 4.4, and Appendix B proves Proposition 4.5. Appendix C of the earlier version, the case
  $d=1$ in the proof of Lemma 4.3, is reproduced at the end; its claims are labeled `A2.d1-*`.
  Numbered equations such as (8) refer to the paper, and named tags such as (zeroMarkov) refer to
  displays in this file.
* **Labels.** A label such as `[A1.markov]` follows the statement it verifies. The index at the
  end lists every claim with its kind and its one-line statement.
* **Kinds of claims.** An *identity* is checked by polynomial expansion (this includes equalities
  of tuples, such as a relabeling, and checks that a substitution permutes a system of hypotheses).
  An *inequality* or *contradiction* is checked by an exact certificate that writes the goal as a
  nonnegative combination of products of the hypotheses and of squares, modulo stated equations,
  possibly after splitting on whether an integer quantity is at least 1 or at most 0. A *mutation
  path* is checked by symbolic mutation after certifying the sign of each entry that the mutation
  formula needs. A *sign pattern* claim (proper wiggle classes, acyclicity, vortices, oriented
  triangles) is checked by enumerating every sign pattern allowed by the hypotheses.
* **Corrections.** Three typographical errors of the earlier version are corrected here: a missing
  backslash before `qquad`, a word split across a line break, and the bound called $k$ instead of
  $K$ in the proof of Lemma 4.3.

# Claims used in the main text

These claims verify calculations in Sections 2 to 5 of the paper.

* `[A0.rect]` (Section 4, eq. (9), inequality): For 1<=r,s<=F-1: r^2+s^2-Frs <= 2-F.
* `[S2.Lk-markov]` (Remark 2.5, identity): L_k = (k,0,0,1,0,k): M = 2k^2+1.
* `[S2.Lk-pf]` (Remark 2.5, identity): L_k: p = k^2.
* `[S3.recurrence]` (Lemma 3.1, mutation path): For t >= 2: (mu_2 Q(t))^{pi_12} = Q(t-2).
* `[S3.Qt-pf]` (Remark 3.3, identity): p(Q(t)) = -4 for every t, so det B = 16.
* `[S3.Qt-class]` (Remark 3.3, sign pattern): For t >= 3, Q(t) has exactly one proper wiggle class, and it contains <1,3,4,2>.
* `[S3.Qt-markov]` (Remark 3.3, identity): M_<1,3,4,2>(Q(t)) = 12 for every t.
* `[S5.Gx-markov]` (Remark 5.6, identity): G_x = (x,x,0,1,x,-1) is acyclic (order 1<2<4<3) with M = x^3+4x^2+x+2.
* `[S5.Gx-mu4]` (Remark 5.6, mutation path): mu_4 G_x = (x, x, 0, x+1, -x, 1), of height x+1.
* `[S3.Qneg]` (Theorem 3.2, sign pattern): For t <= -3, Q(t) = (-2,t+2,t,-t,2-t,0) is acyclic (vertex 2 is a source).
* `[S5.Gx-acyclic]` (Remark 5.6, sign pattern): G_x = (x,x,0,1,x,-1) is acyclic for x >= 1.

# A. Proofs of the local lemmas

Throughout the appendices, retain the setup of Section 4: $Q_*$ is connected and mutation-acyclic, $m=m(Q_*)$, $T\ge m$, and $F=T+1$. Every quiver considered belongs to its mutation class, so $$3\le m\le T,\qquad 2|p|<m$$ by (8). Here $m$ is the Markov invariant of the totally proper class. For each local lemma, relabel the specified vertices as $1,2$.

We first collect two observations used in several proofs.

**Lemma A.1.** Let $P$ be mutation-acyclic, with $\mathbf b(P)=(a,b,-c,d,E,f)$. Assume $b,c,f>0$ and $a\ge0$, and assume moreover that one of the following holds:

1.  $d\ge0$; the entry $E$ may have any sign.

2.  $d<0$, $a=0$, and $E\le0$.

Then $P$ has exactly one proper wiggle class, and this class contains $\omega_0=\langle 1,2,3,4\rangle$. In particular, $m=M_{\omega_0}(P)$.

*Proof.* The complete directed triangle on $\{1,3,4\}$ restricts every proper class to $\langle 1,2,3,4\rangle$, $\langle 1,3,2,4\rangle$, and $\langle 1,3,4,2\rangle$. Constraints on a complete triple hold throughout a wiggle class, since none of its vertex pairs can be swapped.

If $a=0$, the first and last orders differ by the allowed swap of $1,2$. When $d=0$ or $E=0$, the middle order joins them by swapping $2,3$ or $2,4$. Otherwise the complete triple $\{2,3,4\}$ has the path $2\to3\to4$ if $d>0$, or $3\to4\to2$ if $d,E<0$; either path excludes the middle order.

Now suppose $a>0$. The hypotheses then require $d\ge0$. If $d>0$, the complete triple $\{1,2,3\}$ has the path $1\to2\to3$, leaving only $\omega_0$. If $d=0$ and $E\ne0$, the path $4\to1\to2$ in the complete triple $\{1,2,4\}$ leaves the first two orders, joined by the zero edge $\{2,3\}$. If $d=E=0$, all three are joined by the zero edges $\{2,3\},\{2,4\}$. Thus at most one proper class exists in each case. `[A0.ord1, A0.ord2]` Theorem 2.2 supplies a totally proper class, so it is that class. $\square$

**Lemma A.2.** Let $F,r,s$ be positive integers satisfying $1\le r,s\le F-1$ and $rs=2F$. Then $r,s\ge3$ and $$\tag{productbound}
        3(r^2+s^2)\le2F^2-5F+36.$$

*Proof.* If $r\le2$, then $s=2F/r\ge F$, contradicting $s\le F-1$. Thus $r\ge3$, and the same argument gives $s\ge3$. `[A0.pb1]` The inequalities $(r-3)(F-1-r)\ge0$ and $(s-3)(F-1-s)\ge0$ give $$r^2+s^2\le(F+2)(r+s)-6F+6.$$ Also, $0\le(r-3)(s-3)=2F-3(r+s)+9$, so $3(r+s)\le2F+9$. Combining these bounds yields $$3(r^2+s^2)\le(F+2)(2F+9)-18F+18
                 =2F^2-5F+36.$$ `[A0.pb2]` $\square$

## A.1. Proof of Lemma 4.2

Because vertices $1,2$ are not joined, mutation at either one leaves all entries incident to the other unchanged. The low neighbor $\mu_1P$ therefore bounds every entry except $b_{34}$ by $T$. Exchange $3,4$ and reverse arrows as needed to write $$\mathbf b(P)=(0,b,-c,d,E,F),\qquad b,c\ge1,
    \qquad b,c,|d|,|E|\le T.$$ (The signs of $b,c$ are forced, because mutation at $1$ lowers the $b_{34}$ entry only if its arrows point $4\to1\to3$.) `[A1.mu1P]` The case $d<0<E$ is impossible, because mutation at $2$ would increase $b_{34}$ to $F+(-d)E>F$. `[A1.mu2-dneg-Epos, A1.dneg-Epos]`

Lemma A.1 gives $$\tag{zeroMarkov}
    m=b^2+c^2+d^2+E^2+F^2-bcF+dEF.$$ `[A1.markov]`

Mutation at $3$ would create the entries $bF-c$ and $E+F[d]_+$. `[A1.mu3-dpos, A1.mu3-dneg]` If its height were at most $F$, the first forces $b=1$ and the second forces $d\le1$, with $E\le0$ when $d=1$. `[A1.mu3-b1, A1.mu3-d1, A1.mu3-E]` When $d\le0$, the excluded sign pair $d<0<E$ gives $dE\ge0$, and $$4(m-F)=(2c-F)^2+3(F-1)^2+2F+1
          +4d^2+4E^2+4dEF>0.$$ `[A1.id-dnonpos, A1.dzero, A1.dneg-Enonpos]` When $d=1$, we instead have $$4(m-F)=(2c-F)^2+(2E+F)^2+2(F-1)^2+6>0.$$ `[A1.id-d1, A1.d1]` Both contradict $m\le T$. Mutation at $4$ is ruled out by the same argument after reversing arrows and exchanging $3,4$; this sends $(b,c,d,E)$ to $(c,b,-E,-d)$ and preserves the form of the calculation. `[A1.sym34]`

If $\mu_2P$ is high, only its $b_{34}$ entry can have magnitude $F$. That entry either stays $F$ or becomes $-F$. `[A1.mu2-dpos-Eneg, A1.mu2-dpos-Epos, A1.mu2-dneg-Eneg]` The latter requires $d>0,E=-e<0$ and $de=2F$, where $d,e\le F-1$. The rectangle bound (9) and Lemma A.2 give $b^2+c^2-Fbc\le2-F$ and $3(d^2+e^2)\le2F^2-5F+36$. Thus (zeroMarkov) gives $$3m\le3(2-F)+2F^2-5F+36-3F^2
    =42-8F-F^2<0,$$ `[A1.minusF-d3, A1.minusF-e3, A1.minusF]` a contradiction. Thus a second high quiver has the form $(0,b,-c,-d,-E,F)$. It satisfies the same sign restriction and the same Markov bound, so the preceding argument again forbids $3,4$. The next reduced mutation must be at $1$. It gives the entry $F-bc$ at $b_{34}$, exactly as in the low quiver $\mu_1P$, and all its other entries are low. `[A1.second-dneg-Eneg, A1.second-dpos-Epos]` This proves the first assertion.

For the second assertion, the two mutations commute and are involutions, so there are at most four labeled quivers to consider. Only a low endpoint requiring both mutations needs attention. If a one-mutation intermediate quiver $P$ has height greater than $T$, its two neighbors are the low start and low endpoint. Such a temporary corner need not have height at most $F$; the bound $m\le T$ still holds throughout the mutation class. The two low neighbors force every incident entry to be low, and both lower the remaining entry. Thus normalize $$\mathbf b(P)=(0,b,-c,d,-e,f),\qquad
    1\le b,c,d,e\le T,\qquad f>T.$$ The two low neighbors have $b_{34}$ entries $f-bc$ and $f-de$. The other corner of the commuting square has entry $f-bc-de$. `[A1.sq-paths, A1.sq-paths2]` Its upper bound follows from $f-bc\le T$; we must prove $$\tag{zerosquare}
    f-bc-de\ge-T.$$ Lemma A.1 also gives `[A1.sq-markov, A1.sq-pf]` $$m=b^2+c^2+d^2+e^2+f^2-f(bc+de),\qquad p=be-cd,
    \qquad 3\le m\le T,\quad2|p|<m.$$ Assume for a contradiction that $bc+de>f+T$.

First suppose all four incident magnitudes are at least two. Put $r=bc$, $s=de$, $U=b^2+c^2$, $V=d^2+e^2$, exchanging the two pairs if necessary so that $s\le r$. Then $$4U-r^2\le16,\qquad4V\le2s^2\le2rs,\qquad s\ge4.$$ The first follows from $(b^2-4)(c^2-4)\ge0$ and the second from $2(d^2+e^2)\le d^2e^2$. The neighbor bounds imply $r\le f+T<2f$ and $s\ge f-T$, and our assumed failure gives $r+2s>f+T+s\ge2f$. Use the exact identity $$4m=(4U-r^2)+(4V-2rs)-(2f-r)(r+2s-2f).$$ The last two factors are positive integers with sum $2s$, so their product is at least $2s-1$. Hence $4m\le16-(2s-1)\le9$, contradicting $m\ge3$. `[A1.sq-all2-rs, A1.sq-all2-sr]`

There remains the case of a unit entry. The transformations $$(b,c,d,e)\longmapsto(c,b,e,d),\qquad
    (b,c,d,e)\longmapsto(d,e,b,c)$$ preserve all the height inequalities and $m$, and change only the sign of $p$. `[A1.sq-sym1, A1.sq-sym2, A1.sq-sym1-relabel, A1.sq-sym2-relabel]` They can put a unit entry at $b=1$. Define $$u=f-c,\qquad v=de-f.$$ The neighbor bounds and the assumed failure give $$\tag{zeroUnitBounds}
    \begin{gathered}
        de=c+u+v,\qquad 1\le c,d,e,u,v\le T,\\
        T<c+u,\quad T<c+v,\quad 2u<de,\quad2v<de.
    \end{gathered}$$ For example, the failed lower bound is $c+v>T$, while $v\le T<c+u$ gives $2v<de$, and the other inequality is symmetric. Neither $d$ nor $e$ can be $1$, since then the other would equal $de=c+u+v>T$. `[A1.u-d1, A1.u-e1]` Direct substitution gives $$\tag{zeroM}
    \begin{split}
        m&=d^2+e^2+1-de(u+v)+u^2+uv+v^2\\
         &= (d-c)^2+e^2+1-cd(e-2)-uv,\qquad\qquad p=e-cd.
    \end{split}$$

If $c=1$, the inequalities $u,v\le T<1+u,1+v$ force $u=v=T$. `[A1.u-c1-f, A1.u-c1-dehi, A1.u-c1-delo]` Now $de=1+2u$, so $d,e$ are odd and at least three. `[A1.u-c1-d2, A1.u-c1-e2]` Put $N=de=1+2u$. The bound $(d^2-4)(e^2-4)\ge25$ gives $d^2+e^2\le(N^2-9)/4$, and therefore $$m=2+d^2+e^2-(u+1)^2\le-u-1<3.$$ `[A1.u-c1-main]` Assume from now on that $c\ge2$.

We use one common estimate: $$\tag{zeroCommon}
    m\le(d-e)^2+4.$$ To prove it, exchange $u,v$ so that $u\le v$. The exact difference between the right side and $m$ is $$(de-2v-1)(u+v-2)+(u-1)^2+3(u-1)(v-u)+(v-u)^2\ge0,$$ where $de>2v$ and integrality make every term nonnegative. `[A1.u-common]` It remains to compare $c$ with $d,e$.

1.  If $c<\max(d,e)$, put $D=\max(d,e)$, $\ell=\min(d,e)$, and $z=D-c\ge1$. Since $D\le T<c+u,c+v$, we have $u,v\ge z+1$. The formula for $m$ is symmetric in $d,e$, so (zeroM) gives $$m\le\ell^2-2z-cD(\ell-2)\le\ell(4-\ell)-2z\le2,$$ using $cD\ge2\ell$ and $\ell\ge2$. `[A1.u-case1-d, A1.u-case1-e]`

2.  If $e\le d\le c$, put $z=d-e$. Then $$2(cd-e)-\{(d-e)^2+4\} \ge z^2+4ez+2(e-2)(e+1)\ge0,$$ contradicting (zeroCommon) and $2|p|<m$. `[A1.u-case2]`

3.  If $d<e=c$, then (zeroM) gives $$m=d^2-(d-2)e^2+1-uv\le4<2e(d-1)=2|p|.$$ Here $uv\ge1$ gives the bound when $d=2$, and when $d\ge3$, $e>d$ gives $m<0$. `[A1.u-case3-d2, A1.u-case3-d3]`

4.  If $d<e<c$, then $cd-e>e(d-1)$ and $d\ge2$ gives $$f<de<2(cd-e)<m\le T<f,$$ where $f<de$ follows from $v>0$. `[A1.u-case4]`

This proves (zerosquare). Thus whenever one intermediate corner has height greater than $T$, the other is low. The alternative two-mutation path has exactly the same labeled endpoint and stays low, proving the second assertion. $\square$

## A.2. Proof of Lemma 4.3

Put $N_0=C$, $N_1=\mu_1C$, $N_2=\mu_{[1,2]}C$, $N_3=\mu_{[1,2,1]}C$, $N_4=\mu_{[1,2,1,2]}C$. By the pentagon relation (10), there are at most ten labeled quivers reachable using only $1,2$, namely $N_r,N_r^{\pi_{12}}$. Mutation at $1$ or $2$ gives the following transitions:

|       |       $1$        |       $2$        |
|:-----:|:----------------:|:----------------:|
| $N_0$ |      $N_1$       | $N_4^{\pi_{12}}$ |
| $N_1$ |      $N_0$       |      $N_2$       |
| $N_2$ |      $N_3$       |      $N_1$       |
| $N_3$ |      $N_2$       |      $N_4$       |
| $N_4$ | $N_0^{\pi_{12}}$ |      $N_3$       |

The transitions from $N_r^{\pi_{12}}$ follow by swapping the mutation vertices. It is enough to reach the endpoint up to $\pi_{12}$. The endpoints $N_0,N_1,N_4$ require at most one mutation. For $N_2$, use $[1,2]$ if $\operatorname{ht}(N_1)\le K$, and $[2,1,2]$ otherwise. For $N_3$, use $[2,1]$ if $\operatorname{ht}(N_4)\le K$, and $[1,2,1]$ otherwise. The next calculation proves that each detour stays within height $K$.

It remains to justify the detour when a direct intermediate quiver $P$ exceeds height $K$, but both neighbors $\mu_1P,\mu_2P$ have height at most $K$. Every entry touching vertex $1$ or $2$ is bounded by $K$, because one of these mutations simply reverses that entry. Thus only the $b_{34}$ entry can exceed $K$. Reverse arrows and exchange $3,4$ if necessary to make $b_{12}(P)=1$ and $b_{34}(P)=f>K$. For mutation at $1$ to reduce $f$, its incident arrows must be $4\to1\to3$, and for mutation at $2$ to reduce $f$, they must be $4\to2\to3$. Therefore $$\mathbf b(P)=(1,b,-c,d,-e,f),\qquad b,c,d,e\ge1.$$ The tuples of the two low neighbors are $$(-1,-b,c,d,-c-e,f-bc),\qquad (-1,b+d,-c,-d,e,f-de).$$ `[A2.neighbours1, A2.neighbours2]` They give $b+d\le K$, $c+e\le K$, and $|f-bc|,|f-de|\le K$. Lemma A.1 identifies the totally proper class, so $$D=bc+de+cd,\quad m=1+b^2+c^2+d^2+e^2+bd+ce+f^2-fD,\quad p=f+be-cd.$$ `[A2.markov, A2.pf]` Starting at $\mu_1P$, the alternative path $[2,1,2]$ ends at $(\mu_2P)^{\pi_{12}}$. Its two intermediate tuples are $$(1,-b,-e,-d,c+e,f-D),\quad(-1,b,e,-b-d,c,f-D).$$ `[A2.detour]` All their entries are bounded by $K$ except possibly $f-D$. Its upper bound follows from $f-D\le f-bc\le K$. We must prove $f-D\ge-K$. Suppose instead $f+K<D$. Expanding $m$ and using the two neighbor bounds gives

| Range          | Contradiction to $0\le2\lvert p\rvert\le m$ |
|:---------------|:---------------------------------|
| $c=1$ or $d=1$ | $p>0$, $m-2p\le-5$               |
| $c,d\ge2$      | $m\le-1$                         |

For the case $c,d\ge2$, put $$S=b+d,\quad U=c+e,\quad X=\max(S,U),\quad Y=\min(S,U).$$ Then $X\ge Y\ge3$, $bd+ce\ge4$, and $$D\ge2S+2U-4.$$ Indeed, the difference is $$(b-1)(c-2)+(e-1)(d-2)+(c-1)(d-1)-1\ge0.$$ The failed detour gives $f,D-f\ge X+1$. Thus $$f(D-f)\ge(X+1)(D-X-1)\ge(X+1)(X+2Y-5).$$ Using $m=1+S^2+U^2-bd-ce-f(D-f)$, we obtain $$\begin{aligned}
    m&\le6+4X+Y^2-2XY-2Y-bd-ce\\
    &\le6+2Y-Y^2-bd-ce\le2+2Y-Y^2\le-1.
\end{aligned}$$ This contradicts $m\ge0$. `[A2.cd2-SU, A2.cd2-US]`

For $d=1$, the remaining estimate $p>0$ and $m-2p\le-5$ is proved in Appendix C. The case $c=1$ follows by the symmetry $(b,c,d,e)\mapsto(e,d,c,b)$. `[A2.sym, A2.sym-relabel]` Each case contradicts Lemma 2.4. Thus $f-D\ge-K$, proving the height bound. $\square$

## A.3. Proof of Lemma 4.4

Reverse all arrows if necessary so that $a=b_{12}(P)\ge2$. All entries incident to $1$ have magnitude less than $F$, because mutation at $1$ only reverses them. The entries incident to $2$ also have magnitude less than $F$. Indeed, for $k=3,4$, mutation at $1$ replaces $b_{2k}(P)$ by $b_{2k}(P)-a[-b_{1k}(P)]_+$. Thus $b_{2k}(P)=-F$ could not become low. If $b_{2k}(P)=F$ becomes low, then $b_{1k}(P)<0$, and mutation at $2$ would create $$b_{1k}(P)+aF\ge aF-(F-1)>F,$$ contrary to its height bound. `[A3.b23-mu1-ypos, A3.b23-mu1-yneg, A3.b23m-mu1, A3.b23m-mu1-ypos, A3.b23-mu2, A3.b23-big]` Only the entry $b_{34}(P)$ can therefore have magnitude $F$. Exchange $3,4$ if necessary to make that entry positive. For mutation at $1$ to lower it, its two arrows must point $4\to1\to3$. Consequently $$\mathbf b(P)=(a,b,-c,d,E,F),\qquad a\ge2,\quad 
    b,c\ge1,\quad a,b,c,|d|,|E|\le F-1.$$ The two neighbor bounds also give $$|E-ac|\le F-1,\qquad b+ad\le F\quad\text{if }d\ge0.$$ `[A3.nb1, A3.nb2]` Its Pfaffian is $p=aF-bE-cd$. `[A3.pf]`

We first show $d\ge0$ and $E\ge c$. If $d<0<E$, mutation at $2$ creates the entry $F+(-d)E>F$. `[A3.mu2-dneg-Epos, A3.dneg-Epos]` If $d<0$ and $E\le0$, then $p\ge aF\ge2F$, contradicting (8). `[A3.dneg-Enonpos]` The same contradiction excludes $d=0,E<0$. `[A3.d0-Eneg]`

In all remaining cases, Lemma A.1 gives $m=M_{\omega_0}(P)$.

Suppose first that $d\ge0$ and $0\le E<c$. Put $$x=b+(a-1)d,\qquad y=c-E.$$ The neighbor bounds give $1\le x,y\le F-1$. Expanding (4) gives the identity $$m=a^2+x^2+y^2-Fxy-(a-1)F^2+Fp
    -(a-2)\{d(b+ad)+cE+FdE\}.$$ `[A3.identity1]` The braced term is nonnegative. Using the rectangle bound (9) and $2p\le m\le F$ gives $$2m\le2a^2+4-2F-(2a-3)F^2<0.$$ For $a=2$, the last expression is $12-2F-F^2<0$ since $F>a$. For $a\ge3$, use $F>a$ and $2a-3\ge3$. Both contradict $m\ge3$. `[A3.case-Esmall-d1, A3.case-Esmall-d0]`

The other remaining case is $d>0,E=-e<0$, with $e\ge1$. Now $ac+e\le F-1$ and $b+(a-1)d\le F-1$. Direct expansion gives $$\begin{split}
    m={}&a^2+(b^2+d^2+abd)+(c^2+e^2+ace)\\
    &-(a^2-1)F^2+apF-F(bc+de+abe),\qquad p=aF+be-cd.
\end{split}$$ `[A3.identity2]` The first quadratic group is at most $(b+(a-1)d)^2$, since the difference is $(a-2)d(b+ad)\ge0$. The second is at most $(ac+e)^2$, since the difference is $(a^2-1)c^2+ace\ge0$. Dropping the last nonpositive term and using $2p\le F$ therefore gives $$2m\le-(2a^2-a-6)F^2+2a^2-8F+4<0.$$ For $a=2$ this is $12-8F<0$. For $a\ge3$, the coefficient $2a^2-a-6$ is at least $2$, and $F>a$ makes the expression negative. `[A3.case-Eneg]` Thus $d\ge0$ and $E\ge c$ as claimed.

Write $\beta=b+ad$ and $\gamma=aE-c$. Mutation at $2$ gives $$\tag{strongnext}
    \mathbf b(\mu_2P)=(-a,\beta,\gamma,-d,-E,F),\qquad \beta\ge1,\quad \gamma\ge E\ge1.$$ `[A3.mu2-rest, A3.gamma-ge-E]` Mutation at $3$ would create the entry $\gamma+\beta F>F$. `[A3.mu2-then3, A3.mu2-then3-big]` Mutation at $4$ would create an entry of magnitude $d+EF>F$, unless $d=0,E=c=1$. `[A3.mu2-then4, A3.mu2-then4-d, A3.mu2-then4-E]` In this exception the unique proper class identified above gives $$m=a^2+b^2+F^2-a-bF+2\ge a^2-a+2+\tfrac34F^2>F,$$ contradicting $m\le T$. A reduced continuation must therefore mutate at $1$. `[A3.exception-m, A3.exception]`

After this mutation, $b_{12}$ is positive, $b_{34}=F$, and the two columns joining $1,2$ to $3,4$ are $$(-\beta,a\beta-d),\qquad(-\gamma,a\gamma-E).$$ `[A3.mu1-after]` Each has the form $(-X,Y)$ with $1\le X\le Y$. Here $\beta=b+ad>d$ and $\gamma\ge E$ give the required inequalities. `[A3.form-beta, A3.form-gamma]` From any quiver of this form, mutation at $3$ creates the $b_{24}$ entry $Y_4+Y_3F>F$, and mutation at $4$ creates the $b_{13}$ entry $-X_3-X_4F<-F$. `[A3.W-mu3, A3.W-mu3-big, A3.W-mu4, A3.W-mu4-big]` Only $1,2$ can be used. To see that the same argument keeps applying, mutate at $2$ and exchange labels $1,2$. A column $(-X,Y)$ becomes $$(-Y,aY-X),\qquad aY-X\ge Y\ge1.$$ `[A3.W-mu2, A3.W-form3, A3.W-form4]` The entry $b_{12}$ is again positive, and $b_{34}$ remains $F$. Thus every reduced continuation is forced to alternate at $1,2$, and a forbidden choice at $3$ or $4$ exceeds height $F$. The unchanged entry $b_{34}=F$ prevents any return to a low quiver. $\square$

# B. Proof of Proposition 4.5

We keep the setup of Section 4 and of Proposition 4.5. In particular, the route minimizes (11), its maximum height is $F$, and $C$ is the low quiver preceding a high segment of this route; the first two mutation vertices are $1,2$, and $b_{12}(C)=1$. Part (a) is Lemma 4.3 with $K=T$. From now on the segment uses a third vertex. No quiver before the endpoint of a minimizing route is acyclic. Otherwise, truncating there would decrease its maximum height, its number of visits at that height, or its length, in that order. In particular, the low predecessor $C$ is not acyclic. We use this observation to discard acyclic sign cases immediately.

## B.1. The prefix before the third vertex is $[1,2]$

Before the first mutation at a third vertex, the route alternates at $1,2$ and reaches a quiver of height at most $F$ from the low quiver $C$. By Lemma 4.3 with $K=F$, that quiver is reached, up to the swap of $1,2$, by at most three mutations within height $F$. If the alternating prefix had length four or more, replacing it by this shorter route and transporting the tail by (3) would remove at least one high quiver (the prefix consists of high quivers, and the shorter route contains fewer of them), contradicting the minimizing-route hypothesis in Proposition 4.5. Hence the prefix is $[1,2]$ or $[1,2,1]$. We now exclude $[1,2,1]$. The pentagon relation gives $\mu_{[2,1]}C=(\mu_{[1,2,1]}C)^{\pi_{12}}$. If $\mu_2C$ had height at most $F$, replacing $[1,2,1]$ by $[2,1]$ would remove a high quiver. In each replacement, the old prefix has three high quivers, while the new prefix has at most two, and transporting the tail preserves all its heights. Thus minimality forces $\operatorname{ht}(\mu_2C)>F$. The next calculation shows that this is impossible.

Write the tuple of the low starting quiver as $\mathbf b(C)=(1,x,c,d,e,f)$. Because $\mu_{[2,1]}C$ is a relabeling of the third high quiver, it has height at most $F$. Its last mutation reverses every entry touching $1$, and the entries touching $2$ of $\mu_2C$ are reversals of entries of $C$. Hence only the $b_{34}$ entry of $\mu_2C$ can exceed $F$. Exchange $3,4$ to make it less than $-F$. To decrease $f$ at vertex $2$, we must have $d>0$ and $e=-E<0$, giving $$b_{34}(\mu_2C)=f-dE<-F.$$ `[B1.mu2C]` In $\mu_2C$, the $b_{13},b_{14}$ entries are $x+d,c$. For mutation at $1$ to raise its $b_{34}$ entry back into $[-F,F]$, we therefore need $x+d<0<c$. Write $x=-b$, thus $b>d\ge1$ and $c,E\ge1$. The first high quiver $\mu_1C$ can now reach height $F$ only in its $b_{34}$ entry, which is $f+bc$. `[B1.mu1C]` Since $f\ge-(F-1)$ and $bc>0$, this entry cannot be $-F$. Consequently $$\mathbf b(C)=(1,-b,c,d,-E,F-bc),\quad b,c,d,E\ge1,\quad d<b.$$ The tuples after $[1],[1,2],[1,2,1]$ are $$(-1,b,-c,d-b,-E,F),\quad(1,d,-c-E,b-d,E,F),\quad(-1,-d,c+E,b-d,-c,F-d(c+E)).$$ `[B1.prefix]` Their height bounds give $$\begin{gathered}
    bc\le2F-1,\qquad 2F<bc+dE,\qquad c+E\le F,\\
    \text{and either}\quad c+E=F\quad\text{or}\quad d(c+E)=2F.
\end{gathered}$$ The directed triangle $1\to2\to3\to1$ fixes the cyclic order $\langle 1,2,3\rangle$. The path $1\to4\to2$ in the complete triple $\{1,2,4\}$ places $4$ between $1,2$. Thus $C$ has the unique proper wiggle class represented by $\langle 1,4,2,3\rangle$. `[B1.order]` Evaluating in that ordering gives the transported Markov invariant, and the Pfaffian follows directly: $$m=1+b^2+c^2+d^2+E^2+cE-bd+F^2-F(bc+dE),\quad p=F-b(c+E)+cd.$$ `[B1.markov, B1.pf]` If $c+E=F$, we have $b\ge3$, since otherwise $b=2,d=1$ would give $bc+dE=2c+E=F+c<2F$. `[B1.ce-b2]` Also $d\le b-1$ gives $$2b^2-3b-4d\ge2b^2-7b+4=(b-3)(2b-1)+1\ge1.$$ Therefore $$b\{2(-p)-F\}=F(2b^2-3b-4d)+2d(2F-bc)>0.$$ `[B1.ce-identity, B1.ce]` Since $b>0$, this implies $-2p>F$, hence $2|p|>F$. But (8) gives $2|p|<m\le F-1$, a contradiction. Otherwise set $L=c+E$, $z=b-d$. Then $dL=2F$. Since $d,L<F$, neither can be $1$ or $2$, and hence $3\le d,L\le F-1$ and $F\ge5$. `[B1.dl-d3, B1.dl-L3, B1.dl-F5]` Now $$m=1+d^2+L^2-cE-F^2+z^2+dz-Fcz\le d^2+L^2-cE-F^2.$$ For the last inequality, $z+d=b\le F-1$ and $c,z\ge1$ give $1+z^2+dz-Fcz\le1+z(F-1)-Fcz\le0$. Lemma A.2, with $(r,s)=(d,L)$, now gives $3m\le-F^2-5F+36-3cE<0$. `[B1.dl]` Both alternatives contradict (8). Hence the first mutation at a third vertex follows the sequence $[1,2]$.

## B.2. The sign cases

Write the tuple of the low starting quiver as $\mathbf b(C)=(1,x,c,d,e,f)$, and relabel the third vertex as $3$. The quivers after $[1]$ and $[1,2]$ have height $F$, and the quiver after $[1,2,3]$ has height at most $F$. There are three cases, according to the signs of $x$ and $d$. The outcome is that only the quivers $A_c$ and $I_{t,u}$ of (12) survive.

### B.2.1. Case $x=-b<0<d$

Here $1\le b,d\le F-1$, and all entries of $C$ have absolute value at most $F-1$.

First suppose $c>0$. The first mutation can reach height $F$ only through its $b_{34}$ entry, so $f+bc=F$ and $$P=\mu_1C,\qquad \mathbf b(P)=(-1,b,-c,d-b,e,F).$$ `[B21.P-cpos]` We consider the three possible comparisons between $b$ and $d$.

If $d<b$, put $r=b-d\ge1$. The next two quivers have tuples $$\begin{aligned}
    Q&=\mu_2P,\qquad \mathbf b(Q)=(1,d,-c-[-e]_+,r,-e,F+r[e]_+),\\
    \mathbf b(\mu_3Q)&=(1,-d,-c-[-e]_++dF,-r,-e+rF,-F)\qquad(e\le0).
\end{aligned}$$ `[B21.a-Q-epos, B21.a-Q-eneg]` The height bound on $Q$ first gives $e\le0$. `[B21.a-epos]` If $e<0$, the $b_{24}$ entry of $\mu_3Q$ is greater than $F$, so $e=0$. `[B21.a-eneg]` Its $b_{24}$ entry is now $rF$, giving $r=1$. `[B21.a-r]` Its $b_{14}$ entry is $dF-c$, and since $c\le F-1$, the inequality $dF-c\le F$ gives $d=1$. `[B21.a-d]` Thus $b=2$ and $$\mathbf b(C)=(1,-2,c,1,0,F-2c)=\mathbf b(A_c).$$

If $b<d$, put $r=d-b\ge1$. When $e\ge0$, the Pfaffian is $$p=f+be+cd=F+rc+be\ge F,$$ `[B21.b-pf, B21.b-epos]` contrary to (8). Hence $e=-E<0$. The next two mutations give $$\mathbf b(Q)=(1,b,-c-E,-r,E,F-rE),\qquad b_{12}(\mu_3Q)=1+br,\qquad b_{24}(\mu_3Q)=E-r[rE-F]_+.$$ `[B21.b-Q, B21.b-mu3Q-a, B21.b-mu3Q-b]` Because $Q$ has height $F$, either $c+E=F$ or $rE=2F$. The latter is impossible, since $E\le F-1$ would give $r\ge3$, and then $b_{24}(\mu_3Q)=E-rF<-F$. `[B21.b-rE2, B21.b-rE3]` Consequently $c+E=F$.

The Markov value used here is the transported invariant, rather than an arbitrary choice of cyclic ordering. Indeed, the directed triangle $1\to2\to3\to1$ forces the cyclic order $\langle 1,2,3\rangle$ on those vertices, while the path $1\to4\to2$ forces $\langle 1,4,2\rangle$. All pairs in each of these triples are joined, so wiggles cannot change either restriction. Together they leave only the ordering $\langle 1,4,2,3\rangle$. Thus there is only one possible proper wiggle class, and evaluation in this ordering gives $$\tag{positive-order-markov}
    m=1+b^2+c^2+d^2+E^2+f^2+cE+bcf-bd-dEf-bcdE.$$ `[B1.order, B21.markov-1423]` Using $d=b+r$, $c+E=F$, and $f=F-bc$, this becomes $$m=1+b^2+br+r^2-(b-2)F^2-rFE-cE,\qquad p=(r+1)c-(b-1)E.$$ `[B21.b-reduced, B21.b-reduced-p]` If $b\ge3$, then $b+r=d\le F-1$ gives $$m\le1+(b+r)^2-F^2\le2-2F<3.$$ `[B21.b-b3]` If $b=2$, write $$m=6+2r+r^2-(r+1)F-(E-1)\{(r+1)F-E-1\}.$$ The last product is nonnegative, since $1\le E\le F-1$. Also $r+2=d\le F-1$, so $F\ge r+3$ and $$m\le6+2r+r^2-(r+1)(r+3)=3-2r\le1.$$ `[B21.b-b2-identity, B21.b-b2]` Both cases contradict $m\ge3$. We must therefore have $b=1$. Now $p=(r+1)c>0$, and $2p\le m\le F-1=c+E-1$ gives $$E\ge(2r+1)c+1\ge2r+2.$$ `[B21.b-b1-E]` But $f=E$, so the full triangle on $\{2,3,4\}$ is an oriented cycle with multiplicities $(r+1,E,E)$. Its three-vertex Markov value is $$(r+1)^2+2E^2-(r+1)E^2=(r+1)^2-(r-1)E^2.$$ `[B21.b-b1-triangle, B21.b-b1-markov3]` This equals $4$ if $r=1$, and is at most $(r+1)^2-E^2<0$ if $r\ge2$. All three multiplicities are at least two, so Proposition 2.1 excludes this triangle. Thus $b<d$ is impossible when $c>0$.

If $b=d$, the Pfaffian is $p=F+be$, so again $e=-E<0$. `[B21.c-pf, B21.c-epos]` Here $$\mathbf b(Q)=(1,b,-c-E,0,E,F),\qquad b_{14}(\mu_3Q)=bF-c-E.$$ `[B21.c-Q]` Since $c,E\le F-1$, the inequality $bF-c-E\le F$ gives $b\le2$. `[B21.c-b3]` The same two ordering restrictions as above identify the transported Markov value with (positive-order-markov). At $b=1$, put $f=F-c\ge1$. Then $$m=2+c^2+E^2+f^2+cf-Ef,$$ and the following identity makes the contradiction explicit: $$m-F=2+c(c-1)+cf+(E-f)^2+f(E-1)>0.$$ `[B21.c-b1-m, B21.c-b1]` At $b=2$, the height bound on $Q$ gives $c+E\le F$, while the $b_{14}$ entry of $\mu_3Q$ gives $c+E\ge F$. Thus $c+E=F$ and $f=E-c$. Substitution in (positive-order-markov) gives $m=5-cE$. `[B21.c-b2-m]` Since $m\ge3$, we have $cE\le2$. Positive integers with product at most two have sum at most three, contradicting $c+E=F\ge4$. `[B21.c-b2]`

Now suppose $c\le0$. The first mutation is $$\mathbf b(P)=(-1,b,-c,d-b,e+c,f).$$ `[B21.n-P]` Its only entry that can have magnitude $F$ is $e+c$. Hence $c=-t<0$, $e=-v<0$, and $t+v=F$, with $t,v\ge1$. If $f<0$, vertex $4$ is a source and $1\to2\to3\to1$ is an oriented triangle. The quiver is complete, so Lemma 2.7 excludes it. `[B21.n-vortex]` We may assume $0\le f\le F-1$.

If $d<b$, put $r=b-d\ge1$. Then $$\mathbf b(Q)=(1,d,-v,r,F,f),\qquad b_{24}(\mu_3Q)=F+rf.$$ `[B21.n-dlt]` The third height bound gives $f=0$, but then $|p|=bv+td\ge v+t=F$, contradicting (8). `[B21.n-dlt-f, B21.n-dlt-p]`

If $d=b$, then $p=f-bF$. `[B21.n-deq-p]` For $b\ge2$, $|p|\ge2F-(F-1)>F$, so $b=1$. `[B21.n-deq-b2]` The unique proper wiggle class is represented by $\langle 1,2,3,4\rangle$, because the directed triangle on $\{1,2,3\}$ and the path $4\to1\to2$ leave only $\langle 1,2,3,4\rangle$ and $\langle 1,2,4,3\rangle$. If $f=0$, these differ by a wiggle. If $f>0$, the directed triangle $2\to3\to4\to2$ excludes the second ordering. `[B21.n-deq-order0, B21.n-deq-order1]` Evaluation in this class gives $$m=2+t^2+v^2+f^2+tv-vf.$$ `[B21.n-deq-m]` Completing the square gives $$m-F=2+t(t-1)+(t-1)v+\frac34v^2+\left(f-\frac v2\right)^2>0,$$ `[B21.n-deq-b1]` again impossible.

Finally, if $d>b$, put $r=d-b\ge1$. Then $$\mathbf b(Q)=(1,b,-v,-r,F,f-rF),\qquad b_{34}(\mu_3Q)=rF-f.$$ `[B21.n-dgt]` Since $f\le F-1$, the third height bound forces $r=1$. `[B21.n-dgt-r]` Put $u=F-f\ge1$. The absolute Pfaffian is $$|p|=bv+td-f=(b-1)F+t+u.$$ `[B21.n-dgt-p]` If $b\ge2$, this is greater than $F$, contrary to (8). `[B21.n-dgt-b2]` Thus $b=1$, $d=2$, and $2(t+u)\le m\le F-1$ gives $u\le F-1$. `[B21.n-dgt-b1]` The starting quiver therefore has tuple $$\mathbf b(C)=(1,-1,-t,2,t-F,F-u)=\mathbf b(I_{t,u}),\qquad 1\le t,u\le F-1.$$ These cases leave only $A_c$ and $I_{t,u}$.

### B.2.2. Case $x=-b<0$, $d=-D\le0$

Here $1\le b\le T$ and $0\le D\le T$. Put $$h=e-[-c]_+,\qquad g=f+b[c]_+,\qquad z=g+(b+D)[h]_+.$$ The tuples of the first two quivers are $$\mathbf b(P)=(-1,b,-c,-D-b,h,g),\qquad\mathbf b(Q)=(1,-D,-c-[-h]_+,D+b,-h,z).$$ Two entries after the third mutation are $$b_{12}(\mu_3Q)=1-D(D+b),\qquad b_{24}(\mu_3Q)=-h+(D+b)[z]_+.$$ `[B22.paths-+++, B22.paths-++-, B22.paths-+-+, B22.paths-+--, B22.paths--++, B22.paths--+-, B22.paths---+, B22.paths----]` All entries of $C$ have absolute value at most $T$. Consequently $P$ can reach height $F$ only through $$h=-F,\qquad g=F,\qquad\text{or}\qquad b+D=F.$$ We exclude these possibilities in that order, since they need not be disjoint.

If $h=-F$, then $c,e<0$ and $g=z=f$. The third height bound $F+(b+D)[f]_+\le F$ forces $f\le0$. Thus $4<3<1<2$ `[B22.hF-f]` is a topological ordering of $C$, contrary to its nonacyclicity. `[B22.hF-acyclic]`

If $g=F$, then $c>0$ and $z\le F$ forces $h\le0$. `[B22.gF-e]` The third height bound $-h+(b+D)F\le F$ forces $b=1$, $D=h=0$. `[B22.gF-bD, B22.gF-e0]` Hence $e=0$, $c+f=F$, and $c,f>0$. Again $C$ is acyclic, with topological ordering $3<1<2<4$. `[B22.gF-acyclic]`

It remains to consider $b+D=F$. Since $b\le T$, we have $D\ge1$. The bound $1-DF\ge-F$ gives $DF\le F+1$, hence $D=1$ and $b=T$. `[B22.bD-D]` Moreover $$-h+F[z]_+\le F,\qquad h\le T$$ implies $z\le1$, since an integer $z\ge2$ would give $-h+Fz\ge2F-T>F$. `[B22.bD-z]`

If $c>0$, then $$z=f+Tc+F[e]_+\le1.$$ The bounds $f\ge-T$ and $c\ge1$ first give $e\le0$, and then $f\le1-Tc$. `[B22.bD-cpos-e]` But the Pfaffian satisfies $$p=f+Te-c\le1-(T+1)c+Te\le-T,$$ `[B22.bD-pf, B22.bD-cpos-p]` contrary to (8).

We may therefore put $c=-t$, where $t\ge0$. If $f>0$, the inequality $z=f+F[e-t]_+\le1$ forces $f=1$ and $e\le t$. `[B22.bD-cneg-f2, B22.bD-cneg-et]` The third $b_{24}$ entry is then $F+t-e$, so $e\ge t$ as well. `[B22.bD-cneg-b24, B22.bD-cneg-ete]` Thus $e=t$. If $t>0$, the complete quiver is a vortex, with source $3$ and directed triangle $1\to2\to4\to1$. `[B22.bD-vortex]` If $t=0$, $C$ is acyclic with topological ordering $3<1<2<4$. `[B22.bD-t0]` Both are impossible.

Finally suppose $f\le0$. Since $$p=f+Te+t,\qquad f\ge-T,$$ an integer $e\ge2$ would give $p\ge T$, so $e\le1$. `[B22.bD-fneg-pf, B22.bD-fneg-e2]` If $e\le0$, then $4<3<1<2$ is a topological ordering, so only $e=1$ remains. `[B22.bD-fneg-e0]` The case $t=f=0$ is also acyclic, with topological ordering $3<1<2<4$. `[B22.bD-fneg-e1-00]` Otherwise, the path $3\to1\to2$ and the directed triangle $1\to2\to4\to1$ (if $t>0$) or $2\to4\to3\to2$ (if $f<0$) leave a single proper wiggle class containing $\langle 1,2,4,3\rangle$. `[B22.bD-order-tf, B22.bD-order-t0, B22.bD-order-f0]` Indeed, insert the fourth vertex in the three gaps of the indicated triangle, then the other path and triangle constraints exclude the wrong gaps, while any remaining placements across a missing edge are wiggle equivalent. Evaluation gives $$m=T^2+T+3+t(t-1)+f^2+f(T+1-Tt)\ge T^2+T+3-\frac{(T+1)^2}{4}>T.$$ `[B22.bD-m, B22.bD-mbig]` Here $t(t-1)\ge0$, $T+1-Tt\le T+1$, and $f\le0$ give the lower bound. This excludes the whole case $x<0$, $d\le0$.

### B.2.3. Case $x\ge0$

The first mutation can reach height $F$ only if $c=-t<0$, where $1\le t\le T$. Write $w=f-xt$ and $$z=w+[-d]_+[e-t]_+-[d]_+[t-e]_+.$$ The tuples of the first two quivers are $$\mathbf b(P)=(-1,-x,t,d,e-t,w),\qquad\mathbf b(Q)=(1,-x-[-d]_+,\min(t,e),-d,t-e,z).$$ The entries we need after the third mutation are $$\begin{aligned}
    b_{12}(\mu_3Q)&=1-(x+[-d]_+)[-d]_+,\\
    b_{14}(\mu_3Q)&=\min(t,e)-(x+[-d]_+)[-z]_+,\\
    b_{24}(\mu_3Q)&=t-e+[-d]_+[z]_+-[d]_+[-z]_+.
\end{aligned}$$ `[B23.paths-+++, B23.paths-++-, B23.paths-+-+, B23.paths-+--, B23.paths--++, B23.paths--+-, B23.paths---+, B23.paths----]` The Pfaffian is $p=f-xe-td$. `[B23.pf]` Since every starting entry has absolute value at most $T$, the first high quiver must satisfy $e-t=-F$ or $w=-F$.

First suppose $e-t=-F$. Put $u=F-t\ge1$, so $e=-u$. Then $z=w-[d]_+F$, and the third $b_{14}$ entry gives $$\tag{nonneg-first-bound}
    (x+[-d]_+)[-z]_+\le t.$$ If $d=-D<0$, the third $b_{24}$ entry is $F+D[w]_+$, so $w\le0$. `[B23.eF-dneg-w]` Set $v=-w\ge0$. Equation (nonneg-first-bound) gives $(x+D)v\le t$. If $x\ge1$, then $$p=xF+tD-v\ge F+tD-t\ge F,$$ `[B23.eF-dneg-pf, B23.eF-dneg-x]` which is impossible. Thus $x=0$ and $f=w\le0$.

If $d\ge0$, the second height bound gives $w-dF\ge-F$. Since $w\le T$, this forces $d\le1$. `[B23.eF-dpos-d]` For $d=0$, equation (nonneg-first-bound) is $x[-w]_+\le t$. An $x\ge2$ is impossible. If $w\ge0$, then $p=xF+w\ge2F$, and if $w<0$, then $-w\le t$ and $p=xF+w\ge2F-t>F$. `[B23.eF-d0-pf, B23.eF-d0-x2a, B23.eF-d0-x2b]` Thus $x\le1$. When $x=1$, the same inequality gives $f=t+w\ge0$. `[B23.eF-d0-x1]` For $d=1$, the second height bound gives $w\ge0$. If $x\ge1$, then $f=xt+w\le T$ gives $F-w\ge1+xt$, whereas (nonneg-first-bound) gives $x(F-w)\le t$. These are incompatible because $x(1+xt)>t$. `[B23.eF-d1-x]` Hence $x=0$ and $f=w\ge0$.

The cases $x=0,d<0,f\le0$ and $x=d=0$ make $C$ acyclic. `[B23.eF-acyc1, B23.eF-acyc2]` Thus only $(x,d)=(0,1)$ or $(1,0)$ remains, with $f>0$, because $f=0$ is again acyclic. `[B23.eF-acyc3, B23.eF-acyc4]` For $(x,d)=(0,1)$, the directed triangle $2\to3\to4\to2$ and the path $4\to1\to2$ in the complete triple $\{1,2,4\}$ force $\omega_0=\langle 1,2,3,4\rangle$. For $(x,d)=(1,0)$, use the directed triangle $1\to3\to4\to1$ and the same path; the two remaining orders differ by the allowed swap of $2,3$. `[B23.eF-ord01, B23.eF-ord10]` Hence in both cases the transported invariant is $$m=2+t^2+u^2+tu+f^2-\lambda f,\qquad\lambda=\begin{cases}
        F,&(x,d)=(0,1),\\
        t,&(x,d)=(1,0).
        \end{cases}$$ Since $0\le\lambda\le F=t+u$ and $f>0$, both cases have the same contradiction: $$m\ge2+\frac34F^2+f^2-Ff\ge2+\frac12F^2>F.$$ `[B23.eF-m01, B23.eF-m01-big, B23.eF-m10, B23.eF-m10-big]` Here $t^2+u^2+tu=F^2-tu\ge3F^2/4$. This excludes $e-t=-F$.

We may now suppose $w=-F$ and $e-t>-F$. Since $f=xt-F>-F$, we have $x\ge1$. `[B23.wF-x]` Also $|e-t|<F$ and $|\min(t,e)|<F$. For $d=-D<0$, $$z=-F+D[e-t]_+.$$ The second quiver can be high only if $x+D=F$ or $z=\pm F$. If $x+D=F$, the third $b_{12}$ bound gives $D=1$. `[B23.wF-dneg-D]` The third $b_{14}$ bound then gives $z\ge-1$, since $z\le-2$ would yield $$\min(t,e)-F[-z]_+\le T-2F<-F.$$ `[B23.wF-dneg-z]` Thus $[e-t]_+\ge F-1$, impossible because $e-t\le T-1=F-2$. `[B23.wF-dneg-et]` If $z=-F$, the third $b_{14}$ entry is at most $T-(x+D)F\le T-2F<-F$. `[B23.wF-dneg-zmF]` If $z=F$, then $e-t>0$ and the third $b_{24}$ bound gives $$(D-1)F\le e-t\le F-2.$$ `[B23.wF-dneg-zF-D]` Hence $D=1$, but $z=-F+[e-t]_+=F$ would then require $e-t=2F$. `[B23.wF-dneg-zF]` All possibilities with $d<0$ are excluded.

For $d\ge0$, we have $z=-F-d[t-e]_+\le-F$. The second height bound therefore gives $z=-F$ and $d[t-e]_+=0$. `[B23.wF-dpos-z]` The third $b_{14}$ bound reads $$\min(t,e)-xF\ge-F.$$ Since $x\ge1$ and $\min(t,e)\le T$, it forces $x=1$ and $e\ge0$. `[B23.wF-dpos-x, B23.wF-dpos-e]` If $d>0$, then $e\ge t$ and the third $b_{24}$ bound gives $$(e-t)+(d-1)F\le0.$$ Thus $d=1$ and $e=t$. `[B23.wF-dpos-d, B23.wF-dpos-e2]` But then $p=(t-F)-t-t=-F-t$, contrary to (8). `[B23.wF-d1-pf, B23.wF-d1-p]`

Only $d=0$ remains. Put $u=F-t$, so $\mathbf b(C)=(1,1,-t,0,e,-u)$ with $t,u\ge1$ and $e\ge0$. If $e=0$, $C$ is acyclic. `[B23.wF-d0-acyc]` For $e>0$, the triangle $1\to2\to4\to1$ together with the path $4\to1\to3$ in the complete triple $\{1,3,4\}$ forces the single proper wiggle class represented by $\langle 1,3,2,4\rangle$. The order $\langle 1,2,3,4\rangle$ is in that same class because vertices $2,3$ are not joined. `[B23.wF-d0-order]` Evaluation in this class gives $$m=2+t^2+u^2+e^2+tu-te\ge2+\frac34t^2+u^2+tu>t+u=F.$$ `[B23.wF-d0-m, B23.wF-d0-big]` This final contradiction excludes every case with $x\ge0$, including zero entries. Together with Appendices B.2.1 and B.2.2, this shows that $C$ is $A_c$ or $I_{t,u}$.

## B.3. The two remaining cases

For $A_c$ with $\mathbf b(A_c)=(1,-2,c,1,0,F-2c)$, $1\le c\le T$, the successive tuples are listed below. In the row for $\mathbf v$, each entry column gives $b_{ij}(\mu_{\mathbf v}A_c)$:

| Sequence      | $b_{12}$ | $b_{13}$ | $b_{14}$ | $b_{23}$ | $b_{24}$ | $b_{34}$ |
|:--------------|---------:|---------:|---------:|---------:|---------:|---------:|
| $[1]$         |     $-1$ |      $2$ |     $-c$ |     $-1$ |      $0$ |      $F$ |
| $[1,2]$       |      $1$ |      $1$ |     $-c$ |      $1$ |      $0$ |      $F$ |
| $[1,2,3]$     |      $1$ |     $-1$ |    $F-c$ |     $-1$ |      $F$ |     $-F$ |
| $[1,2,3,1]$   |     $-1$ |      $1$ |    $c-F$ |     $-2$ |      $F$ |     $-c$ |
| $[1,2,3,1,3]$ |      $1$ |     $-1$ |    $c-F$ |      $2$ |   $F-2c$ |      $c$ |
| $[2]$         |     $-1$ |     $-1$ |      $c$ |     $-1$ |      $0$ |   $F-2c$ |
| $[2,1]$       |      $1$ |      $1$ |     $-c$ |     $-1$ |      $c$ |    $F-c$ |
| $[2,1,3]$     |      $2$ |     $-1$ |   $F-2c$ |      $1$ |      $c$ |    $c-F$ |

After $[1,2,3]$, mutations at $2,4$ create entries $2F-c>F$ and $F^2-1>F$, respectively. Repeating the last mutation would cancel, so the next vertex must be $1$. After $[1,2,3,1]$, mutations at $2,4$ create entries $2F-c>F$ and $-1-F(F-c)<-F$, so the next vertex must be $3$. Thus the first return is exactly $[1,2,3,1,3]$. `[B3.A-segment, B3.A-forced1, B3.A-forced1b, B3.A-forced2, B3.A-forced2b, B3.A-forced-2Fc, B3.A-forced-F2, B3.A-forced-FFc]` All three quivers along $[2,1,3]$ are low. `[B3.A-replacement, B3.A-low-lo0, B3.A-low-hi0, B3.A-low-lo1, B3.A-low-hi1]` For the relabeling $\pi_{123}$, $$\mu_{[2,1,3]}A_c=(\mu_{[1,2,3,1,3]}A_c)^{\pi_{123}}.$$ `[B3.A-relabel]` This replacement removes four high quivers, and the tail is transported by (3).

For $I_{t,u}$ with $\mathbf b(I_{t,u})=(1,-1,-t,2,t-F,F-u)$, the tuples after $[1],[1,2],[1,2,3]$ are $$(-1,1,t,1,-F,F-u),\quad(1,1,t-F,-1,F,-u),\quad(2,-1,t-F,1,F-u,u).$$ Exactly the first two are high, so the first return is $[1,2,3]$. `[B3.I-segment]` Both replacement mutation sequences terminate at the quiver $E$ with $\mathbf b(E)=(1,-2,F-u,1,u,t-F)=\mathbf b((\mu_{[1,2,3]}I_{t,u})^{\pi_{123}})$. `[B3.I-endpoint]` For $t>u$, the first four tuples along $[2,1,3,2,3]$ are $$\begin{aligned}
    &(-1,1,-t,-2,F-t,2t-F-u),\quad(1,-1,t,-1,F-t,t-F-u),\\
    &(1,1,2t-F-u,1,-u,F+u-t),\quad(-1,2,2t-F-u,-1,u,F-t).
\end{aligned}$$ `[B3.I-tgu]` For $u>t$, the first four tuples along $[3,1,3,2,1]$ are $$\begin{aligned}
    &(-1,1,-t,-2,F+t-2u,u-F),\quad(1,-1,t,-1,F+t-2u,u-F-t),\\
    &(1,1,u-F,1,-u,F+t-u),\quad(-1,2,u-F,-1,u,F+t-2u).
\end{aligned}$$ `[B3.I-ugt]` For $t>u$, put $v=F+u-t$. The bounds $1\le u<t\le F-1$ give $2\le v\le T$, and the only less immediate entry is $2t-F-u=t-v$, whose magnitude is at most $T$. For $u>t$, put $v=F+t-u$. Again $2\le v\le T$, and the less immediate entries are $F+t-2u=v-u$ and $u-F-t=-v$. Every other entry is $0$, $\pm1$, $\pm2$, or one of $\pm t,\pm u,\pm(F-t),\pm(F-u)$. All are low because $T\ge3$. `[B3.I-low-tgu-lo0, B3.I-low-tgu-hi0, B3.I-low-tgu-lo1, B3.I-low-tgu-hi1, B3.I-low-tgu-lo2, B3.I-low-tgu-hi2, B3.I-low-tgu-lo3, B3.I-low-tgu-hi3, B3.I-low-tgu-lo4, B3.I-low-tgu-hi4, B3.I-low-tgu-lo5, B3.I-low-tgu-hi5, B3.I-low-ugt-lo0, B3.I-low-ugt-hi0, B3.I-low-ugt-lo1, B3.I-low-ugt-hi1, B3.I-low-ugt-lo2, B3.I-low-ugt-hi2, B3.I-low-ugt-lo3, B3.I-low-ugt-hi3, B3.I-low-ugt-lo4, B3.I-low-ugt-hi4, B3.I-low-ugt-lo5, B3.I-low-ugt-hi5]` Thus both replacement paths, including their common endpoint $E$, are entirely low and each removes two high quivers.

Finally, suppose $t=u$. The Pfaffian of $I_{t,t}$ is $p=-2t$. `[B3.I-tt-pf]` Thus (8) gives $$4t<m\le F-1.$$ In particular $k=F-t\ge2$. `[B3.I-tt-k]` The full triangle on $\{2,3,4\}$ is an oriented cycle with multiplicities $(2,k,k)$, and $$2^2+k^2+k^2-2k^2=4.$$ `[B3.I-tt-triangle, B3.I-tt-markov]` By Proposition 2.1, this triangle is mutation-cyclic, contradicting mutation-acyclicity of the whole quiver. So $t\ne u$, and Proposition 4.5 is proved. $\square$

# C. The remaining single-arrow estimate (the case $d=1$ of Appendix A.2)

We complete the $d=1$ row in the proof of Lemma 4.3. Keep the notation as it is there, so $$D=bc+e+c,\quad m=2+b^2+b+c^2+e^2+ce+f^2-fD,\quad p=f+be-c.$$ We are assuming that the detour fails, while both neighbors of the high quiver have height at most $K$. Hence $$f,D-f\ge K+1,\qquad K\ge b+1,\ c+e.$$ The point is that both $f$ and $D-f$ are large. Their product makes $m-2p$ negative.

Put $S=b+1$, $U=c+e$, and $X=\max(S,U)$. We have $D\ge2X+2$. If $b=1$, then $D=2c+e\le2U-1$, impossible. `[A2.d1-b1]` If $c=1$, then $D=S+U-1\le2X-1$, also impossible. `[A2.d1-c1]` Therefore $b,c\ge2$, $S\ge3$, and $U\ge c+1\ge3$. Moreover $p>0$, because $f>K\ge U>c$.

Since $(f-X-1)(D-f-X-1)\ge0$ and $f\ge X+1$, $$f(D-f+2)\ge(X+1)(D-X+1).$$ Consequently $$m-2p\le A-(X+1)(D-X+1),$$ where $$A=S^2-S+2+U^2-ce-2Se+2U,\qquad D=cS+e.$$ We show that this upper bound is at most $-5$.

If $S\ge U$, expansion writes the bound as $$\begin{aligned}
    13-6S&+(U-3)(U+4-3S)\\
         &-(c-2)S(S-2)-c(U-c-1)\le-5.
\end{aligned}$$ Every term after $13-6S$ is nonpositive, since $3\le c+1\le U\le S$. `[A2.d1-SU]`

If $U\ge S$, the bound is $$B(U)=(U-S)^2+U-S+1+c^2+c(S+1-SU).$$ Because $D=c(S-1)+U\ge2U+2$, we have $U\le c(S-1)$. Set $U_0=\max(S,c+1)$. Then $$B(U)-B(U_0)=(U-U_0)\{U+U_0-S(c+2)+1\}\le0.$$ Indeed, the braced factor is at most $1-c-S$ when $U_0=S$, and at most $2-2S$ when $U_0=c+1$. At the lower endpoint, $c^2\le c(S-1)$ if $U_0=S$, whereas $c+1\ge S$ if $U_0=c+1$. Thus $$\begin{aligned}
    B(S)&\le1-cS(S-2)\le1-2S(S-2)\le-5
        &&(c\le S-1),\\
    B(c+1)&=(S-1)^2-(S-2)(c+1)^2\\
          &\le1-S(S-1)(S-2)\le-5
          &&(c\ge S-1).
\end{aligned}$$ Thus $m-2p\le-5$ in every case, contradicting $2|p|\le m$. `[A2.d1-US-i, A2.d1-US-ii]`

# Claim index

| Label | Kind | Used in | Statement |
|---|---|---|---|
| `A0.ord1` | sign pattern | Lemma A.1, case (i) | If a>=0, b,c,f>0 and d>=0, then (a,b,-c,d,E,f) has at most one proper wiggle class, and it contains <1,2,3,4>. |
| `A0.ord2` | sign pattern | Lemma A.1, case (ii) | If a=0, b,c,f>0, d<0 and E<=0, then (0,b,-c,d,E,f) has at most one proper wiggle class, and it contains <1,2,3,4>. |
| `A0.pb1` | inequality | Lemma A.2 | 1<=r,s<=F-1 and rs=2F rule out r<=2. |
| `A0.pb2` | inequality | Lemma A.2 | If 3<=r,s<=F-1 and rs=2F then 3(r^2+s^2) <= 2F^2-5F+36. |
| `A0.rect` | inequality | Section 4, eq. (9) | For 1<=r,s<=F-1: r^2+s^2-Frs <= 2-F. |
| `A1.mu2-dneg-Epos` | mutation path | App. A.1 | If d<=0<=E, mutation at 2 makes b34 = F - dE. |
| `A1.dneg-Epos` | inequality | App. A.1 | d<0<E is impossible: mu_2 P would have b34 = F-dE > F. |
| `A1.markov` | identity | eq. (zeroMarkov) | Markov value of P in the order 1<2<3<4. |
| `A1.mu3-dpos` | mutation path | App. A.1 | Mutation at 3 creates b14 = bF - c and b24 = E + Fd when d >= 0. |
| `A1.mu3-dneg` | mutation path | App. A.1 | Mutation at 3 creates b14 = bF - c and b24 = E when d <= 0. |
| `A1.mu3-b1` | inequality | App. A.1 | If mutation at 3 stays within height F then b = 1 (b>=2 impossible). |
| `A1.mu3-d1` | inequality | App. A.1 | If mutation at 3 stays within height F then d <= 1 (d>=2 impossible). |
| `A1.mu3-E` | inequality | App. A.1 | If d = 1 and mutation at 3 stays within height F then E <= 0. |
| `A1.id-dnonpos` | identity | App. A.1 | 4(m-F) = (2c-F)^2+3(F-1)^2+2F+1+4d^2+4E^2+4dEF when b=1. |
| `A1.dzero` | inequality | App. A.1 | b=1, d=0: m > F, contradicting m <= F-1. |
| `A1.dneg-Enonpos` | inequality | App. A.1 | b=1, d<0, E<=0: m > F, contradicting m <= F-1. |
| `A1.id-d1` | identity | App. A.1 | 4(m-F) = (2c-F)^2+(2E+F)^2+2(F-1)^2+6 when b=d=1. |
| `A1.d1` | inequality | App. A.1 | b=d=1: m > F, contradicting m <= F-1. |
| `A1.sym34` | identity | App. A.1 | Reversing all arrows and exchanging 3,4 sends P(b,c,d,E) to P(c,b,-E,-d). |
| `A1.mu2-dpos-Eneg` | mutation path | App. A.1 | Mutation at 2: the b34 entry stays F unless d > 0 > E, when it is F + dE. |
| `A1.mu2-dpos-Epos` | mutation path | App. A.1 | Mutation at 2: the b34 entry stays F unless d > 0 > E, when it is F + dE. |
| `A1.mu2-dneg-Eneg` | mutation path | App. A.1 | Mutation at 2: the b34 entry stays F unless d > 0 > E, when it is F + dE. |
| `A1.minusF` | inequality | App. A.1 | If mu_2 P has b34 = -F then de = 2F, and then 3m <= 42-8F-F^2 < 9, contradicting m >= 3. |
| `A1.minusF-d3` | inequality | App. A.1 | In that case d >= 3 and e >= 3 (Lemma A.2 with r=d, s=e): d<=2 impossible. |
| `A1.minusF-e3` | inequality | App. A.1 | Likewise e <= 2 is impossible. |
| `A1.second-dneg-Eneg` | mutation path | App. A.1 | From the second high quiver (0,b,-c,-d,-E,F), mutation at 1 gives b34 = F - bc. |
| `A1.second-dpos-Epos` | mutation path | App. A.1 | From the second high quiver (0,b,-c,-d,-E,F), mutation at 1 gives b34 = F - bc. |
| `A1.mu1P` | mutation path | App. A.1 | Mutation at 1 of P gives b34 = F - bc. |
| `A1.sq-markov` | identity | App. A.1 | Markov value of P = (0,b,-c,d,-e,f) in the order 1<2<3<4. |
| `A1.sq-pf` | identity | App. A.1 | Pfaffian of P = (0,b,-c,d,-e,f). |
| `A1.sq-paths` | mutation path | App. A.1 | The corners of the commuting square: b34 = f-bc, then f-bc-de after mutating at 1 then 2. |
| `A1.sq-paths2` | mutation path | App. A.1 | Mutation at 2 first: b34 = f-de. |
| `A1.sq-all2-rs` | inequality | App. A.1 | All four incident entries >= 2: 4m <= 16-(2s-1) <= 9 < 12, where s = min(bc,de). |
| `A1.sq-all2-sr` | inequality | App. A.1 | All four incident entries >= 2: 4m <= 16-(2s-1) <= 9 < 12, where s = min(bc,de). |
| `A1.sq-sym1-relabel` | identity | App. A.1 | (b,c,d,e) -> (c,b,e,d) is realized by reversing all arrows and exchanging 3,4. |
| `A1.sq-sym2-relabel` | identity | App. A.1 | (b,c,d,e) -> (d,e,b,c) is realized by exchanging 1,2. |
| `A1.sq-sym1` | identity | App. A.1 | (b,c,d,e) -> (c,b,e,d) permutes the hypotheses of the commuting square. |
| `A1.sq-sym2` | identity | App. A.1 | (b,c,d,e) -> (d,e,b,c) permutes the hypotheses of the commuting square. |
| `A1.u-d1` | inequality | App. A.1 | With b=1, d=1 is impossible (it would force e > F-1). |
| `A1.u-e1` | inequality | App. A.1 | With b=1, e=1 is impossible. |
| `A1.u-c1-f` | inequality | App. A.1 | With b=c=1, f >= F+1 is impossible, so f = F. |
| `A1.u-c1-dehi` | inequality | App. A.1 | With b=c=1 and f=F, de >= 2F is impossible. |
| `A1.u-c1-delo` | inequality | App. A.1 | With b=c=1 and f=F, de <= 2F-2 is impossible; hence de = 2F-1. |
| `A1.u-c1-d2` | inequality | App. A.1 | de = 2F-1 is odd, so neither d nor e equals 2 (integer parity). |
| `A1.u-c1-e2` | inequality | App. A.1 | de = 2F-1 is odd, so neither d nor e equals 2 (integer parity). |
| `A1.u-c1-main` | inequality | App. A.1 | With b=c=1, f=F, de=2F-1 and d,e>=3: (d^2-4)(e^2-4)>=25 gives m <= -F < 3. |
| `A1.u-common` | inequality | App. A.1, eq. (zeroCommon) | With b=1 and c,d,e>=2: m <= (d-e)^2 + 4. |
| `A1.u-case1-d` | inequality | App. A.1, case 1 | b=1, 2<=c<d, e<=d: m <= 4-(e-2)^2-2z < 3 with z=d-c. |
| `A1.u-case1-e` | inequality | App. A.1, case 1 | b=1, 2<=c<e, d<=e: the same estimate with d and e exchanged. |
| `A1.u-case2` | inequality | App. A.1, case 2 | b=1, e<=d<=c: 2\|p\| = 2(cd-e) >= (d-e)^2+4 >= m, contradicting 2\|p\|<m. |
| `A1.u-case3-d2` | inequality | App. A.1, case 3 | b=1, d=2 < e=c: m <= 4 < 2e+1 <= 2\|p\|+1. |
| `A1.u-case3-d3` | inequality | App. A.1, case 3 | b=1, 3<=d<e=c: m - 2\|p\| < 0. |
| `A1.u-case4` | inequality | App. A.1, case 4 | b=1, d<e<c: f < de < 2(cd-e) < m <= F-1 < f. |
| `A2.markov` | identity | App. A.2 | Markov value of P = (1,b,-c,d,-e,f) in the order 1<2<3<4. |
| `A2.pf` | identity | App. A.2 | Pfaffian of P = (1,b,-c,d,-e,f). |
| `A2.neighbours1` | mutation path | App. A.2 | mu_1 P = (-1,-b,c,d,-c-e,f-bc). |
| `A2.neighbours2` | mutation path | App. A.2 | mu_2 P = (-1,b+d,-c,-d,e,f-de). |
| `A2.detour` | mutation path | App. A.2 | From mu_1 P the detour [2,1,2] passes (1,-b,-e,-d,c+e,f-D), (-1,b,e,-b-d,c,f-D) and ends at (mu_2 P)^{pi_12}. |
| `A2.cd2-SU` | inequality | App. A.2, case c,d >= 2 | c,d >= 2 and f - D < -K: m <= 2 + 2Y - Y^2 - (bd+ce-4) <= -1, contradicting m >= 3. |
| `A2.cd2-US` | inequality | App. A.2, case c,d >= 2 | c,d >= 2 and f - D < -K: m <= 2 + 2Y - Y^2 - (bd+ce-4) <= -1, contradicting m >= 3. |
| `A2.sym-relabel` | identity | App. A.2 | (b,c,d,e) -> (e,d,c,b) is realized by reversing all arrows and relabeling by (1 2)(3 4). |
| `A2.sym` | identity | App. A.2 | (b,c,d,e) -> (e,d,c,b) permutes the hypotheses, so c=1 reduces to d=1. |
| `A2.d1-b1` | inequality | App. A.2, case d = 1 | d=1, b=1: D = 2c+e <= 2(c+e) <= 2K < 2K+2 <= D. |
| `A2.d1-c1` | inequality | App. A.2, case d = 1 | d=1, c=1: D = b+e+1 <= 2K-1 < 2K+2 <= D. |
| `A2.d1-SU` | inequality | App. A.2, case d = 1 | d=1, S=b+1 >= U=c+e: m - 2p <= -5, contradicting 2\|p\| < m. |
| `A2.d1-US-i` | inequality | App. A.2, case d = 1 | d=1, U >= S, c <= S-1: m - 2p <= B(S) <= -5. |
| `A2.d1-US-ii` | inequality | App. A.2, case d = 1 | d=1, U >= S, c >= S-1: m - 2p <= B(c+1) <= -5. |
| `A3.b23-mu1-ypos` | mutation path | App. A.3 | If b13 >= 0, mutation at 1 leaves b23 = F unchanged. |
| `A3.b23-mu1-yneg` | mutation path | App. A.3 | If b13 <= 0, mutation at 1 replaces b23 = F by F + a*b13. |
| `A3.b23-mu2` | mutation path | App. A.3 | Mutation at 2 replaces b13 by b13 + aF. |
| `A3.b23-big` | inequality | App. A.3 | If b13 >= -(F-1) then b13 + aF > F, so mu_2 leaves height F. |
| `A3.b23m-mu1-ypos` | mutation path | App. A.3 | b23 = -F is unchanged by mutation at 1 when b13 >= 0. |
| `A3.b23m-mu1` | mutation path | App. A.3 | b23 = -F stays <= -F after mutation at 1 (case b13 <= 0). |
| `A3.pf` | identity | App. A.3 | p = aF - bE - cd. |
| `A3.nb1` | mutation path | App. A.3 | mu_1 P has b24 = E - ac. |
| `A3.nb2` | mutation path | App. A.3 | mu_2 P has b13 = b + ad when d >= 0. |
| `A3.mu2-dneg-Epos` | mutation path | App. A.3 | If d <= 0 <= E, mutation at 2 makes b34 = F - dE. |
| `A3.dneg-Epos` | inequality | App. A.3 | d<0<E is impossible. |
| `A3.dneg-Enonpos` | inequality | App. A.3 | d<0, E<=0 give p >= aF >= 2F, contradicting 2\|p\| < m <= F-1. |
| `A3.d0-Eneg` | inequality | App. A.3 | d=0, E<0 give p >= 2F as well. |
| `A3.identity1` | identity | App. A.3 | m = a^2+x^2+y^2-Fxy-(a-1)F^2+Fp-(a-2)(d(b+ad)+cE+FdE), x=b+(a-1)d, y=c-E. |
| `A3.case-Esmall-d1` | inequality | App. A.3 | d>=0, 0<=E<c: the rectangle bound and 2p <= F-2 give 2m <= 2a^2+4-4F-(2a-3)F^2 < 6. |
| `A3.case-Esmall-d0` | inequality | App. A.3 | d>=0, 0<=E<c: the rectangle bound and 2p <= F-2 give 2m <= 2a^2+4-4F-(2a-3)F^2 < 6. |
| `A3.identity2` | identity | App. A.3 | m = a^2+(b^2+d^2+abd)+(c^2+e^2+ace)-(a^2-1)F^2+apF-F(bc+de+abe) for E=-e. |
| `A3.case-Eneg` | inequality | App. A.3 | d>0>E: 2m <= -(2a^2-a-6)F^2+2a^2-8F-2aF+4 < 6. |
| `A3.mu2-rest` | mutation path | App. A.3 | For d>=0, E>=c: mu_2 P = (-a, b+ad, aE-c, -d, -E, F). |
| `A3.gamma-ge-E` | inequality | App. A.3 | gamma = aE - c >= E. |
| `A3.mu2-then3` | mutation path | App. A.3 | Then mutation at 3 creates b14 = gamma + beta*F. |
| `A3.mu2-then3-big` | inequality | App. A.3 | gamma + beta*F > F. |
| `A3.mu2-then4` | mutation path | App. A.3 | Mutation at 4 instead creates b23 = -d - EF. |
| `A3.mu2-then4-d` | inequality | App. A.3 | If d >= 1 then \|b23\| = d + EF > F. |
| `A3.mu2-then4-E` | inequality | App. A.3 | If E >= 2 then \|b23\| = d + EF > F. |
| `A3.exception-m` | identity | App. A.3 | For d=0, E=c=1: m = a^2+b^2+F^2-a-bF+2. |
| `A3.exception` | inequality | App. A.3 | For d=0, E=c=1: 4m = 4a^2-4a+8+(2b-F)^2+3F^2 > 4F, contradicting m <= F-1. |
| `A3.mu1-after` | mutation path | App. A.3 | Mutation at 1 then gives (a, -beta, -gamma, a*beta-d, a*gamma-E, F). |
| `A3.form-beta` | inequality | App. A.3 | a*beta - d >= beta >= 1. |
| `A3.form-gamma` | inequality | App. A.3 | a*gamma - E >= gamma >= 1. |
| `A3.W-mu3` | mutation path | App. A.3 | From W, mutation at 3 creates b24 = y4 + y3 F. |
| `A3.W-mu3-big` | inequality | App. A.3 | y4 + y3 F > F. |
| `A3.W-mu4` | mutation path | App. A.3 | From W, mutation at 4 creates b13 = -x3 - x4 F. |
| `A3.W-mu4-big` | inequality | App. A.3 | x3 + x4 F > F. |
| `A3.W-mu2` | mutation path | App. A.3 | Mutation at 2 and the swap of 1,2 give (a, -y3, -y4, a y3 - x3, a y4 - x4, F). |
| `A3.W-form3` | inequality | App. A.3 | a*y - x >= y >= 1, so the new columns have the same form. |
| `A3.W-form4` | inequality | App. A.3 | a*y - x >= y >= 1, so the new columns have the same form. |
| `B1.prefix` | mutation path | App. B.1 | The quivers after [1], [1,2], [1,2,1]. |
| `B1.mu2C` | mutation path | App. B.1 | For d >= 0 >= -E, mu_2 C has b13 = x+d, b14 = c, b34 = f - dE. |
| `B1.mu1C` | mutation path | App. B.1 | For x = -b <= 0 and c >= 0, mu_1 C has b34 = f + bc. |
| `B1.order` | sign pattern | App. B.1 and B.2.1 | C = (1,-b,c,d,-E,f) with b,c,d,E > 0 (any f) has at most one proper wiggle class, containing <1,4,2,3>. |
| `B1.markov` | identity | App. B.1 | m = 1+b^2+c^2+d^2+E^2+cE-bd+F^2-F(bc+dE) in the order <1,4,2,3>. |
| `B1.pf` | identity | App. B.1 | p = F - b(c+E) + cd. |
| `B1.ce-b2` | inequality | App. B.1 | c+E=F and b=2 (so d=1): bc+dE = F+c < 2F, contradiction. |
| `B1.ce-identity` | identity | App. B.1 | b(-2p-F) = F(2b^2-3b-4d) + 2d(2F-bc) when E = F-c. |
| `B1.ce` | inequality | App. B.1 | c+E=F, b>=3: -2p > F, contradicting 2\|p\| < m <= F-1. |
| `B1.dl-F5` | inequality | App. B.1 | d, c+E >= 3 and d(c+E) = 2F force F >= 5. |
| `B1.dl-d3` | inequality | App. B.1 | d(c+E) = 2F with d, c+E <= F-1 forces d, c+E >= 3 (Lemma A.2). |
| `B1.dl-L3` | inequality | App. B.1 | d(c+E) = 2F with d, c+E <= F-1 forces d, c+E >= 3 (Lemma A.2). |
| `B1.dl` | inequality | App. B.1 | d(c+E) = 2F: 3m <= -F^2-5F+36-3cE < 9, contradicting m >= 3. |
| `B21.P-cpos` | mutation path | App. B.2.1 | For c > 0: mu_1 C = (-1, b, -c, d-b, e, f+bc). |
| `B21.a-Q-epos` | mutation path | App. B.2.1 | d<b, e>=0: Q = mu_2 P = (1, d, -c, r, -e, F+re). |
| `B21.a-Q-eneg` | mutation path | App. B.2.1 | d<b, e<=0: Q = (1, d, -c+e, r, -e, F) and mu_3 Q = (1,-d,-c+e+dF,-r,-e+rF,-F). |
| `B21.a-epos` | inequality | App. B.2.1 | e > 0 makes b34(Q) = F + re > F. |
| `B21.a-eneg` | inequality | App. B.2.1 | e < 0 makes b24(mu_3 Q) = -e + rF > F. |
| `B21.a-r` | inequality | App. B.2.1 | e = 0: b24(mu_3 Q) = rF <= F forces r = 1. |
| `B21.a-d` | inequality | App. B.2.1 | e = 0, r = 1: b14(mu_3 Q) = dF - c <= F forces d = 1, so b = 2 and C = A_c. |
| `B21.b-pf` | identity | App. B.2.1 | With d = b+r and f = F-bc: p = F + rc + be. |
| `B21.b-epos` | inequality | App. B.2.1 | b<d, e>=0: p >= F, contradicting 2\|p\| < m <= F-1. |
| `B21.b-Q` | mutation path | App. B.2.1 | b<d, e=-E<0: Q = mu_2 P = (1, b, -c-E, -r, E, F-rE). |
| `B21.b-mu3Q-a` | mutation path | App. B.2.1 | If rE >= F: mu_3 Q has b12 = 1+br and b24 = E - r(rE-F). |
| `B21.b-mu3Q-b` | mutation path | App. B.2.1 | If rE <= F: mu_3 Q has b12 = 1+br and b24 = E. |
| `B21.b-rE2` | inequality | App. B.2.1 | rE = 2F with E <= F-1 forces r >= 3. |
| `B21.b-rE3` | inequality | App. B.2.1 | rE = 2F, r >= 3: b24(mu_3 Q) = E - rF < -F. |
| `B21.markov-1423` | identity | App. B.2.1, eq. (positive-order-markov) | M in the order <1,4,2,3> for C = (1,-b,c,d,-E,f). |
| `B21.b-reduced` | identity | App. B.2.1 | With d=b+r, E=F-c, f=F-bc: m = 1+b^2+br+r^2-(b-2)F^2-rFE-cE. |
| `B21.b-reduced-p` | identity | App. B.2.1 | ... and p = (r+1)c - (b-1)E. |
| `B21.b-b3` | inequality | App. B.2.1 | b >= 3: m <= 1+(b+r)^2-F^2 <= 2-2F < 3. |
| `B21.b-b2-identity` | identity | App. B.2.1 | b = 2: m = 6+2r+r^2-(r+1)F-(E-1)((r+1)F-E-1). |
| `B21.b-b2` | inequality | App. B.2.1 | b = 2: m <= 3-2r <= 1. |
| `B21.b-b1-E` | inequality | App. B.2.1 | b = 1: p = (r+1)c > 0 and 2p < m <= F-1 = c+E-1 give E >= (2r+1)c + 2. |
| `B21.b-b1-triangle` | sign pattern | App. B.2.1 | b = 1: C = (1,-1,c,1+r,-E,E) contains the oriented triangle 2 -> 3 -> 4 -> 2. |
| `B21.b-b1-markov3` | inequality | App. B.2.1 | b = 1: the triangle (r+1, E, E) has Markov constant (r+1)^2-(r-1)E^2 <= 4 (all weights >= 2). |
| `B21.c-pf` | identity | App. B.2.1 | d = b, f = F-bc: p = F + be. |
| `B21.c-epos` | inequality | App. B.2.1 | d = b, e >= 0: p >= F, contradiction. |
| `B21.c-Q` | mutation path | App. B.2.1 | d = b, e = -E: Q = (1, b, -c-E, 0, E, F) and b14(mu_3 Q) = bF - c - E. |
| `B21.c-b3` | inequality | App. B.2.1 | d = b: bF - c - E <= F forces b <= 2. |
| `B21.c-b1-m` | identity | App. B.2.1 | b = d = 1: m = 2+c^2+E^2+f^2+cf-Ef. |
| `B21.c-b1` | inequality | App. B.2.1 | b = d = 1 (F = c+f): m - F = 2+c(c-1)+cf+(E-f)^2+f(E-1) > 0. |
| `B21.c-b2-m` | identity | App. B.2.1 | b = d = 2, c+E = F: m = 5 - cE. |
| `B21.c-b2` | inequality | App. B.2.1 | b = d = 2: cE <= 2 forces c+E <= 3 < F. |
| `B21.n-P` | mutation path | App. B.2.1 | For c = -t <= 0: mu_1 C = (-1, b, t, d-b, e-t, f). |
| `B21.n-vortex` | sign pattern | App. B.2.1 | If f < 0 then C = (1,-b,-t,d,-v,f) is a vortex (4 is a source). |
| `B21.n-dlt` | mutation path | App. B.2.1 | d = b - r < b: Q = (1, d, -v, r, F, f) and b24(mu_3 Q) = F + rf. |
| `B21.n-dlt-f` | inequality | App. B.2.1 | f > 0 would give b24(mu_3 Q) = F + rf > F. |
| `B21.n-dlt-p` | inequality | App. B.2.1 | f = 0: \|p\| = bv + td >= F, contradiction. |
| `B21.n-deq-p` | identity | App. B.2.1 | d = b: p = f - bF. |
| `B21.n-deq-b2` | inequality | App. B.2.1 | d = b >= 2: \|p\| >= 2F-(F-1) > F. |
| `B21.n-deq-order0` | sign pattern | App. B.2.1 | b = d = 1, f >= 0: the unique proper wiggle class contains <1,2,3,4>. |
| `B21.n-deq-order1` | sign pattern | App. B.2.1 | b = d = 1, f >= 0: the unique proper wiggle class contains <1,2,3,4>. |
| `B21.n-deq-m` | identity | App. B.2.1 | b = d = 1: m = 2+t^2+v^2+f^2+tv-vf. |
| `B21.n-deq-b1` | inequality | App. B.2.1 | b = d = 1 (F = t+v): m - F > 0. |
| `B21.n-dgt` | mutation path | App. B.2.1 | d = b + r > b: Q = (1, b, -v, -r, F, f-rF) and b34(mu_3 Q) = rF - f. |
| `B21.n-dgt-r` | inequality | App. B.2.1 | rF - f <= F with f <= F-1 forces r = 1. |
| `B21.n-dgt-p` | identity | App. B.2.1 | d = b+1, f = F-u: -p = bv + td - f = (b-1)F + t + u. |
| `B21.n-dgt-b2` | inequality | App. B.2.1 | b >= 2: \|p\| >= F, contradiction. |
| `B21.n-dgt-b1` | inequality | App. B.2.1 | b = 1, d = 2: 2(t+u) < m <= F-1, so C = I_{t,u} with 2(t+u) <= F-2. |
| `B22.paths-+++` | mutation path | App. B.2.2 | P, Q and two entries of mu_3 Q, for sign case c+0, h+0, z+0. |
| `B22.paths-++-` | mutation path | App. B.2.2 | P, Q and two entries of mu_3 Q, for sign case c+0, h+0, z-0. |
| `B22.paths-+-+` | mutation path | App. B.2.2 | P, Q and two entries of mu_3 Q, for sign case c+0, h-0, z+0. |
| `B22.paths-+--` | mutation path | App. B.2.2 | P, Q and two entries of mu_3 Q, for sign case c+0, h-0, z-0. |
| `B22.paths--++` | mutation path | App. B.2.2 | P, Q and two entries of mu_3 Q, for sign case c-0, h+0, z+0. |
| `B22.paths--+-` | mutation path | App. B.2.2 | P, Q and two entries of mu_3 Q, for sign case c-0, h+0, z-0. |
| `B22.paths---+` | mutation path | App. B.2.2 | P, Q and two entries of mu_3 Q, for sign case c-0, h-0, z+0. |
| `B22.paths----` | mutation path | App. B.2.2 | P, Q and two entries of mu_3 Q, for sign case c-0, h-0, z-0. |
| `B22.hF-f` | inequality | App. B.2.2 | h = -F: f > 0 would make b24(mu_3 Q) = F + (b+D)f > F. |
| `B22.hF-acyclic` | sign pattern | App. B.2.2 | h = -F and f <= 0: C is acyclic (topological order 4<3<1<2). |
| `B22.gF-e` | inequality | App. B.2.2 | g = F: e > 0 would make b34(Q) = z = F + (b+D)e > F. |
| `B22.gF-bD` | inequality | App. B.2.2 | g = F, e <= 0: b24(mu_3 Q) = -e + (b+D)F <= F forces b + D = 1. |
| `B22.gF-e0` | inequality | App. B.2.2 | g = F, b = 1, D = 0: -e + F <= F forces e >= 0, so e = 0. |
| `B22.gF-acyclic` | sign pattern | App. B.2.2 | Then C = (1,-1,c,0,0,F-c) with 0<c<F is acyclic (3<1<2<4). |
| `B22.bD-D` | inequality | App. B.2.2 | b + D = F: b12(mu_3 Q) = 1 - DF >= -F forces D = 1 (so b = F-1). |
| `B22.bD-z` | inequality | App. B.2.2 | b24(mu_3 Q) = -h + F[z]_+ <= F with h <= F-1 forces z <= 1. |
| `B22.bD-pf` | identity | App. B.2.2 | With b = T = F-1 and D = 1: p = f + Te - c. |
| `B22.bD-cpos-e` | inequality | App. B.2.2 | c > 0: z = f + Tc + F[e]_+ <= 1 forces e <= 0. |
| `B22.bD-cpos-p` | inequality | App. B.2.2 | c > 0, e <= 0, f + Tc <= 1: p = f + Te - c <= -T, contradiction. |
| `B22.bD-cneg-f2` | inequality | App. B.2.2 | c = -t <= 0, f > 0: z = f + F[e-t]_+ <= 1 forces f = 1 ... |
| `B22.bD-cneg-et` | inequality | App. B.2.2 | ... and e <= t. |
| `B22.bD-cneg-b24` | mutation path | App. B.2.2 | c = -t, f = 1, e <= t: b24(mu_3 Q) = F + t - e. |
| `B22.bD-cneg-ete` | inequality | App. B.2.2 | F + t - e <= F forces e >= t, so e = t. |
| `B22.bD-vortex` | sign pattern | App. B.2.2 | e = t > 0, f = 1: C = (1,-T,-t,-1,t,1) is a vortex (3 is a source). |
| `B22.bD-t0` | sign pattern | App. B.2.2 | e = t = 0, f = 1: C = (1,-T,0,-1,0,1) is acyclic. |
| `B22.bD-fneg-pf` | identity | App. B.2.2 | c = -t: p = f + Te + t. |
| `B22.bD-fneg-e2` | inequality | App. B.2.2 | f <= 0, e >= 2: p >= T, contradiction. |
| `B22.bD-fneg-e0` | sign pattern | App. B.2.2 | f <= 0, e <= 0: C is acyclic. |
| `B22.bD-fneg-e1-00` | sign pattern | App. B.2.2 | e = 1, t = f = 0: C is acyclic. |
| `B22.bD-order-tf` | sign pattern | App. B.2.2 | e = 1, (t,f) != (0,0): the unique proper class contains <1,2,4,3>. |
| `B22.bD-order-t0` | sign pattern | App. B.2.2 | e = 1, (t,f) != (0,0): the unique proper class contains <1,2,4,3>. |
| `B22.bD-order-f0` | sign pattern | App. B.2.2 | e = 1, (t,f) != (0,0): the unique proper class contains <1,2,4,3>. |
| `B22.bD-m` | identity | App. B.2.2 | m = T^2+T+3+t(t-1)+f^2+f(T+1-Tt). |
| `B22.bD-mbig` | inequality | App. B.2.2 | m >= T^2+T+3-(T+1)^2/4 > T, contradicting m <= T. |
| `B23.paths-+++` | mutation path | App. B.2.3 | P, Q and three entries of mu_3 Q, for sign case d+0, e-t+0, z+0. |
| `B23.paths-++-` | mutation path | App. B.2.3 | P, Q and three entries of mu_3 Q, for sign case d+0, e-t+0, z-0. |
| `B23.paths-+-+` | mutation path | App. B.2.3 | P, Q and three entries of mu_3 Q, for sign case d+0, e-t-0, z+0. |
| `B23.paths-+--` | mutation path | App. B.2.3 | P, Q and three entries of mu_3 Q, for sign case d+0, e-t-0, z-0. |
| `B23.paths--++` | mutation path | App. B.2.3 | P, Q and three entries of mu_3 Q, for sign case d-0, e-t+0, z+0. |
| `B23.paths--+-` | mutation path | App. B.2.3 | P, Q and three entries of mu_3 Q, for sign case d-0, e-t+0, z-0. |
| `B23.paths---+` | mutation path | App. B.2.3 | P, Q and three entries of mu_3 Q, for sign case d-0, e-t-0, z+0. |
| `B23.paths----` | mutation path | App. B.2.3 | P, Q and three entries of mu_3 Q, for sign case d-0, e-t-0, z-0. |
| `B23.pf` | identity | App. B.2.3 | p = f - xe - td. |
| `B23.eF-dneg-w` | inequality | App. B.2.3 | d = -D < 0: b24(mu_3 Q) = F + D[w]_+ <= F forces w <= 0. |
| `B23.eF-dneg-x` | inequality | App. B.2.3 | d = -D < 0, w = -v <= 0, (x+D)v <= t: x >= 1 gives p = xF + tD - v >= F. |
| `B23.eF-dneg-pf` | identity | App. B.2.3 | with d=-D, e=-u, f=w+xt, w=-v, u=F-t: p = xF + tD - v. |
| `B23.eF-acyc1` | sign pattern | App. B.2.3 | x = 0, d < 0, f <= 0: C is acyclic. |
| `B23.eF-dpos-d` | inequality | App. B.2.3 | d >= 2: b34(Q) = w - dF >= -F would force w >= F, but w <= f <= F-1. |
| `B23.eF-d0-pf` | identity | App. B.2.3 | d = 0, e = -u = t - F: p = w + xF. |
| `B23.eF-d0-x2a` | inequality | App. B.2.3 | d = 0, x >= 2, w >= 0: p >= 2F, contradiction. |
| `B23.eF-d0-x2b` | inequality | App. B.2.3 | d = 0, x >= 2, w < 0 with x(-w) <= t: p = xF + w >= 2F - t > F. |
| `B23.eF-d0-x1` | inequality | App. B.2.3 | d = 0, x = 1, -w <= t: f = t + w >= 0. |
| `B23.eF-d1-x` | inequality | App. B.2.3 | d = 1, x >= 1: F - w >= 1 + xt and x(F - w) <= t are incompatible. |
| `B23.eF-acyc2` | sign pattern | App. B.2.3 | x = d = 0: C = (1,0,-t,0,-u,f) is acyclic for any f. |
| `B23.eF-acyc3` | sign pattern | App. B.2.3 | (x,d) = (0,1) or (1,0) with f = 0: C is acyclic. |
| `B23.eF-acyc4` | sign pattern | App. B.2.3 | (x,d) = (0,1) or (1,0) with f = 0: C is acyclic. |
| `B23.eF-ord01` | sign pattern | App. B.2.3 | f > 0: the unique proper wiggle class contains <1,2,3,4>. |
| `B23.eF-ord10` | sign pattern | App. B.2.3 | f > 0: the unique proper wiggle class contains <1,2,3,4>. |
| `B23.eF-m01` | identity | App. B.2.3 | m = 2+t^2+u^2+tu+f^2-lambda f with lambda = F or t. |
| `B23.eF-m01-big` | inequality | App. B.2.3 | m >= 2 + F^2/2 > F (F = t+u), contradicting m <= F-1. |
| `B23.eF-m10` | identity | App. B.2.3 | m = 2+t^2+u^2+tu+f^2-lambda f with lambda = F or t. |
| `B23.eF-m10-big` | inequality | App. B.2.3 | m >= 2 + F^2/2 > F (F = t+u), contradicting m <= F-1. |
| `B23.wF-x` | inequality | App. B.2.3 | w = -F: f = xt - F >= -(F-1) forces x >= 1. |
| `B23.wF-dneg-D` | inequality | App. B.2.3 | x + D = F: b12(mu_3 Q) = 1 - FD >= -F forces D = 1. |
| `B23.wF-dneg-z` | inequality | App. B.2.3 | x + D = F, D = 1: b14(mu_3 Q) = min(t,e) - F[-z]_+ >= -F forces z >= -1. |
| `B23.wF-dneg-et` | inequality | App. B.2.3 | z = -F + [e-t]_+ >= -1 needs e - t >= F-1, but e - t <= F-2. |
| `B23.wF-dneg-zmF` | inequality | App. B.2.3 | z = -F: b14(mu_3 Q) = min(t,e) - (x+D)F <= F-1-2F < -F. |
| `B23.wF-dneg-zF-D` | inequality | App. B.2.3 | z = F: b24(mu_3 Q) = t - e + DF <= F with e - t <= F-2 forces D = 1. |
| `B23.wF-dneg-zF` | inequality | App. B.2.3 | z = F, D = 1: -F + (e - t) = F is impossible since e - t <= F-2. |
| `B23.wF-dpos-z` | inequality | App. B.2.3 | d >= 0: z = -F - d[t-e]_+ >= -F forces d[t-e]_+ = 0. |
| `B23.wF-dpos-x` | inequality | App. B.2.3 | z = -F: b14(mu_3 Q) = min(t,e) - xF >= -F forces x <= 1. |
| `B23.wF-dpos-e` | inequality | App. B.2.3 | x = 1: min(t,e) - F >= -F forces e >= 0. |
| `B23.wF-dpos-d` | inequality | App. B.2.3 | d > 0, e >= t: b24(mu_3 Q) = t - e - dF >= -F forces d = 1 ... |
| `B23.wF-dpos-e2` | inequality | App. B.2.3 | ... and e = t. |
| `B23.wF-d1-pf` | identity | App. B.2.3 | x = d = 1, e = t, f = t - F: p = -F - t. |
| `B23.wF-d1-p` | inequality | App. B.2.3 | \|p\| = F + t > F, contradiction. |
| `B23.wF-d0-acyc` | sign pattern | App. B.2.3 | d = 0, e = 0: C = (1,1,-t,0,0,-u) is acyclic. |
| `B23.wF-d0-order` | sign pattern | App. B.2.3 | d = 0, e > 0: the unique proper wiggle class contains <1,2,3,4>. |
| `B23.wF-d0-m` | identity | App. B.2.3 | m = 2+t^2+u^2+e^2+tu-te. |
| `B23.wF-d0-big` | inequality | App. B.2.3 | m >= 2 + 3t^2/4 + u^2 + tu > t + u = F. |
| `B3.A-segment` | mutation path | App. B.3 | The excursion [1,2,3,1,3] from A_c (table rows 1-5). |
| `B3.A-replacement` | mutation path | App. B.3 | The replacement [2,1,3] from A_c (table rows 6-8). |
| `B3.A-relabel` | identity | App. B.3 | mu_[2,1,3] A_c = (mu_[1,2,3,1,3] A_c)^{pi_123}. |
| `B3.A-forced1` | mutation path | App. B.3 | After [1,2,3], mutation at 2 or 4 creates 2F - c or F^2 - 1. |
| `B3.A-forced1b` | mutation path | App. B.3 | (mutation at 4) |
| `B3.A-forced2` | mutation path | App. B.3 | After [1,2,3,1], mutation at 2 or 4 creates 2F - c or -1 - F(F-c). |
| `B3.A-forced2b` | mutation path | App. B.3 | (mutation at 4) |
| `B3.A-forced-2Fc` | inequality | App. B.3 | These entries exceed F in absolute value. |
| `B3.A-forced-F2` | inequality | App. B.3 | These entries exceed F in absolute value. |
| `B3.A-forced-FFc` | inequality | App. B.3 | These entries exceed F in absolute value. |
| `B3.A-low-lo0` | inequality | App. B.3 | Every entry along [2,1,3] (and A_c, and the endpoint) is low. |
| `B3.A-low-hi0` | inequality | App. B.3 | Every entry along [2,1,3] (and A_c, and the endpoint) is low. |
| `B3.A-low-lo1` | inequality | App. B.3 | Every entry along [2,1,3] (and A_c, and the endpoint) is low. |
| `B3.A-low-hi1` | inequality | App. B.3 | Every entry along [2,1,3] (and A_c, and the endpoint) is low. |
| `B3.I-segment` | mutation path | App. B.3 | The excursion [1,2,3] from I_{t,u}. |
| `B3.I-endpoint` | identity | App. B.3 | J = (mu_[1,2,3] I_{t,u})^{pi_123} = (1,-2,F-u,1,u,t-F). |
| `B3.I-tgu` | mutation path | App. B.3 | t > u: the replacement [2,1,3,2,3] ends at J. |
| `B3.I-ugt` | mutation path | App. B.3 | u > t: the replacement [3,1,3,2,1] ends at J. |
| `B3.I-low-tgu-lo0` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-tgu-hi0` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-tgu-lo1` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-tgu-hi1` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-tgu-lo2` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-tgu-hi2` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-tgu-lo3` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-tgu-hi3` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-tgu-lo4` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-tgu-hi4` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-tgu-lo5` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-tgu-hi5` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-ugt-lo0` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-ugt-hi0` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-ugt-lo1` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-ugt-hi1` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-ugt-lo2` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-ugt-hi2` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-ugt-lo3` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-ugt-hi3` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-ugt-lo4` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-ugt-hi4` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-ugt-lo5` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-low-ugt-hi5` | inequality | App. B.3 | Every entry along the replacement is low. |
| `B3.I-tt-pf` | identity | App. B.3 | p(I_{t,t}) = -2t. |
| `B3.I-tt-k` | inequality | App. B.3 | t = u: 4t < m <= F-1, so k = F - t >= 2. |
| `B3.I-tt-triangle` | sign pattern | App. B.3 | I_{t,t} contains the oriented triangle 2 -> 3 -> 4 -> 2 with weights (2,k,k). |
| `B3.I-tt-markov` | identity | App. B.3 | Its Markov constant is 2^2 + k^2 + k^2 - 2k^2 = 4. |
| `S2.Lk-markov` | identity | Remark 2.5 | L_k = (k,0,0,1,0,k): M = 2k^2+1. |
| `S2.Lk-pf` | identity | Remark 2.5 | L_k: p = k^2. |
| `S3.recurrence` | mutation path | Lemma 3.1 | For t >= 2: (mu_2 Q(t))^{pi_12} = Q(t-2). |
| `S3.Qt-pf` | identity | Remark 3.3 | p(Q(t)) = -4 for every t, so det B = 16. |
| `S3.Qt-class` | sign pattern | Remark 3.3 | For t >= 3, Q(t) has exactly one proper wiggle class, and it contains <1,3,4,2>. |
| `S3.Qt-markov` | identity | Remark 3.3 | M_<1,3,4,2>(Q(t)) = 12 for every t. |
| `S5.Gx-markov` | identity | Remark 5.6 | G_x = (x,x,0,1,x,-1) is acyclic (order 1<2<4<3) with M = x^3+4x^2+x+2. |
| `S5.Gx-mu4` | mutation path | Remark 5.6 | mu_4 G_x = (x, x, 0, x+1, -x, 1), of height x+1. |
| `S3.Qneg` | sign pattern | Theorem 3.2 | For t <= -3, Q(t) = (-2,t+2,t,-t,2-t,0) is acyclic (vertex 2 is a source). |
| `S5.Gx-acyclic` | sign pattern | Remark 5.6 | G_x = (x,x,0,1,x,-1) is acyclic for x >= 1. |
