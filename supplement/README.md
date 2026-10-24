# Supplement to "Mutation-acyclicity in rank four is decidable but not semialgebraic"

K. T. K. Armstrong-Williams, E. Hirst, B. Jackson, K.-H. Lee.

This package contains every computation used in the paper. It needs Python 3.8 or later and
nothing beyond the standard library. (The development tools `find_certificates.py` and
`build_certificates.py`, which search for certificates, also need SciPy; checking does not.)

## Quick start

```
python3 run_all.py                 # all checks except the conjecture evidence (a few minutes)
python3 run_all.py --full          # also conjecture_evidence.py, and bruteforce_local.py with T <= 7
python3 run_all.py path/to/main.tex   # also check the claim labels cited in the paper
```

`run_all.py` runs each program below with the same interpreter, verifies `SHA256SUMS.txt`,
and writes a transcript with the interpreter version and timings to `run_log.txt`. The checksummed
files contain no interpreter versions or timestamps, so the checksums are the same on every
Python version. The full suite passes, with identical checksums, on CPython 3.8, 3.9, 3.10, 3.11,
3.12, 3.13 and 3.14.

## What is verified, and how

| Paper | Program | What it does |
|---|---|---|
| Appendices A and B, and the calculations in Sections 2 to 5 cited as `[label]` | `check_proofs.py` | Checks all 300 claims of `proof_claims.py` exactly, for all integer values of their parameters. |
| Theorem 6.2 and Remark 6.3 | `census.py`, `check_census.py` | `census.py` writes certificates for the 695 quivers of height at most two to `census_certificates.json`; `check_census.py` checks every certificate with the independent implementation `reference_q4.py`. |
| Theorem 3.2, Remarks 3.3, 3.4, 4.6 and 5.6, Example 5.4, Corollary 5.2 | `examples.py` | Concrete checks of the examples and remarks, and the decision procedure on sample inputs. |
| Lemmas 4.2 to 4.4 and Proposition 4.5 | `bruteforce_local.py` | An independent finite check of the case analysis for $T\le 6$ (default), by enumerating all excursions using only the constraints the proof uses. A sanity check, not part of the proof. |
| Conjecture 5.5 | `conjecture_evidence.py` | Exhaustive check for connected quivers of height at most three, regions of mutation classes, and random quivers. Evidence, not proof. |
| Claim labels | `check_references.py` | Every label cited in `main.tex` and in `APPENDIX_CALCULATIONS.md` exists, and every claim is cited. |
| Basic operations | `tests.py` | Cross-checks against `reference_q4.py`, algebraic identities, the pentagon relation, invariance of the Markov value under proper mutation, and the certificate checker on wrong certificates. |

### The claims behind the appendices

Each calculation that the appendices delegate is a *claim* in `proof_claims.py`, with a label
(cited in the paper in typewriter font, for example `[A1.markov]`), a pointer to where it is used,
a one-line statement, its hypotheses and its goal. All variables are integers. The standing
hypotheses of the appendices ($F\ge4$, $3\le m\le F-1$ and $2|p|<m$, where $F=T+1$) are included
in each claim that uses them. There are four kinds.

* **Identities** (51): polynomial identities, equalities of tuples (such as a relabeling), and
  checks that a substitution permutes a system of hypotheses. Checked by exact expansion.
* **Inequalities and contradictions** (151): from hypotheses $h_i\ge0$ and equations $e_j=0$,
  conclude $g\ge0$, $g>0$, or a contradiction. Checked by a certificate
  $g=\sum_k c_k\prod_{i\in S_k}h_i\, s_k^2+\sum_j \lambda_j e_j + c_0$ with rational $c_k,c_0\ge0$
  and polynomial $s_k,\lambda_j$, verified by exact polynomial arithmetic (for a contradiction,
  $g=-1$; for $g>0$, $c_0>0$). Some certificates first split on whether an integer polynomial is
  at least $1$ or at most $0$. Hand-written certificates are in `proof_claims.py`; the others were
  found by linear programming and are stored in `certificates.json`.
* **Mutation paths** (70): a mutation word applied to a tuple of polynomials gives the stated
  tuples or entries. The mutation formula needs the sign of each entry incident to the mutation
  vertex; each such sign is certified as above from the claim's hypotheses, and then the mutation
  is carried out symbolically.
* **Sign patterns** (28): statements about proper wiggle classes, acyclicity, vortices and
  oriented triangles. These depend only on the signs of the six entries, so the checker certifies
  the allowed sign of each entry and then enumerates every allowed sign pattern.

`APPENDIX_CALCULATIONS.md` reproduces the hand calculations of an earlier version of the
appendices, with the claim labels attached to the steps they verify, and ends with an index of all
claims. It is for reading; `check_proofs.py` does not use it.

The case logic of the proofs (which cases occur and why they are exhaustive) is in the paper.
`bruteforce_local.py` tests that logic independently for small $T$.

## Files

Core (used by the proofs):
* `polynomial.py`: exact multivariate polynomials with rational coefficients. Floating-point
  coefficients are rejected.
* `certificates.py`: the certificate checker, and helpers for writing certificates by hand.
* `symbolic.py`: mutation of tuples of polynomials under given signs, and sign-pattern enumeration.
* `quiver4.py`: four-vertex quivers (mutation, relabeling, reversal, acyclicity, full triangles,
  vortices, cyclic orderings, proper wiggle classes, the Markov invariant, the bound $H(Q)$ of
  equation (13), the search of Corollary 5.2 as `decide`).
* `claims_core.py`: the four kinds of claims and their checks.
* `proof_claims.py`: the claims.
* `certificates.json`: stored certificates.
* `check_proofs.py`: checks all claims.

Census, examples and evidence:
* `census.py`, `census_certificates.json`, `check_census.py`, `reference_q4.py`.
* `examples.py`, `bruteforce_local.py`, `conjecture_evidence.py`.

Tests and tools:
* `tests.py`, `check_references.py`, `run_all.py`.
* `find_certificates.py`, `build_certificates.py` (development only, need SciPy).

Documentation: `README.md`, `APPENDIX_CALCULATIONS.md`, `SHA256SUMS.txt`.

## Conventions

These are the conventions of the paper.
* A quiver is a tuple `(b12, b13, b14, b23, b24, b34)` of Python ints, and `b_ij > 0` means
  `b_ij` arrows `i -> j`. Vertices are `1, 2, 3, 4` in every public function. (Internally,
  `reference_q4.py` uses 0-based indices; `check_census.py` converts.)
* A mutation word is a tuple of vertices applied from left to right: `(1, 2, 3)` means
  mutate at 1, then at 2, then at 3.
* `relabel(q, pi)` is $Q^\pi$ with $b_{ij}(Q^\pi)=b_{\pi(i)\pi(j)}(Q)$, where
  `pi = (pi(1), pi(2), pi(3), pi(4))`. So `PI12 = (2, 1, 3, 4)` and `PI123 = (2, 3, 1, 4)`.
* A cyclic ordering is a tuple of the four vertices read clockwise, normalized to start at 1;
  `markov(q, order)` evaluates equation (4) in the linear order `order[0] < ... < order[3]`.

## Robustness

* All arithmetic is exact, on Python ints (arbitrary precision, so nothing can overflow) and
  `fractions.Fraction`. No check uses floating point.
* Public functions validate their inputs: a quiver must be a tuple of six ints (booleans are
  rejected), and vertices must be the ints 1 to 4.
* Two implementations of the basic operations, `quiver4.py` and `reference_q4.py`, were written
  independently and are cross-checked by `tests.py`; the census checker uses only the second.
* Generated files are deterministic (sorted keys, no timestamps or interpreter versions).
* Searches that could be large take an optional state limit and report when it is reached
  instead of returning an inconclusive answer as a negative one.
