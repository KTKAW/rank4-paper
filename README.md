# Mutation-acyclicity in rank four is decidable but not semialgebraic

**Kymani T. K. Armstrong-Williams, Edward Hirst, Blake Jackson, and Kyu-Hwan Lee**

This repository supports the accompanying paper, which is being prepared for
submission to arXiv. It contains the exact-arithmetic Python supplement and
the complete retained Lean source tree for researchers and referees who want
to inspect the proofs or reproduce the computations.

The manuscript PDF and LaTeX sources are not included in this repository.
The arXiv identifier and a link to the submitted version will be added once
available.

**[Supplement documentation](supplement/README.md)** ·
**[Appendix calculations](supplement/APPENDIX_CALCULATIONS.md)**

## Main results

- **Decidability in rank four.** A mutation-acyclic four-vertex quiver *Q* has a
  path to an acyclic quiver within height max{ht(*Q*), *m*(*Q*)}, where height is
  the largest arrow multiplicity and *m* is the Markov invariant of its totally
  proper wiggle class. The computable search bound uses the largest Markov
  value over all proper wiggle classes. For input height *h* ≥ 1, the decision
  procedure searches *O*(*h*<sup>24</sup>) states (Theorem 5.1 and
  Corollaries 5.2–5.3). This is a pseudo-polynomial bound in the arrow
  multiplicities, not a polynomial bound in their binary encoding length.
- **No fixed polynomial-sign criterion in higher rank.** For every *n* ≥ 4,
  no fixed finite Boolean combination of polynomial equations and strict
  inequalities decides mutation-acyclicity on all integral *n*-vertex quivers,
  even when restricted to connected quivers (Theorem 1.2). The polynomials
  need not be mutation-invariant.
- **Corrected height-two classification.** Theorem 6.2 corrects the criterion
  in the authors' earlier paper and certifies all 695 representatives of
  four-vertex quivers of height at most two. Every positive representative
  reaches an acyclic quiver in at most three mutations within height two.
- **A sharper bound remains conjectural.** Conjecture 5.5 proposes that the
  input height alone suffices, which would give *O*(*h*<sup>6</sup>) states.
  The paper reports verification through height three and further finite and
  random evidence; this does not establish the conjecture in general.

The height-two counts are taken up to vertex relabeling; reversal of all arrows
is **not** identified:

| Quivers | Mutation-acyclic | Mutation-cyclic | Total |
| --- | ---: | ---: | ---: |
| Connected | 534 | 133 | 667 |
| Disconnected | 27 | 1 | 28 |
| **Total** | **561** | **134** | **695** |

## Quick start

The supplement requires **Python 3.8 or later** and only the standard library
for checking. From the repository root, run:

```sh
python3 supplement/run_all.py
```

This runs the unit tests, exact claim checks, census generation and independent
certificate checks, examples, local case-analysis checks through *T* = 6, and
appendix-label checks. It finishes by verifying the 22 entries in
[`SHA256SUMS.txt`](supplement/SHA256SUMS.txt). A successful run ends with
`ALL CHECKS PASSED`.

The default and extended suites were independently rerun on CPython 3.12.14
on 24 October 2026. Both passed, including all 300 claims, the census and
certificate checks, and all 22 checksums. The extended suite also passed in
an isolated copy excluding the historical files subsequently removed from
this repository. Fresh audit transcripts are held separately from the
supplied `supplement/run_log.txt`; they are not included in this checkout.

For extended reproduction:

```sh
python3 supplement/run_all.py --full
```

This also runs the conjecture-evidence program and extends the local
case-analysis check through *T* = 7. Runtime depends on the interpreter and
hardware. The supplied supplement documentation reports successful full runs
on CPython 3.8–3.14; that complete version matrix has not been independently
rerun. The independent audit used CPython 3.12.14 only.

The runner regenerates `supplement/census_certificates.json` and overwrites
`supplement/run_log.txt`. Use a separate copy to preserve the supplied
transcript. The certificate file is deterministic and must retain its checksum;
the log records interpreter information and timings and is not checksummed.

SciPy is needed only by the development tools `find_certificates.py` and
`build_certificates.py`, which search for certificates. It is not needed to
check the stored certificates or use the decision procedure.

Manuscript compilation and checking claim references against matching LaTeX
source are unavailable from this checkout. The default run checks references
in the supplied appendix Markdown; it does not establish correspondence
with the manuscript PDF.

## Using the decision procedure

Run this example from the repository root; the shell changes into the
supplement directory so that its modules can be imported:

```sh
cd supplement
python3 - <<'PY'
from quiver4 import decide, is_acyclic, mutate_word

# A positive example from Remark 6.3, with a replayable mutation witness.
q = (-2, -1, 2, -1, -1, -1)
status, word = decide(q)
print(status, word)                         # acyclic (4, 1, 3)
assert status == "acyclic"
assert is_acyclic(mutate_word(q, word))

# Example 5.4: the entire component within the proved bound is cyclic.
r = (-3, -2, 2, 0, 3, -3)
print(decide(r))
# ('cyclic', 'component within height 41 exhausted (238 quivers)')

# A state limit can stop the search before it decides the input.
print(decide(r, max_states=1))               # ('aborted', 2)
PY
```

[`decide(q, max_states=None)`](supplement/quiver4.py) returns:

| Result | Meaning |
| --- | --- |
| `("acyclic", word)` | The input is mutation-acyclic; applying `word` yields an acyclic quiver. |
| `("cyclic", reason)` | The input is mutation-cyclic, certified by an obstruction or exhaustive search within the proved bound. |
| `("aborted", n)` | The state limit was exceeded after discovering `n` states; the result is inconclusive. |

A resource limit is never evidence of mutation-cyclicity. The label `acyclic`
describes the successful decision and its endpoint; the input itself may
contain directed cycles.

## Conventions

- A quiver is a tuple `(b12, b13, b14, b23, b24, b34)` of six exact Python
  integers. Positive `bij` means arrows from vertex `i` to vertex `j`;
  negative entries mean arrows in the opposite direction. Booleans and
  floating-point entries are rejected.
- Public supplement functions use vertices **1, 2, 3, 4**. Mutation words are
  applied from left to right: `(1, 2, 3)` mutates first at 1, then 2, then 3.
- The supplement's matrix representation is the signed, skew-symmetric
  exchange matrix. A relabeling `pi` makes old vertex `pi(i)` the new vertex
  `i`; see the [complete conventions](supplement/README.md#conventions).

The Lean development uses vertices indexed from **0**. Convert vertex labels
when comparing Lean mutation words with the supplement’s public API.

## Verification and repository guide

The final paper's computational material is in `supplement/`. Its checking
arithmetic uses arbitrary-precision integers and exact rational coefficients.

| Paper material | Programs | Verification scope |
| --- | --- | --- |
| Appendices A–B and labeled calculations in Sections 2–5 | [`check_proofs.py`](supplement/check_proofs.py), [`proof_claims.py`](supplement/proof_claims.py) | 300 claims: 51 identities, 151 inequalities or contradictions, 70 mutation paths, and 28 sign-pattern claims. Exact certificates apply to all integer parameters satisfying each claim's hypotheses. |
| Theorem 6.2 and Remark 6.3 | [`census.py`](supplement/census.py), [`check_census.py`](supplement/check_census.py) | Enumerate 15,625 labeled tuples and check coverage and certificates for 695 representatives using the independent [`reference_q4.py`](supplement/reference_q4.py). |
| Selected examples and remarks in Sections 3–5 | [`examples.py`](supplement/examples.py) | Concrete examples, identities, and sample decisions; see the supplement README for individual references. |
| Lemmas 4.2–4.4 and Proposition 4.5 | [`bruteforce_local.py`](supplement/bruteforce_local.py) | Finite sanity checks of the local case analysis, not a universal proof. |
| Conjecture 5.5 | [`conjecture_evidence.py`](supplement/conjecture_evidence.py) | Exhaustive bounded searches and sampled evidence, not proof of the conjecture. |
| Operations and claim references | [`tests.py`](supplement/tests.py), [`check_references.py`](supplement/check_references.py) | Independent implementation comparisons, rejection of invalid certificates, and appendix-label consistency. |

The paper supplies the case logic and its exhaustiveness arguments; the exact
checker verifies the calculations delegated to it. The readable
[appendix calculations](supplement/APPENDIX_CALCULATIONS.md) explain those steps
but are not an input to the mathematical claim checker.

| Location | Role |
| --- | --- |
| [`supplement/`](supplement/) | Author-supplied computational package, with documentation, stored certificates, independent checks, checksums and the supplied run log. |
| [`lean/`](lean/) | All 573 retained Lean source modules, the source provenance manifest, and pinned toolchain and dependencies. |
| [`scripts/check_lean.py`](scripts/check_lean.py) | Source-build verification runner. Use `--full`; the historical focused modes require private research directories. |
| [`scripts/package_lean.py`](scripts/package_lean.py) | Historical source-packaging recipe retained for provenance. It uses author-local paths and is not needed to build the supplied sources. |

The earlier classifier, benchmark package and manuscript-generation scripts
have been removed from this checkout. The supplement is the computational
entry point for the accompanying paper.

## Lean proofs: scope and reproduction

The complete retained Lean tree is preserved, including modules outside the
principal theorem files. The [source manifest](lean/source-manifest.json)
records module provenance, source hashes and build order. The configured
targets collectively depend on all 573 project modules.

| Entry point | Formal content and relationship to the paper |
| --- | --- |
| [ClassificationCompletion.lean](lean/Rank4CoordinatorR2/ClassificationCompletion.lean) | Rank-four height coverage and decidability. Its height budget is the sum of absolute entries and absolute Markov values over all six cyclic orders; it differs from the sharper bound printed in the paper and implemented by the supplement. |
| [BoundedClassificationCompletion.lean](lean/QuiverProofs/BoundedClassificationCompletion.lean) | Height-two classification, the three-mutation positive bound, and census counts. |
| [NoPolynomialSignClassifier.lean](lean/Rank4Round7/Coordinator/NoPolynomialSignClassifier.lean) | The polynomial-sign obstruction for rational coefficients in rank four. The paper's real-coefficient, higher-rank and connected-quiver extensions require the separate arguments in the manuscript. |
| [AlternatingIntegerLine.lean](lean/Rank4Round8/Arithmetic/AlternatingIntegerLine.lean) | Classification of the integer alternating family: mutation-acyclic exactly for negative or even parameters. |
| [ChoiceFreeListDedup.lean](lean/Rank4Round8/Reduction/ChoiceFreeListDedup.lean) | A deduplicated finite search bound using the Lean development's height budget. |

These formal statements support the paper but do not constitute a complete
formalization of every statement in its final form. The Python supplement is
not extracted from Lean, and no end-to-end formal verification of the Python
implementation is claimed. Its public verification workflow is described above.

Use the pinned **Lean 4.24.0** toolchain and revisions in
[`lake-manifest.json`](lean/lake-manifest.json). With `elan` and its `lean` and
`lake` commands available on your PATH, run the following from the repository
root in a fresh copy:

```sh
(
  cd lean
  mkdir -p audit
  lake exe cache get
  python3 ../scripts/check_lean.py --full --lean "$(command -v lean)"
)
```

The cache command obtains matching third-party dependency objects. Do not run
`lake update` when reproducing the pinned sources. The full checker compiles
all project modules in manifest order with `--trust=0 -j1`, writing project
objects under `lean/.fresh-full/` and reports under `docs/checks/lean_full/`.
It stops at the first failure. The `audit` directory is required because one
module writes `audit/ResolvedModules.json` during compilation. The historical
focused and assembly modes reuse project objects from private directories;
use `--full` for a source-only project replay.

**A complete clean Lean build remains unverified.** The 24 October 2026 audit
compiled 135 of 573 modules successfully, with no compiler rejections among
the attempted modules. Eight modules exceeded an audit-imposed five-minute
limit, four were interrupted, 35 were blocked by those dependencies, and 391
were not attempted before the audit's time budget ended. These resource
outcomes are not proof failures, but they also do not establish a successful
all-module build. The command above is the reproduction procedure; it is not
a claim that the audit completed it.

## Citation and attribution

The arXiv identifier is pending. Until it is available, the following is a
provisional manuscript citation. Once assigned, add the arXiv identifier and
versioned paper URL; the repository URL below identifies the supporting code.

```bibtex
@misc{ArmstrongWilliamsEtAl2026RankFour,
  author = {Armstrong-Williams, Kymani T. K. and Hirst, Edward
            and Jackson, Blake and Lee, Kyu-Hwan},
  title  = {Mutation-acyclicity in rank four is decidable but not semialgebraic},
  year   = {2026},
  note   = {Manuscript; arXiv submission forthcoming},
  url    = {https://github.com/KTKAW/rank4-paper}
}
```

Original source headers and the [Lean source manifest](lean/source-manifest.json)
preserve source attribution and provenance, including hashes for packaged
sources. Lean, mathlib and their dependencies retain their respective
licences and notices. This repository currently has no root licence file;
a repository licence remains to be specified by the authors.
