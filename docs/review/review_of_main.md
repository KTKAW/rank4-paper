# Review of `main.pdf` — "Beyond polynomial decision boundaries for four-vertex mutation-acyclicity" (working draft, 8 October 2026)

Reviewer notes prepared 8 October 2026. All explicit computations in the paper were re-derived independently in Python (`review_checks_main.py`, same folder). Lean claims were checked by reading the sources in `importantproofs/` and its `research/` update; no Lean toolchain is installed here, so no kernel rebuild was run.

## 0. Verdict on the three questions asked

**(a) Is the correction to [1, Theorem 2.9] correct and clearly proved?**
The corrected statement (Proposition 3.2: for weights in [−2, 2], MA ⟺ an acyclicizing word of length ≤ 3 exists) is correct. It is kernel-checked in the October 4 package as `bounded_MA_iff_three_mutations` / `corrected_bounded_classification` (standard axioms only, see §3 below), and it agrees with the independent box-search classification I ran in the earlier session (534/133 connected, 27/1 disconnected).
But the paper does **not** present it as a correction and does **not** prove it. The draft never says that [1, Theorem 2.9] is false, never gives the counterexample (the double-arrow box), never states the class counts, and gives no proof or proof outline of Proposition 3.2. It only says "This is the project's stronger bounded-depth certificate theorem, not a restatement of Theorem 2.9 of [1]". As written, a reader of [1] would not learn that Theorem 2.9 needs correcting. See §1, item 1 for what to add.

**(b) Is the algorithm construction correct and clear?**
Corollary 7.2 (explore the mutation graph inside the box ht ≤ H(B)) is correct *given* Theorem 7.1, and the loop-erasure argument for the word bound N(B) − 1 is right. Two problems: Theorem 7.1 is cited to an unpublished manuscript [4] that is not available to readers, so the paper's decidability claim cannot be checked from the paper; and the description of the "implemented hybrid" is not reproducible from the text (no pseudocode, undefined jargon). See §1, items 4–5.

**(c) Is the impossibility proof correct and clear?**
Theorem 4.2 is correct and its proof (Lemma 4.1 + Theorem 3.4) is clear. Every computation behind it checks out (Lemma 3.1 for all t ≥ 0, Lemma 3.3, Theorem 3.4 including the negative half-line). One caveat on scope: it rules out polynomial-sign *decision rules*, not polynomial mutation *invariants* with an arbitrary decoder. That stronger statement is available almost for free (Chelnokov + Proposition 6.3) and should be added; see §1, item 3. Also, the only nontrivial input to the proof, NMA of the seed s₁, can be proved in two lines without the bounded classification (§1, item 2), which makes the main theorem independent of the correction and fully human-checkable modulo [3].

## 1. Errors and gaps in the reasoning (major)

1. **The correction of [1, Theorem 2.9] is absent.** [1, Theorem 2.9] states: for weights in {0, 1, 2}, Q is NMA iff (i) some quiver in its mutation class has an NMA full rank-3 subquiver, or (ii) Q ≅ dreaded torus. The box q□ = (−2, 0, 2, −2, 0, −2) is NMA, is not the torus, and (Warkentin, thesis Ex. 6.11 + the inward-mutation argument of the 30 Sept note, Prop. 5.1) no quiver in its class contains an NMA triangle. So the published equivalence is false even though its class counts (534/133) are right. The paper should contain a section with: the false statement; the counterexample and its proof (or at least the proper-order certificate: μ₀ q□ = (2, 0, −2, −2, 4, −2) has a unique proper class with M = 0 < 3, contradicting [3, Cor. 6.6]); the replacement theorem with counts (667 connected classes: 534 MA, 133 NMA; 28 disconnected: 27 MA, 1 NMA; witnessing words have all intermediate weights ≤ 2); and a proof outline (positive side: explicit words; negative side: 46 classes by the rank-3 Markov criterion [BBH] plus heredity [BMR Cor. 5.3 / Warkentin 2011 Prop. 2.3], 1 by a finite closed class, 86 by proper-order endpoint exclusion [2, 3]), ending with the Lean name `corrected_bounded_classification` and its axiom closure. It must be labelled computer-assisted.

2. **Lemma 3.3 relies on Proposition 3.2 unnecessarily; the seeds have a two-line NMA proof.** s₁ = (−2, −1, −1, 1, −1, 1) and s₃ = (−2, 1, −1, 1, 1, 1) have full support, so every wiggle class is a single cyclic order. Proper vertices per order (right-turn rule of [2, Def. 5.2]):

   | order | s₁ proper vertices | s₃ proper vertices |
   |---|---|---|
   | (0,1,2,3) | 0,2,3 | 1,2,3 |
   | (0,1,3,2) | 0 | 1 |
   | (0,2,1,3) | 0 | 0,1,3 |
   | (0,2,3,1) | 0,1,3 | 0,1,2 |
   | (0,3,1,2) | 0,1,2 | 1 |
   | (0,3,2,1) | 0 | 1 |

   No order is proper at all four vertices, so neither seed admits a proper cyclic ordering [2, Def. 11.1], hence neither is totally proper, hence both are NMA by [3, Theorem 1.1]. This removes the dependence of Theorem 4.2 on the formal bounded classification entirely (the paper's own Introduction wants exactly this separation) and lets a reader verify the whole no-go argument by hand. Keep the 85-word check as a remark if desired, but it should not be the proof.

3. **"No polynomial invariant" is a different statement from Theorem 4.2, and it can be added cheaply.** Theorem 4.2 excludes fixed polynomial-sign formulas (decision rules). It does not exclude, e.g., "MA iff f(B) is even" for a polynomial mutation invariant f. Chelnokov (arXiv:2311.01784) proves that every invariant of 4-vertex quivers under mutation that is polynomial on each sign chamber is a function of det B. Combined with Proposition 6.3 (the MA tuple (1,1,1,2,1,1) and the NMA tuple (−2,1,1,−1,−1,−1) both have P² = det = 4), this gives: *no piecewise-polynomial mutation invariant determines MA, with any decoder.* The September note's Theorem 8.1 (degree ≤ 4 invariants are span{1, det B}) is an independent finite check of the degree-≤4 case. Chelnokov's paper is a short unrefereed preprint, so state the corollary conditionally, but it should be in the paper and in the title/abstract framing. Currently Chelnokov is not cited at all.

4. **Theorem 7.1 (bounded paths) is unverifiable from the paper.** It is cited to [4], "unpublished manuscript supplied with this project", with local file names. Corollary 7.2 — the decidability result the abstract advertises — therefore rests on a document the reader cannot see. Either post [4] (arXiv) and cite it properly, or include a genuine proof sketch (the three-sentence "Proof dependency" paragraph is not one). In the earlier session I audited the Lean package behind `heightCoverage` (no `sorry`/axioms/`native_decide`, standard axioms in the recorded build) and tested the statement on 13,497 random MA inputs without finding a violation, so I have no reason to doubt it; but the paper must make it checkable.

5. **The algorithm is not specified.** Section 7's "implemented hybrid ... may test a bounded number of neighboring states, then apply a certified preprocessing transformation and invoke a deduplicated breadth-first frontier search with an appropriate verified budget" cannot be reproduced. Give pseudocode: (1) disconnected ⟹ Prop. 5.1; (2) sufficient MA guards (Props. 5.2–5.4, the line of Theorem 3.4); (3) NMA rejections (Prop. 6.2, the (11,16)/(18,49) exclusions); (4) otherwise BFS over mutation-reachable states with ht ≤ H(B), returning MA iff an acyclic state is found. State the cost theorem (`firstGapSparseExpandedMutationEvals_le`: at most 4 + 4(2H+1)⁶ mutation evaluations) and note that the reachable set is usually far smaller than N(B): for s₁, H = 71, N ≈ 8.8·10¹², but the reachable box component has 22,896 states (0.9 s in Python). Note also that the October 4 package's fallback `findPositive` enumerates all 4^L words rather than states; say which implementation the paper means.

6. **Proposition 6.2's proof has a missing step.** The transported totally proper order at the acyclic endpoint need not be a topological order, and M depends on the order (for the acyclic quiver 0→1→2→3, 0→3 with unit weights, the proper order (0,3,1,2) gives M = 4 = 2|P| while the topological order gives M = 5). The gap is closed by [2, Theorem 14.3] (at most one totally proper ordering up to wiggles), [2, Observation 11.6] / [3, Remark 1.2] (the topological ordering of an acyclic quiver is totally proper), and wiggle-invariance of M (it is a coefficient of the Alexander polynomial, [2, (9.6)–(9.7)]). The Lean proof does contain this step (`QuiverProofs.ProperEndpoint.endpointTopological4`, used in `allProperScalarsFailGap_NMA`); the prose should too. Also cite [2, Cor. 14.2] for "proper transport preserves the ordered scalar".

7. **Proposition 5.2's converse is correct but too compressed to check.** I verified both directions for all x, y, z, u, v ∈ {1,…,4} and confirmed: the input has a unique proper class {(0,1,3,2),(0,3,2,1)}; the Fomin–Neville proper mutation at 0 ([2, Def. 6.1]: the mutated vertex moves clockwise past Out(0) = {3} without passing In(0) = {2}) lands on the singleton class (0,2,1,3); when xy > v the path 2→3→1 is a left turn there. But μ₀q has *another* proper class {(0,1,2,3),(0,2,3,1)}, so the reader needs the argument spelled out: uniqueness of the initial proper class pins down the only candidate totally proper class, and total properness is closed under proper mutation [2, Def. 14.1], so an improper transported class proves NMA. State the placement rule before using it.

8. **The intro's dependency claim is true for the proof term but false for the Lean module.** `Rank4Round7.Coordinator.NoPolynomialSignClassifier` imports `Rank4Round7.Structure.AlternatingLineIdentity` → `ExecutableMAInvariant` → `ClassifierBridge` → `Rank4CoordinatorR2.ClassificationCompletion` (i.e. `heightCoverage`), although the proof of `no_fixed_polynomial_sign_classifier` only uses `PolynomialTail` and `Rank7Adversarial.PolynomialAlternation`, whose 340-file closure does not contain the bounded-path modules. Drop the unused import (it only serves `alternatingPolynomial_eval`) so the "small entry point" recommended in Section 9 actually exists.

9. **Lemma 3.1's proof should say which positive-part evaluations use t ≥ 0.** The recurrence fails for every t < 0 (checked t = −6,…,−1). The evaluations used are [t]₊ = t, [−t]₊ = 0, [t+2]₊ = t+2, [−(t+4)]₊ = 0, [−(t+2)]₊ = 0. "Including the cancellation at t = 0" is not understandable; write out μ₀ and μ₁ explicitly (two short displays).

## 2. Smaller mathematical remarks

- Corollary 4.3 can be made concrete: μ[1,0]ⁿ q(4n) = q(0), so q(4n) has an acyclicizing word of length 2n; computation shows 2n is minimal for n ≤ 5 and q(4n+2) needs exactly 2n+1 (n ≤ 5).
- Section 6.1: also record the simpler necessary condition M ≥ 3 for connected MA inputs ([3, Cor. 6.6], n − 1 = 3); it is what kills the box.
- Section 6.2: the (11,16) and (18,49) exclusions are 4⁶ and 5⁶ evaluations; say so, so readers can repeat them (I did: no nonnegative tuple with entries ≤ ⌊√m⌋ has either pair).
- Proposition 5.1: define "consecutive cycle entries": for the triangle (i,j,k), (x,y,z) = (b_ij, b_jk, b_ki); the four substitutions T(a,d,−b), T(a,e,−c), T(b,f,−c), T(d,f,−e) are then forced. Verified against box search for all 1,441 disconnected inputs with entries in [−3,3].
- Proposition 5.1's proof cites "[1]" for the rank-3 criterion; cite Beineke–Brüstle–Hille directly (Theorems 1.1–1.2).
- The 24-state closed class for (−2,1,1,−1,−1,−1) is confirmed (24 labelled states, all cyclic); this is the right kind of certificate to print, since it is independent of Theorem 7.1.
- Theorem 7.1 as stated includes the empty prefix; fine. N(B) counts labelled integer matrices in the box, so "at most N(B) labeled integer matrices occur" is right only because states are labelled; say "labelled".
- Section 8: "transitive axiom closures [propext, Quot.sound]" for executables is a true but unimportant observation; consider cutting.

## 3. What was verified and how

- Lemma 3.1 for t = 0,…,60 (and failure for t < 0). Lemma 3.3: q(0) acyclic with ranks (1,0,2,2); μ₁q(2) = (2,0,2,2,0,0) with ranks (0,1,2,1); no word of length ≤ 3 acyclicizes s₁ or s₃; μ[0,1]s₁ = q(1); μ[1,0]q(3) = s₃. Theorem 3.4: ranks (2,0,1,1) for t ≤ −2 and (2,0,3,1) for t = −1; connectedness for all t.
- Independent labels by box search inside H(B): s₁, s₃, q(1), q(3) NMA (22,896 / 22,896 / 36,576 / 86,352 states).
- Props. 5.1–5.4, Remark 6.1, the endpoint inequality (7) on [0,4]⁶, the connected-strictness claim, the Prop. 6.2 example (0,0,2,−3,1,−1) (NMA, unique proper class with M = 12 = 2|P|), the (11,16)/(18,49) exclusions, Prop. 6.3, and the Section 7.1 example (μ₂ acyclicizes (−2,−1,1,−1,2,−1)).
- Lean: `bounded_MA_iff_three_mutations`, `no_fixed_polynomial_sign_classifier`, `NoAlgebraicMAFormula`, `alternatingLine_MA_iff_even`, `alternatingLineInt_MA_iff`, `classifyFirstGapSparseExpandedEndpoint_MA_iff/_NMA_iff`, `classifyStrictConnectedGap_true_sound/_false_sound` all exist with the stated meanings. `Formula`/`PolyTerm` match Definition 2.1 exactly; `RepresentsMA` quantifies over all of `Fin 6 → Int`. The 512-file import closure of the no-go module contains no `sorry`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, or kernel bypass; the only `decide +kernel` calls are kernel-checked. `final_build.log` lists the three standard axioms for all 17 printed closures; `NO_GO_AUDIT.md` records an independent recompilation with `--trust=0 -j1`.
- Not verified: a fresh Lean build; the proof of Theorem 7.1 beyond the earlier package audit and random testing; Chelnokov's theorem beyond its abstract; the theorems of [2] and [3] themselves.

## 4. Clarity and terminology

- Undefined or internal jargon used as if standard: "the project", "the archive", "round", "certified", "certificate", "seed labels", "sound shortcuts", "front end", "guard", "wrapper", "hybrid", "strict arithmetic selector", "runtime-directness", "chamber" (abstract and §5.2), "initially proper" (Prop. 6.2), "acyclicizing word" (used in Prop. 3.2 before it is ever defined), "support"/"undirected support", "ordered scalar", "transport", "endpoint", "coordinate box", "height" (defined only in §7 after being used), "source map". Each needs a definition at first use or should be replaced by mathematics.
- The abstract names "Machine learning mutation-acyclicity of quivers" without quotation marks, italics or a citation.
- "Scope of this draft" (§1) and most of §8 read as an internal audit log ("staged Q179 reconstruction", "bridge-adjusted", "reused checkpoints"). For a journal, move provenance to a short appendix or a repository README and keep in the body only: toolchain, axiom closure, entry-point theorem names, and the archival identifier.
- Section 2: define "topological order", "connected support", "acyclicizing word", "height ht", and the notation q(B) ↔ B(q) once, at the start.
- Section 6: the definitions of proper vertex, wiggle, proper class and totally proper are given in a single paragraph in prose; give them as numbered definitions with the Fomin–Neville numbers ([2, Defs. 5.2, 2.3, 5.4/11.1, 6.1, 14.1]) and state the placement rule of Def. 6.1 explicitly since Prop. 5.2 uses it. Cite [2, (9.6)] for M and [2, Remark 9.4] for the fact that M and det B together are the Alexander polynomial in rank 4.
- Section 7.1's table is useful; "strict arithmetic selector" must be defined before the table.
- Proposition 3.2 should say "computer-assisted" and give the one-paragraph proof outline (item 1 above) rather than "its source and archive provenance are listed in the source map".
- Lemma 3.3: "The formal finite check verifies ..." — just say the check is 85 words, trivially recomputed, and then give the proper-order proof.

## 5. Citations: missing, incorrect, or unusable

Missing:
- Fomin–Zelevinsky, Cluster algebras I (J. AMS 15, 2002) for mutation and the sign convention.
- Beineke–Brüstle–Hille, Algebr. Represent. Theory 14 (2011) 97–112, for the rank-3 Markov criterion (used in Prop. 5.1 and needed for the correction).
- Buan–Marsh–Reiten, Comment. Math. Helv. 83 (2008), Cor. 5.3, and/or Warkentin arXiv:1102.3382 Prop. 2.3 (hereditary property), needed once the correction section exists.
- Warkentin, Exchange graphs via quiver mutation, PhD thesis Chemnitz 2014 (the box, Ex. 6.11), needed for the counterexample.
- Chelnokov, arXiv:2311.01784 (polynomial invariants of 4×4 skew-symmetric matrices under mutation) — directly on the paper's topic; see item 3.
- Lean 4 (de Moura–Ullrich, CADE 2021) and Mathlib (The mathlib Community, CPP 2020), standard when a formalization is claimed.
- Optional: Felikson–Tumarkin, Adv. Math. 340 (2018) (cited in the project manuscript for 2-complete acyclic quivers); Casals arXiv:2311.03601 (binary mutation invariant) if the invariants discussion is expanded.

Incorrect or incomplete:
- [2] Fomin–Neville is published: Adv. Math. 500 (2026), Paper No. 111059 (the September note and the supplement already cite it this way; the arXiv v3 comment says "to appear in Advances in Math"). Cite the journal version and say which numbering is used.
- [3] Neville: give the version (v2, 23 Oct 2025) since theorem numbers are cited.
- [4] is "unpublished manuscript supplied with this project ... Local files: Quiver_Paper.pdf and short_paper_supplement.pdf". This is not citable; see item 4. Note that only `Quiver_Paper.txt` is in the supplied folder, not the PDF.
- [1] is fine (J. Comput. Algebra 15 (2025) 100040, arXiv:2411.04209v2). "Theorem 2.9" matches the arXiv v2 and journal numbering.
- Section 8 refers to `SOURCE_MAP.txt` and `verify_examples.py`; neither file exists anywhere in the supplied folder or zip.

## 6. Typesetting

- Page 9: the mathlib revision is cut off by an overfull line ("…cd14afaa" should end "…cd14afaafc7"); wrap it in `\texttt{}` with `\sloppy` or a line break.
- Page 9: "–trust=0" prints an en-dash; use `-{}-trust=0` or `\texttt{--trust=0}`.
- Page 10 (Appendix A): "classifyStrictConnectedGa" is truncated; same fix.
- Title page: author list, affiliations and archival identifier are placeholders.
- Equation (2): the case split is typeset as a displayed brace with "[x]₊ = max(x,0)" on the same line; put the definition of [x]₊ in the text.
- Section 7.1 table: first-column entries wrap awkwardly ("for-/mula"); widen the column.

## 7. Suggested restructuring (brief)

1. Introduction: state the three results in order — (i) correction of [1, Thm 2.9] with the box counterexample and the replacement theorem; (ii) the parity line and the no-go theorem for polynomial-sign rules, plus the Chelnokov-based corollary for polynomial invariants; (iii) decidability via the bounded-path theorem (cited to a public preprint) and the box-search algorithm, stated as pseudocode.
2. Section 3 (new): the correction, with proof outline and Lean theorem name.
3. Section 4: the line; prove the seed labels by the proper-order argument.
4. Sections 5–6 as now, with definitions moved earlier and the missing steps in Props. 5.2 and 6.2 filled.
5. Section 7: algorithm pseudocode, cost statement, and a table of reachable-set sizes versus N(B) on examples.
6. Section 8: one page: toolchain, entry-point theorems, axiom closures, archive DOI.
