PAPER DRAFT — 8 October 2026

main.tex is a standalone LaTeX manuscript with its bibliography embedded.
Open it in the Codex LaTeX editor for the editable source and PDF preview.
No additional TeX files or bibliography processor are required. A conventional
LaTeX installation can also compile it; repeat compilation to resolve references.

The paper is a sequel to:
K. T. K. Armstrong-Williams, E. Hirst, B. Jackson, K.-H. Lee,
Machine learning mutation-acyclicity of quivers,
Journal of Computational Algebra 15 (2025), 100040.
https://doi.org/10.1016/j.jaca.2025.100040
https://arxiv.org/abs/2411.04209v2

The narrative centers on the Round 7 polynomial-sign impossibility theorem,
the Round 8 exact parity classification, selected proved arithmetic regions,
and the distinction between a total hybrid and a partial arithmetic selector.
The early research/REPORT.md predates the main no-go theorem and must not be
used as the current status of that question.

The bounded-path theorem is attributed to the existing local manuscript and
supplement. The draft does not claim to reproduce its full excursion proof.
The separate all-input arithmetic-only classification target remains open.

Authorship, affiliations, acknowledgments/funding, public proof-package URL,
and the bibliographic status of the local bounded-path manuscript should be
completed before submission. No new ML experiment or performance measurement
has been invented. The short discussion of future experiments is explicitly
prospective.

Companion files:
- SOURCE_MAP.txt: mathematical claims mapped to exact local sources and audits.
- verify_examples.py: standard-library checks for printed finite calculations.
- example_checks.json: output from those checks.
- verification.txt: draft-session checks and compilation outcome.

Run the independent finite checks from the project root:
  python3 Paper_draft/verify_examples.py

These finite checks are not substitutes for universal theorem proofs.
