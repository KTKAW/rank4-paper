Classifier and census: CPython 3.9.6 (measured interpreter), standard library
only. The source supports Python >=3.9; timings from other versions will vary.
Benchmark machine: Apple M1, 8 cores, 16 GiB RAM, macOS 26.3 arm64.
Full measured metadata: experiments/environment.json.

Plotting: CPython 3.12.14, matplotlib 3.10.7, complete resolved versions in
plot-requirements.txt. Create a separate environment:
  python3.12 -m venv environment/.venv
  environment/.venv/bin/python -m pip install -r environment/plot-requirements.txt
  environment/.venv/bin/python experiments/summarize.py
The source tables and PDF figure are committed, so LaTeX builds do not need
Python or Matplotlib. Plotting installation may resolve platform-specific
binary wheels; the lock pins versions, not wheel hashes.

Lean: leanprover/lean4:v4.24.0 in lean/lean-toolchain. The exact mathlib and
transitive package revisions are committed in lean/lake-manifest.json.
Do not run lake update when reproducing the pinned draft.

LaTeX measured build: pdfTeX/TeX Live 2026, latexmk; amsart with common TeX
Live packages. Build with pdfLaTeX, not XeLaTeX. No shell escape is needed.
