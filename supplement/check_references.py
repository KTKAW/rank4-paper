"""Check that the claim labels cited in the paper and in APPENDIX_CALCULATIONS.md match proof_claims.py.

  * every label cited with \\claim{...} in the paper's main.tex exists, and every claim in
    proof_claims.py is cited there (ranges written "\\claim{X} through \\claim{Y}" or
    "\\claim{X, \\dots, Y}" cover the claims between X and Y in the order of proof_claims.py);
  * every label in APPENDIX_CALCULATIONS.md exists, and every claim is attached to a step of the
    calculations there (not only listed in the index at the end);
  * every supplementary file named in main.tex with \\file{...} exists.
Run:  python3 check_references.py [path/to/main.tex]
(without an argument only the markdown file is checked).
"""
import re
import sys
from pathlib import Path
import claims_core as CC
import proof_claims  # noqa: F401  (registers the claims)

HERE = Path(__file__).resolve().parent
ORDER = [c.id for c in CC.REGISTRY]
POS = {cid: n for n, cid in enumerate(ORDER)}


def expand(items):
    """Expand a list of labels that may contain '\\dots' between two endpoints."""
    out = []
    for n, x in enumerate(items):
        if x in ("\\dots", "...", "\\ldots"):
            a, b = items[n - 1], items[n + 1]
            out.extend(ORDER[POS[a] + 1:POS[b]])
        else:
            out.append(x)
    return out


def labels_in_tex(text):
    found, unknown = [], []
    for m in re.finditer(r"\\claim\{([^}]*)\}(\s*through\s*\\claim\{([^}]*)\})?", text):
        items = [x.strip() for x in m.group(1).split(",") if x.strip()]
        bad = [x for x in items if x not in POS and x not in ("\\dots", "...", "\\ldots")]
        if bad:
            unknown.extend(bad)
            continue
        items = expand(items)
        if m.group(3):
            end = m.group(3).strip()
            if end not in POS:
                unknown.append(end)
                continue
            items = ORDER[POS[items[-1]]:POS[end] + 1] if len(items) == 1 else items + [end]
        found.extend(items)
    return found, unknown


def check_tex(path):
    text = Path(path).read_text()
    found, unknown = labels_in_tex(text)
    missing = [c for c in ORDER if c not in set(found)]
    files = sorted({f.replace("\\_", "_") for f in re.findall(r"\\file\{([^}]*)\}", text)})
    absent = [f for f in files if f.endswith((".py", ".json", ".md")) and not (HERE / f).exists()]
    print("main.tex: %d claim citations, %d distinct; unknown labels: %s; claims never cited: %s; "
          "missing files: %s" % (len(found), len(set(found)), unknown, missing, absent))
    return not unknown and not missing and not absent


def check_md():
    text = (HERE / "APPENDIX_CALCULATIONS.md").read_text()
    body, _, index = text.partition("# Claim index")
    cited = []
    for m in re.finditer(r"`\[([^\]`]*)\]`", body):
        cited.extend(x.strip() for x in m.group(1).split(","))
    unknown = [x for x in cited if x not in POS]
    missing = [c for c in ORDER if c not in set(cited)]
    indexed = set(re.findall(r"^\| `([^`]*)` \|", index, flags=re.M))
    not_indexed = [c for c in ORDER if c not in indexed]
    print("APPENDIX_CALCULATIONS.md: %d labels attached to steps; unknown: %s; claims not attached: %s; "
          "claims missing from the index: %s" % (len(cited), unknown, missing, not_indexed))
    return not unknown and not missing and not not_indexed


def main(argv):
    ok = check_md()
    if len(argv) > 1:
        ok = check_tex(argv[1]) and ok
    print("References consistent." if ok else "INCONSISTENT REFERENCES")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
