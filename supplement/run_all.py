"""Run every check in the supplement and verify the checksums.

Usage:
  python3 run_all.py [path/to/main.tex]          all checks except the conjecture evidence (a few minutes)
  python3 run_all.py --full [path/to/main.tex]   also conjecture_evidence.py and bruteforce_local.py 7

Each program is run with the same Python interpreter as this script. Standard library only.
A transcript is written to run_log.txt, which records the interpreter version and the timings;
it is not covered by SHA256SUMS.txt, so the checksums do not depend on the interpreter.
"""
import hashlib
import platform
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for block in iter(lambda: fh.read(1 << 16), b""):
            h.update(block)
    return h.hexdigest()


def check_sums():
    lines = (HERE / "SHA256SUMS.txt").read_text().splitlines()
    bad = []
    for line in lines:
        if not line.strip():
            continue
        digest, name = line.split(None, 1)
        name = name.strip().lstrip("*")
        if not (HERE / name).exists() or sha256(HERE / name) != digest:
            bad.append(name)
    return len(lines), bad


def main(argv):
    full = "--full" in argv
    tex = [a for a in argv[1:] if a != "--full"]
    steps = [
        ("unit and cross-implementation tests", ["tests.py"]),
        ("appendix calculations (all parameter values)", ["check_proofs.py"]),
        ("height-two census: generate certificates", ["census.py"]),
        ("height-two census: independent check", ["check_census.py"]),
        ("examples and remarks", ["examples.py"]),
        ("finite check of the local case analysis", ["bruteforce_local.py", "7" if full else "6"]),
        ("claim labels in the paper and in APPENDIX_CALCULATIONS.md", ["check_references.py"] + tex),
    ]
    if full:
        steps.append(("evidence for Conjecture 5.5", ["conjecture_evidence.py"]))
    log = ["Python %s on %s" % (platform.python_version(), platform.platform()), ""]
    failures = []
    for title, cmd in steps:
        t0 = time.time()
        proc = subprocess.run([sys.executable] + cmd, cwd=str(HERE), capture_output=True, text=True)
        dt = time.time() - t0
        status = "ok" if proc.returncode == 0 else "FAILED (exit %d)" % proc.returncode
        head = "== %s: %s [%s, %.0f s]" % (title, " ".join(cmd), status, dt)
        print(head)
        out = (proc.stdout + proc.stderr).rstrip()
        print(out)
        log.extend([head, out, ""])
        if proc.returncode != 0:
            failures.append(title)
    n, bad = check_sums()
    msg = "== checksums: %d files listed in SHA256SUMS.txt, %s" % (n, "all match" if not bad else "MISMATCH: %s" % bad)
    print(msg)
    log.append(msg)
    if bad:
        failures.append("checksums")
    final = "ALL CHECKS PASSED" if not failures else "FAILED: %s" % ", ".join(failures)
    print(final)
    log.append(final)
    (HERE / "run_log.txt").write_text("\n".join(log) + "\n")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
