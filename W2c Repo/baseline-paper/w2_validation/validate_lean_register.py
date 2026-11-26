# SPDX-License-Identifier: MIT
# MIT License
#
# Copyright (c) 2026 Roger Cooperman; A.E. Petrunina V.V.
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

"""Lean register: integrity of the formal evidence cited by the paper.

This script does not run Lean.  It checks that the shipped Lean sources are the
ones whose kernel check is recorded, that they contain no `sorry`, `admit` or
user axiom, that the recorded axiom audit uses only Lean's three standard axioms,
and that every Lean name cited by the 44 numbered targets exists.
To re-run the kernel check:  cd lean && lake exe cache get && lake build
"""
import hashlib
import json
import re

from common import DATA, LEAN, check, finish

STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    sums = [ln.split(None, 1) for ln in (LEAN / "SHA256SUMS").read_text().splitlines() if ln.strip()]
    bad = [name for digest, name in sums if sha256(LEAN / name.strip()) != digest]
    check("Lean", f"SHA-256 digests of all {len(sums)} Lean source and project files match", not bad and len(sums) == 34, ", ".join(bad))

    tool = (LEAN / "lean-toolchain").read_text().strip()
    lake = (LEAN / "lakefile.toml").read_text()
    check("Lean", "toolchain pinned to Lean 4.36.0 with Mathlib v4.36.0",
          tool == "leanprover/lean4:v4.36.0" and 'rev = "v4.36.0"' in lake)

    sources = sorted((LEAN / "W2").rglob("*.lean")) + [LEAN / "W2.lean", LEAN / "W2_final.lean"]
    text = {p: re.sub(r"/-.*?-/", "", p.read_text(), flags=re.S) for p in sources}
    text = {p: re.sub(r"--[^\n]*", "", t) for p, t in text.items()}
    holes = [str(p.relative_to(LEAN)) for p, t in text.items() if re.search(r"\b(sorry|admit)\b", t)]
    axioms = [str(p.relative_to(LEAN)) for p, t in text.items() if re.search(r"^\s*axiom\s", t, flags=re.M)]
    check("Lean", f"no sorry or admit in {len(sources)} Lean files", not holes, ", ".join(holes))
    check("Lean", "no user-declared axiom in any Lean file", not axioms, ", ".join(axioms))

    out = (LEAN / "final.local.out").read_text()
    recs = re.findall(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]", out)
    used = set()
    for _, ax in recs:
        used |= {a.strip() for a in ax.split(",") if a.strip()}
    check("Lean", f"recorded kernel audit: {len(recs)} axiom records, only propext, Classical.choice, Quot.sound",
          len(recs) == 91 and used <= STANDARD and "sorryAx" not in out)
    check("Lean", "recorded master run reports Lean version 4.36.0", '"4.36.0"' in out)
    replay = (LEAN / "module-replay.txt").read_text()
    n_pass = replay.count("CHECK PASSED")
    check("Lean", f"per-module replay record: {n_pass} modules CHECK PASSED, none failed",
          n_pass >= 26 and "FAIL" not in replay.upper().replace("CHECK PASSED", ""))

    released = [ln.split("\t") for ln in (DATA / "released.tsv").read_text().splitlines() if ln and not ln.startswith("#")]
    names = [r[0] for r in released]
    audited = {n for n, _ in recs}
    alltext = "\n".join(text.values())
    declared = [n for n in names if re.search(r"\b(theorem|lemma)\s+" + re.escape(n.split(".")[-1]) + r"\b", alltext)]
    check("Lean", f"{len(names)} public theorems in the release index", len(names) == 74)
    check("Lean", "every public theorem is declared in the sources and appears in the recorded axiom audit",
          len(declared) == 74 and set(names) <= audited)

    claims = json.loads((DATA / "claims.json").read_text())["claims"]
    per_unit = {}
    for c in claims:
        unit = c["id"].split(".")[0]
        per_unit[unit] = per_unit.get(unit, 0) + 1
    check("Lean", "44 numbered targets: W2a-R 10, W2b 11, W2c 6, W2d 7, W2e 5, W2f 5",
          len(claims) == 44 and per_unit == {"W2a-R": 10, "W2b": 11, "W2c": 6, "W2d": 7, "W2e": 5, "W2f": 5})
    missing = []
    for c in claims:
        for n in c.get("lean", []):
            if n not in names:
                missing.append(n)
        for n in c.get("inputs", []):
            short = n.split(".")[-1]
            if not re.search(r"\b(def|structure|abbrev|class)\s+" + re.escape(short) + r"\b", alltext):
                missing.append(n)
    check("Lean", "every Lean proof and hypothesis cited by the 44 targets exists", not missing, ", ".join(missing))
    finish("Lean register")


if __name__ == "__main__":
    print("Lean register")
    main()
