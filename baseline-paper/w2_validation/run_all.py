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

"""Run the complete W2 validation suite.

Exit code 0 only if every check passes AND every one of the 44 numbered
targets of the paper is covered by at least one check.
"""
import json
import re
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPTS = [
    ("validate_w2ar.py", "W2a-R  physical clock and Wilson calibration"),
    ("validate_w2b.py", "W2b    exact Gaussian block"),
    ("validate_w2c.py", "W2c    gauge reduction and eliminated gap"),
    ("validate_w2d.py", "W2d    transport and retained form"),
    ("validate_w2e.py", "W2e    conditional scores and Schur form"),
    ("validate_w2f.py", "W2f    small-field assembly and transfer"),
    ("validate_numerical_tables.py", "Numerical reference tables"),
    ("validate_lean_register.py", "Lean register and kernel-audit record"),
]


def main():
    total = passed = 0
    covered = set()
    failed = []
    log = []
    for script, title in SCRIPTS:
        t0 = time.time()
        r = subprocess.run([sys.executable, str(HERE / script)], capture_output=True, text=True, cwd=HERE)
        out = r.stdout + r.stderr
        log.append(out)
        print(out, end="")
        n_pass = out.count("[PASS]"); n_fail = out.count("[FAIL]")
        total += n_pass + n_fail; passed += n_pass
        covered |= set(re.findall(r"\[PASS\] (W2[a-f](?:-R)?\.\d+):", out))
        status = "PASS" if (r.returncode == 0 and n_fail == 0) else "FAIL"
        if status == "FAIL":
            failed.append(script)
        print(f"  {status}  {script}  ({time.time() - t0:.0f} s)\n")
    targets = [c["id"] for c in json.loads((HERE / "data" / "claims.json").read_text())["claims"]]
    missing = [t for t in targets if t not in covered]
    print(f"Targets covered: {len(targets) - len(missing)}/{len(targets)}" + (f"  missing: {missing}" if missing else ""))
    print(f"Checks passed: {passed}/{total}")
    ok = not failed and not missing and passed == total
    print("ALL CHECKS PASSED" if ok else f"FAILURES: {failed}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
