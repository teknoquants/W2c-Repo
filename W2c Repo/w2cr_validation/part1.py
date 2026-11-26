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

"""Check the frozen W2 inputs and invoke both independent upstream Python regressions."""
import subprocess,sys
from common import ROOT,Checks,output,save
def run(out):
    c=Checks();report={}
    for name,args,markers in [
        ('released',['baseline/scripts/validate.py','--python-only'],['9579','44 numbered targets','VALIDATION PASSED']),
        ('paper',['baseline-paper/w2_validation/run_all.py'],['44/44','189/189','ALL CHECKS PASSED'])]:
        raw=subprocess.run([sys.executable,*args],cwd=ROOT,capture_output=True,check=True,text=True).stdout
        for marker in markers:c.test('W2',marker in raw,name+' contains '+marker)
        report[name]=[v.strip() for v in raw.splitlines() if any(m in v for m in markers)]
    save(out/'baseline.json',report);c.finish(1,out)
if __name__=='__main__':run(output())
