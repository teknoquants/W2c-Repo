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

"""Create or verify the release manifest, or build the distributable ZIP."""
import argparse
import hashlib
from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED

ROOT=Path(__file__).resolve().parents[1]
MANIFEST=ROOT/'SHA256SUMS'
IGNORED={'.lake','.git','__pycache__','.pytest_cache','.DS_Store'}
def files():
    for path in sorted(ROOT.rglob('*')):
        if path.is_file() and not any(p in IGNORED for p in path.relative_to(ROOT).parts) and path.suffix!='.pyc':
            yield path
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def write():
    MANIFEST.write_text(''.join(f'{digest(p)}  {p.relative_to(ROOT).as_posix()}\n' for p in files() if p!=MANIFEST))
def verify():
    rows=MANIFEST.read_text().splitlines()
    names=set()
    for r in rows:
        h,n=r.split('  ',1);path=ROOT/n
        if n in names or Path(n).is_absolute() or '..' in Path(n).parts or digest(path)!=h:
            raise ValueError('Manifest mismatch: '+n)
        names.add(n)
    expected={p.relative_to(ROOT).as_posix() for p in files() if p!=MANIFEST}
    # A separately obtained author-hosted record is deliberately external to the release.
    extra=expected-names-{'records/w2c-r/final.out'}
    if extra or names-expected:raise ValueError('Inventory mismatch: '+str(sorted(extra| (names-expected))))
    return len(names)
def archive(output):
    verify()
    if output.resolve().is_relative_to(ROOT):raise ValueError('ZIP must be outside the release directory')
    output.parent.mkdir(parents=True,exist_ok=True)
    with ZipFile(output,'w',compression=ZIP_DEFLATED,compresslevel=7) as z:
        for p in files():z.write(p,'W2c-R-Rebuilt/'+p.relative_to(ROOT).as_posix())
    with ZipFile(output) as z:
        if z.testzip() is not None:raise ValueError('ZIP CRC error')
    print(output.name,digest(output))
if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=['manifest','verify','zip'])
    parser.add_argument('output',type=Path,nargs='?')
    a=parser.parse_args()
    if a.mode=='manifest':write()
    if a.mode=='zip':archive(a.output)
    else:print(verify(),'files verified')
