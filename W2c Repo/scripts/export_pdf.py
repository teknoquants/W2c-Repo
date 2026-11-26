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

"""Export the dark Word edition with readable native equations and selectable PDF text."""
import argparse
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import fitz
from catalogue import BOOK

def finish(source, output):
    doc=fitz.open(source)
    for page in doc:
        for xref in page.get_contents():
            stream=doc.xref_stream(xref)
            # LibreOffice's Math renderer paints black regardless of an OMML
            # run's explicit ink colour. Preserve the full-page black fill;
            # correct subsequent black text and vector equation rules only.
            prefix,marker,content=stream.partition(b'EMC')
            if not marker:raise ValueError('Unrecognized PDF page preamble')
            rgb=b'0.92941176 0.94901961 0.96078431 '
            content=re.sub(rb'(?<![\d.])0 0 0 (rg|RG)\b',lambda m:rgb+m[1],content)
            if content!=stream[len(prefix)+len(marker):]:
                doc.update_stream(xref,prefix+marker+content)
    doc.save(output,garbage=4,deflate=True);doc.close()
    with fitz.open(output) as check:
        for index,page in enumerate(check):
            corner=page.get_pixmap(matrix=fitz.Matrix(.5,.5),clip=fitz.Rect(3,3,7,7),alpha=False).samples
            if max(corner,default=0)>15:raise ValueError(f'Background on page {index+1}')
            for block in page.get_text('dict')['blocks']:
                for line in block.get('lines',[]):
                    for span in line['spans']:
                        if span['color']==0 and span['text'].strip():
                            raise ValueError(f'Dark ink on page {index+1}: '+span['text'])
        print(len(check),'PDF pages with dark backgrounds and visible text')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rendered',type=Path,help='existing LibreOffice PDF export')
    parser.add_argument('--out',type=Path,default=BOOK.with_suffix('.pdf'))
    args=parser.parse_args()
    if args.rendered:finish(args.rendered,args.out);return
    with tempfile.TemporaryDirectory() as name:
        work=Path(name)
        executable=shutil.which('soffice') or shutil.which('libreoffice')
        if not executable:raise RuntimeError('Install LibreOffice to regenerate the PDF')
        subprocess.run([executable,'-env:UserInstallation='+ (work/'profile').as_uri(),'--headless','--convert-to','pdf','--outdir',str(work),str(BOOK)],check=True)
        finish(work/BOOK.with_suffix('.pdf').name,args.out)
if __name__=='__main__':main()
