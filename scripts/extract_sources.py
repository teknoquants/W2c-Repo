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

"""Read all editable source, statement, target and table controls from native Word XML."""
import argparse
from pathlib import Path
from zipfile import ZipFile
from lxml import etree as ET
from catalogue import BOOK, NS, ROOT

def read_book(path=BOOK):
    with ZipFile(path) as z:
        doc=ET.fromstring(z.read('word/document.xml'))
        media={z.read(n) for n in z.namelist() if n.startswith('word/media/')}
    result={}
    for box in doc.xpath('//w:sdt',namespaces=NS):
        tag=box.xpath('./w:sdtPr/w:tag/@w:val',namespaces=NS)[0]
        if tag in result:raise ValueError('Duplicate control '+tag)
        content=box.find('w:sdtContent',NS)
        def paras(parent):
            def value(line):
                return ''.join('\t' if node.tag.endswith('}tab') else node.text or ''
                               for node in line.xpath('.//w:t|.//w:tab',namespaces=NS))
            return [value(p) for p in parent.findall('w:p',NS)]
        if tag.startswith('tbl:'):
            result[tag]=[['\n'.join(paras(cell)) for cell in row.findall('w:tc',NS)]
                         for row in content.find('w:tbl',NS).findall('w:tr',NS)]
        elif tag.startswith('src:'):
            desc=box.xpath('./w:sdtPr/w:alias/@w:val',namespaces=NS)[0]
            eol,terminal=desc.split(',')
            sep='\r\n' if eol=='CRLF' else '\n'
            result[tag]=(sep.join(paras(content))+(sep if terminal=='1' else '')).encode()
        else:result[tag]='\n'.join(paras(content))
    return result,media

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('destination',type=Path)
    parser.add_argument('--book',type=Path,default=BOOK)
    args=parser.parse_args()
    for name,value in read_book(args.book)[0].items():
        if not name.startswith('src:'):continue
        rel=Path(name[4:])
        if rel.is_absolute() or '..' in rel.parts:raise ValueError('Unsafe source path')
        target=args.destination/rel
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(value)
