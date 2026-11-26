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

"""Read the mathematical target headings directly from the integrated Word specification."""
import re
from xml.etree import ElementTree as ET
from zipfile import ZipFile

W='{http://schemas.openxmlformats.org/wordprocessingml/2006/main}'
M='{http://schemas.openxmlformats.org/officeDocument/2006/math}'
TARGET=re.compile(r'^Target (Theorem|Proposition|Corollary|Lemma|Definition|Conjecture) (W2(?:a-R|[bcdef])\.\d+)')
def native_formulas(path):
    """Read the actual Word equations through Pandoc's OMML reader."""
    import json
    import subprocess
    data=json.loads(subprocess.check_output(['pandoc',str(path),'-f','docx','-t','json']))
    def visit(node):
        if isinstance(node,dict):
            if node.get('t')=='Math':
                yield node['c'][1]
            else:
                for child in node.values():yield from visit(child)
        elif isinstance(node,list):
            for child in node:yield from visit(child)
    return list(visit(data['blocks']))

def math_shape(node):
    # Include mathematical operators, fractions and script structure while ignoring run styling.
    if node.tag in (W+'rPr',M+'rPr',M+'ctrlPr'):return None
    children=[shape for e in node if (shape:=math_shape(e)) is not None]
    return [node.tag,sorted((k,v) for k,v in node.attrib.items() if k.startswith(M)),(node.text or '').strip(),children]

def read_targets(path, convert_math=False):
    import hashlib
    import json
    with ZipFile(path) as file:
        body=ET.fromstring(file.read('word/document.xml')).find(W+'body')
    result={};ident=None
    equations=iter(native_formulas(path)) if convert_math else None
    for p in body.iter(W+'p'):
        text=''.join(e.text or '' for e in p.iter() if e.tag in (W+'t',M+'t')).strip()
        native=list(p.iter(M+'oMath'))
        rendered=[next(equations) for _ in native] if equations is not None else []
        terms=[math_shape(e) for e in native]
        match=TARGET.match(text)
        if match:
            kind,ident=match.groups()
            if ident in result:raise ValueError('Repeated target '+ident)
            result[ident]={'kind':kind,'statement':[],'signature_inputs':[kind]}
        elif ident and (not text or text.startswith(('Checkpoint.','Task.','Part ','Target ')) or p.find(W+'pPr/'+W+'pStyle') is not None):
            ident=None
        elif ident:
            result[ident]['signature_inputs'].append([text,terms])
            if rendered:
                text='\n\n'.join('$$'+tex+'$$' for tex in rendered)
            result[ident]['statement'].append(text)
    if len(result)!=44 or any(not v['statement'] for v in result.values()):
        raise ValueError('A W2 target or statement was missing before exercise generation.')
    if equations is not None and next(equations,None) is not None:raise ValueError('Unmapped native equation.')
    for entry in result.values():
        raw=json.dumps(entry.pop('signature_inputs'),ensure_ascii=False,separators=(',',':')).encode()
        entry['signature']=hashlib.sha256(raw).hexdigest()
    return result
