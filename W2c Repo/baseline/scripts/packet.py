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

"""Frozen source inventory, packet generation, and kernel-output verification."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
UNITS = ('Common', 'W2aR', 'W2b', 'W2c', 'W2d', 'W2e', 'W2f', 'W2')
SLOTS = re.compile(r'^-- W2 PROOF BEGIN ([\w.]+)\n(.*?)^-- W2 PROOF END \1\n', re.S | re.M)
NAMES = re.compile(r"^(?:@\[[^\]]+\] )?(?:(private) )?(?:theorem|lemma) ([\w']+)", re.M)
DEFS = re.compile(r'^(?:noncomputable )?(?:def|abbrev|structure) ([\w.]+)', re.M)
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def ensure(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def sources():
    return sorted(str(p.relative_to(ROOT)) for p in (ROOT / 'W2').rglob('*.lean'))


def frozen():
    freeze = json.loads((ROOT/'study/frozen.json').read_text())
    current = {p: sha((ROOT/p).read_bytes()) for p in [*sources(), 'W2.lean', 'lean-toolchain', 'lake-manifest.json', 'lakefile.toml']}
    ensure(freeze == current, 'Frozen module, toolchain, or dependency manifest changed.')


def module_decls(path):
    s = (ROOT/path).read_text()
    ns = re.search(r'^namespace (W2[.\w]*)', s, re.M)[1]
    return [(ns+'.'+m[2], bool(m[1])) for m in NAMES.finditer(s)]


def selected(unit):
    paths = sources()
    roots = [p for p in paths if unit == 'W2' or p.startswith('W2/'+unit+'/')]
    extra = {'W2aR':['W2/Common/Trig.lean','W2/Common/Constants.lean','W2/Research/ClockSupplement.lean'],
             'W2b':['W2/Common/Trig.lean'], 'W2e':['W2/Framework/Schur.lean']}
    return list(dict.fromkeys([*roots, *extra.get(unit, []), 'W2/Research/Obligations.lean']))


def ordered(roots):
    done = []
    def visit(path):
        if path not in done:
            for dep in re.findall(r'^(?:public )?import (W2[.\w]+)$', (ROOT/path).read_text(), re.M):
                visit(dep.replace('.', '/')+'.lean')
            done.append(path)
    for path in roots:
        visit(path)
    return done


def subst(text, replacements):
    return SLOTS.sub(lambda m: '-- W2 PROOF BEGIN '+m[1]+'\n'+replacements.get(m[1], m[2])+'-- W2 PROOF END '+m[1]+'\n', text)


def bodies(s):
    result = {m[1]:m[2] for m in SLOTS.finditer(s)}
    ensure(len(result) == s.count('-- W2 PROOF BEGIN ') == s.count('-- W2 PROOF END '), 'Malformed or duplicated proof boundaries.')
    return result


def make(unit, module=None, prelude=False, solved=False):
    frozen()
    ensure(unit in UNITS, 'Unknown unit.')
    if prelude:
        roots = ['W2/Common/Basic.lean', 'W2/Common/Hypotheses.lean']
    elif module:
        ensure(module in selected(unit) and (ROOT/module).is_file(), 'Unregistered module for this unit.')
        roots = [module]
    else:
        roots = selected(unit)
    paths = ordered(roots)
    sections, names, open_defs = [], [], []
    for path in paths:
        s = (ROOT/path).read_text()
        names.extend(n for n, _ in module_decls(path))
        section = '\n'.join(line for line in s.splitlines() if not line.startswith(('import ', 'public import ')) and line.strip() not in ('module','@[expose] public section'))
        sections.append('-- Source '+path+'\n'+section.strip()+'\n')
        if prelude or path == 'W2/Research/Obligations.lean':
            ns = re.search(r'^namespace (W2[.\w]*)', s, re.M)[1]
            open_defs.extend(ns+'.'+n for n in DEFS.findall(s))
    edit = list(bodies((ROOT/module).read_text())) if module else []
    audit = names if not prelude else open_defs
    meta = dict(unit=unit, module=module, prelude=prelude, editable=edit, audit=audit)
    head = '-- W2-PACKET '+json.dumps(meta,sort_keys=True,separators=(',',':'))+'\nmodule\npublic import Mathlib\n@[expose] public section\n'
    s = head+'\n'+'\n'.join(sections)+'\n#eval Lean.versionString\n'
    s += ''.join('#check '+name+'\n' for name in open_defs)
    s += ''.join('#print axioms '+name+'\n' for name in audit)
    ensure(not re.search(r'\b(sorry|admit|axiom|sorryAx|native_decide|run_tac)\b',s),'Unfilled source or unauditable declaration in release inputs.')
    template = subst(s,dict.fromkeys(edit,'  sorry\n'))
    return (s if solved else template)+'#eval "W2 packet '+sha(template.encode())+'"\n'


def metadata(s):
    header = s.splitlines()[0]
    ensure(header.startswith('-- W2-PACKET '), 'Missing packet header.')
    return json.loads(header[len('-- W2-PACKET '):])


def verify(template, candidate):
    meta = metadata(template)
    ensure(template == make(meta['unit'], meta['module'], meta['prelude']), 'Retained file differs from frozen packet.')
    old, new = bodies(template), bodies(candidate)
    ensure(old.keys() == new.keys(), 'Proof inventory changed.')
    ensure(subst(candidate,{k:old[k] for k in meta['editable']}) == template, 'Frozen statements or dependencies changed.')
    for k in meta['editable']:
        ensure(new[k].strip() and all(not line.strip() or line.startswith('  ') for line in new[k].splitlines()), 'Malformed tactic block '+k)
    ensure(not re.search(r'\b(sorry|admit|axiom|sorryAx|native_decide|run_tac)\b', candidate), 'Unresolved or unauditable proof.')
    return meta, new


def run_lean(file):
    proc = subprocess.run(['lake','env','lean','--stdin'], input=file.read_bytes(), cwd=ROOT, capture_output=True)
    ensure(proc.returncode == 0, (proc.stdout+proc.stderr).decode(errors='replace')[-6000:])
    ensure(not proc.stderr, proc.stderr.decode(errors='replace'))
    return proc.stdout


def audit(raw, src):
    meta = metadata(src)
    lines = raw.decode().splitlines()
    ensure('"4.36.0"' in lines and lines[-1:] == [src.splitlines()[-1].removeprefix('#eval ')], 'Missing version or terminal packet stamp.')
    result = {}
    pattern = r"^'([\w.']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$"
    for m in re.finditer(pattern,raw.decode(),re.M):
        n = re.sub(r'^_private\..*?\.\d+\.(W2\.)',r'\1',m[1])
        ensure(n not in result, 'Duplicate axiom record '+n)
        deps = {d.strip() for d in (m[2] or '').split(',') if d.strip()}
        ensure(deps <= ALLOWED, f'{n} has disallowed axioms {deps-ALLOWED}')
        result[n] = sorted(deps)
    ensure(list(result) == meta['audit'], 'Incomplete or reordered axiom inventory: '+str(set(meta['audit'])-set(result)))
    return result

def equivalent_output(submitted, replayed, source):
    """Allow only the private module prefix chosen by Lean for a different source filename."""
    if submitted == replayed:
        return True
    audit(submitted,source);audit(replayed,source)
    private={n for path in sources() for n,is_private in module_decls(path) if is_private}
    def canonical(raw):
        def replace(m):
            return b"'"+m[1]+b"' " if m[1].decode() in private else m[0]
        return re.sub(rb"^'_private\.[\w.']+?\.\d+\.(W2\.[\w.']+)' ",replace,raw,flags=re.M)
    return canonical(submitted)==canonical(replayed)
