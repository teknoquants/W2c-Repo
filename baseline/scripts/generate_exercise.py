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

"""Generate the worked exercise from the target boxes in the upgraded Word prompt."""
import argparse
import csv
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
from packet import ROOT, module_decls, sources
from prompt_reader import read_targets

SECTIONS={
    'W2a-R':'The physical clock and Wilson calibration',
    'W2b':'The exact Gaussian block',
    'W2c':'Gauge reduction and the eliminated gap',
    'W2d':'Transport and the retained form',
    'W2e':'Conditional scores and the Schur form',
    'W2f':'Small-field assembly and transfer',
}
def rows(path):
    with (ROOT/path).open() as f:return list(csv.DictReader(f))

def table(labels, values):
    return '| '+' | '.join(labels)+' |\n|'+ '|'.join('---' for _ in labels)+'|\n'+'\n'.join('| '+' | '.join(row)+' |' for row in values)

def measurements():
    axial=rows('study/benchmark/axial.csv');g=rows('study/benchmark/gaussian.csv');o=rows('study/benchmark/open-gaps.csv')
    def nums(data, keys):
        return [[r['L']]+[f'{float(r[k]):.6f}' if r[k] else '—' for k in keys] for r in data]
    return [
        '# Finite-box evidence',
        'Each periodic box has $L$ fine links per side and physical length $La$. The computations set $a=1$, use unitary Fourier transforms, remove the harmonic zero mode and retain both transverse coordinates. The linear Gaussian space consists of centred linear functions of the Gaussian field. It is the first Wiener chaos. The tables report calculations in that space.',
        '## Periodic gap, clock and static covariance',
        table(['$L$','Fine gap','Coarse $m$','Gap ratio','$c_L$','$R(2\\pi/L)$'],nums(axial,['gamma_fine','gamma_coarse','gap_ratio','clock','cov_ratio'])),
        'The two gap columns use the same physical time. The equal-time column divides the blocked variance by its coarse Wilson reference. The signed sinc remainder and its upper bound are retained at full precision in the data files.',
        '## Signed margin at the first axial mode',
        table(['$L$','Retained $A$','Correction','Correction / $A$','Margin','Defect / $m$'],nums(axial,['A_retained','raw_schur','schur_over_A','schur_margin','retained_defect_over_m'])),
        'The margin is $A-m-B^*(D-mI)^{-1}B$. The final column is the W2d defect for a unit-variance observable. The exact limiting bare ratio is $3/4$. The positive finite margin explains how the free gap comparison can pass.',
        '## Open-box calibration',
        'The open path complex has $L+1$ vertices per axis; the coarse path has $L/2+1$. The first co-closed mode has two active path frequencies. The paths in the two complexes determine the open spectrum independently of the periodic formula.',
        table(['Fine links / side','Fine gap','Coarse gap','Open ratio'],nums(o,['open_fine_gap','open_coarse_gap','open_ratio'])),
        '# Scores, spectra and spatial kernels',
        '## Gaussian first-chaos comparisons',
        table(['$L$','$\\alpha$','$a\\Lambda_\\perp$','Mixed norm','$g^2J$','$\\zeta$'],nums(g,['alpha_first_chaos','lambda_eliminated_first_chaos','mixed_energy_norm','g_squared_J_gaussian','zeta_first_chaos'])),
        'The mixed norm is the maximum of the singular norm of $D^{-1/2}BA^{-1/2}$ over coarse momenta. With $a=1$, $2c_k=g^2$, hence $\\zeta=g^2 J/(\\Lambda_\\perp-m)$. $J$ uses an operator norm over Fourier blocks. The absolute row sums below are separate, stronger real-space diagnostics.',
        table(['$L$','Precision row sum','Score row sum','Precision exponent','Score exponent'],nums(g,['precision_row_sum','score_row_sum','precision_shell_exponent','score_shell_exponent'])),
        'Shell exponents are log–log fits of Frobenius-norm shell means from radius two to half the sampled side. A dash means fewer than three shells were available. Finite fits depend on the fit window. The tests do not establish an infinite-volume score bound.',
        '## Independent checks',
        'At $a|p|=0.001$ in direction $(1,2,3)$, the two relative covariance slopes are 1.353390 and 1.353466, converging to the common coefficient 1.353553. The file angular.csv checks five directions and three radii. The scripts diagonalize the discrete periodic and open path Laplacians, Fourier transform a two-link real-space impulse, and compare the four-pole resolvent with independent retained/eliminated matrices. For each of 4,676 nonzero coarse momenta, the archive includes both transverse covariance ratios. The 64 pole records cover all eight aliases for axial and diagonal momenta at all four sizes, with zero-overlap aliases identifiable from their residues. At $L=4$ equal lowest energies are combined when reading the long-time pole.',
        'The supplemental Wb one-block values quoted in the master prompt remain literature benchmarks. Their original model discretization was not supplied as part of this exercise. They are separate from the Gaussian block matrices tabulated here.'
    ]

def markdown(spec):
    targets=read_targets(spec,convert_math=True)
    reg=json.loads((ROOT/'study/claims.json').read_text())
    for row in reg['claims']:
        if targets.get(row['id'],{}).get('signature')!=row['statement_sha256']:
            raise ValueError('Review the proof register for revised target '+row['id'])
    claims=reg['claims'];assert list(targets)==[r['id'] for r in claims]
    decls={n:(p,pv) for p in sources() for n,pv in module_decls(p)}
    npriv=sum(pv for _,pv in decls.values())
    public=len(decls)-npriv
    chunks=['---','title: The small-field Wilson estimates for one blocking step','subtitle: Worked W2 exercise and mathematical proof register','---','',
        '## Scope and main result',
        'For the exact two-link spatial block, the first visible free transverse pole has unit limiting speed in inherited time. Its equal-time covariance already has a linear relative correction at small axial momentum. The bare mixed Schur correction divided by retained energy tends to $3/4$, even though the signed gap margin is positive. These facts distinguish the free estimates that can enter a paper from the proposed interacting comparisons.',
        f'The six units contain {len(claims)} numbered targets. The pinned project includes {public} public kernel-checked theorems and {npriv} private proof lemmas. Every entry below gives its statement from the integrated prompt and a derivation, counterexample or specific missing estimate. Individual Lean names identify the exact scope of the formal evidence.',
        table(['Unit','Research question','Targets'],[[u,desc,str(sum(r['id'].rsplit('.',1)[0]==u for r in claims))] for u,desc in SECTIONS.items()]),
        '**Conventions.** $x=g^2$ is the squared coupling, $a$ the fine spacing, and $2a$ the coarse spacing. The reference gap $m$ is positive. A “free proof” uses the specified Gaussian model. A “conditional proof” lists extra physical or trajectory premises. A typed conjecture gives a proposition whose proof is outstanding. Local records use Lean 4.36.0 and Mathlib v4.36.0.',
        '**Publication fields.** GitHub repository [GITHUB-URL] · archival DOI for this exercise [DOI-PENDING]. The source clock paper has its own published identifier, given in the references.']
    unit=None
    for r in claims:
        this=r['id'].rsplit('.',1)[0]
        if unit!=this:
            unit=this;chunks.append('# '+unit+' • '+SECTIONS[unit])
        item=targets[r['id']]
        chunks.extend(['## '+r['kind']+' '+r['id']+' • '+r['title'],'**Status.** '+r['status']+'.'])
        for i,t in enumerate(item['statement']):
            chunks.append(('**Statement.** ' if i==0 else '')+t)
        lead='Argument and outstanding estimate' if ('open' in r['status'].lower() or 'conjecture' in r['status'].lower()) else ('Definition and verification' if r['kind']=='Definition' else 'Derivation')
        chunks.append('**'+lead+'.** '+r['proof'])
        if r['lean']:chunks.append('**Lean proofs.** '+', '.join('`'+n+'`' for n in r['lean'])+'.')
        if r['inputs']:chunks.append('**Related definitions or hypotheses.** '+', '.join('`'+n+'`' for n in r['inputs'])+'.')
    chunks+=measurements()
    chunks+=['# Constants and publication evidence',
        table(['Constant','Definition or use','Evidence'],[
            ['$A,A_-,A_+,B,x_*$','Inverse-coupling decrement and weak interval','Running bounds assumed; $A=11N\\log2/(12\\pi^2)$ in B2'],
            ['$c_1,M_c,C_\\xi$','Wilson slope, reciprocal remainder, step error','Kernel evaluated; uniform interacting remainder open'],
            ['$\\kappa,c$','Eliminated gap $\\ge\\kappa/a$, fibre constant $g^2/c$','Interacting input W2c.3; $\\kappa=c/2$ conditionally'],
            ['$C_S,C_a$','Uniform retained defect','Open; $1/8$ belongs to the free gap ratio'],
            ["$C_M,C'_a$",'Mixed allowance or signed Schur bound','Raw quadratic estimate obstructed in the free axial sector'],
            ['$C_L,c_{LF},\\delta,D_\\delta$','Large fields and exponential absorption','W3 input; explicit $D_\\delta$ checked'],
            ['$r,a_w,\\bar m$','Loss cap, last weak spacing, mass ceiling','Positive product conditional on $r<1$ and bounds'],
            ['$A_{int},b,M,g_1$','Intermediate decrement, step factor, count, threshold','W4 inputs; conditional count checked'],
            ['$z_L,Z_{clock}$','Strong endpoint and weak time conversion','Strong calibration open; weak product telescopes']]),
        '## Verification record',
        f'The master local transcript contains {len(decls)} proof-axiom records. Public statements and their L1/L2 classifications appear in `scripts/released.tsv`. An L1 proof can have ordinary mathematical hypotheses; L2 identifies an implication consuming a physical estimate or trajectory premise. Shared proofs are counted once. The common prelude separately checks 26 declarations. The Lean kernel audit permits only propext, Classical.choice and Quot.sound. Open predicates are displayed with #check and never entered as proofs.',
        'The archive includes module sources; the combined proof file `packets/W2_final.lean`; the retained local stdout `records/w2-v1/final.local.out`; and the per-module checks. Python executes 9,579 numerical assertions including the original 46 baseline checks, the clock quadrature, the finite Gaussian comparisons and the W2c–W2f diagnostics. Repeated checks at distinct momenta count separately. The official hosted check-only transcript remains outstanding.',
        '## References',
        'R. Cooperman and A.E. Petrunina V.V. *The Physical Clock under Spatial Blocking in SU(N) Lattice Yang–Mills*. First draft, 22 November 2026. DOI 10.5281/zenodo.24446069. In particular Definition 4.1, Lemma 4.2, Proposition 5.1, §§6–9, and Appendix A.',
        'R. Cooperman and A.E. Petrunina V.V. *Weak-Coupling Series Prompt W2*, revision of 21 November 2026, §§1–10. *Amendments to Prompt W2b*, 23 November 2026. The integrated generator retains the supplied series bibliography.',
        'Series dependencies cited by the prompt include *Proving a Uniform Gap Comparison Across Yang–Mills Scales* (DOI 10.5281/zenodo.24348403), *Spectral Comparison Across One Yang–Mills Blocking Step* (DOI 10.5281/zenodo.24365904), and *Two-Coupling One-Loop Matching and the Running Time Unit Under Spatial Blocking in SU(N) Lattice Yang–Mills* (DOI 10.5281/zenodo.24395118).',
        '# License', (ROOT/'LICENSE').read_text().strip()]
    return '\n'.join(chunks[:4])+'\n\n'+'\n\n'.join(chunks[5:])+'\n'

def style_file(path):
    from docx import Document
    from docx.shared import Cm,Pt,RGBColor
    from docx.oxml import OxmlElement
    from docx.oxml.ns import qn
    from docx.enum.text import WD_ALIGN_PARAGRAPH
    doc=Document(path);sec=doc.sections[0];styles={s.name:s for s in doc.styles}
    sec.page_width=Cm(21);sec.page_height=Cm(29.7);sec.top_margin=Cm(2.05);sec.bottom_margin=Cm(1.95);sec.left_margin=Cm(2.25);sec.right_margin=Cm(2.1)
    sec.header_distance=Cm(.9);sec.footer_distance=Cm(.9)
    h=sec.header.paragraphs[0];h.text='W2   /   SMALL-FIELD WILSON ESTIMATES';h.runs[0].font.name='Noto Sans';h.runs[0].font.size=Pt(8);h.runs[0].font.color.rgb=RGBColor.from_string('325E69')
    f=sec.footer.paragraphs[0];f.alignment=WD_ALIGN_PARAGRAPH.RIGHT
    r=f.add_run('Worked exercise     •     ');r.font.size=Pt(8)
    fld=OxmlElement('w:fldSimple');fld.set(qn('w:instr'),'PAGE');f._p.append(fld)
    for name in ('Normal','Body Text','First Paragraph','Compact'):
        if name in styles:
            st=styles[name];st.font.name='Liberation Serif';st.font.size=Pt(11);st.paragraph_format.space_after=Pt(5);st.paragraph_format.line_spacing=1.09
    for name,size,color in [('Title',27,'153747'),('Subtitle',14,'2A6570'),('Heading 1',21,'173E50'),('Heading 2',14,'1C5361')]:
        st=styles[name];st.font.name='Noto Sans';st.font.size=Pt(size);st.font.color.rgb=RGBColor.from_string(color);st.font.bold=name!='Subtitle'
        st.paragraph_format.space_before=Pt(10);st.paragraph_format.space_after=Pt(5);st.paragraph_format.keep_with_next=True
    styles['Heading 1'].paragraph_format.page_break_before=True
    if 'Verbatim Char' in styles:
        st=styles['Verbatim Char'];st.font.name='DejaVu Sans Mono';st.font.size=Pt(8)
    for p in doc.paragraphs:
        if p.text.startswith(('Status.','Statement.','Derivation.','Argument and outstanding estimate.','Definition and verification.','Related definitions or hypotheses.','Lean proofs.')):
            p.paragraph_format.keep_with_next=p.text.startswith('Status.')
            if p.text.startswith(('Lean proofs.','Related definitions or hypotheses.')):
                p.paragraph_format.space_after=Pt(3)
                for r in p.runs:
                    r.font.size=Pt(8.7);r.font.color.rgb=RGBColor.from_string('365968')
    for tab in doc.tables:
        tab.style='Table'
        for i,row in enumerate(tab.rows):
            trp=row._tr.get_or_add_trPr();trp.append(OxmlElement('w:cantSplit'))
            if i==0:trp.append(OxmlElement('w:tblHeader'))
            for cell in row.cells:
                pr=cell._tc.get_or_add_tcPr()
                sh=OxmlElement('w:shd');sh.set(qn('w:fill'),'CADDE0' if i==0 else ('EFF4F4' if i%2 else 'FFFFFF'));pr.append(sh)
                for p in cell.paragraphs:
                    p.paragraph_format.space_after=Pt(3);p.paragraph_format.space_before=Pt(2)
                    for run in p.runs:
                        run.font.name='Noto Sans';run.font.size=Pt(8);run.font.bold=i==0
                        if i==0:run.font.color.rgb=RGBColor.from_string('173E50')
    doc.core_properties.title='W2 • Worked exercise and mathematical proof register';doc.save(path)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--prompt',type=Path,default=ROOT/'W2-Upgraded-Prompt.docx');p.add_argument('--output',type=Path,default=ROOT/'W2-Generated-Exercise.docx')
    a=p.parse_args();md=markdown(a.prompt);a.output.parent.mkdir(exist_ok=True,parents=True)
    if a.output.suffix=='.md':a.output.write_text(md)
    elif a.output.suffix=='.docx':
        with tempfile.TemporaryDirectory() as work:
            source=Path(work)/'exercise.md';source.write_text(md)
            subprocess.run(['pandoc',str(source),'--from','markdown-smart','--to','docx','--output',str(a.output)],check=True)
        style_file(a.output)
    else:p.error('Choose an output ending in .md or .docx')
