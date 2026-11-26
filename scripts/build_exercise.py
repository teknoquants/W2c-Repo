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

"""Build the editable dark-page exercise from target records and the full source distribution."""
import argparse
from copy import deepcopy
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
from zipfile import ZipFile
from lxml import etree as ET
from docx import Document
from docx.enum.style import WD_STYLE_TYPE
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.enum.table import WD_TABLE_ALIGNMENT
from docx.oxml import OxmlElement
from docx.oxml.ns import qn
from docx.shared import Cm, Inches, Pt, RGBColor
from catalogue import (ROOT, DATA, BOOK, FIGURES, counts, signatures, sources,
                        source_bytes, lines_with_format)
from tables import numerical

BG='000000'
INK='EDF2F5'
MUTED='B5C3CF'
TEAL='79DBC9'
GOLD='FFD08A'
WNS='http://schemas.openxmlformats.org/wordprocessingml/2006/main'
MNS='http://schemas.openxmlformats.org/officeDocument/2006/math'
def el(name,**attrs):
    result=OxmlElement(name)
    for k,v in attrs.items():result.set(qn('w:'+k),str(v))
    return result

def style_font(style,name,size,color):
    style.font.name=name;style.font.size=Pt(size);style.font.color.rgb=RGBColor.from_string(color)
    fonts=style.element.get_or_add_rPr().find(qn('w:rFonts'))
    for attr in ('asciiTheme','hAnsiTheme','eastAsiaTheme','cstheme'):
        fonts.attrib.pop(qn('w:'+attr),None)
    for attr in ('ascii','hAnsi','eastAsia','cs'):fonts.set(qn('w:'+attr),name)

def setup(book):
    section=book.sections[0]
    section.page_height=Cm(29.7);section.page_width=Cm(21)
    section.top_margin=Cm(2.05);section.bottom_margin=Cm(1.9)
    section.left_margin=Cm(2.05);section.right_margin=Cm(1.85)
    section.header_distance=Cm(.8);section.footer_distance=Cm(.8)
    back=el('w:background',color=BG);book._element.insert(0,back)
    book.settings.element.append(el('w:displayBackgroundShape'))
    styles=book.styles
    body=styles['Normal'];style_font(body,'DejaVu Serif',10.3,INK)
    body.paragraph_format.space_after=Pt(7);body.paragraph_format.line_spacing=1.15
    for name,font,size,color in [('Title','DejaVu Sans',34,INK),('Heading 1','DejaVu Sans',23,INK),
         ('Heading 2','DejaVu Sans',16,TEAL),('Heading 3','DejaVu Sans',11.5,GOLD)]:
        st=styles[name];style_font(st,font,size,color)
        st.paragraph_format.space_before=Pt(12);st.paragraph_format.space_after=Pt(7)
        st.font.bold=name!='Title'
        if name=='Title':
            base=st.element.get_or_add_pPr();border=base.find(qn('w:pBdr'))
            if border is not None:base.remove(border)
    for name,font,size,color,after in [('Kicker','DejaVu Sans',9,TEAL,8),('Status','DejaVu Sans',9,GOLD,7),
         ('Small note','DejaVu Sans',8.4,MUTED,6),('Code line','DejaVu Sans Mono',7.9,INK,0),
         ('Signature','DejaVu Sans Mono',8.15,INK,0),('Cell','DejaVu Sans',8.4,INK,2),
         ('Source heading','DejaVu Sans',12,TEAL,7)]:
        st=styles.add_style(name,WD_STYLE_TYPE.PARAGRAPH);style_font(st,font,size,color)
        st.paragraph_format.space_after=Pt(after);st.paragraph_format.line_spacing=1.04
        if name in ('Code line','Signature','Cell'):
            st.paragraph_format.widow_control=False
        if name in ('Source heading','Kicker'):st.paragraph_format.keep_with_next=True
    header=section.header.paragraphs[0];header.alignment=WD_ALIGN_PARAGRAPH.RIGHT
    r=header.add_run('WEAK-COUPLING SERIES     /     THE ELIMINATED FIBRE GAP');style_font_run(r,8,MUTED)
    footer=section.footer.paragraphs[0];footer.alignment=WD_ALIGN_PARAGRAPH.RIGHT
    r=footer.add_run('XISOSIS     ·     W2c-R     /     ');style_font_run(r,8,MUTED)
    f=el('w:fldSimple',instr='PAGE');rr=el('w:r');rp=el('w:rPr');rp.append(el('w:color',val=MUTED));rr.append(rp)
    t=el('w:t');t.text='1';rr.append(t);f.append(rr);footer._p.append(f)
    book.core_properties.title='The Eliminated Fibre Gap'
    book.core_properties.subject='W2c-R rebuilt mathematical exercise and executable source edition'
    book.core_properties.author='Roger Cooperman and A.E. Petrunina V.V.'
    book.core_properties.keywords='lattice Yang–Mills, Poincaré inequality, Lean 4, reproducibility'

def style_font_run(run,size,color):
    run.font.name='DejaVu Sans';run.font.size=Pt(size);run.font.color.rgb=RGBColor.from_string(color)

def control(nodes,tag,alias=None):
    first=nodes[0];parent=first.getparent();pos=parent.index(first)
    box=el('w:sdt');pr=el('w:sdtPr');pr.append(el('w:tag',val=tag))
    if alias:pr.append(el('w:alias',val=alias))
    box.append(pr);content=el('w:sdtContent');box.append(content)
    parent.insert(pos,box)
    for node in nodes:content.append(node)

def paragraph(text,style,book):return book.add_paragraph(text,style)
def lines_control(book,tag,lines,style,alias=None):
    body=book._element.body;before=body.index(body.sectPr)
    # Construct one native paragraph per physical source line without repeated body scans.
    box=el('w:sdt');pr=el('w:sdtPr');pr.append(el('w:tag',val=tag))
    if alias:pr.append(el('w:alias',val=alias))
    box.append(pr);content=el('w:sdtContent');box.append(content)
    styleid=book.styles[style].style_id
    for value in lines:
        p=el('w:p');params=el('w:pPr');params.append(el('w:pStyle',val=styleid));p.append(params)
        run=el('w:r')
        for i,v in enumerate(value.split('\t')):
            if i:run.append(el('w:tab'))
            t=el('w:t');t.set('{http://www.w3.org/XML/1998/namespace}space','preserve')
            t.text=v;run.append(t)
        p.append(run);content.append(p)
    body.insert(before,box)

def table(book,rows,tag=None,widths=None):
    tb=book.add_table(rows=0,cols=len(rows[0]));tb.alignment=WD_TABLE_ALIGNMENT.CENTER
    tb.autofit=False
    n=len(rows[0]);w=6.72
    for i,col in enumerate(tb.columns):col.width=Inches(w*(widths[i] if widths else 1/n))
    for j,values in enumerate(rows):
        row=tb.add_row()
        if j==0:row._tr.get_or_add_trPr().append(el('w:tblHeader',val='true'))
        row._tr.get_or_add_trPr().append(el('w:cantSplit'))
        for i,(cell,v) in enumerate(zip(row.cells,values,strict=True)):
            cell.width=Inches(w*(widths[i] if widths else 1/n))
            cell._tc.get_or_add_tcPr().append(el('w:shd',fill=('223340' if j==0 else '10171E' if j%2==1 else '141D26')))
            p=cell.paragraphs[0];p.style=book.styles['Cell'];p.paragraph_format.space_before=Pt(2)
            r=p.add_run(str(v))
            if j==0:r.bold=True;r.font.color.rgb=RGBColor.from_string(TEAL)
            if n>7:r.font.size=Pt(7.5)
    if tag:control([tb._tbl],'tbl:'+tag)
    book.add_paragraph('',style='Small note').paragraph_format.space_after=Pt(1)
    return tb

def equations(rows):
    with tempfile.TemporaryDirectory() as name:
        tmp=Path(name);src=tmp/'eq.md'
        src.write_text('\n\n'.join('$$\n'+r['equation']+'\n$$' for r in rows))
        subprocess.run(['pandoc','-f','markdown','-t','docx',str(src),'-o',str(tmp/'eq.docx')],check=True)
        with ZipFile(tmp/'eq.docx') as z:doc=ET.fromstring(z.read('word/document.xml'))
    math=doc.findall('.//{'+MNS+'}oMath')
    if len(math)!=len(rows):raise ValueError(f'Native equation conversion: {len(math)} of {len(rows)}')
    for eq in math:
        for run in eq.findall('.//{'+MNS+'}r'):
            prop=run.find('{'+WNS+'}rPr')
            if prop is None:
                prop=el('w:rPr');before=1 if run.find('{'+MNS+'}rPr') is not None else 0;run.insert(before,prop)
            prop.append(el('w:color',val=INK))
            prop.append(el('w:sz',val=19))
        for prop in eq.findall('.//{'+MNS+'}ctrlPr'):
            wp=prop.find('{'+WNS+'}rPr')
            if wp is None:wp=el('w:rPr');prop.append(wp)
            wp.append(el('w:color',val=INK))
    return {r['id']:e for r,e in zip(rows,math,strict=True)}

def h(book,title,level=1,new=False):
    p=book.add_heading(title,level=level)
    if new:p.paragraph_format.page_break_before=True
    return p

def pic(book,i):
    name,caption=FIGURES[i];p=book.add_paragraph()
    p.alignment=WD_ALIGN_PARAGRAPH.CENTER;p.paragraph_format.keep_with_next=True
    p.add_run().add_picture(str(ROOT/'figures'/f'{name}.png'),width=Inches(6.6))
    book.add_paragraph(f'Figure {i+1}. {caption}','Small note')

def main(out):
    editorial=json.loads((ROOT/'docs/editorial.json').read_text())
    rows=json.loads((ROOT/'docs/targets.json').read_text())
    sigs=signatures();bytarget=defaultdict(list)
    for entry in sigs:bytarget[entry['target']].append(entry)
    cnt=counts();math=equations(rows)
    book=Document();setup(book);p=book.add_paragraph
    top=p('XISOSIS  ·  Institutional Research Paper','Kicker');top.paragraph_format.space_before=Pt(74)
    p('THE ELIMINATED\nFIBRE GAP','Title')
    p('W2c-R  /  Rebuilt mathematical exercise','Heading 2')
    q=p();t=q.add_run('A volume-independent Gaussian certificate and a pinned SU(2) curvature bound identify what can be proved in one blocking step. The interacting Wilson estimate still requires uniform curvature and cut-domain control.');t.italic=True;t.font.size=Pt(14)
    p('Weak-Coupling Series  ·  SU(N) lattice Yang–Mills','Small note')
    p('Roger Cooperman   ·   https://orcid.org/0009-0009-5011-2135')
    p('A.E. Petrunina V.V.   ·   https://orcid.org/0009-0002-4595-736X')
    p('Vienna  ·  25 November 2026')
    p('GitHub   [GITHUB PLACEHOLDER]\nDOI        [DOI PLACEHOLDER]','Small note')
    h(book,'Abstract',new=True)
    p('One factor-two spatial blocking step retains the products of consecutive fine links. The energy of the remaining fluctuations controls a missing estimate in the W2 programme. We construct the quotient and its canonical conditional measure, distinguish three Gaussian forms, and obtain an open-box physical Gaussian lower certificate of 1/64. A continuous-symbol argument encloses the scalar periodic infima at 0.549994 and 1.389207 to six decimals. A short quotient geodesic refutes general convexity of the plaquette cut. A one-link SU(2) model admits a curvature estimate throughout 0<x≤1/6. The uniform Wilson curvature bound and its boundary implication remain open. Local Lean transcripts certify the finite formal implications; interval proofs, spectra and seeded trials have their own reproducible evidence.')
    h(book,'Contents',2)
    for label in ['Origins and scope','1   The exercise','0   Definitions and conventions','2   Main results','3–8   Units A–F','9   Numerical data','10   Formal verification','11   Status of the targets','12   Corrections to the prompt','13   Hand-off and reader problems','14   Repository, citation and license','References','Appendix A   Declaration index','Appendix B   Complete source edition','Appendix C   Open predicates and hypotheses']:p(label,'Small note')
    h(book,'Origins and scope',new=True)
    p('The W2 programme studies how much of a spectral gap can be retained as a spatial lattice is coarsened. W1 controls accumulated losses; the clock work connects a lattice step to physical mass. W2a-R and W2b supply the clock and free blocking calculations. W2c reduces the eliminated interacting sector to a conditional Poincaré inequality. The rebuilt exercise studies this missing input. The open problem here is one analytic component of a wider programme for Yang–Mills theory.')
    table(book,[['Unit','Question','Targets']]+[[u,editorial['units'][u][0],f"{u}.1–{u}.{sum(r['unit']==u for r in rows)}"] for u in 'ABCDEF'],widths=[.11,.63,.26])
    p('The dated six-unit prompt in the supplied images governs this edition. The separate Word attachment contains the earlier nine-target treatment and the source of the inherited Lean annex. The available images skip the full wording of B.3–B.8. Those six entries use the visible cross-references and numerical specification; their source status is marked individually.')
    h(book,'1   The exercise',new=True)
    p('Fix the isotropic SU(N) Hamiltonian at one spatial blocking step. Determine the geometry and Gaussian gap of the eliminated variables, then identify the uniform analytic input needed for their interacting gap. The quantifiers range over admissible open boxes, scales, initial cutoff, coarse configurations and test functions. Each open estimate must be stated with its variables and its independence from the volume.')
    p('Success requires a statement and status for all 46 targets, full arguments for proved results, explicit missing premises for reductions, numerical results with errors and reproducible local formal evidence. Several expected outcomes in the prompt change under examination. The status register records the actual outcomes.')
    h(book,'0   Definitions and conventions',new=True)
    p('A gauge transformation changes the frame at each vertex; link values transform by multiplication at their two endpoints. A plaquette holonomy is the ordered product around an elementary square. Its Wilson energy is 2(1−Re Tr U/N). Haar measure is the normalized invariant group measure. The Laplacian uses the convention that −Δ is nonnegative. The positive ground state ψ gives the probability law ψ² dHaar. An integration by parts in (H−E₀)(ψf) identifies its quadratic form with x/(2a) times the ψ²-weighted gradient integral.')
    p('A Poincaré constant bounds variance by energy; its reciprocal is the first nonzero Neumann eigenvalue in the relevant normalization. Conditional centring subtracts the mean on each retained field. A colour singlet is invariant under the global SU(N) action. Wiener chaos is the decomposition by Hermite degree. In weak coupling the square roots of the transverse Maxwell frequencies define the fine precision E. Coarse path sums are projected onto the coarse transverse sector before defining the vertical space.')
    table(book,[['Symbol','Meaning']]+editorial['notation'],widths=[.25,.75])
    h(book,'One blocking step in numbers',2)
    p('For SU(2) in an open fine cube of side four the quotient dimension is 444. Its linearization has 176 transverse fine modes and 28 retained modes per colour. The open scalar fibre and joint gaps are respectively 1.312796 and 1.497923. The physical quadratic singlet trial has value 2.186794 in dimension 15,170. These numbers already separate the three variational problems at the smallest example used here.')
    p('An ordinary proof, a theorem conditional on named premises, a finite numerical result and an open predicate carry different evidentiary meanings. Each target has its actual status at the start. Arithmetic proof fragments and exact definitions have their own declaration levels.')
    h(book,'2   Main results',new=True)
    table(book,[['Domain','Result'],['Open uncut Gaussian boxes','1/27648 classical certificate, strengthened to 1/384 by counts and 1/64 with finite incidence enumeration.'],['Scalar periodic limit','Fibre and joint degree-one infima are enclosed to ten decimal places in §9.'],['Small-field quotient cut','Ordinary geodesic convexity fails in an explicit SU(2) open cube.'],['Finite pinned link','A direct positive curvature floor holds at every weak coupling; four interval checks support the analytic estimate.'],['Interacting Wilson fibre','A volume-independent curvature comparison and a suitable cut-domain implication would give the uniform conditional gap.'],['Public release','Local evidence is included. Authors’ hosted transcript and public identifiers are pending.']],widths=[.29,.71])
    for u in 'ABCDEF':
        title,intro=editorial['units'][u];h(book,str(3+ord(u)-ord('A'))+'   '+title,new=True);p(intro)
        if u=='A':pic(book,0)
        if u=='C':pic(book,1)
        if u=='E':pic(book,3)
        for r in [v for v in rows if v['unit']==u]:
            h(book,r['id']+'   '+r['name'],2)
            pstatus=p(r['actual']+' | '+str(cnt[r['id']])+' tagged checks','Status');control([pstatus._p],'target:'+r['id'])
            pp=p('Prompt status   '+r['expected'],'Small note');control([pp._p],'prompt:'+r['id'])
            p(r['statement'])
            q=p();q.paragraph_format.space_after=Pt(10);q._p.append(deepcopy(math[r['id']]))
            for para in r['proof']:p(para)
            if r['premises']:p(r['premises'],'Small note')
            if u=='B' and r['id'] not in ('B.1','B.2'):p(r['source'],'Small note')
            for d in bytarget[r['id']]:
                q=p('Lean 4   '+d['name']+'   ·   '+d['level']+'   ·   '+d['path'],'Kicker')
                lines_control(book,'sig:'+d['name'],d['signature'].split('\n'),'Signature')
            if not bytarget[r['id']]:p('Lean evidence is recorded at the dependent targets or in the underlying W2 library. The argument or numerical computation above supplies the evidence at this target.','Small note')
            pn=8 if r['id'] in ('F.5','F.6','F.7') else ord(u)-ord('A')+2
            p(f"Python validation   w2cr_validation/part{pn}.py   ·   {cnt[r['id']]} target-tagged checks",'Small note')
    h(book,'9   Numerical data and finite boxes',new=True)
    p('The tables below are generated from the distributed numerical records. Part 8 reads the editable table cells and compares them with the numerical files. Eigenvalue residuals test the finite operator. Intervals marked certified use outward interval arithmetic or exact inequalities. Monte Carlo standard errors and confidence intervals describe stochastic variation at the specified finite settings.')
    for key,(title,rows_table) in numerical().items():
        h(book,title,3)
        if key=='separation':p('Illustration with aKm=0.1, initial x=1/6, b=22/(48π²), d=4bn log 2 and assumed κ=1.3892074859. This periodic scalar reference is an illustrative input.','Small note')
        table(book,rows_table,tag=key)
        if key=='open':pic(book,2)
        if key=='kernel':pic(book,4)
        if key=='strip':pic(book,5)
    h(book,'10   Formal verification in Lean 4',new=True)
    h(book,'Reading the evidence',2)
    p('The statement beside each target is its exact canonical source. Def denotes a definition, including a typed open estimate. L1 denotes a result with ordinary mathematical premises, L2 consumes a named or explicitly supplied bound, and Supplemental marks an arithmetic or order-theoretic fragment of a larger proof. The full compilation unit and its imports appear in Appendix B.')
    h(book,'Kernel and axiom audit',2)
    p('Local Lean 4.36.0 and Mathlib v4.36.0 checked seven statement packets, seven filled packets and a combined packet containing 77 declarations. Complete records are under records/w2c-r. The final source invokes #print axioms and a source fingerprint. Permitted axioms are propext, Classical.choice and Quot.sound. The 91-proof upstream W2 master record is separately compared to its original. No author-hosted record has been supplied.')
    h(book,'Rebuilding the proofs and tables',2)
    for cmd in ['lake exe cache get','bash scripts/run_lean.sh','python3 scripts/formal.py audit','python3 w2cr_validation/run_all.py --out ../fresh-w2cr','python3 scripts/release.py verify']:p(cmd,'Signature')
    p('Run these commands from the extracted root. The Python suite is independent of the Lean executable. It replays kernel output as data. The numerical and released reference suites are included in Appendix B.')
    h(book,'11   Status of the targets',new=True)
    table(book,[['Target','Outcome','Next step']]+[[r['id'],r['actual'],
        'Confirm original wording' if r['unit']=='B' and int(r['id'][2:])>=3 else
        'Check the named analytic premise' if ('onditional' in r['actual'] or 'open' in r['actual'].lower()) else
        'Author-hosted run' if r['id']=='F.5' else 'Assign public identifiers' if r['id']=='F.7' else
        'Replay numerical evidence' if 'umerical' in r['actual'] else 'Review argument and associated records'] for r in rows],widths=[.12,.52,.36])
    h(book,'12   Corrections to the prompt',new=True)
    for a,b in [('A.5','Pointwise conditional estimates require a specified version of the law.'),('A.7 and E.1','The ordinary plaquette cut can fail geodesic convexity. A Neumann implication for it requires a separate boundary argument.'),('B.1','A curl-relative Wilson Taylor remainder fails for constant noncommuting links. An additive estimate survives.'),('B.2–B.7','The three Gaussian forms have different minimizations. A joint quadratic singlet need not cost twice the scalar joint gap. At side eight the elementary degree-three exclusion is inconclusive.'),('C.5–C.7','Nested periodic grids have downward steps and plateaus. The limiting periodic quantities are scalar. An equality with the sharp open physical infimum remains unresolved.'),('D.1–D.2','A singlet floor is insufficient for all tangent directions. A fixed-volume expansion needs twice-differentiable control over the moving cut.'),('E.3','The uniform loss-adjusted floor is at most every pointwise floor.'),('F.1–F.4','Finite Ritz trials are upper estimates and finite-time samples include statistical and systematic effects.')]:p(a+'   '+b)
    h(book,'13   Hand-off and reader problems',new=True)
    table(book,[['Receiver','Output'],['W2d','Canonical conditional law, admissible class and transport domain.'],['W2e','Conditional floor γ, positive threshold margin and resolvent estimates.'],['W2f','Integrated form of the fibre inequality and the conditional assembly theorem.'],['W3','Large-field complements, boundary corrections and conditional concentration estimates.'],['W4','Physical mass/clock data and the strong-coupling passage.']],widths=[.18,.82])
    for i,prob in enumerate(editorial['problems'],1):p(f'{i}.   {prob}')
    h(book,'14   Repository citation and license',new=True)
    p('New release   GitHub [GITHUB PLACEHOLDER]   ·   DOI [DOI PLACEHOLDER]')
    p('Source provenance and pending author actions are described in the release README. The following grant covers the authored exercise and code. Previously released materials retain their own attribution.')
    for block in (ROOT/'LICENSE').read_text().strip().split('\n\n'):p(' '.join(block.splitlines()))
    h(book,'References',new=True)
    for ref in editorial['references']:
        p('['+ref[0]+']   '+ref[1]);p('\n'.join(ref[2:]),'Small note')
    h(book,'Appendix A   Declaration index',new=True)
    p('Names below the W2.W2cR namespace are listed by target. The exact statement is printed at its target and the full proof is printed with its canonical file.')
    table(book,[['Target','Declaration','Level']]+[[v['target'],v['name'],v['level']] for v in sorted(sigs,key=lambda v:(v['target'],v['name']))],widths=[.13,.69,.18])
    h(book,'Appendix B   Complete source edition',new=True)
    p('The following listings are embedded as editable text. Each is tagged with its path and line-ending convention. scripts/extract_sources.py recovers the original bytes. This appendix contains all canonical Lean files, the final check packet, every active Python script, the release tooling and the two earlier Python control suites.')
    items=sources();index=[]
    order=lambda name:(0 if name.startswith('W2') else 1 if name.startswith('packets/') else 2 if name.startswith('w2cr_validation/') else 3 if name.startswith('scripts/') else 4,name)
    for name in sorted(items,key=order):
        book.add_paragraph(name,'Source heading')
        data=source_bytes(name);lines,eol,end=lines_with_format(data)
        index.append([name,len(lines),hashlib.sha256(data).hexdigest()])
        lines_control(book,'src:'+name,lines,'Code line',eol+','+str(int(end)))
    (ROOT/'docs/source-index.tsv').write_text('path\tlines\tsha256\n'+''.join(f'{n}\t{k}\t{d}\n' for n,k,d in index))
    h(book,'Appendix C   Open predicates and hypotheses',new=True)
    p('The following statements specify the outstanding analytic comparison, the boundary condition and the data needed by the assembly. Their quantifiers and definitions also appear in the formal evidence listings.')
    for r in rows:
        if r['premises'] and (r['unit'] in 'DE' or r['id']=='A.7'):
            h(book,r['id']+'   '+r['name'],3);p(r['premises'])
    p('End of the exercise.   GitHub [GITHUB PLACEHOLDER]   ·   DOI [DOI PLACEHOLDER]','Small note')
    book.save(out)
if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--out',type=Path,default=BOOK)
    main(parser.parse_args().out)
