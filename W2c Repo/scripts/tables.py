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

"""Generate all quantitative comparison tables in the Word exercise from artifacts."""
import csv
import json
from pathlib import Path
from catalogue import DATA

def numerical(out=DATA):
    def js(name):return json.loads((out/(name+'.json')).read_text())
    def csvrows(name):return list(csv.DictReader((out/(name+'.csv')).open()))
    def fmt(x,n=6):return f'{float(x):.{n}f}'
    def sci(x):return f'{float(x):.2e}'
    def cols(rows,keys):
        return [[str(r[k]) if n is None else fmt(r[k],n) for k,n in keys] for r in rows]
    result={}
    def add(key,title,head,rows):
        result[key]=(title,[head]+[[str(v) for v in r] for r in rows])
    add('wilson','Wilson plaquette remainder for constant noncommuting links',['N','Amplitude','Curl squared','Wilson action','Additive C'],cols(js('gaussian')['wilson'],[('N',None),('t',2),('linear_curl_squared',None),('wilson',8),('absolute_cubic_constant',3)]))
    add('geodesic','Horizontal quotient geodesics on a four-cell cube',['Angle','Midpoint','Max endpoint','Other face','Angle second derivative'],cols(js('convexity'),[('angle',3),('mid',7),('endpoint_max',7),('other_max_at_center',7),('second',6)]))
    add('chaos','Singlet quadratic sector and degree-one comparison',['L','Quadratic','Residual','Degree one','Ratio to double','Higher floor'],[[r['L'],fmt(r['quadratic']),sci(js('chaos-'+str(r['L']))['residual']),fmt(r['joint_degree_one']),fmt(r['ratio'],4),fmt(js('chaos-'+str(r['L']))['higher_floor'])] for r in js('doubling')])
    add('paths','Exact incidence certificate',['Dimension','Max swaps','Max column','Squared bound','Certified floor'],[[r['d'],r['max_swaps'],r['max_incidence'],r['schur_squared'],f"1/{4*r['schur_squared']}" if r['d']==3 else f"1/(2√{r['d']}·{r['schur_squared']})"] for r in js('paths')])
    add('periodic','Periodic alias minima and multiplicities',['L','Fibre','Ties','Joint','Ties'],[[r['L'],fmt(r['fibre']['gap'],9),len(r['fibre']['ties']),fmt(r['joint']['gap'],9),len(r['joint']['ties'])] for r in js('periodic')])
    add('infinite','Certified continuous periodic infima',['Form','Lower','Upper','Interval boxes'],[[r['form'],*map(lambda n:fmt(n,10),r['decimals']),r['certified_boxes']] for r in js('infinite-periodic')])
    add('open','Open cubes and boundary localization',['L','Fibre','Residual F','Joint','Residual J','Face mass F','Edge share'],[[n,fmt(r['fibre']['gap'],8),sci(r['fibre']['residual']),fmt(r['joint']['gap'],8),sci(r['joint']['residual']),fmt(r['fibre']['boundary_mass'],3),fmt(r['fibre']['edge_share'],3)] for n in (4,8,16,32) for r in [js('open-'+str(n))]])
    add('kernel','Embedded conditional precision',['L','Maximum absolute row sum','Fitted exponent'],[[r['L'],fmt(r['maximum_absolute_row_sum'],6),'—' if r['finite_fit'] is None else fmt(r['finite_fit'],3)] for r in js('kernel')['rows']])
    add('curvature','Pinned SU(2) interval curvature certificates',['x','ODE cells','Rigorous floor','Analytic floor','Defect δ'],cols(js('curvature'),[('x',5),('cells',None),('radial_curvature_lower',6),('analytic_floor',5),('delta_uniform_comparison',6)]))
    add('collapse','Collapse upper trials and exponential bound',['s','Trial quotient','Analytic upper bound'],[[s,sci(v),sci(b)] for s,v,b in js('consequences')['collapse']])
    add('separation','Illustrative separation using the periodic joint reference value',['Steps','Running x','Weak lower bound','Dyadic bound'],[[n,fmt(x),fmt(v),fmt(b)] for n,x,v,b in js('consequences')['separation']])
    for name in ('su2','su3'):
        r=csvrows(name); degrees=['ritz6','ritz10','ritz14'] if name=='su2' else ['ritz4','ritz5','ritz6']
        add(name,'Pinned '+('SU(2)' if name=='su2' else 'SU(3)')+' full and cut convergence',['x','Domain',*degrees,'Rel. change','z / z pin'],[[fmt(a['x'],4),a['domain'],*[fmt(a[k],5) for k in degrees],sci(a['change']),fmt(a['ratio'],6)] for a in r])
    add('transfer','Finite Euclidean transfer from forty seeded trials',['x','Domain','ε','T','j','Estimate','SE','Quadrature','Δ/SE'],[[fmt(r['x'],3),r['domain'],fmt(r['eps'],4),fmt(r['T'],1),r['power'],fmt(r['estimate'],4),fmt(r['se'],4),fmt(r['quadrature'],4),fmt(r['zscore'],2)] for r in csvrows('slab')])
    add('aligned','Cut-aligned transfer quadrature at the finest time setting',['x','Nodes','First test','Second test'],cols(js('aligned-slab'),[('x',4),('N',None),('q1',7),('q2',7)]))
    add('strip','Coupled midpoint strips and chain-level 95% intervals',['n','x','ε','T','Ratio','CI low','CI high','τ int'],cols(csvrows('multilink'),[('n',None),('x',4),('eps',3),('T',1),('ratio',4),('ci_low',4),('ci_high',4),('integrated_autocorrelation',2)]))
    return result
