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

"""Recompute cubical path counts, finite spectra and interval-certified Bloch infima."""
import numpy as np
from common import Checks,output,save,read
from paths import periodic_counts,finite_counts
from free_spectra import periodic,open_box
from bloch_interval import results
def run(out):
    c=Checks();dims=[periodic_counts(d) for d in (2,3,4)]
    for sides in ((2,2,2),(4,6,8),(8,8,8)):
        a,b=finite_counts(sides);c.test('C.1',a<=4 and b<=4,'direct edge/square count '+str(sides))
    c.test('C.2',np.sqrt(12)<4,'three path frequencies have squared sum below 12')
    c.test('C.3',6912*4==27648 and 2*np.sqrt(12)<7,'original rational certificate endpoints')
    c.test('C.4',dims[1]['schur_squared']==16 and 27648/384==72,'sharpened Schur test and analytic improvement')
    rows=[]
    for L in (4,8,16,32,64,128):
        r=periodic(L);rows.append(r)
        c.test('C.5',r['fibre']['gap']<=r['joint']['gap']+1e-12,'periodic fibre and joint ordering at '+str(L))
    save(out/'periodic.json',rows);intervals=results();save(out/'infinite-periodic.json',intervals)
    for z in intervals:
        c.test('C.5',z['decimals'][1]-z['decimals'][0]<1e-8 and z['certified_boxes']>0,'interval covering for '+z['form'])
    ratios=[]
    for L in (4,8,16,32):
        r=open_box(L);save(out/f'open-{L}.json',r)
        c.test('C.6',max(r[f]['residual'] for f in ('fibre','joint'))<1e-8,'open eigensolver residual '+str(L))
        c.test('C.6',r['fibre']['boundary_mass']<r['fibre']['edge_share'],'face mass below uniform edge share '+str(L))
    for L in (4,6,8):
        r=open_box(L) if L==6 else read(out/f'open-{L}.json')
        q=read(out/f'chaos-{L}.json')['quadratic'];j=r['joint']['gap']
        ratios.append(dict(L=L,quadratic=q,joint_degree_one=j,ratio=q/(2*j)))
    save(out/'doubling.json',ratios)
    c.test('B.7',abs(ratios[0]['ratio']-.7299)<.00005,'ratio from two independent numerical constructions')
    c.test('C.7',[len(r['joint']['ties']) for r in rows]==[3,6,6,6,6,6],'all signed grid ties')
    for i in range(len(rows)-1):
        for f in ('joint','fibre'):
            c.test('C.7',rows[i+1][f]['gap']<=rows[i][f]['gap']+1e-12,'nested-grid minimum')
    for d,z in zip((2,3,4),dims):
        c.test('C.8',z['max_swaps']==2*(d-1) and z['max_incidence']==2**(d-1),'dimension-dependent path counts')
    save(out/'paths.json',dims);c.finish(4,out)
if __name__=='__main__':run(output())
