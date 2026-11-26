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

"""Reproduce the geometry, spectra, conditional implications and finite-model figures."""
import csv
import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
from matplotlib import pyplot as plt
import numpy as np
from catalogue import DATA, ROOT

OUT=ROOT/'figures'
BG='#090d13'
INK='#edf2f7'
TEAL='#73dece'
GOLD='#ffcb84'
GREY='#96a7ba'

def panel(w=8,h=3.0):
    fig,ax=plt.subplots(figsize=(w,h),layout='constrained')
    return fig,ax

def done(fig,key):
    fig.savefig(OUT/(key+'.png'),dpi=165,facecolor=BG)
    plt.close(fig)

def make():
    OUT.mkdir(exist_ok=True)
    plt.rcParams.update({'font.size':10,'font.family':'DejaVu Sans','figure.facecolor':BG,
        'axes.facecolor':BG,'axes.edgecolor':GREY,'axes.labelcolor':INK,'text.color':INK,
        'xtick.color':GREY,'ytick.color':GREY,'legend.facecolor':BG,'legend.frameon':False})
    fig,ax=panel(8,2.4)
    for x in range(5):ax.plot([x,x],[-.7,.7],color=GREY,ls=':',lw=1)
    for y in [-.7,0,.7]:ax.plot([0,4],[y,y],color=GREY,ls=':',lw=1)
    ax.plot([0,1,2],[0,0,0],color=TEAL,lw=3)
    ax.plot([2,3,4],[0,0,0],color=GOLD,lw=3)
    ax.scatter([0,2,4],[0]*3,s=85,facecolor=BG,edgecolors=INK,lw=1.5,zorder=3)
    ax.scatter([1,3],[0]*2,s=50,c=[TEAL,GOLD],zorder=3)
    for x,t in ((.5,'U₁'),(1.5,'U₂'),(2.5,'V₁'),(3.5,'V₂')):ax.text(x,.16,t,ha='center')
    ax.text(1,-.38,'retained product W = U₁U₂',ha='center',color=TEAL)
    ax.text(3,-.38,'second coarse path',ha='center',color=GOLD)
    ax.text(2,.84,'Dotted links illustrate the transverse directions',ha='center',color=GREY)
    ax.set(xlim=(-.48,4.48),ylim=(-.82,1.08));ax.axis('off');done(fig,'geometry')
    fig,ax=panel(8,2.1)
    words=['x y z z','x z y z','z x y z','z x z y','z z x y']
    for i,word in enumerate(words):
        ax.text(i,.56,word,ha='center',fontfamily='DejaVu Sans Mono',fontsize=14,color=TEAL if i in (0,4) else INK)
        if i<4:ax.annotate('',(i+.66,.6),(i+.32,.6),arrowprops={'arrowstyle':'->','color':GOLD})
    ax.text(2,.04,'Each exchange fills one elementary oriented square.',ha='center',color=GREY)
    ax.set(xlim=(-.5,4.5),ylim=(-.2,1.1));ax.axis('off');done(fig,'swaps')
    periodic=json.loads((DATA/'periodic.json').read_text())
    fig,axes=plt.subplots(1,2,figsize=(8,3.0),layout='constrained')
    for ax,key in zip(axes,['fibre','joint']):
        ns=[4,8,16,32]
        ax.plot(ns,[json.loads((DATA/f'open-{n}.json').read_text())[key]['gap'] for n in ns],'o-',color=GOLD,label='Open')
        ax.plot([r['L'] for r in periodic],[r[key]['gap'] for r in periodic],'s-',color=TEAL,label='Periodic',ms=4)
        limit=next(r for r in json.loads((DATA/'infinite-periodic.json').read_text()) if r['form']==key)
        ax.axhline(limit['decimals'][0],ls=':',color=GREY,label='Periodic limit')
        ax.set(xscale='log',xlabel='Fine side L',ylabel=key.capitalize()+' minimum')
        ax.set_xticks([4,8,16,32,64,128],[4,8,16,32,64,128]);ax.legend(fontsize=8);ax.grid(alpha=.15)
    done(fig,'spectra')
    fig,ax=panel(9,3.5)
    cells={0:(.19,.80,'D.1  HessianLowerBoundHyp'),1:(.77,.80,'E.1  BakryEmery\\ncut-domain implication'),2:(.48,.5,'E.2  fibre_poincare_of_hessian'),
           3:(.20,.17,'E.3  eliminated_gap_small_field'),4:(.78,.17,'E.7  assembly_with_gap')}
    def arrow(i,j):
        x,y,_=cells[i];a,b,_=cells[j]
        ax.annotate('',xy=(a,b),xytext=(x,y),arrowprops={'arrowstyle':'->','color':GREY,'lw':1.4,'shrinkA':32,'shrinkB':49})
    for i,j in [(0,2),(1,2),(2,3),(3,4)]:arrow(i,j)
    for i,(x,y,t) in cells.items():
        ax.text(x,y,t.replace('\\n','\n'),ha='center',va='center',fontsize=10,color=GOLD if i<2 else TEAL,
                bbox=dict(boxstyle='round,pad=.5',fc=BG,ec=GOLD if i<2 else TEAL))
    ax.set(xlim=(-.02,1.02),ylim=(0,1));ax.axis('off');done(fig,'chain')
    fig,ax=panel()
    for r in json.loads((DATA/'kernel.json').read_text())['rows']:
        a=np.array(r['shell_frobenius_means']);ax.loglog(a[:,0],a[:,1],'o-',label='L = '+str(r['L']))
    x=np.arange(1,9);ax.loglog(x,.75/x**3,'--',color=GREY,label='r⁻³ reference')
    ax.set(xlabel='Cell distance shell r',ylabel='Mean Frobenius norm');ax.legend(ncol=2);ax.grid(alpha=.15);done(fig,'kernel')
    fig,ax=panel()
    with (DATA/'multilink.csv').open() as f:rows=list(csv.DictReader(f))
    for k,color in zip((.05,1/6),(TEAL,GOLD)):
        r=[t for t in rows if float(t['x'])==k and float(t['eps'])==.125]
        n=np.array([int(t['n']) for t in r]);v=np.array([float(t['ratio']) for t in r])
        yerr=[v-[float(t['ci_low']) for t in r],[float(t['ci_high']) for t in r]-v]
        ax.errorbar(n*(1.025 if k==.05 else .975),v,yerr=yerr,fmt='o-',color=color,capsize=4,label=f'x = {k:.4f}')
    ax.axhline(1,ls=':',color=GREY);ax.set(xlabel='Dynamic midpoint variables',ylabel='Trial ratio z / z pin')
    ax.set_xticks([1,2,4,8]);ax.legend(ncol=2);ax.grid(alpha=.15);done(fig,'strip')
if __name__=='__main__':make()
