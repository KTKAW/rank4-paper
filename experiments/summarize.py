"""Regenerate every results table and figure exclusively from saved raw JSONL."""
from pathlib import Path
from collections import defaultdict,Counter
from statistics import median
import csv,json,math,os
ROOT=Path(__file__).resolve().parents[1]
os.environ.setdefault('MPLCONFIGDIR',str(ROOT/'environment/.mplconfig'))
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

def main():
 raw=[json.loads(l) for l in (ROOT/'experiments/raw.jsonl').read_text().splitlines()]
 inputs=json.loads((ROOT/'experiments/inputs.json').read_text());groups=defaultdict(list)
 for r in raw:groups[r['id'],r['method']].append(r)
 metrics=['elapsed_seconds','states_discovered','states_expanded','mutation_evaluations','witness_check_mutations','max_frontier']
 summary=[]
 for inp in inputs:
  for method in ('hybrid','search'):
   rows=groups[inp['id'],method];assert len(rows)==3
   assert len({r['label'] for r in rows})==1 and len({r['branch'] for r in rows})==1
   d={'id':inp['id'],'group':inp['group'],'method':method,'label':rows[0]['label'],'branch':rows[0]['branch'],'H':rows[0]['H'],'N':rows[0]['state_bound'],'log10_N':math.log10(rows[0]['state_bound'])}
   for m in metrics:
    vals=[r[m] for r in rows]
    for suffix,fn in [('median',median),('min',min),('max',max)]:d[m+'_'+suffix]=fn(vals)
   summary.append(d)
 with (ROOT/'experiments/summary.csv').open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=list(summary[0]));w.writeheader();w.writerows(summary)
 index={(r['id'],r['method']):r for r in summary};aggregates=[]
 for group in ('named','uniform','planted'):
  for method in ('hybrid','search'):
   rr=[r for r in summary if r['group']==group and r['method']==method];times=[sum(r['elapsed_seconds'] for r in raw if r['group']==group and r['method']==method and r['repetition']==rep) for rep in range(3)]
   aggregates.append({'group':group,'method':method,'labels':dict(Counter(r['label'] for r in rr)),'sum_seconds_median':median(times),'sum_seconds_range':[min(times),max(times)],'sum_states':sum(r['states_discovered_median'] for r in rr),'sum_mutations':sum(r['mutation_evaluations_median'] for r in rr)})
 (ROOT/'experiments/statistics.json').write_text(json.dumps({'aggregates':aggregates,'capped_inputs':sorted({r['id'] for r in raw if r['label']=='UNKNOWN'}),'rows':len(raw)},indent=2)+'\n')
 short={'acyclic':'acyc.','disconnected':'disc.','triangle':'tri.','double_arrow_box':'box','finite_orbit':'orbit','proper_order':'proper','alternating_line':'line','five_parameter':'five','product_cone':'prod.','quadratic_cone':'quad.','bounded_bfs':'BFS'}
 print('Branches:',sorted({r['branch'] for r in summary}))
 selected=['acyclic','disconnected_MA','disconnected_NMA','double_box','finite_orbit','seed_1','seed_3','five_MA','five_NMA','product','quadratic','scalar_gap','BFS_positive','line_10','line_11','line_128','line_129','line_1000','line_1001']
 names={'acyclic':'Acyclic','disconnected_MA':'Disconnected +','disconnected_NMA':'Disconnected --','double_box':'Double box','finite_orbit':'Finite orbit','seed_1':'$s_1$','seed_3':'$s_3$','five_MA':'Five +','five_NMA':'Five --','product':'Product','quadratic':'Quadratic','scalar_gap':'Scalar equality','BFS_positive':'Search positive'}
 tex=r'''The experiment is a fixed suite of 64 labelled inputs, with three repetitions per input and method (384 calls). We kept every generated input. The 28 named inputs comprise 14 examples chosen to exercise the stated branches and 14 parameters $t=-5,0,1,2,3,4,10,11,32,33,128,129,1000,1001$ of the alternating line. Using Python's pseudorandom generator with seed $20261009$, we also draw 24 independent six-tuples uniformly from $[-3,3]^6$. Finally, 12 planted MA inputs are obtained by drawing all six nonnegative topological entries uniformly from $\{0,1,2\}$ and applying six independent uniformly chosen mutations. The exact draws and generating words are saved.

Runs used an Apple M1 CPU (8 cores, 16 GiB RAM), macOS 26.3 on arm64, and CPython 3.9.6. The program is single-process. For each input the method order is hybrid/search, search/hybrid, hybrid/search. One acyclic warm-up call precedes measurement; there is no result cache. The finite-orbit table is built and checked at import. Each named call is capped at 100,000 discovered states or 3 seconds; each generated call at 25,000 states or 1 second. Timeouts are cooperative, checked once per BFS expansion (and during iterative witness construction). A state cap can therefore be reached before a time cap. Such runs return UNKNOWN.

Timing uses \code{perf_counter} inside the diagnostic call, including the calculation of $H$, tests, search and independent positive-witness replay. It excludes imports and file I/O. Discovered states and expanded states count only BFS states; shortcut-only calls report zero. Mutation evaluations count candidates in BFS, rank-three descent and iterative line reduction, including duplicate or out-of-box candidates. Fixed-word criteria construct their words directly. Witness replay mutations are a separate counter. These conventions explain, for example, why a positive fixed-word shortcut can have zero counted candidate mutations.

\begin{table}[htbp]\centering\scriptsize
\caption{Selected named inputs. Times are medians of three runs, in milliseconds. The full minimum/median/maximum values, expanded states and witness-replay counts are in the saved summary. $S$ and $E$ are discovered states and candidate mutations for search alone. A star means UNKNOWN at the state cap; the displayed time is time spent, not completion time. All hybrid calls in this table complete.}\label{tab:named}
\begin{tabular}{@{}lcrrrrrr@{}}\toprule
Input & Hybrid branch & $H$ & $\log_{10}N$ & Hybrid ms & Search ms & $S$ & $E$\\\midrule
'''
 for name in selected:
  h=index[name,'hybrid'];s=index[name,'search'];label=names.get(name,'$q('+name.removeprefix('line_')+')$');branch=short.get(h['branch'],h['branch']);cap='^{*}' if s['label']=='UNKNOWN' else ''
  tex+=f"{label} & {branch} & {h['H']:,} & {h['log10_N']:.1f} & {1000*h['elapsed_seconds_median']:.3f} & ${1000*s['elapsed_seconds_median']:.3f}{cap}$ & {int(s['states_discovered_median']):,} & {int(s['mutation_evaluations_median']):,} \\\\\n"
 tex+=r'''\bottomrule\end{tabular}\end{table}
The branch abbreviations denote acyclicity, disconnected descent, a rank-three obstruction, the double-box certificate, the finite closed orbit, proper-order exclusion, the line formula, the five-parameter criterion, the product and quadratic criteria, and bounded BFS, respectively. Every reported MA witness was also replayed after the experiment with a separate dense-matrix implementation. Completed labels agree between methods.

\begin{table}[htbp]\centering\small
\caption{All inputs, aggregated by sample. Time is the median of the three sums over the sample, in seconds. State and mutation columns sum the per-input medians. UNKNOWN calls are retained.}\label{tab:generated}
\begin{tabular}{llrrrrrr}\toprule
Sample & Method & MA & NMA & Unknown & Time (s) & States & Mutations\\\midrule
'''
 for a in aggregates:
  tex+=f"{a['group'].capitalize()} & {a['method']} & {a['labels'].get('MA',0)} & {a['labels'].get('NMA',0)} & {a['labels'].get('UNKNOWN',0)} & {a['sum_seconds_median']:.4f} & {int(a['sum_states']):,} & {int(a['sum_mutations']):,} \\\\\n"
 tex+=r'''\bottomrule\end{tabular}\end{table}

The hybrid method resolves all 64 inputs under these limits. Search alone resolves 59; four named inputs and one uniform draw reach their state caps in all repetitions. All 12 planted inputs are confirmed MA by both methods. This sample is small and deliberately includes structured cases; it is not an estimate of the proportion of MA quivers or of average complexity under a canonical distribution.

The contrast is especially clear for the two negative seeds: each has 22,896 states in its reachable height-bounded component, whereas the hybrid proof only inspects its six cyclic orders. For $q(1000)$ the line witness has 500 mutations and must be constructed and checked; its running time consequently grows with the witness length. The odd-line negative certificate does not construct such a trajectory. This is a difference in output work as well as search avoidance. The a priori state bound remains vastly larger than the explored components, including on inputs where BFS is required. It proves termination but is a poor practical predictor of runtime.

\begin{figure}[htbp]\centering
\includegraphics[width=\textwidth]{figures/performance.pdf}
\caption{Each marker represents one of the 64 inputs (medians of three calls). Left: paired runtimes; open upward triangles denote capped search-only runs and must not be read as completion times. The diagonal marks equal time. Right: discovered search-only states versus the labelled bound $N$; capped runs are open triangles. An initially acyclic input has zero BFS states, displayed here at one solely for the logarithmic axis.}\label{fig:performance}
\end{figure}
The plotting environment uses Python 3.12.14 and Matplotlib 3.10.7; its dependency lock is separate from the standard-library-only classifier. Tables and the figure are generated from the saved raw measurements, not from timings in the review report.
'''
 (ROOT/'paper/results.tex').write_text(tex)
 plt.rcParams.update({'font.family':'DejaVu Sans','font.size':9,'axes.spines.top':False,'axes.spines.right':False,'pdf.fonttype':42})
 fig,axes=plt.subplots(1,2,figsize=(9,3.5),layout='constrained');colors={'named':'#245c88','uniform':'#ce7534','planted':'#41875b'}
 for group in colors:
  for cap in (False,True):
   rr=[inp for inp in inputs if inp['group']==group and (index[inp['id'],'search']['label']=='UNKNOWN')==cap]
   hs=[index[i['id'],'hybrid'] for i in rr];ss=[index[i['id'],'search'] for i in rr]
   kw=dict(marker='^' if cap else 'o',s=30,edgecolors=colors[group],facecolors='none' if cap else colors[group],alpha=.8,linewidths=1)
   axes[0].scatter([h['elapsed_seconds_median']*1e3 for h in hs],[s['elapsed_seconds_median']*1e3 for s in ss],label=group if not cap else None,**kw)
   axes[1].scatter([s['N'] for s in ss],[max(1,s['states_discovered_median']) for s in ss],**kw)
 axes[0].plot([.001,2500],[.001,2500],color='#999999',lw=.7,ls='--');axes[0].set(xscale='log',yscale='log',xlabel='Hybrid runtime (ms)',ylabel='Search-only runtime (ms)');axes[0].legend(frameon=False,loc='lower right')
 axes[1].set(xscale='log',yscale='log',xlabel='A priori labelled-state bound N',ylabel='Search-only discovered states')
 for ax in axes:ax.grid(alpha=.18,which='major');ax.set_axisbelow(True)
 out=ROOT/'paper/figures';out.mkdir(exist_ok=True)
 fig.savefig(out/'performance.pdf');fig.savefig(out/'performance.png',dpi=180);plt.close(fig)
 print(json.dumps(aggregates,indent=2))
if __name__=='__main__':main()
