"""Focused fresh replay against explicitly recorded pre-existing dependencies.
Use --full with --external packages directories to compile all project modules from source.
"""
from pathlib import Path
import argparse,os,json,subprocess,time,hashlib,re,shutil
ROOT=Path(__file__).resolve().parents[1];WORK=ROOT.parent;SRC=ROOT/'lean'
def main():
 p=argparse.ArgumentParser();p.add_argument('--full',action='store_true');p.add_argument('--assembly',action='store_true');p.add_argument('--lean');p.add_argument('--external',action='append',default=[]);args=p.parse_args()
 lean=Path(args.lean or shutil.which('lean') or str(WORK/'research/audit/toolchain/.elan/toolchains/leanprover--lean4---v4.24.0/bin/lean'))
 reportdir=ROOT/'docs/checks'/('lean_full' if args.full else 'lean_assembly' if args.assembly else 'lean_focused');reportdir.mkdir(parents=True,exist_ok=True)
 out=SRC/('.fresh-full' if args.full else '.fresh-focused');out.mkdir(exist_ok=True)
 manifest=json.loads((SRC/'source-manifest.json').read_text())
 fresh={'Rank4Formula.PolynomialTail','Rank7Adversarial.PolynomialAlternation','Rank4Round7.Coordinator.NoPolynomialSignClassifier','Rank4Round8.Arithmetic.AlternatingLineParity','Rank4Round8.Arithmetic.AlternatingLineRecognizer','Rank4Round8.Arithmetic.AlternatingIntegerLine'}
 if args.assembly:fresh={'Rank4CoordinatorR2.ClassificationCompletion','QuiverProofs.BoundedClassificationCompletion','Rank4Round8.Reduction.ChoiceFreeListDedup'}
 selected=manifest['build_order'] if args.full else [n for n in manifest['build_order'] if n in fresh]
 # No old project objects are present in full mode.
 dependencies=[] if args.full else [WORK/'research/round8/coordinator/verified_build',WORK/'research/round8/arithmetic/build',WORK/'research/round7/coordinator/final_build',WORK/'research/round6/coordinator/build',WORK/'research/round2/obstruction/build',WORK/'research/round3/build_audit/build-full-r3-split-q179-v1/lib/lean']
 packages=SRC/'.lake/packages' if args.full else WORK/'research/archive/important proofs/lean/.lake/packages'
 if not args.external and not packages.exists():raise SystemExit('Install the locked Lean packages first: cd lean && lake exe cache get, or supply --external LIB_DIR for each dependency.')
 externals=[Path(d) for d in args.external] or [x/'.lake/build/lib/lean' for x in packages.iterdir() if (x/'.lake/build/lib/lean').exists()]
 if not args.full:
  excluded={Path(*n.split('.')).with_suffix('.olean') for n in selected}
  for d in dependencies:
   for f in d.rglob('*.olean'):
    rel=f.relative_to(d)
    if rel in excluded:continue
    t=out/rel
    if not t.exists():t.parent.mkdir(parents=True,exist_ok=True);t.symlink_to(f.resolve())
  for rel in excluded:
   t=out/rel
   if t.is_symlink():t.unlink()
 env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[out]+externals)))
 results=[]
 for n in selected:
  f=SRC/Path(*n.split('.')).with_suffix('.lean');o=out/Path(*n.split('.')).with_suffix('.olean');o.parent.mkdir(parents=True,exist_ok=True)
  log=reportdir/(n+'.log');start=time.monotonic()
  with log.open('w') as stream:r=subprocess.run([str(lean),'--trust=0','-j1','--root='+str(SRC),'-o',str(o),str(f)],cwd=SRC,env=env,stdout=stream,stderr=subprocess.STDOUT)
  body=log.read_text();ok=r.returncode==0 and not re.search(r'(^|\n).*error:|sorryAx|declaration uses .sorry.',body)
  results.append({'module':n,'exit_code':r.returncode,'ok':ok,'seconds':time.monotonic()-start,'source_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'object_sha256':hashlib.sha256(o.read_bytes()).hexdigest() if o.exists() else None})
  print(n,ok,flush=True)
  if not ok:print(body,flush=True);break
 report={'kind':'full fresh project build' if args.full else ('three assembly modules freshly checked with reused project dependency objects' if args.assembly else 'six-module fresh replay with reused project dependency objects'),'lean_version':subprocess.check_output([str(lean),'--version'],text=True).strip(),'flags':['--trust=0','-j1'],'results':results,'all_requested_passed':len(results)==len(selected) and all(x['ok'] for x in results),'reused_dependency_roots':[str(x) for x in dependencies],'external_roots':[str(x) for x in externals]}
 # Hash each reused object actually present in the selected transitive source closure.
 graph={n:re.findall(r'^import\s+([^\n]+)',(SRC/Path(*n.split('.')).with_suffix('.lean')).read_text(),re.M) for n in manifest['modules']}
 todo=list(selected);closure=set()
 while todo:
  n=todo.pop()
  if n in closure or n not in graph:continue
  closure.add(n);todo.extend(x for line in graph[n] for x in line.split())
 report['selected_closure_size']=len(closure);report['selected_closure_contains_heightCoverage_module']='Rank4CoordinatorR2.ClassificationCompletion' in closure;report['selected_closure_contains_bounded_classification']='QuiverProofs.BoundedClassificationCompletion' in closure
 reused={}
 for n in sorted(closure-set(selected)):
  rel=Path(*n.split('.')).with_suffix('.olean')
  f=next((d/rel for d in dependencies if (d/rel).exists()),None)
  if f:reused[n]={'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'resolved':str(f.resolve())}
 report['reused_objects']=reused
 (reportdir/'report.json').write_text(json.dumps(report,indent=2)+'\n')
 return 0 if report['all_requested_passed'] else 1
if __name__=='__main__':raise SystemExit(main())
