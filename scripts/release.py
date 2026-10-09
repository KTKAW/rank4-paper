"""Compile, bundle, extract and compile an Overleaf source archive.
Run from a Git checkout. Requires pdfLaTeX and standard TeX Live packages.
"""
from pathlib import Path
import subprocess,shutil,zipfile,json,hashlib,re,datetime
ROOT=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def compile_paper(directory,compiler):
 for i in range(3):
  result=subprocess.run([compiler,'-interaction=nonstopmode','-halt-on-error','main.tex'],cwd=directory,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
  if result.returncode:raise RuntimeError(result.stdout[-8000:])
 log=(directory/'main.log').read_text()
 bad=re.findall(r'Overfull \\[hv]box[^\n]*|[^\n]*undefined[^\n]*|[^\n]*LaTeX Error[^\n]*',log,re.I)
 if bad:raise RuntimeError('LaTeX QA: '+repr(bad))
 pages=re.search(r'Output written on main.pdf \((\d+) pages?',log)
 return int(pages.group(1)),log

def main():
 compiler=shutil.which('pdflatex') or '/Library/TeX/texbin/pdflatex'
 version=subprocess.check_output([compiler,'--version'],text=True).splitlines()[0]
 commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
 dirty=subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=ROOT,text=True).strip()
 if dirty:raise RuntimeError('Commit tracked source changes before release: '+dirty)
 (ROOT/'paper/revision.tex').write_text('Source snapshot: \\texttt{'+commit[:12]+'}. The full commit is recorded in the accompanying source bundle.\n')
 (ROOT/'docs/DRAFT_COMMIT.txt').write_text(commit+'\n')
 pages,log=compile_paper(ROOT/'paper',compiler)
 out=ROOT/'output';(out/'pdf').mkdir(parents=True,exist_ok=True)
 shutil.copy2(ROOT/'paper/main.pdf',out/'pdf/rank4-mutation-acyclicity.pdf')
 paperfiles=sorted((ROOT/'paper').glob('*.tex'))+sorted((ROOT/'paper/figures').glob('*.pdf'))
 readme='Upload this ZIP as an Overleaf project. Set main.tex as the main file and select pdfLaTeX. All required sources and the generated figure are included. No shell escape or bibliography processor is needed. Source commit: '+commit+'\n'
 archive=out/'rank4-overleaf.zip'
 with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
  for f in paperfiles:z.write(f,f.relative_to(ROOT/'paper'))
  z.writestr('README.txt',readme)
 scratch=ROOT/'tmp/overleaf-extracted'
 if scratch.exists():shutil.rmtree(scratch)
 scratch.mkdir(parents=True)
 with zipfile.ZipFile(archive) as z:z.extractall(scratch)
 copied_pages,copied_log=compile_paper(scratch,compiler)
 assert copied_pages==pages
 for f in paperfiles:assert sha(f)==sha(scratch/f.relative_to(ROOT/'paper'))
 tracked=subprocess.check_output(['git','ls-files','-z'],cwd=ROOT).decode().split('\0')
 with zipfile.ZipFile(out/'rank4-research.zip','w',zipfile.ZIP_DEFLATED) as z:
  for name in tracked:
   if name:z.write(ROOT/name,'rank4-paper/'+name)
  z.write(ROOT/'docs/DRAFT_COMMIT.txt','rank4-paper/docs/DRAFT_COMMIT.txt')
  z.write(ROOT/'paper/revision.tex','rank4-paper/paper/revision.tex')
  z.write(out/'pdf/rank4-mutation-acyclicity.pdf','rank4-paper/output/pdf/rank4-mutation-acyclicity.pdf')
 subprocess.run(['git','bundle','create',str(out/'rank4-repository.bundle'),'--all'],cwd=ROOT,check=True)
 report={'status':'PASS','source_commit':commit,'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'compiler':version,'pages':pages,'extracted_bundle_pages':copied_pages,'source_hashes':{str(f.relative_to(ROOT/'paper')):sha(f) for f in paperfiles},'output_sha256':{str(f.relative_to(out)):sha(f) for f in (out/'pdf/rank4-mutation-acyclicity.pdf',archive,out/'rank4-research.zip',out/'rank4-repository.bundle')},'undefined_references':False,'overfull_boxes':False,'bundle_test':'ZIP extracted into a fresh directory; all input hashes match; pdfLaTeX passed three runs; same page count'}
 (out/'release-report.json').write_text(json.dumps(report,indent=2)+'\n');(out/'latex-final.log').write_text(log)
 print(json.dumps(report,indent=2))
if __name__=='__main__':main()
