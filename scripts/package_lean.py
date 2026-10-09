"""Assemble required source closure from local research; never include cached objects."""
from pathlib import Path
import re,json,hashlib,shutil
ROOT=Path(__file__).resolve().parents[1];WORK=ROOT.parent;ARCH=WORK/'research/archive/important proofs/lean';DEST=ROOT/'lean'
allfiles=[p for p in (WORK/'research').rglob('*.lean') if not any(x in p.parts for x in ('.lake','__MACOSX','build','staged','generated')) and 'build-' not in str(p) and 'audit_build' not in str(p)]
byname={}
for p in allfiles:byname.setdefault(p.name,[]).append(p)
explicit={
 'Rank4Formula.PolynomialTail':WORK/'research/round2/obstruction/Rank4Formula/PolynomialTail.lean',
 'Rank7Adversarial.PolynomialAlternation':WORK/'research/round7/adversarial/PolynomialAlternation.lean',
 'Rank4Round7.Coordinator.NoPolynomialSignClassifier':WORK/'research/round7/coordinator/NoPolynomialSignClassifier.lean',
 'QuiverProofs.BoundedLStarQ179':WORK/'research/round3/build_audit/q179_split/generated/q179/QuiverProofs/BoundedLStarQ179.lean',
}
roots=['Rank4CoordinatorR2.ClassificationCompletion','QuiverProofs.BoundedClassificationCompletion','Rank4Round7.Coordinator.NoPolynomialSignClassifier','Rank4Round8.Arithmetic.AlternatingIntegerLine','Rank4Round8.Reduction.ChoiceFreeListDedup','QuiverProofs.Box']
external={'Mathlib','Lean','Init','Std','Batteries','Aesop','Qq','Plausible','ImportGraph','LeanSearchClient','ProofWidgets'}
def resolve(name):
 if name in explicit:return explicit[name]
 rel=Path(*name.split('.')).with_suffix('.lean')
 if (ARCH/rel).exists():return ARCH/rel
 split=WORK/'research/round3/build_audit/q179_split/generated/q179'/rel
 if split.exists():return split
 cand=byname.get(rel.name,[])
 exact=[p for p in cand if str(p).endswith(str(rel))]
 if len(exact)==1:return exact[0]
 cand=[p for p in cand if '/archive/' not in str(p)]
 if len(cand)==1:return cand[0]
 par='namespace '+name.rsplit('.',1)[0]
 match=[p for p in cand if par in p.read_text()]
 if len(match)==1:return match[0]
 raise ValueError((name,[str(p.relative_to(WORK)) for p in cand]))
seen={};ordered=[]
def visit(name):
 if name.split('.')[0] in external:return
 if name in seen:return
 source=resolve(name);text=source.read_text();original=text
 if name=='Rank4Round7.Coordinator.NoPolynomialSignClassifier':
  text=text.replace('import Rank4Round7.Structure.AlternatingLineIdentity\n','')
  start=text.index('theorem alternatingPolynomial_eval (');end=text.index('private theorem alternatingPolynomial_eval_adversarial')
  text=text[:start]+text[end:];text=text.replace('#print axioms alternatingPolynomial_eval\n','')
 if name=='Rank7Adversarial.PolynomialAlternation':
  text=text.replace('import Rank4Round4.BoundedTwoDepthFormula','import Rank4Formula.FormulaLanguage\nimport QuiverProofs.MAHasTotalProper4Completion').replace('open Rank4Formula Rank4Round4.Formula QuiverProofs','open Rank4Formula QuiverProofs')
  start=text.index('theorem negativeSeed_box');end=text.index('theorem seed_to_line_one')
  proof='''theorem negativeSeed_NMA : ¬ MutationAcyclic (ofTuple negativeSeed) := by
  intro hm
  have hs : SkewSymmetric (ofTuple negativeSeed) := ofSix_skew _ _ _ _ _ _
  obtain ⟨p,hp⟩ := MAHasTotalProper4Completion.maHasTotalProper4 _ hs hm
  obtain ⟨i,hi⟩ := ProperOrder.cyclic_order_exhaustive p
  have hproper := ProperMutation.totalProper_proper _ _ hp
  have htable := (ProperWiggle.properClass_iff_table _ hs p i hi).mp hproper
  have hf : ∀ i : Fin 6, ¬ ProperWiggle.ProperClassTable (ofTuple negativeSeed) i := by decide
  exact hf i htable

'''
  text=text[:start]+proof+text[end:]
 if name=='Rank4Round8.Arithmetic.AlternatingLineParity':
  text=text.replace('open Rank4Formula Rank4Round4.Formula Rank7Adversarial QuiverProofs','open Rank4Formula Rank7Adversarial QuiverProofs')
  start=text.index('theorem oddThreeSeed_box');end=text.index('theorem line_three_to_seed')
  proof="""theorem oddThreeSeed_NMA : ¬ MutationAcyclic (ofTuple oddThreeSeed) := by
  intro hm
  have hs : SkewSymmetric (ofTuple oddThreeSeed) := ofSix_skew _ _ _ _ _ _
  obtain ⟨p,hp⟩ := MAHasTotalProper4Completion.maHasTotalProper4 _ hs hm
  obtain ⟨i,hi⟩ := ProperOrder.cyclic_order_exhaustive p
  have hproper := ProperMutation.totalProper_proper _ _ hp
  have htable := (ProperWiggle.properClass_iff_table _ hs p i hi).mp hproper
  have hf : ∀ i : Fin 6, ¬ ProperWiggle.ProperClassTable (ofTuple oddThreeSeed) i := by decide
  exact hf i htable

"""
  text=text[:start]+proof+text[end:]
  text=text.replace('a BoxTwo NMA certificate','a direct proper-order NMA certificate')
 if name=='MA4EulerMonoEpiTriangleConsumer01a0fee4':
  text=re.sub(r'(IO\.FS\.writeFile\s+)"[^"\n]+ResolvedModules\.json"',r'\1"audit/ResolvedModules.json"',text)
 target=DEST/Path(*name.split('.')).with_suffix('.lean');target.parent.mkdir(parents=True,exist_ok=True);target.write_text(text)
 seen[name]={'source':str(source.relative_to(WORK)),'original_sha256':hashlib.sha256(original.encode()).hexdigest(),'sha256':hashlib.sha256(text.encode()).hexdigest(),'modified':text!=original}
 for imp in re.findall(r'^import\s+([^\n]+)',text,re.M):
  for n in imp.split():visit(n)
 ordered.append(name)
for r in roots:visit(r)
(DEST/'source-manifest.json').write_text(json.dumps({'roots':roots,'modules':seen,'build_order':ordered},indent=2)+'\n')
for n in ('lean-toolchain','lake-manifest.json'):shutil.copy2(ARCH/n,DEST/n)
manifest=json.loads((DEST/'lake-manifest.json').read_text());manifest['name']='rank4_paper';(DEST/'lake-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
s='name = "rank4_paper"\nversion = "0.1.0"\ndefaultTargets = ["Rank4Paper"]\n\n[[require]]\nname = "mathlib"\nscope = "leanprover-community"\ngit = "https://github.com/leanprover-community/mathlib4"\nrev = "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"\n\n[[lean_lib]]\nname = "Rank4Paper"\nroots = '+json.dumps(sorted({n.split('.')[0] for n in seen}))+'\nglobs = '+json.dumps(roots)+'\nmoreLeanArgs = ["--trust=0", "-j1"]\n'
(DEST/'lakefile.toml').write_text(s);(DEST/'audit').mkdir(exist_ok=True)
print('Packaged',len(seen),'source modules;',sum(v['modified'] for v in seen.values()),'modified')
