import MA4EulerMonoEpi01a0fee4
import QuiverProofs.MACompletionCategoricalTriangles
import Lean.Util.CollectAxioms
namespace MA4EulerMonoEpiTriangleConsumer01a0fee4
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open MA4EulerMonoEpi01a0fee4 QuiverProofs.MACompletionCategoricalTriangles
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Original Hom/Hom/Ext consumer: hMaps is derived from local endomorphism
rings and the reverse Ext premise. None of this is numerical realization. -/
theorem hom_hom_ext_consumer (X Y Z : C)
    [IsLocalRing (End Y)] [IsLocalRing (End Z)]
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hXY : ∃ f : X ⟶ Y, f ≠ 0)
    (hYZ : ∃ g : Y ⟶ Z, g ≠ 0)
    (hXZ : ∀ f : X ⟶ Z, f = 0)
    (hExtXY : ∀ e : Ext X Y 1, e = 0)
    (hExtXZ : ∃ e : Ext X Z 1, e ≠ 0)
    (hExtZY : ∀ e : Ext Z Y 1, e = 0) : False := by
  letI := hHered X
  exact no_hom_hom_ext_triangle X Y Z hXY hYZ hXZ hExtXY hExtXZ
    (fun g hg => nonzero_map_mono_or_epi hHered hExtZY g hg)

/-- Original Ext/Ext/Hom consumer with its ordinary map premise eliminated;
local endomorphism rings and reverse Ext(Z,X) vanishing are explicit inputs. -/
theorem ext_ext_hom_consumer (X Y Z : C)
    [IsLocalRing (End X)] [IsLocalRing (End Z)]
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hExtXY : ∃ e : Ext X Y 1, e ≠ 0)
    (hExtYZ : ∃ e : Ext Y Z 1, e ≠ 0)
    (hXZ : ∃ f : X ⟶ Z, f ≠ 0)
    (hExtYX : ∀ e : Ext Y X 1, e = 0)
    (hExtZY : ∀ e : Ext Z Y 1, e = 0)
    (hExtZX : ∀ e : Ext Z X 1, e = 0) : False := by
  exact no_ext_ext_hom_triangle X Y Z hHered hExtXY hExtYZ hXZ hExtYX hExtZY
    (fun f hf => nonzero_map_mono_or_epi hHered hExtZX f hf)

#print axioms hom_hom_ext_consumer
#print axioms ext_ext_hom_consumer
end MA4EulerMonoEpiTriangleConsumer01a0fee4
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut roots : Array Name := #[]
  for (n, _) in env.constants do
    if (n.toString.startsWith "MA4EulerMonoEpi01a0fee4." ||
        n.toString.startsWith "MA4EulerMonoEpiTriangleConsumer01a0fee4.") &&
        getOriginalConstKind? env n == some .thm then roots := roots.push n
  let action : CollectAxioms.M Unit := do
    for n in roots do CollectAxioms.collect n
  let (_, closure) := (action.run env).run {}
  for n in closure.axioms do
    unless #[`propext, `Quot.sound, `Classical.choice].contains n do throwError "Forbidden axiom: {n}"
  for n in closure.visited.toList do
    let some ci := env.checked.get.find? n | throwError "Unchecked proof: {n}"
    if ci.isUnsafe || ci.isPartial || n == `sorryAx then throwError "Unsafe proof: {n}"
    if n.toString.startsWith "Lean.ofReduce" || n.toString.startsWith "Lean.trustCompiler" then
      throwError "Compiler-trusting proof: {n}"
  let mut modules : Array Json := #[]
  for m in env.header.moduleNames do
    let p ← findOLean m
    modules := modules.push (Json.mkObj [("module",toJson m.toString),("olean",toJson p.toString)])
  IO.FS.writeFile "audit/ResolvedModules.json" <|
    (Json.mkObj [("roots",toJson (roots.map Name.toString)),
      ("axioms",toJson (closure.axioms.map Name.toString)),
      ("safe_checked_constants",toJson closure.visited.size),
      ("modules",toJson modules)]).pretty
  logInfo m!"PASS: {roots.size} theorem roots; {closure.visited.size} checked safe constants; standard3 only"
