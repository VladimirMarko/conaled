import Examples.CubicalCocycleAssignment
import SquareKit.Internal.Cubical.CocycleHigherNonzero

/-! The original frozen homotopy binder receives the chosen nonzero second identity. -/
noncomputable section
namespace Examples.CubicalCocycleAssignment
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open SquareKit.Cubical.CategoryCocycles
open Examples.FrozenMemoStages

private theorem cast_section_reindex {Γ Δ : Context.{0}} {A B : LawfulFamily Γ}
    (e : A = B) (t : ULift.{1} (Term A.family)) (σ : Δ ⟶ Γ) :
    HEq (((cast (congrArg (fun C : LawfulFamily Γ => ULift.{1} (Term C.family)) e) t).down).reindex σ)
      (t.down.reindex σ) := by cases e; rfl

private theorem normalizedIdentity_congr {Γ : Context.{0}} {A B : Family Γ} (e : A = B)
    {a b : Term A} {c d : Term B} (ha : HEq a c) (hb : HEq b d) :
    normalizedIdentity A a b = normalizedIdentity B c d := by
  cases e
  cases ha
  cases hb
  rfl

theorem selected_p : HEq (parallelPoints.p.down.reindex assignParallel)
    (normalizedIdentityRefl (zeroTerm terminal.{0})) := by
  have h₁ := cast_section_reindex
    (CM.identity_sub onePath.family onePath.x onePath.y (CM.weaken onePath.context onePath.path))
    (CM.subTm onePath.p (CM.weaken onePath.context onePath.path)) assignParallel
  have h₂ := cast_section_reindex
    (CM.identity_sub points.family points.x points.y (CM.weaken points.context points.path))
    (CM.genericVariable points.context points.path) assignP
  exact h₁.trans (h₂.trans (Term.convert_heq path_at_assignment.symm (normalizedIdentityRefl (zeroTerm terminal))))

theorem selected_parallel_p : HEq (parallelPoints.p'.down.reindex assignParallel)
    (normalizedIdentityRefl (zeroTerm terminal.{0})) := by
  have h := cast_section_reindex
    (CM.identity_sub onePath.family onePath.x onePath.y (CM.weaken onePath.context onePath.path))
    (CM.genericVariable onePath.context onePath.path) assignParallel
  exact h.trans (Term.convert_heq parallel_path_at_assignment.symm (normalizedIdentityRefl (zeroTerm terminal)))

theorem homotopy_at_assignment : reindex parallelPoints.identity.family assignParallel =
    SecondIdentityFamily terminal.{0} := by
  have hi := normalizedIdentity_reindex parallelPoints.family.family parallelPoints.x.down parallelPoints.y.down assignParallel
  have ho := normalizedIdentity_reindex parallelPoints.path.family parallelPoints.p.down parallelPoints.p'.down assignParallel
  exact ho.trans (normalizedIdentity_congr hi selected_p selected_parallel_p)

def assignedHomotopy : Term (reindex parallelPoints.identity.family assignParallel) :=
  (secondIdentity terminal).convert homotopy_at_assignment.symm

def assignHomotopy : terminal.{0} ⟶ homotopyContext CM cocycleBase cocycleRootedFamily :=
  pair assignParallel assignedHomotopy

end Examples.CubicalCocycleAssignment
