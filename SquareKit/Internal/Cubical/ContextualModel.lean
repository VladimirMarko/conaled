import SquareKit.Internal.Cubical.ContextualIdentityEliminationSubstitution

/-! The existing typed source model is instantiated by the constructed cubical
families, selected fillers, strict identity, and finite-tail J. -/
namespace SquareKit.Cubical.Contextual
open Presheaf SquareKit.Internal.PathTransport.Typed
universe u

private theorem ulift_heq {X Y : Type u} {x : X} {y : Y} (h : HEq x y) :
    HEq (ULift.up.{u+1} x) (ULift.up.{u+1} y) := by cases h; rfl

noncomputable def model (Base : LawfulFamily terminal.{u})
    (Fiber : LawfulFamily (total Base.family)) : Model.{u+1} where
  toStructuralModel := structuralModel Base Fiber
  j A a T C d := ⟨IdentityElimination.eliminate Base Fiber A a T C d.down⟩
  j_beta A a T C d := ulift_heq (heq_of_eq (IdentityElimination.eliminate_beta Base Fiber A a T C d.down))
  j_sub A a T C d σ := ulift_heq (heq_of_eq (IdentityElimination.eliminate_reindex Base Fiber A a T C d σ).symm)

theorem model_j_beta (Base : LawfulFamily terminal.{u})
    (Fiber : LawfulFamily (total Base.family))
    {Γ : (structuralModel Base Fiber).Context}
    (A : (structuralModel Base Fiber).Family Γ)
    (a : (structuralModel Base Fiber).Section Γ A) {n : ℕ}
    (T : StructuralModel.Telescope (structuralModel Base Fiber)
      ((structuralModel Base Fiber).pathContext A a) n)
    (C : (structuralModel Base Fiber).Family T.total)
    (d : (structuralModel Base Fiber).Section
      (StructuralModel.Telescope.pullback (structuralModel Base Fiber) T
        ((structuralModel Base Fiber).rootSub A a)).total
      ((structuralModel Base Fiber).subTy C ((structuralModel Base Fiber).rootTail A a T))) :
    ((model Base Fiber).j A a T C d).down.reindex
      ((structuralModel Base Fiber).rootTail A a T).down = d.down :=
  IdentityElimination.eliminate_beta Base Fiber A a T C d.down

end SquareKit.Cubical.Contextual
