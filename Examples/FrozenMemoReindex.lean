import Examples.FrozenMemoRealization

/-! Arbitrary substitution of the frozen input preserves its dependent types.
The conversions below come from the model's comprehension and identity laws. -/
noncomputable section
namespace Examples.FrozenMemoRealization
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open SquareKit.Internal.DependentJudgments.Contextual.Memo
open Examples.GuardedGroupoidMemo
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward false
universe u
variable (M : SquareKit.Internal.PathTransport.Typed.Model.{u}) {V : Type}
variable {Ω : List (Contextual.Judgment V)} (ρ : V → Value M.toStructuralModel)

theorem section_lift_type {G H : M.Context} (A : M.Family G)
    (B : M.Family (M.extend G A)) (x : M.Section G A) (s : M.Substitution H G) :
    M.subTy (M.subTy B (M.toStructuralModel.sectionSub A x)) s =
      M.subTy (M.subTy B (M.toStructuralModel.lift A s))
        (M.toStructuralModel.sectionSub (M.subTy A s) (M.subTm x s)) := by
  rw [M.subTy_comp, M.subTy_comp, M.toStructuralModel.section_lift]

theorem converted_eval {G : M.Context} {A B : M.Family G}
    (e : A = B) (t : M.Section G A) {st : Contextual.Expression V}
    (ht : st.eval (Contextual.algebra M) ρ = .term G A t) :
    st.eval (Contextual.algebra M) ρ = .term G B (cast (congrArg (M.Section G) e) t) :=
  ht.trans (Value.term_eq e (cast_heq _ _).symm)

namespace InputRealization
variable {M ρ} {F : Frozen.Input Ω} (R : InputRealization M ρ F)

def reindex {Δ σ : Contextual.Expression V} (hσ : Sub (Ω := Ω) Δ F.Γ σ)
    (H : M.Context) (s : M.Substitution H R.context)
    (hΔ : Δ.eval (Contextual.algebra M) ρ = .context H)
    (hs : σ.eval (Contextual.algebra M) ρ = .substitution H R.context s) :
    InputRealization M ρ (F.reindex hσ) := by
  let A := M.subTy R.family s
  let B := M.subTy R.fiber (M.toStructuralModel.lift R.family s)
  let x := M.subTm R.x s
  let y := M.subTm R.y s
  let z := M.subTm R.z s
  let ep := M.identity_sub R.family R.x R.y s
  let p := cast (congrArg (M.Section H) ep) (M.subTm R.p s)
  let p' := cast (congrArg (M.Section H) ep) (M.subTm R.p' s)
  let eq := M.identity_sub R.family R.y R.z s
  let q := cast (congrArg (M.Section H) eq) (M.subTm R.q s)
  have eh : M.subTy (M.identity (M.identity R.family R.x R.y) R.p R.p') s =
      M.identity (M.identity A x y) p p' :=
    (M.identity_sub _ _ _ s).trans (M.toStructuralModel.identity_congr ep
      (cast_heq _ _).symm (cast_heq _ _).symm)
  let h := cast (congrArg (M.Section H) eh) (M.subTm R.h s)
  let eu := section_lift_type M R.family R.fiber R.x s
  let element := cast (congrArg (M.Section H) eu) (M.subTm R.element s)
  exact {
    context := H
    family := A
    fiber := B
    x := x
    y := y
    z := z
    p := p
    p' := p'
    h := h
    q := q
    element := element
    context_eval := hΔ
    family_eval := subTy_eval M ρ F.A σ R.context H R.family s R.family_eval hs
    fiber_eval := subTy_eval M ρ F.B _ _ _ R.fiber _ R.fiber_eval
      (lift_eval M ρ Δ F.A σ R.context H R.family s hΔ R.family_eval hs)
    x_eval := subTm_eval M ρ F.x σ R.context H R.family R.x s R.x_eval hs
    y_eval := subTm_eval M ρ F.y σ R.context H R.family R.y s R.y_eval hs
    z_eval := subTm_eval M ρ F.z σ R.context H R.family R.z s R.z_eval hs
    p_eval := converted_eval M ρ ep _
      (subTm_eval M ρ F.p σ R.context H _ R.p s R.p_eval hs)
    p'_eval := converted_eval M ρ ep _
      (subTm_eval M ρ F.p' σ R.context H _ R.p' s R.p'_eval hs)
    q_eval := converted_eval M ρ eq _
      (subTm_eval M ρ F.q σ R.context H _ R.q s R.q_eval hs)
    h_eval := converted_eval M ρ eh _
      (subTm_eval M ρ F.h σ R.context H _ R.h s R.h_eval hs)
    element_eval := converted_eval M ρ eu _
      (subTm_eval M ρ F.u σ R.context H _ R.element s R.element_eval hs) }

end InputRealization
end Examples.FrozenMemoRealization
