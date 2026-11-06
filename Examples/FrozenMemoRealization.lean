import Examples.GuardedGroupoidMemo

/-! Evaluation of the unchanged frozen client in an arbitrary contextual model.
The input records only the interpretation of its declared binders. Selected
outputs are computed using that model's J, rather than supplied as assumptions. -/
noncomputable section
namespace Examples.FrozenMemoRealization
open SquareKit.GuardedTheory SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open SquareKit.Internal.DependentJudgments.Contextual.Memo
open Examples.GuardedGroupoidMemo
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward false
universe u
variable (M : SquareKit.Internal.PathTransport.Typed.Model.{u}) {V : Type}
variable {Ω : List (Contextual.Judgment V)} (ρ : V → Value M.toStructuralModel)

structure InputRealization (F : Frozen.Input Ω) where
  context : M.Context
  family : M.Family context
  fiber : M.Family (M.extend context family)
  x : M.Section context family
  y : M.Section context family
  z : M.Section context family
  p : M.Section context (M.identity family x y)
  p' : M.Section context (M.identity family x y)
  h : M.Section context (M.identity (M.identity family x y) p p')
  q : M.Section context (M.identity family y z)
  element : M.Section context (M.subTy fiber (M.toStructuralModel.sectionSub family x))
  context_eval : F.Γ.eval (Contextual.algebra M) ρ = .context context
  family_eval : F.A.eval (Contextual.algebra M) ρ = .family context family
  fiber_eval : F.B.eval (Contextual.algebra M) ρ = .family (M.extend context family) fiber
  x_eval : F.x.eval (Contextual.algebra M) ρ = .term context family x
  y_eval : F.y.eval (Contextual.algebra M) ρ = .term context family y
  z_eval : F.z.eval (Contextual.algebra M) ρ = .term context family z
  p_eval : F.p.eval (Contextual.algebra M) ρ = .term context (M.identity family x y) p
  p'_eval : F.p'.eval (Contextual.algebra M) ρ = .term context (M.identity family x y) p'
  h_eval : F.h.eval (Contextual.algebra M) ρ = .term context (M.identity (M.identity family x y) p p') h
  q_eval : F.q.eval (Contextual.algebra M) ρ = .term context (M.identity family y z) q
  element_eval : F.u.eval (Contextual.algebra M) ρ =
    .term context (M.subTy fiber (M.toStructuralModel.sectionSub family x)) element

namespace InputRealization
variable {M ρ} {F : Frozen.Input Ω} (R : InputRealization M ρ F)
variable (hΩ : ∀ j ∈ Ω, j.eval (Contextual.algebra M) ρ)

def selectedValue := transportValue M R.family R.fiber R.y R.z R.q
  (transportValue M R.family R.fiber R.x R.y R.p R.element)
def selectedComposite := transportValue M R.family R.fiber R.x R.z
  (concatValue M R.family R.x R.y R.z R.p R.q) R.element
def selectedCertificate := etaValue M R.family R.fiber R.x R.y R.z R.p R.q R.element

include hΩ in
theorem value_eval : (F.parameters.value F.p).eval (Contextual.algebra M) ρ =
    .term R.context _ R.selectedValue := by
  have e := Contextual.interpret (F.parameters.value_atPath F.hp) M ρ hΩ
  change (F.parameters.value F.p).eval (Contextual.algebra M) ρ = _ at e
  rw [e]
  have hp := transport_eval M ρ F.Γ F.A F.B F.x F.y F.p F.u R.context R.family
    R.fiber R.x R.y R.p R.element R.context_eval R.family_eval R.fiber_eval
    R.x_eval R.y_eval R.p_eval R.element_eval
  exact transport_eval M ρ F.Γ F.A F.B F.y F.z F.q _ R.context R.family
    R.fiber R.y R.z R.q _ R.context_eval R.family_eval R.fiber_eval R.y_eval R.z_eval R.q_eval hp

include hΩ in
theorem certificate_eval : (F.parameters.certificate F.p).eval (Contextual.algebra M) ρ =
    .term R.context _ R.selectedCertificate := by
  have e := Contextual.interpret (F.parameters.certificate_atPath F.hp) M ρ hΩ
  change (F.parameters.certificate F.p).eval (Contextual.algebra M) ρ = _ at e
  rw [e]
  exact eta_eval M ρ F.Γ F.A F.B F.x F.y F.z F.p F.q F.u R.context R.family R.fiber
    R.x R.y R.z R.p R.q R.element R.context_eval R.family_eval R.fiber_eval
    R.x_eval R.y_eval R.z_eval R.p_eval R.q_eval R.element_eval

end InputRealization
end Examples.FrozenMemoRealization
