import SquareKit.Internal.PathTransport.TwoFamilyVerticalValueAt
import SquareKit.Internal.PathTransport.TwoFamilySectionValueFormula
import SquareKit.NaturalConjugation
import SquareKit.Internal.PathTransport.TwoFamilyRootedRightSectionAction
import SquareKit.Internal.PathTransport.TwoFamilyOrdinarySourceReduction
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
private theorem locallyDiscrete_mk_heq {X Y : Type u} {a : X} {b : Y} (h : HEq a b) :
 HEq (LocallyDiscrete.mk a) (LocallyDiscrete.mk b) := by
 cases type_eq_of_heq h
 cases eq_of_heq h
 rfl
namespace SourceContraction
variable {Γ Δ Θ : Context.{u}} {i : StrictPseudofunctor Δ Γ} (c : SourceContraction i)
 (F : Family Γ) (t : TwoFamily.Section F.data)
 (σ : StrictPseudofunctor Θ Γ) (G : Family Θ) (p : TwoFamily.Section G.data)
 (V : Γ → Type u) (v : ∀ z, V z)
theorem rightEndpointValue_action (hr : c.ReducedIdentityEndpointAction F t σ G p)
 (ht : ∀ z, HEq (t.normalMap F.data (c.homotopy.app z)).fiber (v z)) :
 RightEndpointValueFormula σ G p V v := by
 intro γ
 exact (hr γ).trans (locallyDiscrete_mk_heq (ht (σ.obj γ)))
end SourceContraction
variable (C D : Context.{u}) {Γ : Context.{u}} (A : Family Γ)
variable (t : ULift.{u+1} (TwoFamily.Section (reindex (projectionHigher A.data) A.data)))
variable (x : ULift.{u+1} (TwoFamily.Section A.data))
local notation "M" => fullModel C D
def OrdinaryApRightFormula : Prop :=
 ∀ z, HEq ((ordinaryApRight M A A t x).down.normalMap
  (motive M A ((M).subTy A ((M).weaken Γ A)) x).data
  ((rootContraction C D A x).val.homotopy.app z)).fiber
  (t.down.lift.map ((fiberInclusion A.data z.base.base).map z.fiber.as)).fiber
theorem ordinaryApRight_action : OrdinaryApRightFormula C D A t x := by
 have h := rootContraction_right_section_action C D A x t.down
 run_tac Lean.Elab.Tactic.withMainContext do
  let d ← Lean.Meta.getLocalDeclFromUserName `h
  (← Lean.Elab.Tactic.getMainGoal).assign d.toExpr
  Lean.Elab.Tactic.replaceMainGoal []
variable (y : ULift.{u+1} (TwoFamily.Section A.data))
 (p : ULift.{u+1} (TwoFamily.Section (closedId A.data x.down y.down)))
def OrdinaryApVerticalAction : Prop :=
 VerticalValueAt A x.down t.down ((M).endpointSub A x y p).down
  ((M).identity A (ordinaryApply M A A t x) (ordinaryApply M A A t y))
  (ordinaryApValue M A A t x y p).down
set_option linter.defProp false
theorem ordinaryApValue_vertical_action [∀γ, Subsingleton (A.data.obj γ)] :
 OrdinaryApVerticalAction C D A t x y p := by
 have f := SourceContraction.rightEndpointValue_action (rootContraction C D A x).val
  (motive M A ((M).subTy A ((M).weaken Γ A)) x) (ordinaryApRight M A A t x).down
  ((M).endpointSub A x y p).down
  ((M).identity A (ordinaryApply M A A t x) (ordinaryApply M A A t y))
  (ordinaryApValue M A A t x y p).down
  _ (fun z => (t.down.lift.map ((fiberInclusion A.data z.base.base).map z.fiber.as)).fiber)
  (ordinaryApValue_reduced C D A A t x y p)
 have h := ordinaryApRight_action C D A t x
 run_tac Lean.Elab.Tactic.withMainContext do
  let f ← Lean.Meta.getLocalDeclFromUserName `f
  let h ← Lean.Meta.getLocalDeclFromUserName `h
  let e := Lean.mkApp f.toExpr h.toExpr
  (← Lean.Elab.Tactic.getMainGoal).assign e
  Lean.Elab.Tactic.replaceMainGoal []
/-- Recover the typed arrow of a source identity value using its proved endpoint type. -/
noncomputable def identityValueArrow {V : Type u} (v : V) {C : Type u} [Category.{u} C] {a b : C}
 (e : V = LocallyDiscrete (Discrete (a ⟶ b))) : a ⟶ b := (Eq.mp e v).as.as
theorem identityValueArrow_eq {V : Type u} (v : V) {C : Type u} [Category.{u} C] {a b : C}
 (k : a ⟶ b) (h : HEq v (LocallyDiscrete.mk (Discrete.mk k))) :
 identityValueArrow v (type_eq_of_heq h) = k := by
 cases type_eq_of_heq h
 cases eq_of_heq h
 rfl
theorem identityValue_conjugation {C : Type u} [Category.{u} C]
 (T : C ⥤ C) (β : T ⟶ 𝟭 C) {a b : C} [IsIso (β.app a)]
 (h : a ⟶ b) {V : Type u} (v : V)
 (hv : HEq v (LocallyDiscrete.mk (Discrete.mk (T.map h)))) :
 inv (β.app a) ≫ identityValueArrow v (type_eq_of_heq hv) ≫ β.app b = h := by
 rw [identityValueArrow_eq v (T.map h) hv]
 exact SquareKit.natural_conjugation β h
end SquareKit.Internal.PathTransport.HigherInterpretation
