import SquareKit.Internal.Cubical.NativeStructureRecovery
import SquareKit.Internal.Cubical.CartesianNativeStructureRecovery
import Examples.CompositionalStructureIdentity

/-! A higher-universe state package, including its host-proposition invariant,
recovers through both native presentations. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.UniverseStructureLaws
open CategoryTheory SquareKit.StructureIdentity
universe u

abbrev rawState (P : Type u) := Description.product .carrier
  (.product (.function .carrier .carrier) (.function .carrier (.fixed P)))

def invariant {P : Type u} [PropositionCarrier P] {C : Description.{u}}
    (a : Expression (rawState P) C .carrier) : Formula (rawState P) C :=
  .holds (.apply (.second (.second .data)) a)

def state (P : Type u) [PropositionCarrier P] : Specification.{u} where
  description := rawState P
  law := .and (invariant (.first .data))
    (.all .carrier (.implies (invariant (.second .var))
      (invariant (.apply (.first (.second .data)) (.second .var)))))

example : state Prop = Examples.CompositionalStructureIdentity.state := rfl

/-- This is the established state package, with the fixed proposition encoding
removed by an equivalence. Neither invariant proof is discarded. -/
def stateModelEquiv (P X : Type u) [PropositionCarrier P] :
    (state P).Model X ≃ Examples.CubicalStateTransport.StatePackage X where
  toFun s := {
    initial := s.val.1
    step := s.val.2.1
    Invariant := fun x => (PropositionCarrier.decode (P := P)) (s.val.2.2 x)
    initial_valid := s.property.1
    preserves := s.property.2 }
  invFun s := ⟨(s.initial, s.step, fun x => (PropositionCarrier.decode (P := P)).symm (s.Invariant x)),
    by simpa [state, invariant, Formula.Eval, Expression.eval, Description.Data, Equiv.apply_symm_apply] using
      And.intro s.initial_valid s.preserves⟩
  left_inv s := by
    apply Subtype.ext
    change (s.val.1, s.val.2.1, fun x =>
      (PropositionCarrier.decode (P := P)).symm ((PropositionCarrier.decode (P := P)) (s.val.2.2 x))) = s.val
    exact Prod.ext rfl (Prod.ext rfl (funext fun x =>
      (PropositionCarrier.decode (P := P)).symm_apply_apply (s.val.2.2 x)))
  right_inv s := by
    cases s
    simp

abbrev Carrier := ULift.{1} Bool
abbrev higherState := state (ULift.{1} Prop)

def complement : Carrier ≃ Carrier where
  toFun x := ⟨!x.down⟩
  invFun x := ⟨!x.down⟩
  left_inv x := by cases x; simp
  right_inv x := by cases x; simp

def source : higherState.Model Carrier :=
  ⟨(⟨false⟩, id, fun b => ⟨b.down = false⟩), ⟨rfl, fun _ h => h⟩⟩

def target : higherState.Model Carrier := higherState.transport complement source

example : (stateModelEquiv _ _ target).initial = ⟨true⟩ := rfl
example : (stateModelEquiv _ _ target).Invariant ⟨true⟩ := rfl
example : ¬ (stateModelEquiv _ _ target).Invariant ⟨false⟩ := Bool.noConfusion
example : ¬ higherState.Preserves complement source source := by
  intro h
  have eq := (higherState.preserves_iff complement source source).mp h
  exact Bool.noConfusion (congrArg (fun s => s.val.1.down) eq)

namespace Presheaf
open SquareKit.Cubical.Presheaf StructureIdentity.Native
variable {Γ : Context.{2}}

def encoded (s : higherState.Model Carrier) :
    Term (modelsFamily higherState (constantFamily Γ (ULift.{2} Carrier))) :=
  Term.map (presentedModelsIso higherState (Iso.refl _)).inv
    ⟨fun _ => ⟨s⟩, fun _ => rfl⟩

theorem encoded_recovery (s : higherState.Model Carrier) (x : Γ.Elements) :
    (presentedModelsEquiv higherState (Iso.refl _) x ((encoded s).val x)).down = s :=
  congrArg ULift.down ((presentedModelsEquiv higherState (Iso.refl _) x).apply_symm_apply ⟨s⟩)

def moved : Term (modelsFamily higherState (constantFamily Γ (ULift.{2} Carrier))) :=
  Term.map (presentedModelsTransport higherState (Iso.refl _) (Iso.refl _) complement).hom
    (encoded source)

theorem moved_recovery (x : Γ.Elements) :
    (presentedModelsEquiv higherState (Iso.refl _) x (moved.val x)).down = target := by
  change (presentedModelsEquiv higherState (Iso.refl _) x
    ((presentedModelsTransport higherState (Iso.refl _) (Iso.refl _) complement).hom.app x
      ((encoded source).val x))).down = _
  rw [presentedModelsTransport_recovery, encoded_recovery]
  rfl

example (x : Γ.Elements) :
    (stateModelEquiv _ _
      (presentedModelsEquiv higherState (Iso.refl _) x (moved.val x)).down).Invariant ⟨true⟩ := by
  rw [moved_recovery]
  rfl

theorem unchanged_rejected (x : Γ.Elements) : moved.val x ≠ (encoded source).val x := by
  intro h
  have eq := congrArg (fun s => (presentedModelsEquiv higherState (Iso.refl _) x s).down) h
  rw [moved_recovery, encoded_recovery] at eq
  exact Bool.noConfusion (congrArg (fun s => s.val.1.down) eq)

example (x : Γ.Elements)
    (s : (modelsFamily higherState (constantFamily Γ (ULift.{2} Carrier))).obj x) :
    (presentedModelsEquiv higherState (Iso.refl _) x).symm
      (presentedModelsEquiv higherState (Iso.refl _) x s) = s :=
  (presentedModelsEquiv higherState (Iso.refl _) x).symm_apply_apply s

example (x : Γ.Elements) (s : higherState.Model Carrier) :
    presentedModelsEquiv higherState (Iso.refl _) x
      ((presentedModelsEquiv higherState (Iso.refl _) x).symm ⟨s⟩) = ⟨s⟩ :=
  (presentedModelsEquiv higherState (Iso.refl _) x).apply_symm_apply ⟨s⟩
end Presheaf

namespace Cartesian
open SquareKit.Cubical.Cartesian StructureIdentity.Native
variable {Γ : Context.{2}}

def encoded (s : higherState.Model Carrier) :
    Term (modelsFamily higherState (constantFamily Γ (ULift.{2} Carrier))) :=
  Term.map (presentedModelsIso higherState (Iso.refl _)).inv
    ⟨fun _ => ⟨s⟩, fun _ => rfl⟩

theorem encoded_recovery (s : higherState.Model Carrier) (x : Γ.Elements) :
    (presentedModelsEquiv higherState (Iso.refl _) x ((encoded s).val x)).down = s :=
  congrArg ULift.down ((presentedModelsEquiv higherState (Iso.refl _) x).apply_symm_apply ⟨s⟩)

def moved : Term (modelsFamily higherState (constantFamily Γ (ULift.{2} Carrier))) :=
  Term.map (presentedModelsTransport higherState (Iso.refl _) (Iso.refl _) complement).hom
    (encoded source)

theorem moved_recovery (x : Γ.Elements) :
    (presentedModelsEquiv higherState (Iso.refl _) x (moved.val x)).down = target := by
  change (presentedModelsEquiv higherState (Iso.refl _) x
    ((presentedModelsTransport higherState (Iso.refl _) (Iso.refl _) complement).hom.app x
      ((encoded source).val x))).down = _
  rw [presentedModelsTransport_recovery, encoded_recovery]
  rfl

example (x : Γ.Elements) :
    (stateModelEquiv _ _
      (presentedModelsEquiv higherState (Iso.refl _) x (moved.val x)).down).Invariant ⟨true⟩ := by
  rw [moved_recovery]
  rfl

theorem unchanged_rejected (x : Γ.Elements) : moved.val x ≠ (encoded source).val x := by
  intro h
  have eq := congrArg (fun s => (presentedModelsEquiv higherState (Iso.refl _) x s).down) h
  rw [moved_recovery, encoded_recovery] at eq
  exact Bool.noConfusion (congrArg (fun s => s.val.1.down) eq)

example (x : Γ.Elements)
    (s : (modelsFamily higherState (constantFamily Γ (ULift.{2} Carrier))).obj x) :
    (presentedModelsEquiv higherState (Iso.refl _) x).symm
      (presentedModelsEquiv higherState (Iso.refl _) x s) = s :=
  (presentedModelsEquiv higherState (Iso.refl _) x).symm_apply_apply s

example (x : Γ.Elements) (s : higherState.Model Carrier) :
    presentedModelsEquiv higherState (Iso.refl _) x
      ((presentedModelsEquiv higherState (Iso.refl _) x).symm ⟨s⟩) = ⟨s⟩ :=
  (presentedModelsEquiv higherState (Iso.refl _) x).apply_symm_apply ⟨s⟩
end Cartesian

end Examples.UniverseStructureLaws
