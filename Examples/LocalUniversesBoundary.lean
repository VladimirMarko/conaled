import Examples.LocalUniverses
import Examples.DependentCongruence
import Examples.GroupoidRoutes
import Examples.SecondIdentity
import SquareKit.Internal.PathTransport.UniversalTransfer

/-!
Retained source and witness boundaries for #292. These are separate from the
Type-family specialization: no interpretation of general higher identity in
`SquareKit.LocalUniverses` is asserted. Only already public #106/#107 transport,
dependent-tail, and higher-loop cases are used; no #108 theorem is selected.
-/

namespace Examples.LocalUniversesBoundary

open SquareKit.Internal.PathTransport
open SquareKit.Internal.PathTransport.Typed

namespace MissingTerminal

/-- A full current source model whose context category is discrete on Bool.
The interface has no axiom requiring `empty` to be terminal. -/
def model : Model where
  Context := Bool
  Family _ := Unit
  Section _ _ := Unit
  Substitution Δ Γ := PLift (Δ = Γ)
  empty := false
  extend Γ _ := Γ
  idSub _ := ⟨rfl⟩
  compSub σ τ := ⟨τ.down.trans σ.down⟩
  subTy _ _ := ()
  subTm t _ := t
  weaken _ _ := ⟨rfl⟩
  genericVariable _ _ := ()
  pairSub _ σ _ := σ
  base _ := ()
  fiber _ := ()
  identity _ _ _ := ()
  reflexivity _ _ := ()
  comp_id_left _ := rfl
  comp_id_right _ := rfl
  comp_assoc _ _ _ := rfl
  subTy_id _ := rfl
  subTy_comp _ _ _ := rfl
  subTm_id _ := HEq.rfl
  subTm_comp _ _ _ := HEq.rfl
  base_sub _ := rfl
  fiber_sub _ _ := rfl
  identity_sub _ _ _ _ := rfl
  refl_sub _ _ _ := HEq.rfl
  weaken_pair _ _ _ := rfl
  variable_pair _ _ _ := HEq.rfl
  pair_eta _ _ := rfl
  j _ _ _ _ _ := ()
  j_beta _ _ _ _ _ := HEq.rfl
  j_sub _ _ _ _ _ _ := HEq.rfl

/-- Hence the current `Model` interface alone does not entail LF's finite
products. This says nothing negative about the concrete groupoid model. -/
theorem no_terminal :
    ¬ ∃ Γ : model.Context, ∀ Δ : model.Context, Nonempty (model.Substitution Δ Γ) := by
  rintro ⟨Γ, h⟩
  cases Γ with
  | false => obtain ⟨s⟩ := h true; exact Bool.noConfusion s.down
  | true => obtain ⟨s⟩ := h false; exact Bool.noConfusion s.down

end MissingTerminal

namespace Source

open Authoring

/-- Use the existing generated source term and its existing composition rule.
The result compares repeated substitution of that fixed term, not a newly
constructed concatenation in a different context presentation. -/
def transport_twice
    (hs : SubDeriv Δ δ (TransferFrame.contextRaw UniversalTransfer.context)
      (TransferFrame.contextCode UniversalTransfer.context) σ s)
    (ht : SubDeriv Θ θ Δ δ τ t) :=
  TmEqDeriv.subComp UniversalTransfer.proof hs ht

/-- The known dependent second-component conversion remains generated source
conversion, and remains available under two further substitutions. -/
def dependent_tail_twice
    (hs : SubDeriv Δ δ (TransferFrame.contextRaw CongruenceCaller.context)
      (TransferFrame.contextCode CongruenceCaller.context) σ s)
    (ht : SubDeriv Θ θ Δ δ τ t) :=
  SubEqDeriv.comp
    (SubEqDeriv.comp DependentCongruence.DependentArguments.dependentPair (.refl hs)) (.refl ht)

end Source

namespace Witnesses

open CategoryTheory
open GroupoidTransport

/-- This equation is obtained by interpreting the pre-existing generated
transport proof, then applied to the existing nonconstant groupoid action. -/
theorem source_transport (b : ZMod 2) :
    GroupoidRoutes.binary.map (label 1 ≫ label 1) b =
      GroupoidRoutes.binary.map (label 1) (GroupoidRoutes.binary.map (label 1) b) :=
  GroupoidModel.UniversalTransfer.transport_concat C4 GroupoidRoutes.binary _ _ b

example : GroupoidRoutes.binary.map (label 1) (0 : ZMod 2) = 1 :=
  GroupoidRoutes.generator_zero

example : ¬ Nonempty (GroupoidRoutes.binary ≅ (Functor.const C4).obj (ZMod 2)) :=
  GroupoidRoutes.not_constant

open SquareKit.Internal.TwoLoop

def higherFirst (_ : Unit) : Expr Unit := .inverse (.var ())
def higherSecond (_ : Unit) : Expr Unit := .horizontal (.var ()) .unit
def higherTwice : Expr Unit :=
  (SecondIdentity.construction.subst higherFirst).subst higherSecond

/-- Both substitutions still feed the same algebraic 2-loop derivation to
the existing Boolean and ZMod interpretations. -/
theorem higher_routes_agree :
    SecondIdentity.encode (higherTwice.eval SecondIdentity.bitInput) =
      higherTwice.eval SecondIdentity.labelInput :=
  SecondIdentity.routes_agree higherTwice

theorem higher_observation :
    SecondIdentity.labelObservation (higherTwice.eval SecondIdentity.labelInput) = 1 := by
  rw [← higher_routes_agree, SecondIdentity.observation_encode]
  decide

/-- Any replacement that uses native equality for these 2-cell witnesses
fails to preserve their observation, even if substitution is strict. -/
example (forget : SquareKit.DoubleDelooping.Cell SecondIdentity.Label → (true = true)) :
    ¬ ∃ observe : (true = true) → Nat,
      ∀ c, observe (forget c) = SecondIdentity.labelObservation c :=
  SecondIdentity.no_native_identity_observation true forget

end Witnesses

end Examples.LocalUniversesBoundary
