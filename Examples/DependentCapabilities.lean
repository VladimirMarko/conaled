import SquareKit.TypeFamilyRepresentation
import SquareKit.Internal.PathTransport.Representability
import SquareKit.Internal.PathTransport.UniversalTransfer
import SquareKit.Internal.DependentJudgments.NativeTypeModel
import Examples.GroupoidRoutes

/-! The sections-over-a-base consumer needs only represented indexed families.
The same consumer recovers the selected operations of the existing models and
the complete interpreted universal transport proof. -/
namespace Examples.DependentCapabilities
open CategoryTheory
open SquareKit.Internal.PathTransport
open Typed
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SignatureFree
open SquareKit.TypeFamilyRepresentation

def family (n : Nat) := Fin (n + 1)
def base : Nat ⟶ Nat := ↾fun n => 2 * n
def term : families.Tm Nat (families.pullTy family base) :=
  ⟨fun n => ⟨n, by change n < 2 * n + 1; omega⟩⟩

/-- A varying family and nonidentity base require no base/fiber signature,
empty context, identity type or J assignment. -/
def arrow := representation.sectionsOver family base term

theorem arrow_apply (n : Nat) : arrow.val n = ⟨2 * n, ⟨n, by omega⟩⟩ := rfl

theorem recover_term : (representation.sectionsOver family base).symm arrow = term :=
  (representation.sectionsOver family base).symm_apply_apply term

/-- First increment the input, then double the base. At 3 the base is 8 and
the retained fiber value is 4; reversing the base maps would give 7. -/
theorem composed_arrow :
    ((↾fun n : Nat => n + 1) ≫ arrow.val) 3 = ⟨8, ⟨4, by decide⟩⟩ := by
  rw [arrow, representation.sectionsOver_natural]
  rfl

/-- Distinct selected sections remain distinguishable after representation. -/
theorem distinguishes_sections :
    representation.sectionsOver (fun _ : Unit => Fin 2) (𝟙 Unit) ⟨fun _ => (0 : Fin 2)⟩ ≠
      representation.sectionsOver (fun _ : Unit => Fin 2) (𝟙 Unit) ⟨fun _ => (1 : Fin 2)⟩ := by
  intro h
  have ht := (representation.sectionsOver (fun _ : Unit => Fin 2) (𝟙 Unit)).injective h
  have hv := congrArg (fun t => t.down ()) ht
  exact (by decide : (0 : Fin 2) ≠ 1) hv

end SignatureFree

namespace Native
abbrev M := SquareKit.Internal.DependentJudgments.NativeType.structuralModel Nat
  (fun n => Fin (n + 1))

/-- The old Type provider uses lifted functions; the adapter retains those
chosen arrows and terms rather than replacing the provider's signature. -/
theorem same_consumer {Γ Δ : M.Context} (A : M.Family Γ) (σ : M.Substitution Δ Γ) :
    M.representedSectionsOver A σ = M.sectionsOver A σ :=
  M.representedSectionsOver_eq A σ

theorem chosen_pair (n : Nat) :
    (M.representedSectionsOver SignatureFree.family ⟨fun n : Nat => 2 * n⟩
      ⟨fun n => ⟨n, by change n < 2 * n + 1; omega⟩⟩).val.down n =
        ⟨2 * n, ⟨n, by omega⟩⟩ := by
  rw [same_consumer]
  rfl
end Native

namespace Groupoids
open SquareKit.GroupoidTransport
open Examples.GroupoidTransport

noncomputable abbrev M := GroupoidModel.Instance.structuralModel C4 Examples.GroupoidRoutes.binary

/-- The independent consumer recovers the existing equivalence on actual
functors and sections, including their action on arrows. -/
theorem same_consumer {Γ Δ : M.Context} (A : M.Family Γ) (σ : M.Substitution Δ Γ) :
    M.representedSectionsOver A σ = M.sectionsOver A σ :=
  M.representedSectionsOver_eq A σ

theorem selected_section {Γ Δ : M.Context} (A : M.Family Γ) (σ : M.Substitution Δ Γ)
    (t : M.Section Δ (M.subTy A σ)) :
    (M.representedSectionsOver A σ).symm (M.sectionsOver A σ t) = t := by
  rw [← same_consumer]
  exact (M.representedSectionsOver A σ).symm_apply_apply t

/-- This provider's family detects a nontrivial base loop. Recovering sections
above does not assert that this transport can be replaced by identity. -/
theorem nonconstant_action :
    Examples.GroupoidRoutes.binary.map (label 1) (0 : ZMod 2) ≠ 0 := by
  rw [Examples.GroupoidRoutes.generator_zero]
  change (1 : ZMod 2) ≠ 0
  decide

end Groupoids

namespace FullClient
set_option maxHeartbeats 1000000
universe u
variable (M : Model.{u})

/-- The retained source client uses contextual J to prove transport along a
concatenation. Representation packages its actual interpreted certificate. -/
noncomputable def transportArrow :=
  M.toStructuralModel.representation.sections _
    (interpretTm M Authoring.UniversalTransfer.proof)

noncomputable def recoveredTransport :=
  (M.toStructuralModel.representation.sections _).symm (transportArrow M)

/-- Equality is of the complete selected semantic section, before any
specialization to a truncated model or extraction of an endpoint equation. -/
theorem recoveredTransport_eq :
    recoveredTransport M = interpretTm M Authoring.UniversalTransfer.proof :=
  (M.toStructuralModel.representation.sections _).symm_apply_apply _

theorem recoveredTransport_sub {Δ : M.Context}
    (σ : M.Substitution Δ
      (Authoring.TransferFrame.contextCode Authoring.UniversalTransfer.context M)) :
    M.subTm (recoveredTransport M) σ =
      M.subTm (interpretTm M Authoring.UniversalTransfer.proof) σ := by
  rw [recoveredTransport_eq]

end FullClient
end Examples.DependentCapabilities
