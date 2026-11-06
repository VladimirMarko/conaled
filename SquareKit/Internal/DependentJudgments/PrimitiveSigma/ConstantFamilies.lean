import SquareKit.Internal.DependentJudgments.PrimitiveSigma.Capability

/-! A constant-family interpretation with indiscrete object identity.
All admitted motives and branches have an eliminator; the extra flag prevents
host equality of repacking and identity. Contextual J is developed separately. -/
namespace SquareKit.Internal.DependentJudgments.PrimitiveSigma.ConstantFamilies
open PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
universe u

variable (Base : Type u)

def structuralModel : StructuralModel.{u+1} where
  Context := Type u
  Family _ := Type u
  Section Γ A := ULift.{u+1} (Γ → A)
  Substitution Δ Γ := ULift.{u+1} (Δ → Γ)
  empty := PUnit
  extend Γ A := Γ × A
  idSub _ := ⟨id⟩
  compSub σ τ := ⟨σ.down ∘ τ.down⟩
  subTy A _ := A
  subTm t σ := ⟨t.down ∘ σ.down⟩
  weaken _ _ := ⟨Prod.fst⟩
  genericVariable _ _ := ⟨Prod.snd⟩
  pairSub _ σ t := ⟨fun δ => (σ.down δ, t.down δ)⟩
  base _ := Base
  fiber _ := PUnit
  identity _ _ _ := PUnit
  reflexivity _ _ := ⟨fun _ => PUnit.unit⟩
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
  pair_eta _ σ := by cases σ; rfl

local notation "M" => structuralModel Base

/-- Primitive split consumes every admitted motive C and every branch,
including branches varying with the context and both pair components. -/
def capability : Capability M where
  sigma A B := (A × B) × Bool
  pack _ _ := ⟨fun p => (p.1.1, ((p.1.2, p.2), false))⟩
  pack_over _ _ := rfl
  split _ _ _ d := ⟨fun p => d.down ((p.1, p.2.1.1), p.2.1.2)⟩
  split_beta _ _ _ _ := HEq.rfl

/-- The derived projections discard only the flag, not either pair component. -/
theorem unpack_apply {Γ : Type u} (A B : Type u) (g : Γ) (a : A) (b : B) (flag : Bool) :
    ((capability Base).unpack (Γ := Γ) A B).down (g, ((a, b), flag)) = ((g, a), b) := by
  rfl

theorem repack_apply {Γ : Type u} (A B : Type u) (g : Γ) (a : A) (b : B) (flag : Bool) :
    ((capability Base).repack (Γ := Γ) A B).down (g, ((a, b), flag)) = (g, ((a, b), false)) := by
  rfl

/-- The stronger host-equality inverse law fails at the actual flag-true object. -/
theorem repack_ne_identity : (capability Base).repack (Γ := PUnit) PUnit PUnit ≠
    (M).idSub ((M).extend PUnit ((capability Base).sigma (Γ := PUnit) PUnit PUnit)) := by
  intro h
  have e := congrArg (fun f => (f.down (PUnit.unit, ((PUnit.unit, PUnit.unit), true))).2.2) h
  change false = true at e
  cases e

end SquareKit.Internal.DependentJudgments.PrimitiveSigma.ConstantFamilies
