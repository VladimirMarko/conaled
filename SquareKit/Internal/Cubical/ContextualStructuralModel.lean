import SquareKit.Internal.Cubical.FamilyData
import SquareKit.Internal.PathTransport.Model

/-! The legacy contextual source interface is instantiated by selected lawful
cubical families. This adapter uses the constructed normalized marked Id. -/
namespace SquareKit.Cubical.Contextual
open CategoryTheory Presheaf
open SquareKit.Internal.PathTransport.Typed
universe u

private theorem ulift_heq {X Y : Type u} {x : X} {y : Y} (h : HEq x y) :
    HEq (ULift.up.{u+1} x) (ULift.up.{u+1} y) := by cases h; rfl

noncomputable def structuralModel (Base : LawfulFamily terminal.{u})
    (Fiber : LawfulFamily (total Base.family)) : StructuralModel.{u+1} where
  Context := Presheaf.Context.{u}
  Family := LawfulFamily
  Section _ A := ULift.{u+1} (Term A.family)
  Substitution Δ Γ := ULift.{u+1} (Δ ⟶ Γ)
  empty := terminal
  extend _ A := total A.family
  idSub _ := ⟨𝟙 _⟩
  compSub σ τ := ⟨τ.down ≫ σ.down⟩
  subTy A σ := A.reindex σ.down
  subTm t σ := ⟨t.down.reindex σ.down⟩
  weaken _ A := ⟨projection A.family⟩
  genericVariable _ A := ⟨generic A.family⟩
  pairSub _ σ t := ⟨pair σ.down t.down⟩
  base Γ := Base.reindex (terminalSub Γ)
  fiber x := Fiber.reindex (pair (terminalSub _) x.down)
  identity A x y := A.identity x.down y.down
  reflexivity _ x := ⟨normalizedIdentityRefl x.down⟩
  comp_id_left σ := congrArg ULift.up (Category.comp_id σ.down)
  comp_id_right σ := congrArg ULift.up (Category.id_comp σ.down)
  comp_assoc σ τ υ := congrArg ULift.up (Category.assoc υ.down τ.down σ.down).symm
  subTy_id A := LawfulFamily.reindex_id A
  subTy_comp _ _ _ := rfl
  subTm_id _ := HEq.rfl
  subTm_comp _ _ _ := HEq.rfl
  base_sub _ := rfl
  fiber_sub _ _ := rfl
  identity_sub A x y σ := LawfulFamily.identity_reindex A x.down y.down σ.down
  refl_sub A x σ := by
    apply ulift_heq
    exact (Term.convert_heq _ _).symm.trans
      (heq_of_eq (normalizedIdentityRefl_reindex x.down σ.down))
  weaken_pair _ _ _ := rfl
  variable_pair _ _ _ := HEq.rfl
  pair_eta _ _ := rfl

end SquareKit.Cubical.Contextual
