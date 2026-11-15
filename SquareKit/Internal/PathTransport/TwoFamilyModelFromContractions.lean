import SquareKit.Internal.PathTransport.TwoFamilySourceContractionSubstitution
/-! The contextual model laws follow from normalized rooted contractions
and their coherent substitution squares. Concrete contractions are supplied separately. -/
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u})
local notation "M" => structuralModel C D
noncomputable def modelFromContractions
    (root : ∀ {Γ : (M).Context} (A : (M).Family Γ) (x : (M).Section Γ A),
      {c : SourceContraction ((M).rootSub A x).down // c.Normalized})
    (root_square : ∀ {Γ Δ : (M).Context} (A : (M).Family Γ) (x : (M).Section Γ A)
      (σ : (M).Substitution Δ Γ),
      SourceContraction.Square (root A x).val (root ((M).subTy A σ) ((M).subTm x σ)).val
        ((M).pathSub A x σ).down σ.down) : Typed.Model.{u+1} where
  toStructuralModel := M
  j A x T E d := SourceContraction.eliminate C D T ((M).rootSub A x) (root A x) E d
  j_beta A x T E d := heq_of_eq
    (SourceContraction.eliminate_beta C D T ((M).rootSub A x) (root A x) E d)
  j_sub A x T E d σ := heq_of_eq
    (SourceContraction.eliminate_reindex C D T ((M).rootSub A x)
      ((M).rootSub ((M).subTy A σ) ((M).subTm x σ)) ((M).pathSub A x σ) σ
      ((M).pathSub_root A x σ) (root A x) (root ((M).subTy A σ) ((M).subTm x σ))
      (root_square A x σ) E d)
end SquareKit.Internal.PathTransport.HigherInterpretation
