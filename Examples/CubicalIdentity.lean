import SquareKit.Internal.Cubical.IdentityContraction
import Examples.CubicalDiscreteFilling

/-! Marked identities retain constancy data. These examples test strict
contraction boundaries; they do not supply the programme's nonzero higher type. -/
namespace Examples.CubicalIdentity
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf CubicalPresheaf CubicalDiscreteFilling

abbrev fiber := discreteFamily index (fun n => Fin (n+1))
abbrev constantPath := pathLam (finiteLast.reindex (projection (interval naturals))) rfl rfl

def unmarked : Term (identity fiber finiteLast finiteLast) :=
  identityIntro constantPath (Cofibration.bot naturals) (fun _ h => (Bool.false_ne_true h).elim)

theorem markers_retained : unmarked ≠ identityRefl finiteLast := by
  intro h
  have hf := congrArg (fun p => ((p.val (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : ℕ))).face.holds
    (fun _ => none))) h
  cases hf

theorem contraction_starts_at_reflexivity :
    IdentityContraction.atZero unmarked = identityRefl finiteLast :=
  IdentityContraction.atZero_refl unmarked

theorem contraction_recovers_selected_identity : IdentityContraction.atOne unmarked = unmarked :=
  IdentityContraction.atOne_self unmarked

theorem two_substitutions_keep_markers :
    identityFace (Term.map (identityReindex fiber finiteLast finiteLast (twice ≫ successor))
      (unmarked.reindex (twice ≫ successor))) = Cofibration.bot naturals := rfl

end Examples.CubicalIdentity
