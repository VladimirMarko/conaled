import SquareKit.Internal.Cubical.TaggedUnitUniverse

/-! A native non-univalence counterexample with inhabited equivalence target,
positive same-tag paths, and substitution of the genuine generic code. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace Examples.NonUnivalentUniverse
open CategoryTheory SquareKit.Cubical.Presheaf
open SquareKit.Cubical.Presheaf.TaggedUnit

example : IsEmpty (Term (paths (tag (Γ := terminal) false) (tag true))) := no_path
example : Term (equivalences (tag (Γ := terminal) false) (tag true)) := equivalentFibers
example : ¬ Nonempty (HomotopyEquivalence
    (pathToEquiv (tag (Γ := terminal) false) (tag true))) := not_univalent
example (b : Bool) : Term (paths (tag (Γ := terminal) b) (tag b)) := homogeneousRefl _

/-- The generic Boolean code genuinely varies over the code context. -/
abbrev genericCode : Term (codes codeContext) := generic (codes terminal)

example : genericCode.val (codeContext.elementsMk (Opposite.op ⟨0⟩) ⟨PUnit.unit, false⟩) = false := rfl
example : genericCode.val (codeContext.elementsMk (Opposite.op ⟨0⟩) ⟨PUnit.unit, true⟩) = true := rfl
example : decoded genericCode = decoder := rfl

/-- Both tags select the same decoder, and its selected filler survives substitution. -/
example (b : Bool) :
    (decodedFilling genericCode).reindex (pair (A := codes terminal) (𝟙 terminal) (tag b)) =
      decodedFilling (tag b) := rfl

/-- Uniform filling has both the cap and partial-boundary equations. -/
example {Δ : Context.{0}} (p : total (interval Δ) ⟶ codeContext) (φ : Cofibration Δ)
    (b : OpenBox (reindex decoder p) φ) : b.Fills (decoderFilling.fill p φ b) :=
  decoder_fibrant.fills p φ b

/-- Evaluation recovery is available for the decoder despite failure of univalence. -/
example : SquareKit.RepresentableClassification.Evaluation decoder
    (SquareKit.RepresentableClassification.PresheafFamily.system.decode
      SquareKit.RepresentableClassification.PresheafFamily.universalDecode
      (SquareKit.RepresentableClassification.PresheafFamily.system.code decoder)) :=
  SquareKit.RepresentableClassification.PresheafFamily.evaluation decoder

example : classifierRecovery.hom ≫ classifierRecovery.inv = 𝟙 _ := classifierRecovery.hom_inv_id

end Examples.NonUnivalentUniverse
