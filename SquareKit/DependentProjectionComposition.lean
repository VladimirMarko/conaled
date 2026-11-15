import SquareKit.DependentCertificateComposition
import SquareKit.DependentProjectionInclusion

namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps TypedSubstitution DependentPairPresentations

private theorem projectionInclusion_count (r : (projectionPresentation false).Label) :
    (projectionPresentation true).count (projectionInclusionLabel r) =
      (projectionPresentation false).count r := by
  cases r with
  | inl r => rfl
  | inr r =>
    cases r with
    | inr r => rfl
    | inl r => cases r <;> first | rfl | contradiction

/-- The complete beta-to-eta inclusion is a replay, including its selected
premise occurrences. This permits compressed composition with typed maps. -/
def projectionReplay : RuleReplay (projectionPresentation false) (projectionPresentation true) id where
  label := projectionInclusionLabel
  premise r i := i.cast (projectionInclusion_count r)
  premise_eq r i := by
    cases r with
    | inl r => rfl
    | inr r =>
      cases r with
      | inr r => rfl
      | inl r => cases r <;> first | rfl | contradiction
  conclusion_eq r := by
    cases r with
    | inl r => rfl
    | inr r =>
      cases r with
      | inr r => rfl
      | inl r => cases r <;> first | rfl | contradiction

theorem projectionReplay_toTheoryMap : projectionReplay.toTheoryMap = projectionInclusion := by
  apply congrArg TheoryMap.mk
  funext r
  cases r with
  | inl r => rfl
  | inr r =>
    cases r with
    | inr r => rfl
    | inl r => cases r <;> first | rfl | contradiction

/-- The compressed composite uses one target certificate per source rule.
Its equality with executing F then G holds for the actual derivation trees. -/
theorem projectionReplay_composition
    {U : Signature} {P : Rules.{1,1} (Judgment U)} {g : Judgment projectionSignature → Judgment U}
    (G : MetavariableTheoryMap (projectionPresentation true) P g)
    {A : Judgment projectionSignature → Type} {B : Judgment projectionSignature → Type} {C : Judgment U → Type}
    (laws : Local (R := P) (H := C))
    (stable : ∀ j, C j → Reindexed (R := P) (H := C) j)
    (a : ∀ j, A j → B j) (b : ∀ j, B j → C (g j))
    (d : Derivation (projectionPresentation false) A j) :
    (G.precompReplay projectionReplay).transport laws stable (fun j h => b j (a j h)) d =
      G.transport laws stable b (projectionInclusion.transport a d) := by
  simpa only [projectionReplay_toTheoryMap, id_eq] using
    G.precompReplay_transport projectionReplay laws stable a b d

end SquareKit.DependentPairJudgments
