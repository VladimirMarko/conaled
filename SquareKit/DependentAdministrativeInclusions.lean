import SquareKit.DependentAdministrativeProofs

/-! Same-syntax ordinary rule interpretations preserve administrative
substitution instructions directly. -/
namespace SquareKit.DependentPairJudgments.Administrative
open DependentTheoryMaps DependentPairPresentations TypedSubstitution

def inclusion {S : Signature} {R Q : Rules.{1,1} (Judgment S)}
    (F : TheoryMap R Q id) :
    DependentBranchTheoryMaps.TheoryMap (rules R) (rules Q) id where
  certificate r := by
    cases r with
    | ordinary r => exact embed (F.certificate r)
    | substitute j Δ σ =>
      exact .rule (R := rules Q) (.substitute j Δ σ) (fun i => .hyp ⟨i, rfl⟩)

theorem embed_graft {S : Signature} {R : Rules.{1,1} (Judgment S)}
    {H K : Judgment S → Type} {j : Judgment S}
    (f : ∀ j, H j → Derivation R K j) (d : Derivation R H j) :
    embed (d.graft f) = (embed d).graft (fun j h => embed (f j h)) := by
  induction d with
  | hyp => rfl
  | rule r ds ih =>
    simp only [Derivation.graft, embed, DependentBranchTheoryMaps.Derivation.graft]
    congr 1
    funext i
    exact ih i

/-- This equality keeps the ordinary rule choices and premise occurrences.
It concerns embedded source proofs, without imposing a compatibility law on
arbitrary source and target substitution reconstruction algorithms. -/
theorem inclusion_transport_embed {S : Signature} {R Q : Rules.{1,1} (Judgment S)}
    (F : TheoryMap R Q id) {H K : Judgment S → Type} {j : Judgment S}
    (h : ∀ j, H j → K j) (d : Derivation R H j) :
    (inclusion F).transport h (embed d) = embed (F.transport h d) := by
  induction d with
  | hyp => rfl
  | rule r ds ih =>
    simp only [embed, DependentBranchTheoryMaps.TheoryMap.transport, inclusion,
      TheoryMap.transport, embed_graft]
    congr 1
    funext k p
    rcases p with ⟨i, hi⟩
    cases hi
    exact ih i

theorem erase_inclusion_transport {S : Signature} {R Q : Rules.{1,1} (Judgment S)}
    (F : TheoryMap R Q id) {H K : Judgment S → Type} {j : Judgment S}
    (laws : Local (R := Q) (H := K))
    (stable : ∀ j, K j → Reindexed (R := Q) (H := K) j)
    (h : ∀ j, H j → K j) (d : Derivation R H j) :
    erase laws stable ((inclusion F).transport h (embed d)) = F.transport h d := by
  rw [inclusion_transport_embed, erase_embed]

end SquareKit.DependentPairJudgments.Administrative
