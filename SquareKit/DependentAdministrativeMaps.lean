import SquareKit.DependentAdministrativeProofs
import SquareKit.DependentAdministrativeSyntax

/-! Local dependent certificates become composable maps of proof instructions.
Typed substitution is replayed using the syntax map's substitution law. -/
namespace SquareKit.DependentPairJudgments.Administrative
open DependentTheoryMaps DependentPairPresentations

/-- The local certificate for an administrative substitution retains its source
proof, target context proof, and every selected argument proof. -/
def substitutionCertificate {S T : Signature}
    {R : Rules.{1,1} (Judgment S)} {Q : Rules.{1,1} (Judgment T)}
    (F : SyntaxMap S T) (j : Judgment S) (Δ : Context S W)
    (σ : j.Scope → Expr S W) :
    Proof Q (fun k => {i : (rules R).Arity (.substitute j Δ σ) //
      Judgment.map F ((rules R).premise (.substitute j Δ σ) i) = k})
      (Judgment.map F ((rules R).conclusion (.substitute j Δ σ))) := by
  rw [Judgment.map_substituted]
  apply DependentBranchTheoryMaps.Derivation.rule (R := rules Q)
    (.substitute (j.map F) (Δ.map F) (fun v => F.act (σ v)))
  intro i
  cases i with
  | inl u => exact .hyp ⟨.inl (), rfl⟩
  | inr i =>
    cases i with
    | inl u => exact .hyp ⟨.inr (.inl ()), rfl⟩
    | inr v => exact .hyp ⟨.inr (.inr v), Judgment.map_substitution_argument F j Δ σ v⟩

/-- Lift every local dependent certificate. Composition is now the generic
certificate substitution construction, including when both maps expand typed
metavariable applications. -/
def lift {S T : Signature} {R : Rules.{1,1} (Judgment S)}
    {Q : Rules.{1,1} (Judgment T)} (F : SyntaxMap S T)
    (M : MetavariableTheoryMap R Q (Judgment.map F)) :
    DependentBranchTheoryMaps.TheoryMap (rules R) (rules Q) (Judgment.map F) where
  certificate := fun r => match r with
    | .ordinary r => fromCertificate (M.certificate r)
    | .substitute j Δ σ => substitutionCertificate F j Δ σ

/-- On embedded source derivations, erasure agrees with the retained typed
certificate translator as an equality of complete ordinary proof trees. -/
theorem erase_lift {S T : Signature} {R : Rules.{1,1} (Judgment S)}
    {Q : Rules.{1,1} (Judgment T)} (F : SyntaxMap S T)
    (M : MetavariableTheoryMap R Q (Judgment.map F))
    {H : Judgment S → Type} {K : Judgment T → Type}
    (laws : TypedSubstitution.Local (R := Q) (H := K))
    (stable : ∀ j, K j → TypedSubstitution.Reindexed (R := Q) (H := K) j)
    (h : ∀ j, H j → K (Judgment.map F j))
    {j : Judgment S} (d : Derivation R H j) :
    erase laws stable ((lift F M).transport h (embed d)) = M.transport laws stable h d := by
  induction d with
  | hyp => rfl
  | rule r ds ih =>
    simp only [embed, DependentBranchTheoryMaps.TheoryMap.transport, lift,
      MetavariableTheoryMap.transport]
    refine (erase_certificate_graft laws stable (fun i => (lift F M).transport h (embed (ds i))) (M.certificate r)).trans ?_
    congr 1
    funext i
    exact ih i

end SquareKit.DependentPairJudgments.Administrative
