import SquareKit.DependentTypedSubstitution

/-! Local rule certificates with explicitly typed metavariable applications.
These application nodes belong to the certificate language, not the object
calculus. Grafting removes them by admissible typed substitution. -/
namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps DependentPairPresentations TypedSubstitution

/-- A premise declaration can be used at a typed substitution into its declared
context. Its argument derivations are children of the certificate node. -/
inductive MetavariableCertificate {S : Signature} (R : Rules.{1,1} (Judgment S))
    {I : Type} (premise : I → Judgment S) : Judgment S → Type 1 where
  | hyp (i : I) : MetavariableCertificate R premise (premise i)
  | rule (r : R.Label)
      (children : ∀ i : Fin (R.count r), MetavariableCertificate R premise (R.premise r i)) :
      MetavariableCertificate R premise (R.conclusion r)
  | apply (i : I) {W : Type} (Δ : Context S W) (σ : (premise i).Scope → Expr S W)
      (context : MetavariableCertificate R premise (Judgment.ctx Δ))
      (arguments : ∀ v, MetavariableCertificate R premise
        (Judgment.term Δ (σ v) (Expr.subst σ ((premise i).context.lookup v)))) :
      MetavariableCertificate R premise ⟨W, Δ, (premise i).form.subst σ⟩

namespace MetavariableCertificate
variable {S : Signature} {R : Rules.{1,1} (Judgment S)} {H : Judgment S → Type}
  {I : Type} {premise : I → Judgment S}

/-- Eliminate every metavariable application by substituting into its supplied
proof. The result is an ordinary proof in R, with no additional object rule. -/
def graft (laws : Local (R := R) (H := H))
    (hypotheses : ∀ j, H j → Reindexed (R := R) (H := H) j)
    (proofs : ∀ i, Derivation R H (premise i)) :
    {j : Judgment S} → MetavariableCertificate R premise j → Derivation R H j
  | _, .hyp i => proofs i
  | _, .rule r children => .rule r (fun i => graft laws hypotheses proofs (children i))
  | _, .apply i Δ σ context arguments =>
      substitute laws hypotheses (proofs i) Δ σ
        ⟨graft laws hypotheses proofs context, fun v => graft laws hypotheses proofs (arguments v)⟩

/-- A direct use can also be reconstructed as an identity application when
its telescope and variables have been derived. -/
def identityApplication (i : I)
    (context : MetavariableCertificate R premise (Judgment.ctx (premise i).context))
    (vars : ∀ v, MetavariableCertificate R premise
      (Judgment.term (premise i).context (.var v) ((premise i).context.lookup v))) :
    MetavariableCertificate R premise (premise i) := by
  have app := MetavariableCertificate.apply i (premise i).context Expr.var context
    (fun v => by simpa only [Expr.subst_id] using vars v)
  simpa only [Form.subst_identity] using app

end MetavariableCertificate
end SquareKit.DependentPairJudgments
