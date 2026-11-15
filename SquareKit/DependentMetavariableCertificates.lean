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
/-- A source primitive rule is certified using its translated, typed premises.
Unlike an arbitrary global proof translator, these certificates are local data. -/
structure MetavariableTheoryMap {S T : Signature}
    (R : Rules.{1,1} (Judgment S)) (Q : Rules.{1,1} (Judgment T))
    (f : Judgment S → Judgment T) where
  certificate : (r : R.Label) → MetavariableCertificate Q
    (fun i : Fin (R.count r) => f (R.premise r i)) (f (R.conclusion r))

namespace MetavariableTheoryMap
variable {S T : Signature} {R : Rules.{1,1} (Judgment S)}
  {Q : Rules.{1,1} (Judgment T)} {f : Judgment S → Judgment T}

/-- Whole-proof translation is derived from local certificates. Hypotheses may
be open only when their target instantiation action is explicitly available. -/
def transport (F : MetavariableTheoryMap R Q f)
    {H : Judgment S → Type} {K : Judgment T → Type}
    (laws : Local (R := Q) (H := K))
    (stable : ∀ j, K j → Reindexed (R := Q) (H := K) j)
    (hypotheses : ∀ j, H j → K (f j)) :
    {j : Judgment S} → Derivation R H j → Derivation Q K (f j)
  | _, .hyp h => .hyp (hypotheses _ h)
  | _, .rule r ds => (F.certificate r).graft laws stable
      (fun i => F.transport laws stable hypotheses (ds i))

def transportClosed (F : MetavariableTheoryMap R Q f)
    (laws : Local (R := Q) (H := fun _ => Empty))
    {j : Judgment S} (d : Derivation R (fun _ => Empty) j) :
    Derivation Q (fun _ => Empty) (f j) :=
  F.transport laws (fun _ h => Empty.elim h) (fun _ h => Empty.elim h) d
end MetavariableTheoryMap

/-- Composable programs of local-certificate translations. Keeping composition
as a program avoids claiming a canonical compression of instantiated proof trees.
The category laws below concern the actual ordinary proof tree produced by run. -/
inductive CertificatePipeline : {S T : Signature} →
    (R : Rules.{1,1} (Judgment S)) → (Q : Rules.{1,1} (Judgment T)) →
    (Judgment S → Judgment T) → Type 2 where
  | identity {S} (R : Rules.{1,1} (Judgment S)) : CertificatePipeline R R id
  | step {S T} {R : Rules.{1,1} (Judgment S)} {Q : Rules.{1,1} (Judgment T)}
      {f : Judgment S → Judgment T} (F : MetavariableTheoryMap R Q f)
      (laws : Local (R := Q) (H := fun _ => Empty)) : CertificatePipeline R Q f
  | comp {S T U} {R : Rules.{1,1} (Judgment S)} {Q : Rules.{1,1} (Judgment T)}
      {P : Rules.{1,1} (Judgment U)} {f : Judgment S → Judgment T} {g : Judgment T → Judgment U} :
      CertificatePipeline R Q f → CertificatePipeline Q P g → CertificatePipeline R P (g ∘ f)

namespace CertificatePipeline
variable {S T U V : Signature} {R : Rules.{1,1} (Judgment S)}
  {Q : Rules.{1,1} (Judgment T)} {P : Rules.{1,1} (Judgment U)}
  {N : Rules.{1,1} (Judgment V)} {f : Judgment S → Judgment T}
  {g : Judgment T → Judgment U} {h : Judgment U → Judgment V}

def run : {S T : Signature} → {R : Rules.{1,1} (Judgment S)} →
    {Q : Rules.{1,1} (Judgment T)} → {f : Judgment S → Judgment T} →
    CertificatePipeline R Q f → {j : Judgment S} →
    Derivation R (fun _ => Empty) j → Derivation Q (fun _ => Empty) (f j)
  | _, _, _, _, _, .identity _, _, d => d
  | _, _, _, _, _, .step F laws, _, d => F.transportClosed laws d
  | _, _, _, _, _, .comp F G, _, d => G.run (F.run d)

@[simp] theorem run_identity (d : Derivation R (fun _ => Empty) j) :
    (identity R).run d = d := rfl

@[simp] theorem run_comp (F : CertificatePipeline R Q f) (G : CertificatePipeline Q P g)
    (d : Derivation R (fun _ => Empty) j) : (F.comp G).run d = G.run (F.run d) := rfl

theorem run_assoc (F : CertificatePipeline R Q f) (G : CertificatePipeline Q P g)
    (K : CertificatePipeline P N h) (d : Derivation R (fun _ => Empty) j) :
    ((F.comp G).comp K).run d = (F.comp (G.comp K)).run d := rfl

theorem run_left_identity (F : CertificatePipeline R Q f) (d : Derivation R (fun _ => Empty) j) :
    ((identity R).comp F).run d = F.run d := rfl

theorem run_right_identity (F : CertificatePipeline R Q f) (d : Derivation R (fun _ => Empty) j) :
    (F.comp (identity Q)).run d = F.run d := rfl
end CertificatePipeline
end SquareKit.DependentPairJudgments
