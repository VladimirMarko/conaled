import SquareKit.DependentBranchTheoryMaps
import SquareKit.DependentMetavariableCertificates

/-! Typed substitution as an eliminable proof instruction. The underlying
object rules are unchanged; erasure reconstructs ordinary derivations by the
already proved admissibility theorem. -/
namespace SquareKit.DependentPairJudgments.Administrative
open DependentTheoryMaps DependentPairPresentations TypedSubstitution

inductive Label {S : Signature} (R : Rules.{1,1} (Judgment S)) where
  | ordinary (r : R.Label)
  | substitute (j : Judgment S) {W : Type} (Δ : Context S W) (σ : j.Scope → Expr S W)

abbrev rules {S : Signature} (R : Rules.{1,1} (Judgment S)) :
    DependentBranchTheoryMaps.Rules.{1,1} (Judgment S) where
  Label := Label R
  Arity := fun r => match r with
    | .ordinary r => Fin (R.count r)
    | .substitute j _ _ => Unit ⊕ (Unit ⊕ j.Scope)
  premise := fun r => match r with
    | .ordinary r => R.premise r
    | .substitute j Δ σ => Sum.elim (fun _ => j)
        (Sum.elim (fun _ => Judgment.ctx Δ)
          (fun v => Judgment.term Δ (σ v) (Expr.subst σ (j.context.lookup v))))
  conclusion := fun r => match r with
    | .ordinary r => R.conclusion r
    | .substitute j Δ σ => ⟨_, Δ, j.form.subst σ⟩

abbrev Proof {S : Signature} (R : Rules.{1,1} (Judgment S))
    (H : Judgment S → Type) (j : Judgment S) :=
  DependentBranchTheoryMaps.Derivation (rules R) H j

/-- Ordinary proofs embed without changing any rule or premise choice. -/
def embed {S : Signature} {R : Rules.{1,1} (Judgment S)} {H : Judgment S → Type} :
    {j : Judgment S} → Derivation R H j → Proof R H j
  | _, .hyp h => .hyp h
  | _, .rule r ds => .rule (R := rules R) (.ordinary r) (fun i => embed (ds i))

/-- A typed premise application becomes a substitution instruction whose
source is exactly the selected premise occurrence. -/
def fromCertificate {S : Signature} {R : Rules.{1,1} (Judgment S)}
    {I : Type} {premise : I → Judgment S} :
    {j : Judgment S} → MetavariableCertificate R premise j →
      Proof R (fun j => {i : I // premise i = j}) j
  | _, .hyp i => .hyp ⟨i, rfl⟩
  | _, .rule r ds => .rule (R := rules R) (.ordinary r) (fun i => fromCertificate (ds i))
  | _, .apply i Δ σ hΔ args =>
    .rule (R := rules R) (.substitute (premise i) Δ σ)
      (fun x => match x with
        | .inl _ => .hyp ⟨i, rfl⟩
        | .inr (.inl _) => fromCertificate hΔ
        | .inr (.inr v) => fromCertificate (args v))

/-- Eliminate every substitution instruction using admissibility. The result
contains only the original object rules, including for nested instructions. -/
def erase {S : Signature} {R : Rules.{1,1} (Judgment S)} {H : Judgment S → Type}
    (laws : Local (R := R) (H := H))
    (stable : ∀ j, H j → Reindexed (R := R) (H := H) j) :
    {j : Judgment S} → Proof R H j → Derivation R H j
  | _, .hyp h => .hyp h
  | _, .rule r ds => match r with
    | .ordinary r => .rule r (fun i => erase laws stable (ds i))
    | .substitute _j Δ σ =>
      substitute laws stable (erase laws stable (ds (.inl ()))) Δ σ
        ⟨erase laws stable (ds (.inr (.inl ()))),
          fun v => erase laws stable (ds (.inr (.inr v)))⟩

@[simp] theorem erase_embed {S : Signature} {R : Rules.{1,1} (Judgment S)}
    {H : Judgment S → Type} {j : Judgment S} (laws : Local (R := R) (H := H))
    (stable : ∀ j, H j → Reindexed (R := R) (H := H) j)
    (d : Derivation R H j) : erase laws stable (embed d) = d := by
  induction d with
  | hyp => rfl
  | rule r ds ih =>
    simp only [embed, erase]
    congr 1
    funext i
    exact ih i

/-- Interpreting a local certificate after supplying administrative premise proofs
agrees with its original typed grafting. This connects the new representation
to the existing certificate implementation rather than changing its meaning. -/
theorem erase_certificate_graft {S : Signature} {R : Rules.{1,1} (Judgment S)}
    {H : Judgment S → Type} {I : Type} {premise : I → Judgment S} {j : Judgment S}
    (laws : Local (R := R) (H := H))
    (stable : ∀ j, H j → Reindexed (R := R) (H := H) j)
    (proofs : ∀ i, Proof R H (premise i))
    (c : MetavariableCertificate R premise j) :
    erase laws stable ((fromCertificate c).graft
      (fun _ p => p.property ▸ proofs p.val)) =
      c.graft laws stable (fun i => erase laws stable (proofs i)) := by
  induction c with
  | hyp i => rfl
  | rule r ds ih =>
    simp only [fromCertificate, DependentBranchTheoryMaps.Derivation.graft,
      erase, MetavariableCertificate.graft]
    congr 1
    funext i
    exact ih i
  | apply i Δ σ hΔ args ihΔ ihArgs =>
    simp only [fromCertificate, DependentBranchTheoryMaps.Derivation.graft,
      erase, Sum.elim_inl, Sum.elim_inr, MetavariableCertificate.graft]
    congr 2
    funext v
    exact ihArgs v

end SquareKit.DependentPairJudgments.Administrative
