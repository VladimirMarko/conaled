import SquareKit.DependentCertificateEmbedding

/-! Compressed composition with rule replay. A replay only changes rule labels
and their premise wiring; the following typed certificate map may use dependent
metavariable applications. The composition theorem compares actual proof trees. -/
namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps TypedSubstitution

namespace MetavariableCertificate
variable {S : Signature} {R : Rules.{1,1} (Judgment S)} {I K : Type}
  {premise : I → Judgment S} {target : K → Judgment S}

private def applyCast (i : K) (j : Judgment S) (eq : target i = j)
    {W : Type} (Δ : Context S W) (σ : j.Scope → Expr S W)
    (ctx : MetavariableCertificate R target (.ctx Δ))
    (args : ∀ v, MetavariableCertificate R target (.term Δ (σ v) (Expr.subst σ (j.context.lookup v)))) :
    MetavariableCertificate R target ⟨W, Δ, j.form.subst σ⟩ := by
  cases eq
  exact .apply i Δ σ ctx args

/-- Rename premise occurrences while retaining their complete typed application
arguments. The index function may duplicate premises; it does not identify data. -/
def reindex (index : I → K) (eq : ∀ i, target (index i) = premise i) :
    {j : Judgment S} → MetavariableCertificate R premise j → MetavariableCertificate R target j
  | _, .hyp i => eq i ▸ .hyp (index i)
  | _, .rule r children => .rule r (fun i => reindex index eq (children i))
  | _, .apply i Δ σ ctx args => applyCast (index i) (premise i) (eq i) Δ σ
      (reindex index eq ctx) (fun v => reindex index eq (args v))

private theorem graft_cast {H : Judgment S → Type}
    (laws : Local (R := R) (H := H))
    (stable : ∀ j, H j → Reindexed (R := R) (H := H) j)
    (proofs : ∀ k, Derivation R H (target k)) {j k : Judgment S}
    (eq : j = k) (d : MetavariableCertificate R target j) :
    (eq ▸ d).graft laws stable proofs = eq ▸ d.graft laws stable proofs := by
  cases eq
  rfl

private theorem graft_applyCast {H : Judgment S → Type}
    (laws : Local (R := R) (H := H))
    (stable : ∀ j, H j → Reindexed (R := R) (H := H) j)
    (proofs : ∀ k, Derivation R H (target k))
    (i : K) (j : Judgment S) (eq : target i = j)
    {W : Type} (Δ : Context S W) (σ : j.Scope → Expr S W)
    (ctx : MetavariableCertificate R target (.ctx Δ))
    (args : ∀ v, MetavariableCertificate R target (.term Δ (σ v) (Expr.subst σ (j.context.lookup v)))) :
    (applyCast i j eq Δ σ ctx args).graft laws stable proofs =
      substitute laws stable (eq ▸ proofs i) Δ σ
        ⟨ctx.graft laws stable proofs, fun v => (args v).graft laws stable proofs⟩ := by
  cases eq
  rfl

theorem graft_reindex {H : Judgment S → Type}
    (laws : Local (R := R) (H := H))
    (stable : ∀ j, H j → Reindexed (R := R) (H := H) j)
    (index : I → K) (eq : ∀ i, target (index i) = premise i)
    (proofs : ∀ k, Derivation R H (target k))
    (d : MetavariableCertificate R premise j) :
    (d.reindex index eq).graft laws stable proofs =
      d.graft laws stable (fun i => eq i ▸ proofs (index i)) := by
  induction d with
  | hyp i =>
      simp only [reindex, graft_cast, graft]
  | rule r children ih =>
      simp only [reindex, graft]
      congr 1
      funext i
      exact ih i
  | apply i Δ σ ctx args ihctx ihargs =>
      simp only [reindex, graft_applyCast, graft]
      congr 1
      congr 1
      funext v
      exact ihargs v
end MetavariableCertificate

/-- Local rule replay: every target premise is an explicitly chosen occurrence
of a translated source premise. No complete-proof transport is a field. -/
structure RuleReplay {S T : Signature}
    (R : Rules.{1,1} (Judgment S)) (Q : Rules.{1,1} (Judgment T))
    (f : Judgment S → Judgment T) where
  label : R.Label → Q.Label
  premise : ∀ r, Fin (Q.count (label r)) → Fin (R.count r)
  premise_eq : ∀ r i, Q.premise (label r) i = f (R.premise r (premise r i))
  conclusion_eq : ∀ r, Q.conclusion (label r) = f (R.conclusion r)

namespace RuleReplay
variable {S T : Signature} {R : Rules.{1,1} (Judgment S)}
  {Q : Rules.{1,1} (Judgment T)} {f : Judgment S → Judgment T}

def toTheoryMap (F : RuleReplay R Q f) : TheoryMap R Q f where
  certificate r := F.conclusion_eq r ▸ Derivation.rule (R := Q) (F.label r)
    (fun i => .hyp ⟨F.premise r i, (F.premise_eq r i).symm⟩)
private theorem graft_cast {H K : Judgment T → Type} {j k : Judgment T}
    (eq : j = k) (d : Derivation Q H j) (hyp : ∀ j, H j → Derivation Q K j) :
    (eq ▸ d).graft hyp = eq ▸ d.graft hyp := by
  cases eq
  rfl

 theorem transport_rule (F : RuleReplay R Q f)
    {H : Judgment S → Type} {K : Judgment T → Type}
    (hyp : ∀ j, H j → K (f j)) (r : R.Label)
    (ds : ∀ i : Fin (R.count r), Derivation R H (R.premise r i)) :
    F.toTheoryMap.transport hyp (.rule r ds) =
      F.conclusion_eq r ▸ Derivation.rule (R := Q) (F.label r)
        (fun i => (F.premise_eq r i).symm ▸ F.toTheoryMap.transport hyp (ds (F.premise r i))) := by
  simp only [TheoryMap.transport, toTheoryMap, graft_cast, Derivation.graft]

end RuleReplay

namespace MetavariableTheoryMap
variable {S T U : Signature} {R : Rules.{1,1} (Judgment S)}
  {Q : Rules.{1,1} (Judgment T)} {P : Rules.{1,1} (Judgment U)}
  {f : Judgment S → Judgment T} {g : Judgment T → Judgment U}

/-- A genuine compressed local certificate map, not a stored execution pipeline. -/
def precompReplay (G : MetavariableTheoryMap Q P g) (F : RuleReplay R Q f) :
    MetavariableTheoryMap R P (g ∘ f) where
  certificate r := by
    change MetavariableCertificate P (fun i : Fin (R.count r) => g (f (R.premise r i))) (g (f (R.conclusion r)))
    exact congrArg g (F.conclusion_eq r) ▸ (G.certificate (F.label r)).reindex
      (target := fun i : Fin (R.count r) => g (f (R.premise r i))) (F.premise r)
      (fun i => (congrArg g (F.premise_eq r i)).symm)

private theorem transport_cast (G : MetavariableTheoryMap Q P g)
    {H : Judgment T → Type} {K : Judgment U → Type}
    (laws : Local (R := P) (H := K))
    (stable : ∀ j, K j → Reindexed (R := P) (H := K) j)
    (hyp : ∀ j, H j → K (g j)) {j k : Judgment T} (eq : j = k)
    (d : Derivation Q H j) :
    G.transport laws stable hyp (eq ▸ d) =
      congrArg g eq ▸ G.transport laws stable hyp d := by
  cases eq
  rfl

theorem precompReplay_transport (G : MetavariableTheoryMap Q P g) (F : RuleReplay R Q f)
    {A : Judgment S → Type} {B : Judgment T → Type} {C : Judgment U → Type}
    (laws : Local (R := P) (H := C))
    (stable : ∀ j, C j → Reindexed (R := P) (H := C) j)
    (a : ∀ j, A j → B (f j)) (b : ∀ j, B j → C (g j))
    (d : Derivation R A j) :
    (G.precompReplay F).transport laws stable (fun j h => b (f j) (a j h)) d =
      G.transport laws stable b (F.toTheoryMap.transport a d) := by
  induction d with
  | hyp h => rfl
  | rule r ds ih =>
      rw [RuleReplay.transport_rule, transport_cast]
      simp only [transport, precompReplay, MetavariableCertificate.graft_cast,
        MetavariableCertificate.graft_reindex, transport_cast, id_eq]
      congr 1
      congr 1
      funext i
      congr 1
      exact ih (F.premise r i)

end MetavariableTheoryMap
end SquareKit.DependentPairJudgments
