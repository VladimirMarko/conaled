import SquareKit.DependentMetavariableCertificates
import SquareKit.DependentCertificateEnvironments

namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps TypedSubstitution

namespace MetavariableCertificate
variable {S : Signature} {R : Rules.{1,1} (Judgment S)} {I : Type}
  {premise : I → Judgment S}

/-- Ordinary local proof trees embed without introducing metavariable
applications. The occurrence index of a repeated premise is retained. -/
def ofPlainDerivation : {j : Judgment S} →
    Derivation R (fun j => {i : I // premise i = j}) j → MetavariableCertificate R premise j
  | _, .hyp ⟨i, h⟩ => h ▸ .hyp i
  | _, .rule r children => .rule r (fun i => ofPlainDerivation (children i))

theorem graft_ofPlainDerivation {H : Judgment S → Type}
    (laws : Local (R := R) (H := H))
    (stable : ∀ j, H j → Reindexed (R := R) (H := H) j)
    (proofs : ∀ i, Derivation R H (premise i))
    (d : Derivation R (fun j => {i : I // premise i = j}) j) :
    (ofPlainDerivation d).graft laws stable proofs =
      d.graft (fun _ p => p.property ▸ proofs p.val) := by
  induction d with
  | hyp p => rcases p with ⟨i, h⟩; cases h; rfl
  | rule r children ih =>
      simp only [ofPlainDerivation, graft, Derivation.graft]
      congr 1
      funext i
      exact ih i
/-- A same-judgment rule interpretation replays a certificate while retaining
its typed metavariable applications and selected argument certificates. -/
def mapRules {Q : Rules.{1,1} (Judgment S)} (F : TheoryMap R Q id) :
    {j : Judgment S} → MetavariableCertificate R premise j → MetavariableCertificate Q premise j
  | _, .hyp i => .hyp i
  | _, .rule r children => CertificateEnvironment.replay
      (fun _ h => h.property ▸ mapRules F (children h.val)) (F.certificate r)
  | _, .apply i Δ σ ctx args => .apply i Δ σ (mapRules F ctx) (fun v => mapRules F (args v))

end MetavariableCertificate

namespace MetavariableTheoryMap
variable {S T U : Signature} {R : Rules.{1,1} (Judgment S)}
  {Q : Rules.{1,1} (Judgment T)} {P : Rules.{1,1} (Judgment U)}
  {f : Judgment S → Judgment T} {g : Judgment T → Judgment U}

def ofTheoryMap (F : TheoryMap R Q f) : MetavariableTheoryMap R Q f where
  certificate r := MetavariableCertificate.ofPlainDerivation (F.certificate r)

/-- The embedding retains the actual output proof tree, not only its endpoint.
The substitution package is unused because these certificates have no apply nodes. -/
theorem transport_ofTheoryMap (F : TheoryMap R Q f)
    {H : Judgment S → Type} {K : Judgment T → Type}
    (laws : Local (R := Q) (H := K))
    (stable : ∀ j, K j → Reindexed (R := Q) (H := K) j)
    (hypotheses : ∀ j, H j → K (f j))
    (d : Derivation R H j) :
    (ofTheoryMap F).transport laws stable hypotheses d = F.transport hypotheses d := by
  induction d with
  | hyp => rfl
  | rule r children ih =>
      simp only [transport, ofTheoryMap, MetavariableCertificate.graft_ofPlainDerivation,
        TheoryMap.transport]
      congr 1
      funext j p
      rcases p with ⟨i, h⟩
      cases h
      exact ih i

/-- For embedded ordinary maps, the stronger compressed local-certificate
composition theorem remains valid in the richer interface. This does not assert
that arbitrary typed-application certificates can be compressed coherently. -/
theorem ordinary_comp_transport (F : TheoryMap R Q f) (G : TheoryMap Q P g)
    {A : Judgment S → Type} {B : Judgment T → Type} {C : Judgment U → Type}
    (q : Local (R := Q) (H := B)) (p : Local (R := P) (H := C))
    (qb : ∀ j, B j → Reindexed (R := Q) (H := B) j)
    (pc : ∀ j, C j → Reindexed (R := P) (H := C) j)
    (a : ∀ j, A j → B (f j)) (b : ∀ j, B j → C (g j))
    (d : Derivation R A j) :
    (ofTheoryMap (F.comp G)).transport p pc (fun j h => b (f j) (a j h)) d =
      (ofTheoryMap G).transport p pc b ((ofTheoryMap F).transport q qb a d) := by
  rw [transport_ofTheoryMap, transport_ofTheoryMap, transport_ofTheoryMap]
  exact TheoryMap.comp_transport F G a b d

end MetavariableTheoryMap
end SquareKit.DependentPairJudgments
