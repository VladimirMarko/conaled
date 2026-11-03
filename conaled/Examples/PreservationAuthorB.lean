import Applications.Interaction.EvidenceBounds
import Dependent

/-! Author B's unchanged proof bodies from the frozen #235 comparison.
Original attempts and diagnostics are in experiments/preservation-authoring. -/
namespace Examples.PreservationAuthorB

namespace AuthorBShared
open DependentSquares
universe u

def twice {Γ Δ Ξ : Type u} {RΓ : CtxRep Γ} {RΔ : CtxRep Δ}
    {RΞ : CtxRep Ξ} {A : Ty Γ} {RA : TyRep RΓ A} {a : Tm A}
    {σ : Sub Δ Γ} {τ : Sub Ξ Δ} (ac : TermCert RΓ RA a)
    (s : SubCert RΔ RΓ σ) (t : SubCert RΞ RΔ τ) :
    TermCert RΞ (reindexRep RA (s.compose t)) (tmSub (tmSub a σ) τ) :=
  ac.reindex (s.compose t)

def context : CtxRep Nat := ⟨Nat × Bool, Prod.fst⟩
def family : Ty Nat := fun n => Fin (n+1)
def rep : TyRep context family where
  Carrier := fun p => Fin (p.1+1)
  meaning := fun _ i => i

def zeroTerm : Tm family := fun n => ⟨0, Nat.zero_lt_succ n⟩
def zeroCert : TermCert context rep zeroTerm where
  code := fun p => ⟨0, Nat.zero_lt_succ p.1⟩
  commutes := fun _ => rfl

def succCert : SubCert context context Nat.succ where
  code := fun p => (p.1+1, !p.2)
  commutes := fun _ => rfl

def result := twice zeroCert succCert succCert
example (p : Nat × Bool) :
    (reindexRep rep (succCert.compose succCert)).meaning p (result.code p) =
      (⟨0, Nat.zero_lt_succ (p.1+1+1)⟩ : Fin (p.1+1+1+1)) :=
  result.commutes p
example : context.meaning (3, true) = context.meaning (3, false) := rfl
example : (3, true) ≠ (3, false) := by decide
end AuthorBShared

namespace AuthorBDirect
open DependentSquares
universe u

def twice {Γ Δ Ξ : Type u} {RΓ : CtxRep Γ} {RΔ : CtxRep Δ}
    {RΞ : CtxRep Ξ} {A : Ty Γ} {RA : TyRep RΓ A} {a : Tm A}
    {σ : Sub Δ Γ} {τ : Sub Ξ Δ} (ac : TermCert RΓ RA a)
    (s : SubCert RΔ RΓ σ) (t : SubCert RΞ RΔ τ) :
    TermCert RΞ (reindexRep RA (s.compose t)) (tmSub (tmSub a σ) τ) :=
  { code := fun ξ => ac.code (s.code (t.code ξ))
    commutes := by
      intro ξ
      change cast (congrArg A ((s.commutes (t.code ξ)).trans
        (congrArg σ (t.commutes ξ))))
        (RA.meaning (s.code (t.code ξ)) (ac.code (s.code (t.code ξ)))) = _
      rw [ac.commutes]
      exact transport_section ((s.commutes (t.code ξ)).trans
        (congrArg σ (t.commutes ξ))) a }

def context : CtxRep Nat := ⟨Nat × Bool, Prod.fst⟩
def family : Ty Nat := fun n => Fin (n+1)
def rep : TyRep context family where
  Carrier := fun p => Fin (p.1+1)
  meaning := fun _ i => i

def zeroTerm : Tm family := fun n => ⟨0, Nat.zero_lt_succ n⟩
def zeroCert : TermCert context rep zeroTerm where
  code := fun p => ⟨0, Nat.zero_lt_succ p.1⟩
  commutes := fun _ => rfl

def succCert : SubCert context context Nat.succ where
  code := fun p => (p.1+1, !p.2)
  commutes := fun _ => rfl

def result := twice zeroCert succCert succCert
example (p : Nat × Bool) :
    (reindexRep rep (succCert.compose succCert)).meaning p (result.code p) =
      (⟨0, Nat.zero_lt_succ (p.1+1+1)⟩ : Fin (p.1+1+1+1)) :=
  result.commutes p
example : context.meaning (3, true) = context.meaning (3, false) := rfl
example : (3, true) ≠ (3, false) := by decide
end AuthorBDirect

namespace AuthorAShared
open Interaction Interaction.Evidence

theorem optional_bound : ∀ t ∈ some '' encodedReachable,
    (t.map Prod.fst).getD 0 ≤ 1 := by
  have optionalCoverage : Refines (fun (x : Encoded) y => some x = y)
      encodedReachable (some '' encodedReachable) := by
    rintro t ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  have composed := encoding_coverage.trans optionalCoverage
  exact composed.bound State.effects (fun t => (t.map Prod.fst).getD 0) id
    (fun _ _ h => h)
    (by
      rintro s t ⟨x, hx, rfl⟩
      cases hx
      exact Nat.le_refl _)
    1 (fun s hs => (reachable_effects s hs).le)

theorem acknowledged_reachable : recorded ∈ reachable :=
  Relation.ReflTransGen.single recovery_can_finish

theorem acknowledged_case :
    some (1, (true, true)) ∈ some '' encodedReachable ∧
    ((some (1, (true, true))).map Prod.fst).getD 0 ≤ 1 := by
  have h : some (1, (true, true)) ∈ some '' encodedReachable :=
    ⟨encode recorded, ⟨recorded, acknowledged_reachable, rfl⟩, rfl⟩
  exact ⟨h, optional_bound _ h⟩
end AuthorAShared

namespace AuthorADirect
open Interaction Interaction.Evidence

theorem optional_bound : ∀ t ∈ some '' encodedReachable,
    (t.map Prod.fst).getD 0 ≤ 1 := by
  rintro t ⟨x, ⟨s, hs, rfl⟩, rfl⟩
  exact (reachable_effects s hs).le

theorem acknowledged_reachable : recorded ∈ reachable :=
  Relation.ReflTransGen.single recovery_can_finish

theorem acknowledged_case :
    some (1, (true, true)) ∈ some '' encodedReachable ∧
    ((some (1, (true, true))).map Prod.fst).getD 0 ≤ 1 := by
  have h : some (1, (true, true)) ∈ some '' encodedReachable :=
    ⟨encode recorded, ⟨recorded, acknowledged_reachable, rfl⟩, rfl⟩
  exact ⟨h, optional_bound _ h⟩
end AuthorADirect


end Examples.PreservationAuthorB
