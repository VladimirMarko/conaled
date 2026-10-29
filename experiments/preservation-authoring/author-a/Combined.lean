import Applications.Interaction.EvidenceBounds
import Dependent
namespace AuthorA
open Interaction Interaction.Evidence

theorem direct : ∀ t ∈ some '' encodedReachable,
    (t.map Prod.fst).getD 0 ≤ 1 := by
  rintro t ⟨e, ⟨s, hs, rfl⟩, rfl⟩
  exact (reachable_effects s hs).le

theorem acknowledged : some (encode recorded) ∈ some '' encodedReachable := by
  refine ⟨encode recorded, ⟨recorded, ?_, rfl⟩, rfl⟩
  exact Relation.ReflTransGen.single recovery_can_finish

example : ((some (encode recorded)).map Prod.fst).getD 0 ≤ 1 :=
  direct _ acknowledged
example : (encode recorded).2 = (true, true) := rfl
end AuthorA
namespace AuthorAShared
open Interaction Interaction.Evidence

theorem shared : ∀ t ∈ some '' encodedReachable,
    (t.map Prod.fst).getD 0 ≤ 1 := by
  have optional : Refines (fun (e : Encoded) (t : Option Encoded) => some e = t)
      encodedReachable (some '' encodedReachable) := by
    rintro t ⟨e, he, rfl⟩
    exact ⟨e, he, rfl⟩
  have covered := encoding_coverage.trans optional
  exact covered.bound State.effects (fun t => (t.map Prod.fst).getD 0) id
    (fun _ _ h => h)
    (by
      rintro s t ⟨e, he, ht⟩
      cases ht
      cases he
      exact le_rfl)
    1 (fun s hs => (reachable_effects s hs).le)

theorem acknowledged : some (encode recorded) ∈ some '' encodedReachable := by
  refine ⟨encode recorded, ⟨recorded, ?_, rfl⟩, rfl⟩
  exact Relation.ReflTransGen.single recovery_can_finish
example : ((some (encode recorded)).map Prod.fst).getD 0 ≤ 1 := shared _ acknowledged
example : (encode recorded).2 = (true, true) := rfl
end AuthorAShared
namespace AuthorBDirect
open DependentSquares
universe u

def twice {Γ Δ Ξ : Type u} {RΓ : CtxRep Γ} {RΔ : CtxRep Δ} {RΞ : CtxRep Ξ}
    {A : Ty Γ} {RA : TyRep RΓ A} {a : Tm A} {σ : Sub Δ Γ} {τ : Sub Ξ Δ}
    (ac : TermCert RΓ RA a) (s : SubCert RΔ RΓ σ) (t : SubCert RΞ RΔ τ) :
    TermCert RΞ (reindexRep RA (s.compose t)) (tmSub (tmSub a σ) τ) where
  code := fun ξ => ac.code (s.code (t.code ξ))
  commutes := by
    intro ξ
    let h := (s.commutes (t.code ξ)).trans (congrArg σ (t.commutes ξ))
    change cast (congrArg A h) (RA.meaning (s.code (t.code ξ))
      (ac.code (s.code (t.code ξ)))) = a (σ (τ (RΞ.meaning ξ)))
    rw [ac.commutes]
    exact transport_section h a

def R : CtxRep Nat := ⟨Nat × Bool, Prod.fst⟩
def F : Ty Nat := fun n => Fin (n+1)
def RF : TyRep R F where
  Carrier := fun ρ => Fin (ρ.1+1)
  meaning := fun _ i => i

def zero : Tm F := fun n => ⟨0, Nat.zero_lt_succ n⟩
def zeroCert : TermCert R RF zero where
  code := fun ρ => ⟨0, Nat.zero_lt_succ ρ.1⟩
  commutes := fun _ => rfl

def plusOne : SubCert R R (fun n => n+1) where
  code := fun ρ => (ρ.1+1, !ρ.2)
  commutes := fun _ => rfl

def double : SubCert R R (fun n => n*2) where
  code := fun ρ => (ρ.1*2, ρ.2)
  commutes := fun _ => rfl

def result := twice zeroCert plusOne double
example (ρ : R.Carrier) : Fin (ρ.1*2+1+1) := result.code ρ
example (ρ : R.Carrier) :
    (reindexRep RF (plusOne.compose double)).meaning ρ (result.code ρ) =
      (⟨0, Nat.zero_lt_succ (ρ.1*2+1)⟩ : Fin (ρ.1*2+1+1)) := result.commutes ρ
example : R.meaning (3, true) = R.meaning (3, false) := rfl
example : (3, true) ≠ (3, false) := by decide
#print axioms twice
#print axioms result
end AuthorBDirect
namespace AuthorBShared
open DependentSquares
universe u

def twice {Γ Δ Ξ : Type u} {RΓ : CtxRep Γ} {RΔ : CtxRep Δ} {RΞ : CtxRep Ξ}
    {A : Ty Γ} {RA : TyRep RΓ A} {a : Tm A} {σ : Sub Δ Γ} {τ : Sub Ξ Δ}
    (ac : TermCert RΓ RA a) (s : SubCert RΔ RΓ σ) (t : SubCert RΞ RΔ τ) :
    TermCert RΞ (reindexRep RA (s.compose t)) (tmSub (tmSub a σ) τ) :=
  ac.reindex (s.compose t)

def R : CtxRep Nat := ⟨Nat × Bool, Prod.fst⟩
def F : Ty Nat := fun n => Fin (n+1)
def RF : TyRep R F where
  Carrier := fun ρ => Fin (ρ.1+1)
  meaning := fun _ i => i

def zero : Tm F := fun n => ⟨0, Nat.zero_lt_succ n⟩
def zeroCert : TermCert R RF zero where
  code := fun ρ => ⟨0, Nat.zero_lt_succ ρ.1⟩
  commutes := fun _ => rfl

def plusOne : SubCert R R (fun n => n+1) where
  code := fun ρ => (ρ.1+1, !ρ.2)
  commutes := fun _ => rfl

def double : SubCert R R (fun n => n*2) where
  code := fun ρ => (ρ.1*2, ρ.2)
  commutes := fun _ => rfl

def result := twice zeroCert plusOne double
example (ρ : R.Carrier) : Fin (ρ.1*2+1+1) := result.code ρ
example (ρ : R.Carrier) :
    (reindexRep RF (plusOne.compose double)).meaning ρ (result.code ρ) =
      (⟨0, Nat.zero_lt_succ (ρ.1*2+1)⟩ : Fin (ρ.1*2+1+1)) := result.commutes ρ
example : R.meaning (3, true) = R.meaning (3, false) := rfl
example : (3, true) ≠ (3, false) := by decide
#print axioms twice
#print axioms result
end AuthorBShared

#print axioms AuthorA.direct
#print axioms AuthorA.acknowledged
#print axioms AuthorAShared.shared
#print axioms AuthorAShared.acknowledged
