import Dependent
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
