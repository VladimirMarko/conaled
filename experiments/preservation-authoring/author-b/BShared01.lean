import Dependent
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
#print axioms twice
#print axioms result
end AuthorBShared
