import Mathlib.Data.List.Perm.Basic

/-! Finite additive/unit CP, with distinct named linear contexts. -/
namespace Session

inductive Formula where
  | one | bottom
  | plus (a b : Formula)
  | with (a b : Formula)
  deriving DecidableEq, Repr

def Formula.dual : Formula → Formula
  | .one => .bottom
  | .bottom => .one
  | .plus a b => .with a.dual b.dual
  | .with a b => .plus a.dual b.dual

@[simp] theorem Formula.dual_dual (a : Formula) : a.dual.dual = a := by
  induction a <;> simp_all [dual]

abbrev Context := List (Nat × Formula)
def Valid (Γ : Context) : Prop := (Γ.map Prod.fst).Nodup
instance (Γ : Context) : Decidable (Valid Γ) := inferInstanceAs (Decidable ((Γ.map Prod.fst).Nodup))

inductive Process where
  | close (x : Nat)
  | wait (x : Nat) (p : Process)
  | select (x : Nat) (right : Bool) (p : Process)
  | offer (x : Nat) (p q : Process)
  | cut (x : Nat) (p q : Process)
  deriving DecidableEq, Repr

/-- No weakening or contraction. Exchange is explicit in this list presentation. -/
inductive Typed : Process → Context → Prop where
  | close : Typed (.close x) [(x, .one)]
  | wait : Valid ((x, .bottom) :: Γ) → Typed p Γ → Typed (.wait x p) ((x, .bottom) :: Γ)
  | left : Typed p ((x,a) :: Γ) → Typed (.select x false p) ((x,.plus a b) :: Γ)
  | right : Typed p ((x,b) :: Γ) → Typed (.select x true p) ((x,.plus a b) :: Γ)
  | offer : Typed p ((x,a) :: Γ) → Typed q ((x,b) :: Γ) →
      Typed (.offer x p q) ((x,.with a b) :: Γ)
  | cut : Valid (Γ ++ Δ) → Typed p ((x,a) :: Γ) → Typed q ((x,a.dual) :: Δ) →
      Typed (.cut x p q) (Γ ++ Δ)
  | exchange : Γ.Perm Δ → Typed p Γ → Typed p Δ

/-- Linear proof data, separately erased into process syntax. -/
inductive Proof : Context → Type where
  | close (x) : Proof [(x, .one)]
  | wait (x) (valid : Valid ((x,.bottom) :: Γ)) : Proof Γ → Proof ((x,.bottom) :: Γ)
  | left : Proof ((x,a) :: Γ) → Proof ((x,.plus a b) :: Γ)
  | right : Proof ((x,b) :: Γ) → Proof ((x,.plus a b) :: Γ)
  | offer : Proof ((x,a) :: Γ) → Proof ((x,b) :: Γ) → Proof ((x,.with a b) :: Γ)
  | cut (x) (a) (valid : Valid (Γ ++ Δ)) :
      Proof ((x,a) :: Γ) → Proof ((x,a.dual) :: Δ) → Proof (Γ ++ Δ)
  | exchange (perm : Γ.Perm Δ) : Proof Γ → Proof Δ

def Proof.erase : Proof Γ → Process
  | .close x => .close x
  | .wait x _ p => .wait x p.erase
  | @Proof.left x _ _ _ p => .select x false p.erase
  | @Proof.right x _ _ _ p => .select x true p.erase
  | @Proof.offer x _ _ _ p q => .offer x p.erase q.erase
  | .cut x _ _ p q => .cut x p.erase q.erase
  | .exchange _ p => p.erase

theorem Proof.typed (p : Proof Γ) : Typed p.erase Γ := by
  induction p with
  | close => exact .close
  | wait _ h _ ih => exact .wait h ih
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | offer _ _ ih jh => exact .offer ih jh
  | cut _ _ h _ _ ih jh => exact .cut h ih jh
  | exchange h _ ih => exact .exchange h ih

theorem Typed.valid (h : Typed p Γ) : Valid Γ := by
  induction h with
  | close => simp [Valid]
  | wait h => exact h
  | left _ ih => exact ih
  | right _ ih => exact ih
  | offer _ _ ih _ => exact ih
  | cut h => exact h
  | exchange perm _ ih => exact (perm.map Prod.fst).nodup_iff.mp ih

inductive Event where
  | label (channel : Nat) (right : Bool)
  | closed (channel : Nat)
  deriving DecidableEq, Repr

/-- Synchronous principal-cut communication, not function evaluation. -/
inductive Step : Process → Event → Process → Prop where
  | left : Step (.cut x (.select x false p) (.offer x q r)) (.label x false) (.cut x p q)
  | right : Step (.cut x (.select x true p) (.offer x q r)) (.label x true) (.cut x p r)
  | close : Step (.cut x (.close x) (.wait x p)) (.closed x) p

inductive Steps : Process → List Event → Process → Prop where
  | nil : Steps p [] p
  | cons : Step p e q → Steps q es r → Steps p (e :: es) r

theorem Steps.append (h : Steps p es q) (k : Steps q fs r) : Steps p (es ++ fs) r := by
  induction h with
  | nil => exact k
  | cons h _ ih => exact .cons h (ih k)

/-- Principal proof-cut reductions preserve their full residual context. -/
inductive CutStep : {Γ : Context} → Proof Γ → Event → Proof Γ → Prop where
  | left (v : Valid (Γ ++ Δ)) (p : Proof ((x,a) :: Γ))
      (q : Proof ((x,a.dual) :: Δ)) (r : Proof ((x,b.dual) :: Δ)) :
      CutStep (.cut x (.plus a b) v (.left p) (.offer q r)) (.label x false) (.cut x a v p q)
  | right (v : Valid (Γ ++ Δ)) (p : Proof ((x,b) :: Γ))
      (q : Proof ((x,a.dual) :: Δ)) (r : Proof ((x,b.dual) :: Δ)) :
      CutStep (.cut x (.plus a b) v (.right p) (.offer q r)) (.label x true) (.cut x b v p r)
  | close (v : Valid Γ) (fresh : Valid ((x,.bottom) :: Γ)) (p : Proof Γ) :
      CutStep (.cut x .one (Γ := []) v (.close x) (.wait x fresh p)) (.closed x) p

theorem CutStep.simulates {p q : Proof Γ} (h : CutStep p e q) : Step p.erase e q.erase := by
  cases h with
  | left => exact .left
  | right => exact .right
  | close => exact .close

end Session
