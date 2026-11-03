import Lean

/-! The binder fragment used by the graph producer. Names and universe arguments
are data. Conversion preserves every node, including binder indices. -/
namespace SquareKit.Internal.CoreSyntax
open Lean

inductive Expr where
  | bvar : Nat → Expr
  | sort : Level → Expr
  | const : Name → List Level → Expr
  | app : Expr → Expr → Expr
  | lam : Expr → Expr → Expr
  | all : Expr → Expr → Expr

def Expr.toLean : Expr → Lean.Expr
  | .bvar n => .bvar n
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app f.toLean a.toLean
  | .lam a b => .lam `x a.toLean b.toLean .default
  | .all a b => .forallE `x a.toLean b.toLean .default

def Expr.ofLean : Lean.Expr → Option Expr
  | .bvar n => some (.bvar n)
  | .sort u => some (.sort u)
  | .const n us => some (.const n us)
  | .app f a => return .app (← ofLean f) (← ofLean a)
  | .lam _ a b .default => return .lam (← ofLean a) (← ofLean b)
  | .forallE _ a b .default => return .all (← ofLean a) (← ofLean b)
  | _ => none

@[simp] theorem Expr.ofLean_toLean (e : Expr) : ofLean e.toLean = some e := by
  induction e <;> simp_all [toLean, ofLean]

theorem Expr.toLean_injective : Function.Injective Expr.toLean := by
  intro a b h
  have := congrArg Expr.ofLean h
  simpa using this

/-- Renaming under a binder preserves its new variable. -/
def liftRen (r : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => r n + 1

def Expr.rename (r : Nat → Nat) : Expr → Expr
  | .bvar n => .bvar (r n)
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (f.rename r) (a.rename r)
  | .lam a b => .lam (a.rename r) (b.rename (liftRen r))
  | .all a b => .all (a.rename r) (b.rename (liftRen r))

def Expr.shift (e : Expr) := e.rename Nat.succ

theorem liftRen_comp (r s : Nat → Nat) :
    liftRen (r ∘ s) = liftRen r ∘ liftRen s := by
  funext n; cases n <;> rfl

@[simp] theorem Expr.rename_id (e : Expr) : e.rename id = e := by
  have h : liftRen id = id := by funext n; cases n <;> rfl
  induction e <;> simp_all [rename]

theorem Expr.rename_comp (e : Expr) (r s : Nat → Nat) :
    (e.rename s).rename r = e.rename (r ∘ s) := by
  induction e generalizing r s <;> simp_all [rename, liftRen_comp]

def liftSub (σ : Nat → Expr) : Nat → Expr
  | 0 => .bvar 0
  | n + 1 => (σ n).shift

def Expr.subst (σ : Nat → Expr) : Expr → Expr
  | .bvar n => σ n
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (f.subst σ) (a.subst σ)
  | .lam a b => .lam (a.subst σ) (b.subst (liftSub σ))
  | .all a b => .all (a.subst σ) (b.subst (liftSub σ))

theorem Expr.subst_rename (e : Expr) (σ : Nat → Expr) (r : Nat → Nat) :
    (e.rename r).subst σ = e.subst (σ ∘ r) := by
  induction e generalizing σ r with
  | bvar => rfl
  | sort => rfl
  | const => rfl
  | app f a hf ha => simp only [rename, subst, hf, ha]
  | lam a b ha hb | all a b ha hb =>
    have h : liftSub σ ∘ liftRen r = liftSub (σ ∘ r) := by
      funext n; cases n <;> rfl
    simp only [rename, subst, ha, hb, h]

theorem Expr.rename_subst (e : Expr) (r : Nat → Nat) (σ : Nat → Expr) :
    (e.subst σ).rename r = e.subst (fun n => (σ n).rename r) := by
  induction e generalizing σ r with
  | bvar => rfl
  | sort => rfl
  | const => rfl
  | app f a hf ha => simp only [rename, subst, hf, ha]
  | lam a b ha hb | all a b ha hb =>
    have h : (fun n => (liftSub σ n).rename (liftRen r)) =
        liftSub (fun n => (σ n).rename r) := by
      funext n
      cases n with
      | zero => rfl
      | succ n =>
        simp only [liftSub, shift, rename_comp]
        rfl
    simp only [subst, rename, ha, hb, h]

theorem Expr.subst_shift (e : Expr) (σ : Nat → Expr) :
    e.shift.subst (liftSub σ) = (e.subst σ).shift := by
  rw [shift, subst_rename, shift, rename_subst]
  rfl

theorem Expr.subst_comp (e : Expr) (σ τ : Nat → Expr) :
    (e.subst σ).subst τ = e.subst (fun n => (σ n).subst τ) := by
  induction e generalizing σ τ with
  | bvar => rfl
  | sort => rfl
  | const => rfl
  | app f a hf ha => simp only [subst, hf, ha]
  | lam a b ha hb | all a b ha hb =>
    have h : (fun n => (liftSub σ n).subst (liftSub τ)) =
        liftSub (fun n => (σ n).subst τ) := by
      funext n; cases n <;> simp only [liftSub, subst, subst_shift]
    simp only [subst, ha, hb, h]

@[simp] theorem Expr.subst_id (e : Expr) : e.subst .bvar = e := by
  have h : liftSub Expr.bvar = Expr.bvar := by funext n; cases n <;> rfl
  induction e <;> simp_all [subst]

def Expr.app2 (f a b : Expr) : Expr := .app (.app f a) b
def Expr.app3 (f a b c : Expr) : Expr := .app (.app2 f a b) c
def Expr.apps (f : Expr) (args : List Expr) := args.foldl Expr.app f

/-- An interpreted syntax relation transfers through a partial decoder.
The relation can be typing, denotation, or a validator contract. -/
def InLean (R : Expr → Prop) (e : Lean.Expr) : Prop :=
  ∃ a, Expr.ofLean e = some a ∧ R a

theorem inLean_toLean (R : Expr → Prop) (a : Expr) : InLean R a.toLean ↔ R a := by
  simp [InLean]

end SquareKit.Internal.CoreSyntax
