import Mathlib.Data.Fin.Basic

/-!
# Raw syntax for the contextual identity fragment

One primitive base and one set-valued primitive family are externally
interpreted. Expressions contain no host-language functions as source terms.
The finite argument vector of `pathInduction` is syntactic substitution data.

`pathInduction k A x C d y p args` binds two variables (the moving endpoint
and its path from `x`), followed by `k` generalized parameters in `C`.
The reflexive branch `d` binds just those `k` parameters. Typing must check
their dependent telescope, including its specialization in the branch.
This module supplies raw syntax and substitution, not typing or soundness.
-/
namespace SquareKit.Internal.PathTransport

/-- Raw syntax. Types and terms are separated by typing judgments, not by
this datatype. There is no universe, Π, equality reflection, or host escape. -/
inductive Expr where
  | var : Nat → Expr
  | base : Expr
  | fiber : Expr → Expr
  | identity : Expr → Expr → Expr → Expr
  | refl : Expr → Expr
  | pathInduction (arity : Nat) (type point motive branch endpoint path : Expr)
      (args : Fin arity → Expr) : Expr

namespace Expr

/-- Renaming under one binder, with the newest variable at index zero. -/
def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

/-- Renaming under a finite telescope. -/
def liftRenN : Nat → (Nat → Nat) → Nat → Nat
  | 0, ρ => ρ
  | k + 1, ρ => liftRen (liftRenN k ρ)

/-- Simultaneous renaming, including the generalized tail of path induction. -/
def rename (ρ : Nat → Nat) : Expr → Expr
  | .var n => .var (ρ n)
  | .base => .base
  | .fiber x => .fiber (rename ρ x)
  | .identity A x y => .identity (rename ρ A) (rename ρ x) (rename ρ y)
  | .refl x => .refl (rename ρ x)
  | .pathInduction k A x C d y p args =>
      .pathInduction k (rename ρ A) (rename ρ x)
        (rename (liftRenN (k + 2) ρ) C) (rename (liftRenN k ρ) d)
        (rename ρ y) (rename ρ p) (fun i => rename ρ (args i))

/-- Simultaneous substitution under one binder. -/
def liftSub (σ : Nat → Expr) : Nat → Expr
  | 0 => .var 0
  | n + 1 => rename Nat.succ (σ n)

/-- Simultaneous substitution under a finite telescope. -/
def liftSubN : Nat → (Nat → Expr) → Nat → Expr
  | 0, σ => σ
  | k + 1, σ => liftSub (liftSubN k σ)

/-- Capture-avoiding simultaneous substitution. -/
def sub (σ : Nat → Expr) : Expr → Expr
  | .var n => σ n
  | .base => .base
  | .fiber x => .fiber (sub σ x)
  | .identity A x y => .identity (sub σ A) (sub σ x) (sub σ y)
  | .refl x => .refl (sub σ x)
  | .pathInduction k A x C d y p args =>
      .pathInduction k (sub σ A) (sub σ x)
        (sub (liftSubN (k + 2) σ) C) (sub (liftSubN k σ) d)
        (sub σ y) (sub σ p) (fun i => sub σ (args i))

@[simp] theorem liftRen_id : liftRen id = id := by funext n; cases n <;> rfl
@[simp] theorem liftRenN_id (k) : liftRenN k id = id := by
  induction k <;> simp_all [liftRenN]

theorem liftRen_comp (ρ τ : Nat → Nat) :
    liftRen (τ ∘ ρ) = liftRen τ ∘ liftRen ρ := by
  funext n; cases n <;> rfl

theorem liftRenN_comp (k) (ρ τ : Nat → Nat) :
    liftRenN k (τ ∘ ρ) = liftRenN k τ ∘ liftRenN k ρ := by
  induction k <;> simp_all [liftRenN, liftRen_comp]

@[simp] theorem rename_id (t : Expr) : rename id t = t := by
  induction t <;> simp_all [rename]

theorem rename_comp (t : Expr) (ρ τ : Nat → Nat) :
    rename τ (rename ρ t) = rename (τ ∘ ρ) t := by
  induction t generalizing ρ τ <;> simp_all [rename, liftRenN_comp]

@[simp] theorem liftSub_var : liftSub var = var := by
  funext n; cases n <;> rfl
@[simp] theorem liftSubN_var (k) : liftSubN k var = var := by
  induction k <;> simp_all [liftSubN]

@[simp] theorem sub_id (t : Expr) : sub var t = t := by
  induction t <;> simp_all [sub]

theorem liftSub_rename (σ : Nat → Expr) (ρ : Nat → Nat) :
    liftSub (fun n => rename ρ (σ n)) =
      fun n => rename (liftRen ρ) (liftSub σ n) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp only [liftSub, rename_comp]; rfl

theorem liftSubN_rename (k) (σ : Nat → Expr) (ρ : Nat → Nat) :
    liftSubN k (fun n => rename ρ (σ n)) =
      fun n => rename (liftRenN k ρ) (liftSubN k σ n) := by
  induction k <;> simp_all [liftSubN, liftRenN, liftSub_rename]

theorem rename_sub (t : Expr) (σ : Nat → Expr) (ρ : Nat → Nat) :
    rename ρ (sub σ t) = sub (fun n => rename ρ (σ n)) t := by
  induction t generalizing σ ρ <;> simp_all [sub, rename, liftSubN_rename]

theorem liftSub_precomp (σ : Nat → Expr) (ρ : Nat → Nat) :
    liftSub (σ ∘ ρ) = liftSub σ ∘ liftRen ρ := by
  funext n; cases n <;> rfl

theorem liftSubN_precomp (k) (σ : Nat → Expr) (ρ : Nat → Nat) :
    liftSubN k (σ ∘ ρ) = liftSubN k σ ∘ liftRenN k ρ := by
  induction k <;> simp_all [liftSubN, liftRenN, liftSub_precomp]

theorem sub_rename (t : Expr) (ρ : Nat → Nat) (σ : Nat → Expr) :
    sub σ (rename ρ t) = sub (σ ∘ ρ) t := by
  induction t generalizing σ ρ <;> simp_all [sub, rename, liftSubN_precomp]

theorem liftSub_comp (σ τ : Nat → Expr) :
    liftSub (fun n => sub τ (σ n)) =
      fun n => sub (liftSub τ) (liftSub σ n) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp only [liftSub, rename_sub, sub_rename]; rfl

theorem liftSubN_comp (k) (σ τ : Nat → Expr) :
    liftSubN k (fun n => sub τ (σ n)) =
      fun n => sub (liftSubN k τ) (liftSubN k σ n) := by
  induction k <;> simp_all [liftSubN, liftSub_comp]

/-- Simultaneous substitutions compose on every expression, including J
motives and the reflexive branches under generalized dependent parameters. -/
theorem sub_comp (t : Expr) (σ τ : Nat → Expr) :
    sub τ (sub σ t) = sub (fun n => sub τ (σ n)) t := by
  induction t generalizing σ τ <;> simp_all [sub, liftSubN_comp]

/-- Renaming is the special case of substitution that assigns variables. -/
theorem sub_var_rename (t : Expr) (ρ : Nat → Nat) :
    sub (var ∘ ρ) t = rename ρ t := by
  have h : ∀ k, liftSubN k (var ∘ ρ) = var ∘ liftRenN k ρ := by
    intro k
    rw [liftSubN_precomp, liftSubN_var]
  induction t generalizing ρ <;> simp_all [sub, rename, liftSubN_precomp]

end Expr
end SquareKit.Internal.PathTransport
