import SquareKit.Internal.PathTransport.Syntax

/-! Raw contexts and substitutions, with newest declarations first. -/

namespace SquareKit.Internal.PathTransport

abbrev RawCtx := List Expr
abbrev RawSub := Nat → Expr

def consSub (t : Expr) (σ : RawSub) : RawSub
  | 0 => t
  | n + 1 => σ n

def pathCtx (Γ : RawCtx) (A x : Expr) : RawCtx :=
  .identity (A.rename Nat.succ) (x.rename Nat.succ) (.var 0) :: A :: Γ

def reflexiveSub (x : Expr) : RawSub := consSub (.refl x) (consSub x Expr.var)

/-- Reindex each declaration under precisely its older tail declarations. -/
def subTail (σ : RawSub) : RawCtx → RawCtx
  | [] => []
  | A :: Δ => A.sub (Expr.liftSubN Δ.length σ) :: subTail σ Δ

/-- Arguments are ordered newest first, as are de Bruijn indices. -/
def argsSub {k : Nat} (args : Fin k → Expr) (σ : RawSub) : RawSub :=
  fun n => if h : n < k then args ⟨n, h⟩ else σ (n - k)

def eliminationSub {k : Nat} (y p : Expr) (args : Fin k → Expr) : RawSub :=
  argsSub args (consSub p (consSub y Expr.var))

@[simp] theorem argsSub_zero (args : Fin 0 → Expr) (σ : RawSub) :
    argsSub args σ = σ := by
  funext n
  simp [argsSub]

@[simp] theorem argsSub_head {k} (args : Fin (k + 1) → Expr) (σ : RawSub) :
    argsSub args σ 0 = args 0 := by simp [argsSub]

@[simp] theorem argsSub_succ {k} (args : Fin (k + 1) → Expr) (σ : RawSub) (n) :
    argsSub args σ (n + 1) = argsSub (fun i => args i.succ) σ n := by
  simp only [argsSub]
  split <;> split
  · rfl
  · omega
  · omega
  · congr 1; omega

theorem argsSub_cons {k} (args : Fin (k + 1) → Expr) (σ : RawSub) :
    argsSub args σ = consSub (args 0) (argsSub (fun i => args i.succ) σ) := by
  funext n; cases n <;> simp [consSub]

/-- Instantiating a lifted substitution preserves the generalized arguments. -/
theorem liftSubN_argsSub (k : Nat) (σ τ : RawSub) (args : Fin k → Expr) :
    (fun n => (Expr.liftSubN k σ n).sub (argsSub args τ)) =
      argsSub args (fun n => (σ n).sub τ) := by
  induction k with
  | zero => simp [Expr.liftSubN]
  | succ k ih =>
    funext n
    cases n with
    | zero => simp [Expr.liftSubN, Expr.liftSub, Expr.sub]
    | succ n =>
      simp only [Expr.liftSubN, Expr.liftSub, Expr.sub_rename, argsSub_succ]
      have h : argsSub args τ ∘ Nat.succ = argsSub (fun i => args i.succ) τ := by
        funext m; exact argsSub_succ args τ m
      rw [h]
      exact congrFun (ih (fun i => args i.succ)) n

theorem sub_liftSubN_argsSub (t : Expr) (k : Nat) (σ τ : RawSub) (args : Fin k → Expr) :
    (t.sub (Expr.liftSubN k σ)).sub (argsSub args τ) =
      t.sub (argsSub args (fun n => (σ n).sub τ)) := by
  rw [Expr.sub_comp, liftSubN_argsSub]

end SquareKit.Internal.PathTransport
