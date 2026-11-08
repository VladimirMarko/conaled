import SquareKit.WeakHigherOrder

/-! Syntactic substitution equations for the existing typed fragment. -/
namespace SquareKit.WeakMachine
open HigherOrderComparison (Ty Ctx Var Env extend empty)
open WeakHigherOrder

abbrev closedSub (x : Term [] a) : Sub [a] [] := fun v => match v with
  | .here => x

def beta (t : Term [a] b) (x : Term [] a) : Term [] b := subst (closedSub x) t

theorem rename_id (t : Term Γ a) : rename (fun v => v) t = t := by
  induction t with
  | var v => rfl
  | lit n => rfl
  | omega => rfl
  | app f x ihf ihx => simp only [rename, ihf, ihx]
  | lam t ih =>
    have h : liftRen (fun v : Var Γ _ => v) = (fun v => v : Ren (_ :: Γ) (_ :: Γ)) := by
      funext a v; cases v <;> rfl
    simp only [rename, h, ih]

theorem rename_comp (t : Term Γ a) (r : Ren Γ Δ) (s : Ren Δ Θ) :
    rename s (rename r t) = rename (fun v => s (r v)) t := by
  induction t generalizing Δ Θ with
  | var v => rfl
  | lit n => rfl
  | omega => rfl
  | app f x ihf ihx => simp only [rename, ihf, ihx]
  | lam t ih =>
    simp only [rename, ih]
    congr 2
    funext a v; cases v <;> rfl

theorem subst_rename (t : Term Γ a) (r : Ren Γ Δ) (s : Sub Δ Θ) :
    subst s (rename r t) = subst (fun v => s (r v)) t := by
  induction t generalizing Δ Θ with
  | var v => rfl
  | lit n => rfl
  | omega => rfl
  | app f x ihf ihx => simp only [rename, subst, ihf, ihx]
  | lam t ih =>
    simp only [rename, subst, ih]
    congr 2
    funext a v; cases v <;> rfl

theorem rename_subst (t : Term Γ a) (s : Sub Γ Δ) (r : Ren Δ Θ) :
    rename r (subst s t) = subst (fun v => rename r (s v)) t := by
  induction t generalizing Δ Θ with
  | var v => rfl
  | lit n => rfl
  | omega => rfl
  | app f x ihf ihx => simp only [rename, subst, ihf, ihx]
  | lam t ih =>
    simp only [rename, subst, ih]
    congr 2
    funext a v
    cases v with
    | here => rfl
    | there v => simp only [liftSub, rename_comp]; rfl

theorem subst_comp (t : Term Γ a) (s : Sub Γ Δ) (r : Sub Δ Θ) :
    subst r (subst s t) = subst (fun v => subst r (s v)) t := by
  induction t generalizing Δ Θ with
  | var v => rfl
  | lit n => rfl
  | omega => rfl
  | app f x ihf ihx => simp only [subst, ihf, ihx]
  | lam t ih =>
    simp only [subst, ih]
    congr 2
    funext a v
    cases v with
    | here => rfl
    | there v => simp only [liftSub, subst_rename, rename_subst]; rfl

theorem subst_id (t : Term Γ a) : subst (fun v => .var v) t = t := by
  induction t with
  | var v => rfl
  | lit n => rfl
  | omega => rfl
  | app f x ihf ihx => simp only [subst, ihf, ihx]
  | lam t ih =>
    have h : liftSub (fun v : Var Γ _ => Term.var v) =
        (fun v => .var v : Sub (_ :: Γ) (_ :: Γ)) := by
      funext a v; cases v <;> rfl
    simp only [subst, h, ih]

def extendSub (s : Sub Γ []) (x : Term [] a) : Sub (a :: Γ) []
  | _, .here => x
  | _, .there v => s v

theorem beta_lift (t : Term (a :: Γ) b) (s : Sub Γ []) (x : Term [] a) :
    beta (subst (liftSub s) t) x = subst (extendSub s x) t := by
  unfold beta
  rw [subst_comp]
  congr 1
  funext b v
  cases v with
  | here => rfl
  | there v =>
    simp only [liftSub, subst_rename, extendSub]
    have h : (fun {a} (v : Var [] a) => closedSub x (Var.there v)) =
        (fun v => Term.var v : Sub [] []) := by funext a v; exact nomatch v
    rw [h, subst_id]

theorem closed_subst (t : Term [] a) (s : Sub [] []) : subst s t = t := by
  have h : s = (fun v => .var v) := by funext a v; exact nomatch v
  rw [h, subst_id]

end SquareKit.WeakMachine
