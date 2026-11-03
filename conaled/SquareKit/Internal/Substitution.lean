import SquareKit.Internal.Logic

/-! Syntactic substitution laws used to introduce an arbitrary formula's witness.
These are equalities of syntax, independent of any interpretation. -/
namespace SquareKit.Internal
universe u
variable {S : Type u} {F P : S → S → Type u}

theorem Term.subst_id (t : Term F Γ s) : t.subst (fun i => .var i) = t := by
  induction t with
  | var => rfl
  | app f t ih => exact congrArg (Term.app f) ih

theorem Term.subst_comp (t : Term F Γ s) (σ : Sub F Γ Δ) (τ : Sub F Δ Ξ) :
    (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ) := by
  induction t with
  | var => rfl
  | app f t ih => exact congrArg (Term.app f) ih

theorem Term.shift_subst_lift (t : Term F Γ s) (σ : Sub F Γ Δ) :
    (t.shift (b := b)).subst σ.lift = (t.subst σ).shift := by
  simp only [Term.shift, Term.subst_comp, Term.subst, Sub.lift]

theorem Sub.lift_comp (σ : Sub F Γ Δ) (τ : Sub F Δ Ξ) :
    (fun {s} (i : Var (b :: Γ) s) => (σ.lift i).subst τ.lift) =
      (fun {s} (i : Var (b :: Γ) s) => (Sub.lift (fun i => (σ i).subst τ)) i) := by
  funext s i
  cases i with
  | zero => rfl
  | succ i => exact Term.shift_subst_lift (σ i) τ

theorem FormulaCore.subst_id (p : Formula F Γ P) : p.subst (fun i => .var i) = p := by
  induction p with
  | atom r a b => simp only [FormulaCore.subst, Term.subst_id]
  | eq a b => simp only [FormulaCore.subst, Term.subst_id]
  | conj p q hp hq => simp only [FormulaCore.subst, hp, hq]
  | @ex s Γ p ih =>
    have h : (fun {t} (i : Var (s :: Γ) t) => Sub.lift (F := F) (fun (i : Var Γ _) => Term.var i) i) =
        (fun {t} (i : Var (s :: Γ) t) => Term.var i) := by funext t i; cases i <;> rfl
    simp only [FormulaCore.subst, h, ih]

theorem FormulaCore.subst_comp (p : Formula F Γ P) (σ : Sub F Γ Δ) (τ : Sub F Δ Ξ) :
    (p.subst σ).subst τ = p.subst (fun i => (σ i).subst τ) := by
  induction p generalizing Δ Ξ with
  | atom r a b => simp only [FormulaCore.subst, Term.subst_comp]
  | eq a b => simp only [FormulaCore.subst, Term.subst_comp]
  | conj p q hp hq => simp only [FormulaCore.subst, hp, hq]
  | ex p ih => simp only [FormulaCore.subst, ih, Sub.lift_comp]

/-- Inserting a context variable underneath the bound variable, then choosing
that context variable as witness, restores the original body. -/
theorem FormulaCore.lift_shift_instantiate (p : Formula F (s :: Γ) P) :
    (p.subst (Sub.lift (fun i => .var (.succ i)))).instantiate (.var .zero) = p := by
  rw [FormulaCore.instantiate, FormulaCore.subst_comp]
  have h : (fun {t} (i : Var (s :: Γ) t) =>
      ((Sub.lift (F := F) (fun i => .var (.succ i))) i).subst (single (.var .zero))) =
      (fun {t} (i : Var (s :: Γ) t) => Term.var i) := by funext t i; cases i <;> rfl
  rw [h, FormulaCore.subst_id]
end SquareKit.Internal
