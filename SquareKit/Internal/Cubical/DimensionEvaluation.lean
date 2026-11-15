import SquareKit.Internal.Cubical.Interval

/-! Interpret arbitrary De Morgan expressions at represented interval values.
Chosen raw representatives disappear in the quotient and commute with every
cube substitution. -/
namespace SquareKit.Cubical
open CategoryTheory

namespace Cube

noncomputable def assemble {I : Cube} {n : ℕ} (r : Fin n → Hom I ⟨1⟩) : Hom I ⟨n⟩ :=
  ofRaw (fun k => (r k).out 0)

theorem comp_assemble {I J : Cube} {n : ℕ} (f : Hom I J) (r : Fin n → Hom J ⟨1⟩) :
    comp f (assemble r) = assemble (fun k => comp f (r k)) := by
  refine Quotient.inductionOn f ?_
  intro f
  apply Quotient.sound
  intro k
  have h : ofRaw (fun i => Expr.subst f ((r k).out i)) = comp (ofRaw f) (r k) := by
    exact congrArg (comp (ofRaw f)) (Quotient.out_eq (r k))
  have h' := h.trans (Quotient.out_eq (comp (ofRaw f) (r k))).symm
  exact (Quotient.exact h') 0

noncomputable def evalDimension {I : Cube} {n : ℕ} (e : Expr (Fin n))
    (r : Fin n → Hom I ⟨1⟩) : Hom I ⟨1⟩ := comp (assemble r) (ofRaw (fun _ => e))

theorem evalDimension_congr {I : Cube} {n : ℕ} {e e' : Expr (Fin n)}
    (h : Expr.Conv e e') (r : Fin n → Hom I ⟨1⟩) : evalDimension e r = evalDimension e' r :=
  congrArg (comp (assemble r)) (Quotient.sound (fun _ => h))

theorem comp_evalDimension {I J : Cube} {n : ℕ} (f : Hom I J) (e : Expr (Fin n))
    (r : Fin n → Hom J ⟨1⟩) :
    comp f (evalDimension e r) = evalDimension e (fun k => comp f (r k)) := by
  exact (@Category.assoc Cube _ I J ⟨n⟩ ⟨1⟩ f (assemble r) (ofRaw (fun _ => e))).symm.trans
    (congrArg (fun h => comp h (ofRaw (fun _ => e))) (comp_assemble f r))

@[simp] theorem evalDimension_var {I : Cube} {n : ℕ} (k : Fin n)
    (r : Fin n → Hom I ⟨1⟩) : evalDimension (.var k) r = r k := by
  calc
    _ = ofRaw (r k).out := by
      apply Quotient.sound
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact .refl _
    _ = _ := Quotient.out_eq _

@[simp] theorem evalDimension_zero {I : Cube} {n : ℕ} (r : Fin n → Hom I ⟨1⟩) :
    evalDimension .zero r = endpoint I false := rfl

@[simp] theorem evalDimension_one {I : Cube} {n : ℕ} (r : Fin n → Hom I ⟨1⟩) :
    evalDimension .one r = endpoint I true := rfl

theorem evalDimension_meet {I : Cube} {n : ℕ} (a b : Expr (Fin n))
    (r : Fin n → Hom I ⟨1⟩) :
    evalDimension (.meet a b) r = meet (evalDimension a r) (evalDimension b r) := rfl

theorem assemble_evalDimension {I : Cube} {m n : ℕ} (σ : Fin m → Expr (Fin n))
    (r : Fin n → Hom I ⟨1⟩) :
    assemble (fun k => evalDimension (σ k) r) = comp (assemble r) (ofRaw σ) := by
  apply Quotient.sound
  intro k
  exact (Quotient.exact (Quotient.out_eq (evalDimension (σ k) r))) 0

theorem evalDimension_subst {I : Cube} {m n : ℕ} (e : Expr (Fin m))
    (σ : Fin m → Expr (Fin n)) (r : Fin n → Hom I ⟨1⟩) :
    evalDimension (Expr.subst σ e) r = evalDimension e (fun k => evalDimension (σ k) r) := by
  have h : (ofRaw (fun _ => Expr.subst σ e) : Hom ⟨n⟩ ⟨1⟩) = comp (ofRaw σ) (ofRaw (fun _ => e)) := rfl
  exact (congrArg (comp (assemble r)) h).trans
    ((@Category.assoc Cube _ I ⟨n⟩ ⟨m⟩ ⟨1⟩ (assemble r) (ofRaw σ) (ofRaw (fun _ => e))).symm.trans
      (congrArg (fun h => comp h (ofRaw (fun _ => e))) (assemble_evalDimension σ r).symm))

end Cube

namespace Presheaf
universe u

noncomputable def intervalDimension {Γ : Context.{u}} {n : ℕ} (e : Expr (Fin n))
    (r : Fin n → Term (interval Γ)) : Term (interval Γ) where
  val x := ⟨Cube.evalDimension e (fun k => (r k).val x |>.down)⟩
  property f := by
    apply congrArg ULift.up
    have h := Cube.comp_evalDimension f.hom.unop e (fun k => (r k).val _ |>.down)
    refine h.trans ?_
    apply congrArg (Cube.evalDimension e)
    funext k
    exact congrArg ULift.down ((r k).property f)

theorem intervalDimension_congr {Γ : Context.{u}} {n : ℕ} {e e' : Expr (Fin n)}
    (h : Expr.Conv e e') (r : Fin n → Term (interval Γ)) :
    intervalDimension e r = intervalDimension e' r := by
  apply Term.ext
  intro x
  exact congrArg ULift.up (Cube.evalDimension_congr h _)

theorem intervalDimension_reindex {Γ Δ : Context.{u}} {n : ℕ} (e : Expr (Fin n))
    (r : Fin n → Term (interval Γ)) (σ : Δ ⟶ Γ) :
    (intervalDimension e r).reindex σ = intervalDimension e (fun k => (r k).reindex σ) := rfl

@[simp] theorem intervalDimension_var {Γ : Context.{u}} {n : ℕ} (k : Fin n)
    (r : Fin n → Term (interval Γ)) : intervalDimension (.var k) r = r k := by
  apply Term.ext
  intro x
  exact congrArg ULift.up (Cube.evalDimension_var k _)

theorem intervalDimension_subst {Γ : Context.{u}} {m n : ℕ} (e : Expr (Fin m))
    (σ : Fin m → Expr (Fin n)) (r : Fin n → Term (interval Γ)) :
    intervalDimension (Expr.subst σ e) r = intervalDimension e (fun k => intervalDimension (σ k) r) := by
  apply Term.ext
  intro x
  exact congrArg ULift.up (Cube.evalDimension_subst e σ _)

@[simp] theorem intervalDimension_zero {Γ : Context.{u}} {n : ℕ}
    (r : Fin n → Term (interval Γ)) : intervalDimension .zero r = endpoint Γ false := by
  apply Term.ext
  intro x
  exact congrArg ULift.up (Cube.evalDimension_zero _)

@[simp] theorem intervalDimension_one {Γ : Context.{u}} {n : ℕ}
    (r : Fin n → Term (interval Γ)) : intervalDimension .one r = endpoint Γ true := by
  apply Term.ext
  intro x
  exact congrArg ULift.up (Cube.evalDimension_one _)

theorem intervalDimension_meet {Γ : Context.{u}} {n : ℕ} (a b : Expr (Fin n))
    (r : Fin n → Term (interval Γ)) :
    intervalDimension (.meet a b) r = intervalMeet (intervalDimension a r) (intervalDimension b r) := by
  apply Term.ext
  intro x
  exact congrArg ULift.up (Cube.evalDimension_meet a b _)

end Presheaf
end SquareKit.Cubical
