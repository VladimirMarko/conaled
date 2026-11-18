import SquareKit.Lawvere.CanonicalPresentation
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SquareKit.Lawvere
open CategoryTheory CategoryTheory.Limits
universe u v
namespace Operations
instance : Category Operations.{u} where
  Hom := Map
  id := Map.id
  comp := Map.comp
end Operations
namespace Presentation
variable (P Q : Presentation.{u})
def sumArity : P.Symbol ⊕ Q.Symbol → Nat := Sum.elim P.arity Q.arity

def leftTerm {n} : P.Term n → FinitaryTerm (P.Symbol ⊕ Q.Symbol) (sumArity P Q) (Fin n) :=
  FinitaryTerm.fold (fun s args => (FinitaryTerm.node (Sum.inl s) args : FinitaryTerm (P.Symbol ⊕ Q.Symbol) (sumArity P Q) (Fin n))) FinitaryTerm.leaf

def rightTerm {n} : Q.Term n → FinitaryTerm (P.Symbol ⊕ Q.Symbol) (sumArity P Q) (Fin n) :=
  FinitaryTerm.fold (fun s args => (FinitaryTerm.node (Sum.inr s) args : FinitaryTerm (P.Symbol ⊕ Q.Symbol) (sumArity P Q) (Fin n))) FinitaryTerm.leaf

def sum : Presentation.{u} where
  Symbol := P.Symbol ⊕ Q.Symbol
  arity := sumArity P Q
  Equation := P.Equation ⊕ Q.Equation
  variableCount := Sum.elim P.variableCount Q.variableCount
  lhs := Sum.rec (fun e => leftTerm P Q (P.lhs e)) (fun e => rightTerm P Q (Q.lhs e))
  rhs := Sum.rec (fun e => leftTerm P Q (P.rhs e)) (fun e => rightTerm P Q (Q.rhs e))

theorem evaluate_left {O : Operations.{v}}
    (op : (s : (sum P Q).Symbol) → O.Op ((sum P Q).arity s)) {n} (t : P.Term n) :
    (sum P Q).evaluate op (leftTerm P Q t) = P.evaluate (fun s => op (.inl s)) t := by
  induction t with
  | leaf => rfl
  | node s ts ih => exact congrArg (O.subst (op (.inl s))) (funext ih)

theorem evaluate_right {O : Operations.{v}}
    (op : (s : (sum P Q).Symbol) → O.Op ((sum P Q).arity s)) {n} (t : Q.Term n) :
    (sum P Q).evaluate op (rightTerm P Q t) = Q.evaluate (fun s => op (.inr s)) t := by
  induction t with
  | leaf => rfl
  | node s ts ih => exact congrArg (O.subst (op (.inr s))) (funext ih)

def sumAssignmentEquiv (O : Operations.{v}) :
    (sum P Q).Assignment O ≃ P.Assignment O × Q.Assignment O where
  toFun a :=
    (⟨fun s => a.op (.inl s), fun e => by
       have h := a.laws (.inl e)
       change (sum P Q).evaluate a.op (leftTerm P Q (P.lhs e)) = (sum P Q).evaluate a.op (leftTerm P Q (P.rhs e)) at h
       simpa only [evaluate_left] using h⟩,
     ⟨fun s => a.op (.inr s), fun e => by
       have h := a.laws (.inr e)
       change (sum P Q).evaluate a.op (rightTerm P Q (Q.lhs e)) = (sum P Q).evaluate a.op (rightTerm P Q (Q.rhs e)) at h
       simpa only [evaluate_right] using h⟩)
  invFun a := ⟨Sum.rec a.1.op a.2.op, by
    intro e
    cases e with
    | inl e =>
      change (sum P Q).evaluate _ (leftTerm P Q (P.lhs e)) = (sum P Q).evaluate _ (leftTerm P Q (P.rhs e))
      simpa only [evaluate_left] using a.1.laws e
    | inr e =>
      change (sum P Q).evaluate _ (rightTerm P Q (Q.lhs e)) = (sum P Q).evaluate _ (rightTerm P Q (Q.rhs e))
      simpa only [evaluate_right] using a.2.laws e⟩
  left_inv a := by apply Assignment.ext; funext s; cases s <;> rfl
  right_inv a := by rfl

def sumMapEquiv (O : Operations.{v}) :
    (sum P Q).operations.Map O ≃ P.operations.Map O × Q.operations.Map O :=
  ((sum P Q).assignmentEquiv O).symm |>.trans
    ((sumAssignmentEquiv P Q O).trans (Equiv.prodCongr (P.assignmentEquiv O) (Q.assignmentEquiv O)))
end Presentation
end SquareKit.Lawvere

namespace SquareKit.Lawvere.Presentation
open CategoryTheory CategoryTheory.Limits
universe u v
variable (P Q : Presentation.{u})
def sumInl : P.operations.Map (sum P Q).operations :=
  ((sumMapEquiv P Q _ ) (Operations.Map.id _)).1

def sumInr : Q.operations.Map (sum P Q).operations :=
  ((sumMapEquiv P Q _ ) (Operations.Map.id _)).2

@[simp] theorem sumInl_symbol (s : P.Symbol) :
    (sumInl P Q).map (P.symbol s) = (sum P Q).symbol (.inl s) := by
  exact P.interpretation_symbol _ s

@[simp] theorem sumInr_symbol (s : Q.Symbol) :
    (sumInr P Q).map (Q.symbol s) = (sum P Q).symbol (.inr s) := by
  exact Q.interpretation_symbol _ s

theorem sumMapEquiv_apply {O : Operations.{v}} (F : (sum P Q).operations.Map O) :
    sumMapEquiv P Q O F = ((sumInl P Q).comp F, (sumInr P Q).comp F) := by
  apply Prod.ext
  · apply (P.assignmentEquiv O).symm.injective
    apply Assignment.ext
    funext s
    change (P.interpretation ((sumAssignmentEquiv P Q O) ((sum P Q).assignment F)).1.op ((sumAssignmentEquiv P Q O) ((sum P Q).assignment F)).1.laws).map (P.symbol s) = F.map ((sumInl P Q).map (P.symbol s))
    rw [sumInl_symbol]
    exact P.interpretation_symbol _ s
  · apply (Q.assignmentEquiv O).symm.injective
    apply Assignment.ext
    funext s
    change (Q.interpretation ((sumAssignmentEquiv P Q O) ((sum P Q).assignment F)).2.op ((sumAssignmentEquiv P Q O) ((sum P Q).assignment F)).2.laws).map (Q.symbol s) = F.map ((sumInr P Q).map (Q.symbol s))
    rw [sumInr_symbol]
    exact Q.interpretation_symbol _ s
end SquareKit.Lawvere.Presentation

namespace SquareKit.Lawvere.Presentation
open CategoryTheory CategoryTheory.Limits
universe u
variable (P Q : Presentation.{u})
def sumIsColimit : IsColimit (BinaryCofan.mk (C := Operations.{u}) (sumInl P Q) (sumInr P Q)) :=
  BinaryCofan.isColimitMk
    (fun s => (sumMapEquiv P Q s.pt).symm (s.inl, s.inr))
    (fun s => by
      have h := (sumMapEquiv P Q s.pt).apply_symm_apply (s.inl, s.inr)
      rw [sumMapEquiv_apply] at h
      exact congrArg Prod.fst h)
    (fun s => by
      have h := (sumMapEquiv P Q s.pt).apply_symm_apply (s.inl, s.inr)
      rw [sumMapEquiv_apply] at h
      exact congrArg Prod.snd h)
    (fun s m hl hr => by
      apply (sumMapEquiv P Q s.pt).injective
      rw [sumMapEquiv_apply, Equiv.apply_symm_apply]
      exact Prod.ext hl hr)
end SquareKit.Lawvere.Presentation

namespace SquareKit.Lawvere.Operations
open CategoryTheory CategoryTheory.Limits
universe u v
variable (O R : Operations.{u})
/-- Coproduct for arbitrary operation theories through their canonical presentations. -/
def sum : Operations.{u} := (Presentation.sum O.canonicalPresentation R.canonicalPresentation).operations

def sumMapEquiv (A : Operations.{v}) : (sum O R).Map A ≃ O.Map A × R.Map A :=
  (Presentation.sumMapEquiv O.canonicalPresentation R.canonicalPresentation A).trans
    (Equiv.prodCongr (O.canonicalMapEquiv A) (R.canonicalMapEquiv A))

def sumInl : O.Map (sum O R) := O.encode.comp (Presentation.sumInl _ _)
def sumInr : R.Map (sum O R) := R.encode.comp (Presentation.sumInr _ _)

theorem sumMapEquiv_apply {A : Operations.{v}} (F : (sum O R).Map A) :
    sumMapEquiv O R A F = ((sumInl O R).comp F, (sumInr O R).comp F) := by
  change (Equiv.prodCongr _ _) (Presentation.sumMapEquiv _ _ _ F) = _
  rw [Presentation.sumMapEquiv_apply]
  rfl

def sumIsColimit : IsColimit (BinaryCofan.mk (C := Operations.{u}) (sumInl O R) (sumInr O R)) :=
  BinaryCofan.isColimitMk
    (fun s => (sumMapEquiv O R s.pt).symm (s.inl, s.inr))
    (fun s => by
      have h := (sumMapEquiv O R s.pt).apply_symm_apply (s.inl, s.inr)
      rw [sumMapEquiv_apply] at h
      exact congrArg Prod.fst h)
    (fun s => by
      have h := (sumMapEquiv O R s.pt).apply_symm_apply (s.inl, s.inr)
      rw [sumMapEquiv_apply] at h
      exact congrArg Prod.snd h)
    (fun s m hl hr => by
      apply (sumMapEquiv O R s.pt).injective
      rw [sumMapEquiv_apply, Equiv.apply_symm_apply]
      exact Prod.ext hl hr)
end SquareKit.Lawvere.Operations
