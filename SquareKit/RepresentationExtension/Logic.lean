import SquareKit.RepresentationExtension.Models
import Mathlib.ModelTheory.Semantics

/-! A tagged-carrier adapter to Mathlib's single-sorted first-order semantics.
 Sort guards express both old quantifiers. Consequence ranges over every
 nonempty two-sorted model, not just one selected interpretation. -/
namespace SquareKit.RepresentationExtension
namespace Logic
universe u v
open FirstOrder FirstOrder.Language

inductive Relation : Nat → Type
  | sortA : Relation 1
  | sortB : Relation 1
  | predicate : Relation 1
  | related : Relation 2

def language : Language := ⟨fun _ => Empty, Relation⟩

abbrev Carrier (M : Model.{u}) := M.A ⊕ M.B

def isA : Carrier M → Prop
  | .inl _ => True
  | .inr _ => False

def isB : Carrier M → Prop
  | .inl _ => False
  | .inr _ => True

def predicate (M : Model.{u}) : Carrier M → Prop
  | .inl a => M.predicate a
  | .inr _ => False

def related (M : Model.{u}) : Carrier M → Carrier M → Prop
  | .inl a, .inl b => M.relation.r a b
  | _, _ => False

instance carrierStructure (M : Model.{u}) : language.Structure (Carrier M) where
  funMap f := nomatch f
  RelMap
    | .sortA, xs => isA (xs 0)
    | .sortB, xs => isB (xs 0)
    | .predicate, xs => predicate M (xs 0)
    | .related, xs => related M (xs 0) (xs 1)

/-- Sort A quantification is an ordinary Mathlib quantifier with a sort guard. -/
def allA {α : Type v} {n} (φ : language.BoundedFormula α (n+1)) :
    language.BoundedFormula α n :=
  .all (.imp (.rel Relation.sortA (fun _ => .var (.inr (Fin.last n)))) φ)

def allB {α : Type v} {n} (φ : language.BoundedFormula α (n+1)) :
    language.BoundedFormula α n :=
  .all (.imp (.rel Relation.sortB (fun _ => .var (.inr (Fin.last n)))) φ)

/-- These equations certify the many-sorted quantifier adapter. -/
theorem realize_allA (M : Model.{u}) {α : Type v} {n}
    (φ : language.BoundedFormula α (n+1)) (ρ : α → Carrier M) (xs : Fin n → Carrier M) :
    (allA φ).Realize ρ xs ↔ ∀ a : M.A, φ.Realize ρ (Fin.snoc xs (.inl a)) := by
  simp only [allA, BoundedFormula.Realize, Term.realize, Sum.elim_inr, Fin.snoc_last]
  constructor
  · intro h a
    exact h (.inl a) trivial
  · intro h x hx
    cases x with
    | inl a => exact h a
    | inr b => exact hx.elim

theorem realize_allB (M : Model.{u}) {α : Type v} {n}
    (φ : language.BoundedFormula α (n+1)) (ρ : α → Carrier M) (xs : Fin n → Carrier M) :
    (allB φ).Realize ρ xs ↔ ∀ b : M.B, φ.Realize ρ (Fin.snoc xs (.inr b)) := by
  simp only [allB, BoundedFormula.Realize, Term.realize, Sum.elim_inr, Fin.snoc_last]
  constructor
  · intro h b
    exact h (.inr b) trivial
  · intro h x hx
    cases x with
    | inl a => exact hx.elim
    | inr b => exact h b

/-- Every old formula and assignment is retained, including arbitrary nesting
 of negation, implication and either sort's quantifier. -/
def Realize (M : Model.{u}) {α : Type v} (φ : language.Formula α) (ρ : α → Carrier M) : Prop :=
  φ.Realize ρ

def ExtendedRealize (N : ExtendedModel.{u}) {α : Type v}
    (φ : language.Formula α) (ρ : α → Carrier N.reduct.reduct) : Prop := φ.Realize ρ

theorem realize_expand (M : Model.{u}) {α : Type v}
    (φ : language.Formula α) (ρ : α → Carrier M) :
    ExtendedRealize (expand M) φ ρ ↔ Realize M φ ρ := Iff.rfl

def Consequence {α : Type v} (Γ : Set (language.Formula α)) (φ : language.Formula α) : Prop :=
  ∀ (M : Model.{u}) (ρ : α → Carrier M), (∀ ψ ∈ Γ, Realize M ψ ρ) → Realize M φ ρ

def ExtendedConsequence {α : Type v} (Γ : Set (language.Formula α))
    (φ : language.Formula α) : Prop :=
  ∀ (N : ExtendedModel.{u}) (ρ : α → Carrier N.reduct.reduct),
    (∀ ψ ∈ Γ, ExtendedRealize N ψ ρ) → ExtendedRealize N φ ρ

/-- The reflection direction expands an arbitrary countermodel candidate.
 No soundness/completeness bridge or claim about proof trees is used. -/
theorem consequence_iff {α : Type v} (Γ : Set (language.Formula α)) (φ : language.Formula α) :
    ExtendedConsequence.{u} Γ φ ↔ Consequence.{u} Γ φ := by
  constructor
  · intro h M ρ hΓ
    exact h (expand M) ρ hΓ
  · intro h N ρ hΓ
    exact h N.reduct.reduct ρ hΓ

/-- A countermodel is retained, together with the same falsifying assignment. -/
theorem countermodel_expands {α : Type v} (M : Model.{u}) (Γ : Set (language.Formula α))
    (φ : language.Formula α) (ρ : α → Carrier M)
    (hΓ : ∀ ψ ∈ Γ, Realize M ψ ρ) (hφ : ¬ Realize M φ ρ) :
    (∀ ψ ∈ Γ, ExtendedRealize (expand M) ψ ρ) ∧ ¬ ExtendedRealize (expand M) φ ρ :=
  ⟨hΓ,hφ⟩
inductive OldSort
  | a | b

def SortCarrier (M : Model.{u}) : OldSort → Type u
  | .a => M.A
  | .b => M.B

def tag (M : Model.{u}) : (s : OldSort) → SortCarrier M s → Carrier M
  | .a, x => .inl x
  | .b, x => .inr x

/-- Typed free-variable assignments retain the specified old sort. -/
def typedAssignment (M : Model.{u}) {α : Type v} (sort : α → OldSort)
    (ρ : ∀ x, SortCarrier M (sort x)) : α → Carrier M := fun x => tag M (sort x) (ρ x)

def TypedConsequence {α : Type v} (sort : α → OldSort)
    (Γ : Set (language.Formula α)) (φ : language.Formula α) : Prop :=
  ∀ (M : Model.{u}) (ρ : ∀ x, SortCarrier M (sort x)),
    (∀ ψ ∈ Γ, Realize M ψ (typedAssignment M sort ρ)) →
      Realize M φ (typedAssignment M sort ρ)

def ExtendedTypedConsequence {α : Type v} (sort : α → OldSort)
    (Γ : Set (language.Formula α)) (φ : language.Formula α) : Prop :=
  ∀ (N : ExtendedModel.{u}) (ρ : ∀ x, SortCarrier N.reduct.reduct (sort x)),
    (∀ ψ ∈ Γ, ExtendedRealize N ψ (typedAssignment N.reduct.reduct sort ρ)) →
      ExtendedRealize N φ (typedAssignment N.reduct.reduct sort ρ)

theorem typed_consequence_iff {α : Type v} (sort : α → OldSort)
    (Γ : Set (language.Formula α)) (φ : language.Formula α) :
    ExtendedTypedConsequence.{u} sort Γ φ ↔ TypedConsequence.{u} sort Γ φ := by
  constructor
  · intro h M ρ hΓ
    exact h (expand M) ρ hΓ
  · intro h N ρ hΓ
    exact h N.reduct.reduct ρ hΓ

/-- An old isomorphism reflects relations and predicates. Forward homomorphisms
 alone cannot supply this Mathlib equivalence. -/
def oldEquiv {M N : Model.{u}} (a : M.A ≃ N.A) (b : M.B ≃ N.B)
    (hr : ∀ x y, N.relation.r (a x) (a y) ↔ M.relation.r x y)
    (hp : ∀ x, N.predicate (a x) ↔ M.predicate x) :
    language.Equiv (Carrier M) (Carrier N) where
  toEquiv := Equiv.sumCongr a b
  map_fun' f := nomatch f
  map_rel' r xs := by
    cases r with
    | sortA =>
      change isA ((Equiv.sumCongr a b) (xs 0)) ↔ isA (xs 0)
      cases h : xs 0 <;> simp [isA]
    | sortB =>
      change isB ((Equiv.sumCongr a b) (xs 0)) ↔ isB (xs 0)
      cases h : xs 0 <;> simp [isB]
    | predicate =>
      change predicate N ((Equiv.sumCongr a b) (xs 0)) ↔ predicate M (xs 0)
      cases h : xs 0 <;> simp [predicate, hp]
    | related =>
      change related N ((Equiv.sumCongr a b) (xs 0)) ((Equiv.sumCongr a b) (xs 1)) ↔
        related M (xs 0) (xs 1)
      cases h : xs 0 <;> cases k : xs 1 <;> simp [related, hr]

theorem realize_oldEquiv {M N : Model.{u}} (a : M.A ≃ N.A) (b : M.B ≃ N.B)
    (hr : ∀ x y, N.relation.r (a x) (a y) ↔ M.relation.r x y)
    (hp : ∀ x, N.predicate (a x) ↔ M.predicate x)
    {α : Type v} (φ : language.Formula α) (ρ : α → Carrier M) :
    Realize N φ (oldEquiv a b hr hp ∘ ρ) ↔ Realize M φ ρ :=
  StrongHomClass.realize_formula (oldEquiv a b hr hp) φ
end Logic
end SquareKit.RepresentationExtension
