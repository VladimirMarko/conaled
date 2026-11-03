import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

/-!
# A finite parameterized presentation in Set families

Experimental bounded geometric syntax for Σ(r). The three source sequents
contain no excluded-middle or decidability assumption. Models interpret them
in predicates on an arbitrary type. The denotation is a family of sets; this
module does not construct a slice topos or prove its classifier property.
`Model.toSection` uses classical host reasoning to select a summand from
propositional coverage. No `DecidablePred r` is part of the interface.
-/
namespace SquareKit.Internal.FiniteSetting

universe u v w

inductive Formula where
  | p | q | parameter | top | bottom
  | and (a b : Formula) | or (a b : Formula)
  deriving DecidableEq

structure Sequent where
  premise : Formula
  conclusion : Formula
  deriving DecidableEq

/-- The bounded presentation has exactly these three relation slots. -/
def axioms : Fin 3 → Sequent
  | 0 => ⟨.top, .or .p .q⟩
  | 1 => ⟨.and .p .q, .bottom⟩
  | 2 => ⟨.p, .parameter⟩

/-- Any type is an admissible parameter context; any predicate is admissible. -/
structure Presentation (X : Type u) where
  parameter : X → Prop

def Presentation.subst {X : Type u} {Y : Type v}
    (T : Presentation X) (σ : Y → X) : Presentation Y := ⟨T.parameter ∘ σ⟩

@[simp] theorem Presentation.subst_id {X : Type u} (T : Presentation X) :
    T.subst id = T := rfl

@[simp] theorem Presentation.subst_comp {X : Type u} {Y : Type v} {Z : Type w}
    (T : Presentation X) (σ : Y → X) (τ : Z → Y) :
    (T.subst σ).subst τ = T.subst (σ ∘ τ) := rfl

/-- Interpretation is separate from syntax and from satisfaction. -/
def Formula.eval {X : Type u} (r P Q : X → Prop) (x : X) : Formula → Prop
  | .p => P x
  | .q => Q x
  | .parameter => r x
  | .top => True
  | .bottom => False
  | .and a b => a.eval r P Q x ∧ b.eval r P Q x
  | .or a b => a.eval r P Q x ∨ b.eval r P Q x

def Satisfies {X : Type u} (T : Presentation X) (P Q : X → Prop) : Prop :=
  ∀ (i : Fin 3) (x : X), (axioms i).premise.eval T.parameter P Q x →
    (axioms i).conclusion.eval T.parameter P Q x

theorem satisfies_iff {X : Type u} (T : Presentation X) (P Q : X → Prop) :
    Satisfies T P Q ↔
      (∀ x, P x ∨ Q x) ∧ (∀ x, ¬ (P x ∧ Q x)) ∧ (∀ x, P x → T.parameter x) := by
  constructor
  · intro h
    exact ⟨fun x => h 0 x trivial, fun x => h 1 x, fun x => h 2 x⟩
  · rintro ⟨hc, hd, hr⟩ i x
    fin_cases i <;> simp only [axioms, Formula.eval]
    · exact fun _ => hc x
    · exact hd x
    · exact hr x

structure Model {X : Type u} (T : Presentation X) where
  P : X → Prop
  Q : X → Prop
  satisfies : Satisfies T P Q

@[ext] theorem Model.ext {X : Type u} {T : Presentation X} {M N : Model T}
    (hp : M.P = N.P) (hq : M.Q = N.Q) : M = N := by
  cases M; cases N; cases hp; cases hq; rfl

theorem Formula.eval_subst {X : Type u} {Y : Type v} (f : Formula)
    (r P Q : X → Prop) (σ : Y → X) (y : Y) :
    f.eval (r ∘ σ) (P ∘ σ) (Q ∘ σ) y = f.eval r P Q (σ y) := by
  induction f <;> simp_all [Formula.eval, Function.comp_def]

def Model.subst {X : Type u} {Y : Type v} {T : Presentation X}
    (M : Model T) (σ : Y → X) : Model (T.subst σ) where
  P := M.P ∘ σ
  Q := M.Q ∘ σ
  satisfies i y := by
    simpa only [Presentation.subst, Formula.eval_subst] using M.satisfies i (σ y)

@[simp] theorem Model.subst_id {X : Type u} {T : Presentation X} (M : Model T) :
    M.subst id = M := rfl

@[simp] theorem Model.subst_comp {X : Type u} {Y : Type v} {Z : Type w}
    {T : Presentation X} (M : Model T) (σ : Y → X) (τ : Z → Y) :
    (M.subst σ).subst τ = M.subst (σ ∘ τ) := rfl

/-- `PLift` makes the proposition's proof type a summand in `Type`. -/
def Fiber {X : Type u} (T : Presentation X) (x : X) := PLift (T.parameter x) ⊕ Unit

def Section {X : Type u} (T : Presentation X) := (x : X) → Fiber T x

def Section.subst {X : Type u} {Y : Type v} {T : Presentation X}
    (s : Section T) (σ : Y → X) : Section (T.subst σ) := fun y => s (σ y)

@[simp] theorem Section.subst_id {X : Type u} {T : Presentation X} (s : Section T) :
    s.subst id = s := rfl

@[simp] theorem Section.subst_comp {X : Type u} {Y : Type v} {Z : Type w}
    {T : Presentation X} (s : Section T) (σ : Y → X) (τ : Z → Y) :
    (s.subst σ).subst τ = s.subst (σ ∘ τ) := rfl

def Section.toModel {X : Type u} {T : Presentation X} (s : Section T) : Model T where
  P x := (s x).isLeft
  Q x := (s x).isRight
  satisfies := (satisfies_iff T _ _).mpr (by
    refine ⟨?_, ?_, ?_⟩
    · intro x; cases s x <;> simp
    · intro x; cases s x <;> simp
    · intro x h; cases hval : s x with
      | inl a => exact a.down
      | inr b => simp [hval] at h)

/-- Classical selection is confined to the Set host, not a source sequent. -/
noncomputable def Model.toSection {X : Type u} {T : Presentation X}
    (M : Model T) : Section T := fun x => by
  classical
  exact if h : M.P x then Sum.inl ⟨((satisfies_iff T _ _).mp M.satisfies).2.2 x h⟩
    else Sum.inr ()

@[simp] theorem Model.toSection_toModel {X : Type u} {T : Presentation X}
    (M : Model T) : M.toSection.toModel = M := by
  classical
  obtain ⟨hc, hd, _⟩ := (satisfies_iff T _ _).mp M.satisfies
  apply Model.ext <;> funext x <;> apply propext
  · by_cases h : M.P x <;> simp [Section.toModel, Model.toSection, h]
  · simp only [Section.toModel, Model.toSection]
    by_cases h : M.P x
    · simp [h]; exact fun hq => hd x ⟨h, hq⟩
    · simp [h]; exact (hc x).resolve_left h

@[simp] theorem Section.toModel_toSection {X : Type u} {T : Presentation X}
    (s : Section T) : s.toModel.toSection = s := by
  classical
  funext x
  cases h : s x with
  | inl a => simp [Model.toSection, Section.toModel, h]; rfl
  | inr b => cases b; simp [Model.toSection, Section.toModel, h]; rfl

/-- The correspondence includes both inverse laws, uniformly in the parameter. -/
noncomputable def modelSectionEquiv {X : Type u} (T : Presentation X) :
    Model T ≃ Section T where
  toFun := Model.toSection
  invFun := Section.toModel
  left_inv := Model.toSection_toModel
  right_inv := Section.toModel_toSection

@[simp] theorem Section.toModel_subst {X : Type u} {Y : Type v} {T : Presentation X}
    (s : Section T) (σ : Y → X) : (s.subst σ).toModel = s.toModel.subst σ := rfl

@[simp] theorem Model.toSection_subst {X : Type u} {Y : Type v} {T : Presentation X}
    (M : Model T) (σ : Y → X) : (M.subst σ).toSection = M.toSection.subst σ := rfl

/-- Total family with its projection to the parameter context. -/
def Total {X : Type u} (T : Presentation X) := (x : X) × Fiber T x

def genericSection {X : Type u} (T : Presentation X) :
    Section (T.subst (fun a : Total T => a.1)) := fun a => a.2

def genericModel {X : Type u} (T : Presentation X) :
    Model (T.subst (fun a : Total T => a.1)) := (genericSection T).toModel

def Section.graph {X : Type u} {T : Presentation X} (s : Section T) : X → Total T :=
  fun x => ⟨x, s x⟩

@[simp] theorem genericSection_recovery {X : Type u} {T : Presentation X}
    (s : Section T) : (genericSection T).subst s.graph = s := rfl

@[simp] theorem genericModel_recovery {X : Type u} {T : Presentation X}
    (s : Section T) : (genericModel T).subst s.graph = s.toModel := rfl

@[simp] theorem genericModel_model_recovery {X : Type u} {T : Presentation X}
    (M : Model T) : (genericModel T).subst M.toSection.graph = M :=
  M.toSection_toModel

/-- The map from a substituted total family to the original total family. -/
def totalMap {X : Type u} {Y : Type v} (T : Presentation X) (σ : Y → X) :
    Total (T.subst σ) → Total T := fun a => ⟨σ a.1, a.2⟩

@[simp] theorem totalMap_id {X : Type u} (T : Presentation X) :
    totalMap T id = id := rfl

@[simp] theorem totalMap_comp {X : Type u} {Y : Type v} {Z : Type w}
    (T : Presentation X) (σ : Y → X) (τ : Z → Y) :
    totalMap T σ ∘ totalMap (T.subst σ) τ = totalMap T (σ ∘ τ) := rfl

@[simp] theorem totalMap_projection {X : Type u} {Y : Type v}
    (T : Presentation X) (σ : Y → X) (a : Total (T.subst σ)) :
    (totalMap T σ a).1 = σ a.1 := rfl

@[simp] theorem genericSection_subst {X : Type u} {Y : Type v}
    (T : Presentation X) (σ : Y → X) :
    (genericSection T).subst (totalMap T σ) = genericSection (T.subst σ) := rfl

@[simp] theorem genericModel_subst {X : Type u} {Y : Type v}
    (T : Presentation X) (σ : Y → X) :
    (genericModel T).subst (totalMap T σ) = genericModel (T.subst σ) := rfl

end SquareKit.Internal.FiniteSetting
