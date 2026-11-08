import SquareKit.CommutingOperations
import SquareKit.GuardedTheory

/-! Independently presented unary equations admit guarded models. Local mixed
commutation also interprets a structural product normal form. -/
namespace SquareKit.UnaryInteraction
set_option backward.isDefEq.respectTransparency false
open CommutingOperations
open GuardedTheory

/-- An equation of unary words, independent of guarded syntax. -/
structure Presentation (S : Type) where
  Law : Type
  lhs : Law → List S
  rhs : Law → List S

def Valid {S X : Type} (P : Presentation S) (op : S → X → X) : Prop :=
  ∀ e x, run op (P.lhs e) x = run op (P.rhs e) x

def unary (S : Type) : Signature := ⟨S, fun _ => 1, Empty, Empty.elim⟩

def term {S : Type} : List S → Term (unary S) (Fin 1)
  | [] => .var 0
  | s :: ss => .app s (fun _ => term ss)

def equation {S : Type} (l r : List S) : Rule (unary S) where
  parameterCount := 1
  hypotheses := 0
  premise := Fin.elim0
  conclusion := .eq (term l) (term r)

def algebra {S X : Type} (op : S → X → X) : Algebra (unary S) where
  Carrier := X
  operation s xs := op s (xs ⟨0, by change 0 < 1; decide⟩)
  predicate p := Empty.elim p

theorem eval_term {S X : Type} (op : S → X → X) (w : List S) (ρ : Fin 1 → X) :
    (term w).eval (algebra op) ρ = run op w (ρ 0) := by
  induction w with
  | nil => rfl
  | cons s ss ih => exact congrArg (op s) ih

def guarded {S : Type} (P : Presentation S) : Theory (unary S) :=
  ⟨P.Law, fun e => equation (P.lhs e) (P.rhs e)⟩

def model {S X : Type} (P : Presentation S) (op : S → X → X) (h : Valid P op) :
    Model (guarded P) where
  toAlgebra := algebra op
  rules e ρ _ := by
    change (term (P.lhs e)).eval (algebra op) ρ = (term (P.rhs e)).eval (algebra op) ρ
    rw [eval_term, eval_term]
    exact h e (ρ ⟨0, by change 0 < 1; decide⟩)

def union {S T : Type} (P : Presentation S) (Q : Presentation T) : Presentation (S ⊕ T) where
  Law := P.Law ⊕ Q.Law
  lhs := Sum.elim (fun e => (P.lhs e).map Sum.inl) (fun e => (Q.lhs e).map Sum.inr)
  rhs := Sum.elim (fun e => (P.rhs e).map Sum.inl) (fun e => (Q.rhs e).map Sum.inr)

def tensor {S T : Type} (P : Presentation S) (Q : Presentation T) : Presentation (S ⊕ T) where
  Law := (union P Q).Law ⊕ (S × T)
  lhs := Sum.elim (union P Q).lhs (fun st => [.inl st.1, .inr st.2])
  rhs := Sum.elim (union P Q).rhs (fun st => [.inr st.2, .inl st.1])

theorem run_map {S T X : Type} (f : S → T) (op : T → X → X) (w : List S) (x : X) :
    run op (w.map f) x = run (fun s => op (f s)) w x := by
  induction w with
  | nil => rfl
  | cons s ss ih => exact congrArg (op (f s)) ih

theorem union_valid {S T X : Type} (P : Presentation S) (Q : Presentation T)
    (l : S → X → X) (r : T → X → X) (hl : Valid P l) (hr : Valid Q r) :
    Valid (union P Q) (Sum.elim l r) := by
  intro e x
  cases e with
  | inl e => simpa only [union, Sum.elim_inl, Sum.elim_inr, run_map] using hl e x
  | inr e => simpa only [union, Sum.elim_inl, Sum.elim_inr, run_map] using hr e x

theorem tensor_valid_iff {S T X : Type} (P : Presentation S) (Q : Presentation T)
    (l : S → X → X) (r : T → X → X) :
    Valid (tensor P Q) (Sum.elim l r) ↔
      Valid P l ∧ Valid Q r ∧ Interchange l r := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro e x
      simpa only [tensor, union, Sum.elim_inl, Sum.elim_inr, run_map] using h (.inl (.inl e)) x
    · intro e x
      simpa only [tensor, union, Sum.elim_inl, Sum.elim_inr, run_map] using h (.inl (.inr e)) x
    · intro s t x
      exact h (.inr (s,t)) x
  · rintro ⟨hl, hr, hm⟩ e x
    cases e with
    | inl e => exact union_valid P Q l r hl hr e x
    | inr st => exact hm st.1 st.2 x

/-- The alternative represents mixed words by a pair of homogeneous blocks. -/
def split {S T : Type} : List (S ⊕ T) → List S × List T
  | [] => ([], [])
  | .inl s :: w => (s :: (split w).1, (split w).2)
  | .inr t :: w => ((split w).1, t :: (split w).2)

def interpret {S T X : Type} (l : S → X → X) (r : T → X → X)
    (p : List S × List T) (x : X) : X := run l p.1 (run r p.2 x)

theorem normalize_sound {S T X : Type} (l : S → X → X) (r : T → X → X)
    (h : Interchange l r) (w : List (S ⊕ T)) (x : X) :
    run (Sum.elim l r) w x = interpret l r (split w) x := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a with
    | inl s => exact congrArg (l s) ih
    | inr t =>
      change r t (run (Sum.elim l r) w x) = run l (split w).1 (r t (run r (split w).2 x))
      rw [ih]
      exact (operation_word r l (fun t s x => (h s t x).symm) t (split w).1 _)

theorem run_append {S X : Type} (op : S → X → X) (a b : List S) (x : X) :
    run op (a ++ b) x = run op a (run op b x) := by
  induction a with
  | nil => rfl
  | cons s ss ih => exact congrArg (op s) ih

/-- Componentwise concatenation is correct because local operations commute. -/
theorem interpret_product {S T X : Type} (l : S → X → X) (r : T → X → X)
    (h : Interchange l r) (a b : List S × List T) (x : X) :
    interpret l r (a.1 ++ b.1, a.2 ++ b.2) x =
      interpret l r a (interpret l r b x) := by
  simp only [interpret, run_append]
  rw [word_word l r h b.1 a.2]

/-- The guarded interpretation and block representation agree on all words. -/
theorem comparison {S T X : Type} (l : S → X → X) (r : T → X → X)
    (h : Interchange l r) (w : List (S ⊕ T)) (ρ : Fin 1 → X) :
    (term w).eval (algebra (Sum.elim l r)) ρ = interpret l r (split w) (ρ 0) := by
  rw [eval_term, normalize_sound l r h]

end SquareKit.UnaryInteraction
