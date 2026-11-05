import SquareKit.WordCoalgebra
import SquareKit.FinitaryTerm

/-! Finitary derivative templates retain original arguments and their successors.
Local semantic compatibility yields correctness for arbitrary finite terms.
This is a restricted rule format, not a general distributive-law library. -/
namespace SquareKit.CompositionalCoalgebra
open WordCoalgebra
universe u v w z d a o

abbrev Term (Op : Type u) (arity : Op → Nat) (X : Type v) := FinitaryTerm Op arity X

variable {Op : Type u} {X : Type v} {Y : Type w} {Z : Type z}
  {D : Type d} {A : Type a} {O : Type o} {arity : Op → Nat}

/-- Any coalgebra morphism preserves every finite-word observation. -/
theorem run_transport (c : Coalgebra A O X) (d : Coalgebra A O Y)
    (f : X → Y) (h : Morphism c d f) (x : X) (word : List A) :
    run d (f x) word = run c x word := by
  induction word generalizing x with
  | nil => exact h.output x
  | cons a word ih =>
    change run d ((d (f x)).2 a) word = _
    rw [h.next]; exact ih _

namespace Term

@[match_pattern] abbrev leaf (x : X) : Term Op arity X := FinitaryTerm.leaf x
@[match_pattern] abbrev node (op : Op) (ts : Fin (arity op) → Term Op arity X) :
    Term Op arity X := FinitaryTerm.node op ts

abbrev bind (f : X → Term Op arity Y) : Term Op arity X → Term Op arity Y := FinitaryTerm.bind f
abbrev map (f : X → Y) : Term Op arity X → Term Op arity Y := FinitaryTerm.map f
abbrev fold (alg : (op : Op) → (Fin (arity op) → D) → D) (f : X → D) :
    Term Op arity X → D := FinitaryTerm.fold alg f

@[simp] theorem bind_leaf (t : Term Op arity X) : bind leaf t = t := FinitaryTerm.bind_leaf t

theorem bind_assoc (t : Term Op arity X) (f : X → Term Op arity Y)
    (g : Y → Term Op arity Z) : bind g (bind f t) = bind (fun x => bind g (f x)) t :=
  FinitaryTerm.bind_assoc t f g

theorem fold_bind (alg : (op : Op) → (Fin (arity op) → D) → D)
    (f : X → Term Op arity Y) (g : Y → D) (t : Term Op arity X) :
    fold alg g (bind f t) = fold alg (fun x => fold alg g (f x)) t :=
  FinitaryTerm.fold_bind alg f g t

theorem fold_node (f : X → Term Op arity Y) (t : Term Op arity X) :
    fold Term.node f t = bind f t := FinitaryTerm.fold_node f t

end Term

/-- Left slots retain arguments; right slots name their successors at the input letter.
Templates can inspect outputs and the letter, but cannot inspect state representations. -/
structure Rule (Op : Type u) (arity : Op → Nat) (A : Type a) (O : Type o) where
  out : (op : Op) → (Fin (arity op) → O) → O
  step : (op : Op) → (Fin (arity op) → O) → A →
    Term Op arity (Fin (arity op) ⊕ Fin (arity op))

namespace Rule
variable (r : Rule Op arity A O)

def layer (op : Op) (xs : Fin (arity op) → X × B A O X) : B A O (Term Op arity X) :=
  (r.out op (fun i => (xs i).2.1), fun a =>
    (r.step op (fun i => (xs i).2.1) a).map
      (Sum.elim (fun i => (xs i).1) (fun i => (xs i).2.2 a)))

/-- Naturality of the one-layer rule, with both retained states and successors mapped. -/
theorem layer_natural (f : X → Y) (op : Op) (xs : Fin (arity op) → X × B A O X) :
    r.layer op (fun i => (f (xs i).1, (xs i).2.1, fun a => f ((xs i).2.2 a))) =
      ((r.layer op xs).1, fun a => Term.map f ((r.layer op xs).2 a)) := by
  apply Prod.ext
  · rfl
  · funext a
    simp only [layer, Term.map, FinitaryTerm.map, FinitaryTerm.bind, FinitaryTerm.bind_assoc, Function.comp_def, Term.bind]
    congr 1
    funext s; cases s <;> rfl

def output (c : Coalgebra A O X) : Term Op arity X → O
  | .leaf x => (c x).1
  | .node op ts => r.out op (fun i => output c (ts i))

def next (c : Coalgebra A O X) : Term Op arity X → A → Term Op arity X
  | .leaf x, a => .leaf ((c x).2 a)
  | .node op ts, a => Term.bind (Sum.elim ts (fun i => next c (ts i) a))
      (r.step op (fun i => r.output c (ts i)) a)

def lift (c : Coalgebra A O X) : Coalgebra A O (Term Op arity X) :=
  fun t => (r.output c t, r.next c t)

/-- Constructor laws only: no premise quantifies over composite syntax. -/
structure Compatible (alg : (op : Op) → (Fin (arity op) → D) → D)
    (d : Coalgebra A O D) : Prop where
  output : ∀ op xs, (d (alg op xs)).1 = r.out op (fun i => (d (xs i)).1)
  next : ∀ op xs a, (d (alg op xs)).2 a =
    Term.fold alg (Sum.elim xs (fun i => (d (xs i)).2 a))
      (r.step op (fun i => (d (xs i)).1) a)

/-- Local constructor laws extend a leaf interpretation to all finite composite terms. -/
theorem fold_morphism (alg : (op : Op) → (Fin (arity op) → D) → D)
    (d : Coalgebra A O D) (hc : r.Compatible alg d)
    (c : Coalgebra A O X) (f : X → D) (hf : Morphism c d f) :
    Morphism (r.lift c) d (Term.fold alg f) := by
  have ho : ∀ t, (d (Term.fold alg f t)).1 = r.output c t := by
    intro t
    induction t with
    | leaf x => exact hf.output x
    | node op ts ih =>
      simp only [Term.fold, FinitaryTerm.fold, output]
      rw [hc.output]
      congr 1; funext i; exact ih i
  refine ⟨ho, ?_⟩
  intro t a
  change (d (Term.fold alg f t)).2 a = Term.fold alg f (r.next c t a)
  induction t with
  | leaf x => exact hf.next x a
  | node op ts ih =>
    simp only [Term.fold, FinitaryTerm.fold, next, Term.fold_bind]
    rw [hc.next]
    have he : (fun i => (d (Term.fold alg f (ts i))).1) = (fun i => r.output c (ts i)) :=
      funext (fun i => ho (ts i))
    rw [he]
    congr 1
    funext s; cases s with
    | inl i => rfl
    | inr i => exact ih i

/-- The lifted coalgebra itself satisfies the local template equations. -/
theorem compatible_lift (c : Coalgebra A O X) : r.Compatible Term.node (r.lift c) where
  output _ _ := rfl
  next op xs a := by rw [Term.fold_node]; rfl

/-- Substitution is compatible whenever each substituted term respects the leaf behavior. -/
theorem bind_morphism (c : Coalgebra A O X) (d : Coalgebra A O Y)
    (f : X → Term Op arity Y) (hf : Morphism c (r.lift d) f) :
    Morphism (r.lift c) (r.lift d) (Term.bind f) := by
  have h := r.fold_morphism Term.node (r.lift d) (r.compatible_lift d) c f hf
  have he : Term.fold Term.node f = Term.bind f := funext (Term.fold_node f)
  rw [he] at h
  exact h

theorem leaf_morphism (c : Coalgebra A O X) : Morphism c (r.lift c) Term.leaf :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- Monad multiplication is a coalgebra morphism; no fresh constructor proof is needed. -/
theorem join_morphism (c : Coalgebra A O X) :
    Morphism (r.lift (r.lift c)) (r.lift c) (Term.bind id) :=
  r.bind_morphism (r.lift c) c id ⟨fun _ => rfl, fun _ _ => rfl⟩

theorem map_morphism (c : Coalgebra A O X) (d : Coalgebra A O Y)
    (f : X → Y) (hf : Morphism c d f) :
    Morphism (r.lift c) (r.lift d) (Term.map f) :=
  r.bind_morphism c d (Term.leaf ∘ f)
    ⟨hf.output, fun x a => congrArg Term.leaf (hf.next x a)⟩

/-- Final finite-word behavior turns the composite morphism into denotational correctness. -/
theorem run_fold (alg : (op : Op) → (Fin (arity op) → Behavior A O) → Behavior A O)
    (hc : r.Compatible alg final) (c : Coalgebra A O X)
    (f : X → Behavior A O) (hf : Morphism c final f)
    (t : Term Op arity X) (w : List A) :
    run (r.lift c) t w = Term.fold alg f t w :=
  correct _ _ (r.fold_morphism alg final hc c f hf) t w
end Rule
end SquareKit.CompositionalCoalgebra
