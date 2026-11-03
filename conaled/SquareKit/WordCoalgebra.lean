import Mathlib.Data.List.Basic

/-! Finite-word behavior is final for output/transition coalgebras. No algebra
on observations or bound on states is required. -/
namespace SquareKit.WordCoalgebra
universe u v w w'

abbrev B (A : Type u) (O : Type v) (X : Type w) := O × (A → X)
abbrev Coalgebra (A : Type u) (O : Type v) (X : Type w) := X → B A O X
abbrev Behavior (A : Type u) (O : Type v) := List A → O

variable {A : Type u} {O : Type v} {X : Type w} {Y : Type w'}

def run (c : Coalgebra A O X) (x : X) : Behavior A O
  | [] => (c x).1
  | a :: w => run c ((c x).2 a) w

def final : Coalgebra A O (Behavior A O) := fun f => (f [], fun a w => f (a :: w))

structure Morphism (c : Coalgebra A O X) (d : Coalgebra A O Y) (f : X → Y) : Prop where
  output : ∀ x, (d (f x)).1 = (c x).1
  next : ∀ x a, (d (f x)).2 a = f ((c x).2 a)

theorem run_morphism (c : Coalgebra A O X) : Morphism c final (run c) := ⟨fun _ => rfl, fun _ _ => rfl⟩

theorem unique (c : Coalgebra A O X) (f : X → Behavior A O)
    (h : Morphism c final f) : f = run c := by
  funext x w
  induction w generalizing x with
  | nil => exact h.output x
  | cons a w ih => exact (congrFun (h.next x a) w).trans (ih _)

/-- A direct semantic law package is a morphism into behavior. -/
theorem correct (c : Coalgebra A O X) (meaning : X → Behavior A O)
    (h : Morphism c final meaning) (x : X) (w : List A) :
    run c x w = meaning x w := congrFun (congrFun (unique c meaning h).symm x) w

def zip (c : Coalgebra A O X) (d : Coalgebra A O Y) (op : O → O → O) :
    Coalgebra A O (X × Y) := fun xy =>
  (op (c xy.1).1 (d xy.2).1, fun a => ((c xy.1).2 a, (d xy.2).2 a))

theorem run_zip (c : Coalgebra A O X) (d : Coalgebra A O Y) (op : O → O → O)
    (x : X) (y : Y) (w : List A) :
    run (zip c d op) (x,y) w = op (run c x w) (run d y w) := by
  induction w generalizing x y with
  | nil => rfl
  | cons a w ih => exact ih _ _

/-- An extra pointwise output operation leaves the old coalgebra available. -/
def mapOutput (c : Coalgebra A O X) (op : O → O) : Coalgebra A O X :=
  fun x => (op (c x).1, (c x).2)

theorem run_mapOutput (c : Coalgebra A O X) (op : O → O) (x : X) (w : List A) :
    run (mapOutput c op) x w = op (run c x w) := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih => exact ih _

inductive Trie (A : Type u) (O : Type v) : Nat → Type (max u v)
  | leaf : O → Trie A O 0
  | node {n} : O → (A → Trie A O n) → Trie A O (n+1)

def Trie.lookup : {n : Nat} → Trie A O n → List A → Option O
  | _, .leaf o, [] => some o
  | _, .leaf _, _ :: _ => none
  | _, .node o _, [] => some o
  | _, .node _ ts, a :: w => (ts a).lookup w

def unfold (c : Coalgebra A O X) (x : X) : (n : Nat) → Trie A O n
  | 0 => .leaf (c x).1
  | n+1 => .node (c x).1 (fun a => unfold c ((c x).2 a) n)

theorem lookup_unfold (c : Coalgebra A O X) (x : X) (w : List A)
    (n : Nat) (h : w.length ≤ n) : (unfold c x n).lookup w = some (run c x w) := by
  induction w generalizing x n with
  | nil => cases n <;> rfl
  | cons a w ih =>
    cases n with
    | zero => simp at h
    | succ n => exact ih _ n (Nat.le_of_succ_le_succ h)

def Trie.head : {n : Nat} → Trie A O n → O
  | _, .leaf o => o
  | _, .node o _ => o

def Trie.truncate : (n : Nat) → {m : Nat} → n ≤ m → Trie A O m → Trie A O n
  | 0, _, _, t => .leaf t.head
  | _+1, 0, h, _ => False.elim (Nat.not_succ_le_zero _ h)
  | n+1, _+1, h, .node o ts => .node o (fun a => (ts a).truncate n (Nat.le_of_succ_le_succ h))

theorem truncate_unfold (c : Coalgebra A O X) (x : X) (n m : Nat) (h : n ≤ m) :
    (unfold c x m).truncate n h = unfold c x n := by
  induction n generalizing x m with
  | zero => cases m <;> rfl
  | succ n ih =>
    cases m with
    | zero => simp at h
    | succ m =>
      simp only [unfold, Trie.truncate]
      congr 1
      funext a
      exact ih _ _ _
end SquareKit.WordCoalgebra
