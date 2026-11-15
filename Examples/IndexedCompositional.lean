import SquareKit.EquationComposition

/-! Independent finite vectors: construction changes length, observation decreases
it, and compound substitution reuses the shared indexed compatibility theorem. -/
namespace IndexedCompositionalExamples
open SquareKit.IndexedCompositional
namespace Vectors

inductive Op : Nat → Type
  | nil : Op 0
  | cons (n value : Nat) : Op (n+1)
  | double (n : Nat) : Op n

abbrev signature : Signature Nat where
  Op := Op
  arity | .nil => 0 | .cons _ _ => 1 | .double _ => 1
  child | .nil, k => Fin.elim0 k | .cons n _, _ => n | .double n, _ => n

abbrev behavior : Behavior Nat where
  Output | 0 => Unit | _+1 => Nat
  Request | 0 => Empty | _+1 => Unit
  next | 0, r => nomatch r | n+1, _ => n

abbrev Vec (n : Nat) := Fin n → Nat

def native : behavior.Coalgebra Vec
  | 0, _ => ((), fun r => nomatch r)
  | _n+1, v => (v 0, fun _ k => v k.succ)

def algebra : {n : Nat} → (op : signature.Op n) → (∀ k, Vec (signature.child op k)) → Vec n
  | _, .nil, _ => fun k => Fin.elim0 k
  | _, .cons _ a, xs => Fin.cases a (xs 0)
  | _, .double _, xs => fun k => 2 * xs 0 k

/-- The source equation vocabulary exposes outputs and finite templates only. -/
inductive Prim : Type → Type → Type 1
  | literal {A : Type} (value : A) : Prim PUnit A
  | child {n} (op : Op n) (k : Fin (signature.arity op)) :
      Prim (ULift (SquareKit.EquationComposition.Outputs signature behavior op))
        (ULift (behavior.Output (signature.child op k)))
  | twice : Prim (ULift Nat) (ULift Nat)

def primitiveMeaning : Prim A B → A → B
  | .literal value, _ => value
  | .child _ k, xs => ⟨xs.down k⟩
  | .twice, x => ⟨2 * x.down⟩

/-- Author each output/next cell once; rows and local rules are generated from it. -/
def equations : SquareKit.EquationTranspose.DataProgram
    (SquareKit.EquationComposition.signature signature behavior) Prim where
  body p obs _ := match obs with
    | .output => match p with
      | ⟨_, .nil⟩ => .prim (.literal ⟨()⟩) (.var .second)
      | ⟨_, .cons _ a⟩ => .prim (.literal ⟨a⟩) (.var .second)
      | ⟨_, .double 0⟩ => .prim (.literal ⟨()⟩) (.var .second)
      | ⟨_, .double (n+1)⟩ => .prim .twice (.prim (.child (.double (n+1)) 0) (.var .first))
    | .next r => match p with
      | ⟨_, .nil⟩ => nomatch r
      | ⟨_, .cons _ _⟩ => .prim (.literal ⟨.leaf (.ret 0)⟩) (.var .second)
      | ⟨_, .double 0⟩ => nomatch r
      | ⟨_, .double (n+1)⟩ =>
          .prim (.literal ⟨.node (.double n) (fun _ => .leaf (.succ 0 ()))⟩) (.var .second)

def rule : Rule signature behavior :=
  SquareKit.EquationComposition.compile equations primitiveMeaning

theorem compatible : rule.Compatible algebra native where
  output n op xs := by
    cases op with
    | nil => rfl
    | cons n a => rfl
    | double n => cases n <;> rfl
  next n op xs a := by
    cases op with
    | nil => exact nomatch a
    | cons n v => rfl
    | double n => cases n with
      | zero => exact nomatch a
      | succ n => rfl

/-- All finite vector coordinates, exposing the indexed morphism as a direct API. -/
def read {X : Nat → Type u} (c : behavior.Coalgebra X) :
    {n : Nat} → X n → Fin n → Nat
  | 0, _, k => Fin.elim0 k
  | _n+1, x, k => Fin.cases (c _ x).1 (fun j => read c ((c _ x).2 ()) j) k

theorem read_morphism {X : Nat → Type u} {Y : Nat → Type v}
    (c : behavior.Coalgebra X) (d : behavior.Coalgebra Y)
    (f : ∀ n, X n → Y n) (h : behavior.Morphism c d f)
    {n : Nat} (x : X n) (k : Fin n) : read d (f n x) k = read c x k := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) k
    · exact h.output _ _
    · change read d ((d _ (f _ x)).2 ()) j = read c ((c _ x).2 ()) j
      rw [h.next]; exact ih _ j

theorem read_native {n} (v : Vec n) (k : Fin n) : read native v k = v k := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    refine Fin.cases rfl (fun j => ?_) k
    exact ih _ j

def meaning {n} (t : Term signature Vec n) : Vec n := Term.fold algebra (fun _ x => x) t

theorem correct {n} (t : Term signature Vec n) (k : Fin n) :
    read (rule.lift native) t k = meaning t k := by
  have h := rule.fold_morphism algebra native compatible native (fun _ x => x)
    ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  exact (read_morphism _ _ _ h t k).symm.trans (read_native _ _)

def cons {X : Nat → Type u} {n} (a : Nat) (t : Term signature X n) : Term signature X (n+1) :=
  .node (.cons n a) (fun _ => t)
def nil {X : Nat → Type u} : Term signature X 0 := .node .nil (fun k => Fin.elim0 k)
def double {X : Nat → Type u} {n} (t : Term signature X n) : Term signature X n :=
  .node (.double n) (fun _ => t)

example : read (rule.lift native) (cons 7 (cons 11 nil)) 0 = 7 := by rw [correct]; rfl
example : read (rule.lift native) (cons 7 (cons 11 nil)) 1 = 11 := by rw [correct]; rfl
example : read (rule.lift native) (double (cons 7 (cons 11 nil))) 1 = 22 := by rw [correct]; rfl
example : read (rule.lift native) (cons 7 (double (cons 11 nil))) 0 = 7 := by rw [correct]; rfl
example : read (rule.lift native) (cons 7 nil) 0 = 7 := by rw [correct]; rfl
example (r : behavior.Request 0) : False := nomatch r
example (k : Fin 0) : False := Fin.elim0 k

abbrev NoLeaves (_ : Nat) := Empty
def emptyCoalgebra : behavior.Coalgebra NoLeaves := fun _ x => nomatch x

/-- Replacing each leaf by its complete, possibly compound, cons syntax. -/
def expand : (n : Nat) → Vec n → Term signature NoLeaves n
  | 0, _ => nil
  | n+1, v => cons (v 0) (expand n (fun k => v k.succ))

theorem expand_morphism : behavior.Morphism native (rule.lift emptyCoalgebra) expand where
  output n v := by cases n <;> rfl
  next n v r := by cases n with
    | zero => exact nomatch r
    | succ n => rfl

theorem substituted {n} (t : Term signature Vec n) (k : Fin n) :
    read (rule.lift emptyCoalgebra) (Term.bind expand t) k = read (rule.lift native) t k :=
  read_morphism _ _ _ (rule.bind_morphism native emptyCoalgebra expand expand_morphism) t k

example : read (rule.lift emptyCoalgebra)
    (Term.bind expand (cons 3 (.leaf (Fin.cases 7 (fun _ : Fin 1 => 11))))) 2 = 11 := by
  rw [substituted, correct]; rfl

/-- A natural, correctly indexed rule can still compute the wrong meaning. -/
def wrong : Rule signature behavior := { rule with
  out := fun {j} op => by
    cases op with
    | nil => exact fun _ => ()
    | cons n a => exact fun _ => a+1
    | double => exact rule.out (.double j) }

theorem wrong_natural {X : Nat → Type u} {Y : Nat → Type v} (f : ∀ n, X n → Y n)
    {n} (op : signature.Op n) (xs : ∀ k, X (signature.child op k))
    (bs : ∀ k, behavior.Layer X (signature.child op k)) :
    wrong.layer op (fun k => f _ (xs k)) (fun k => behavior.map f (bs k)) =
      behavior.map (fun _ => Term.map f) (wrong.layer op xs bs) := wrong.layer_natural f op xs bs

theorem wrong_incompatible : ¬ wrong.Compatible algebra native := by
  intro h
  have bad := h.output 1 (.cons 0 7) (fun _ k => Fin.elim0 k)
  change 7 = 8 at bad
  cases bad
end Vectors
end IndexedCompositionalExamples
