import SquareKit.Internal.InterpretationRoutes

/-! Checked branching, binders and failure of reflection for #119. -/
namespace Examples.BranchingGraphTransport
open SquareKit.Internal SquareKit.Internal.InterpretationRoutes
open Graph

def models : Pair Arrow NoRelations :=
  pair (model (fun n : Nat => n + 1) (fun n => 2 * n))
    (model (fun _ : Nat => 0) (fun n => n))

/-- The source proof yields z = 2(x+1) in the first component. -/
theorem first (x z : Nat) :
    (∃ y, y = x + 1 ∧ z = 2 * y) ↔ z = 2 * (x + 1) :=
  graph models Arrow.first Arrow.second false (environment _ _ x z)

/-- The very same derivations yield z = 0 in the other component. -/
theorem second (x z : Nat) : (∃ y, y = 0 ∧ z = y) ↔ z = 0 :=
  graph models Arrow.first Arrow.second true (environment _ _ x z)

/-- π₁ after swap uses the same source proof and the explicit route comparison. -/
theorem swapped_first (x z : Nat) :
    formula (reindex (swap models) (fun _ : Unit => true))
      (composite Arrow.first Arrow.second) () (environment _ _ x z) ↔
      z = 2 * (x + 1) := by
  have h : InterpretationRoutes.Valid (reindex models (fun _ : Unit => false))
      (composite Arrow.first Arrow.second) (result Arrow.first Arrow.second) :=
    preserve models _ (derivation models (Graph.forward Arrow.first Arrow.second))
  have k : InterpretationRoutes.Valid (reindex models (fun _ : Unit => false))
      (result Arrow.first Arrow.second) (composite Arrow.first Arrow.second) :=
    preserve models _ (derivation models (Graph.backward Arrow.first Arrow.second))
  rw [← first_via_swap] at h k
  exact ⟨h () (environment _ _ x z), k () (environment _ _ x z)⟩

/-- Duplicate the input variable in a larger context; existential substitution
must lift past the intermediate witness, leaving z in the final position. -/
def duplicate : Sub Arrow [.input, .output] [.input, .input, .output]
  | _, .zero => .var .zero
  | _, .succ .zero => .var (.succ (.succ .zero))

/-- An independently chosen expectation, 3 ↦ 4 ↦ 8, also exercises the binder. -/
theorem substituted_graph :
    formula (reindex (swap models) (fun _ : Unit => true))
      ((composite Arrow.first Arrow.second).subst duplicate) ()
      (fun {s} i => match s, i with
        | _, .zero => (3 : Nat)
        | _, .succ .zero => (99 : Nat)
        | _, .succ (.succ .zero) => (8 : Nat)) := by
  apply (substitution (swap models) (fun _ : Unit => true) _ duplicate () _).mpr
  exact (graph (swap models) Arrow.first Arrow.second true _).mpr rfl

/-- Empty input and intermediate carriers require no default witness. -/
def emptyModels : Pair Arrow NoRelations :=
  pair (model (C := Empty) (fun x : Empty => x) (fun x : Empty => nomatch x))
    (model (fun n : Nat => n + 1) (fun n => 2 * n))

theorem empty_graph :
    InterpretationRoutes.Valid emptyModels (result Arrow.first Arrow.second)
      (composite Arrow.first Arrow.second) :=
  derivation emptyModels (Graph.backward Arrow.first Arrow.second)

/-- The inhabited branch remains usable despite the other branch's empty context. -/
theorem inhabited_beside_empty :
    formula emptyModels (composite Arrow.first Arrow.second) true (environment _ _ 3 8) :=
  (graph emptyModels Arrow.first Arrow.second true (environment _ _ 3 8)).mpr rfl

/-- A closed existential observes the empty carrier without supplying an element. -/
def hasMiddle : Formula Arrow [] := .ex (s := .middle) (.eq (.var .zero) (.var .zero))

theorem empty_ex : ¬ formula emptyModels hasMiddle false (fun i => nomatch i) := by
  rintro ⟨x, _⟩
  exact nomatch x

theorem inhabited_ex : formula emptyModels hasMiddle true (fun i => nomatch i) :=
  (existential_route emptyModels id _ true _).mpr ⟨(0 : Nat), rfl⟩

/-- Two paired arrows 1 → (1, Bool) differ only in their second component. -/
def codomain : Bool → Type | false => Unit | true => Bool

def arrow₀ : ∀ b, Unit → codomain b | false => fun _ => () | true => fun _ => false

def arrow₁ : ∀ b, Unit → codomain b | false => fun _ => () | true => fun _ => true

theorem projection_does_not_reflect : arrow₀ false = arrow₁ false ∧ arrow₀ ≠ arrow₁ := by
  constructor
  · rfl
  · intro h
    have bad : false = true := congrFun (congrFun h true) ()
    cases bad

theorem both_detect {f g : ∀ b, Unit → codomain b}
    (h₀ : f false = g false) (h₁ : f true = g true) : f = g :=
  joint_reflection f g h₀ h₁

/-- Route selection also preserves the existing square/map comparison seam;
there is no second implementation of square composition. -/
theorem square_comparison (A B C : Bool → Squares.Rep)
    (g : ∀ b, Squares.Square (B b) (C b)) (f : ∀ b, Squares.Square (A b) (B b))
    (b : Bool) :
    Relational.ofSquare (Squares.compose (g b) (f b)) =
      Relational.compose (Relational.ofSquare (g b)) (Relational.ofSquare (f b)) :=
  Graph.horizontal_comparison (g b) (f b)
end Examples.BranchingGraphTransport
