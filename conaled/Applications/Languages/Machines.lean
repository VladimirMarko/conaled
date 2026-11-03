import Applications.Languages.Regex

/-!
# Automatic derivatives as productive observations of a state coalgebra

Lean's inductive kernel does not accept unrestricted coinductive definitions.
A machine supplies a nullable observation and a next-state operation. Its
finite trie observations are obtained by recursion on an explicit depth, and
the correctness theorem covers every finite word. No termination overrides,
partial definitions, or assumed bisimulation principles are used.
-/

namespace LanguageDerivatives

universe u
variable {α State : Type u}

structure Machine (α State : Type u) where
  nullable : State → Bool
  next : State → α → State

def Machine.run (m : Machine α State) (s : State) : List α → Bool
  | [] => m.nullable s
  | a :: w => m.run (m.next s a) w

/-- Exactly the two local obligations of an automatic language implementation. -/
structure Machine.Correct (m : Machine α State) (meaning : State → Language α) : Prop where
  nullable : ∀ s, m.nullable s = true ↔ [] ∈ meaning s
  next : ∀ s a, meaning (m.next s a) = residual a (meaning s)

theorem Machine.run_correct {m : Machine α State} {meaning : State → Language α}
    (h : m.Correct meaning) (s : State) (w : List α) :
    m.run s w = true ↔ w ∈ meaning s := by
  induction w generalizing s with
  | nil => exact h.nullable s
  | cons a w ih =>
    rw [Machine.run, ih, h.next]
    rfl

def regexMachine [DecidableEq α] : Machine α (Regex α) where
  nullable := RegularExpression.matchEpsilon
  next := derive

theorem regexMachine_correct [DecidableEq α] :
    regexMachine.Correct (RegularExpression.matches' (α := α)) where
  nullable := nullable_correct
  next := derive_correct

/-- Product state spaces implement language intersection directly. -/
def Machine.intersection {S T : Type u} (m : Machine α S) (n : Machine α T) :
    Machine α (S × T) where
  nullable := fun st => m.nullable st.1 && n.nullable st.2
  next := fun st a => (m.next st.1 a, n.next st.2 a)

theorem Machine.intersection_correct {S T : Type u}
    {m : Machine α S} {n : Machine α T}
    {M : S → Language α} {N : T → Language α}
    (hm : m.Correct M) (hn : n.Correct N) :
    (m.intersection n).Correct (fun st => {w | w ∈ M st.1 ∧ w ∈ N st.2}) where
  nullable := by
    intro st
    change (m.nullable st.1 && n.nullable st.2) = true ↔
      ([] ∈ M st.1 ∧ [] ∈ N st.2)
    rw [Bool.and_eq_true, hm.nullable, hn.nullable]
  next := by
    intro st a
    apply Language.ext; intro w
    change (w ∈ M (m.next st.1 a) ∧ w ∈ N (n.next st.2 a)) ↔
      (a :: w ∈ M st.1 ∧ a :: w ∈ N st.2)
    rw [hm.next, hn.next]
    rfl

/-- A depth-indexed trie is an ordinary inductive type with bounded observations. -/
inductive Trie (α : Type u) : ℕ → Type u
  | leaf : Bool → Trie α 0
  | node {n : ℕ} : Bool → (α → Trie α n) → Trie α (n + 1)

def Trie.lookup : {n : ℕ} → Trie α n → List α → Option Bool
  | _, .leaf b, [] => some b
  | _, .leaf _, _ :: _ => none
  | _, .node b _, [] => some b
  | _, .node _ children, a :: w => (children a).lookup w

def Machine.unfold (m : Machine α State) (s : State) : (n : ℕ) → Trie α n
  | 0 => .leaf (m.nullable s)
  | n + 1 => .node (m.nullable s) (fun a => m.unfold (m.next s a) n)

theorem Machine.lookup_unfold (m : Machine α State) (s : State)
    (w : List α) (n : ℕ) (h : w.length ≤ n) :
    (m.unfold s n).lookup w = some (m.run s w) := by
  induction w generalizing s n with
  | nil => cases n <;> rfl
  | cons a w ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at h
      exact ih (m.next s a) n h

@[reducible] def boundedRep (α : Type u) (n : ℕ) : Squares.Rep.{u} where
  R := Trie α n
  S := {w : List α // w.length ≤ n} → Prop
  decode := fun t w => t.lookup w.1 = some true

/-- The source square certifies unfolding a symbolic machine into an automatic trie. -/
def snapshotSquare [DecidableEq α] (n : ℕ) :
    Squares.Square (rep α) (boundedRep α n) where
  impl := fun p => regexMachine.unfold p n
  spec := fun L w => w.1 ∈ L
  commutes := by
    intro p
    funext w
    apply propext
    change (regexMachine.unfold p n).lookup w.1 = some true ↔ w.1 ∈ p.matches'
    rw [Machine.lookup_unfold _ _ _ _ w.2, Option.some.injEq]
    exact Machine.run_correct regexMachine_correct p w.1

theorem snapshot_recognizes [DecidableEq α] (p : Regex α) (w : List α)
    (n : ℕ) (h : w.length ≤ n) :
    ((snapshotSquare n).impl p).lookup w = some true ↔ w ∈ p.matches' := by
  change (regexMachine.unfold p n).lookup w = some true ↔ w ∈ p.matches'
  rw [Machine.lookup_unfold _ _ _ _ h, Option.some.injEq]
  exact Machine.run_correct regexMachine_correct p w

example : (regexMachine.unfold sample 5).lookup "aabab".toList = some true := by decide
example : (regexMachine.unfold sample 4).lookup "aabab".toList = none := by decide

end LanguageDerivatives
