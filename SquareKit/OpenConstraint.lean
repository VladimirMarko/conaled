import SquareKit.RelationalSemanticBoundary

/-! Open constraints retain all satisfying internal assignments. Hiding forgets
those assignments but retains exactly the extendable boundary pairs. -/
namespace SquareKit.OpenConstraint
universe u

structure Network (A B : Type u) where
  Internal : Type u
  accepts : A → Internal → B → Prop

def behavior {A B : Type u} (n : Network A B) : A → B → Prop :=
  fun a b => ∃ i, n.accepts a i b

def compose {A B C : Type u} (n : Network A B) (m : Network B C) : Network A C where
  Internal := n.Internal × B × m.Internal
  accepts a i c := n.accepts a i.1 i.2.1 ∧ m.accepts i.2.1 i.2.2 c

/-- Every intermediate boundary and internal solution is quantified. -/
theorem behavior_compose {A B C : Type u} (n : Network A B) (m : Network B C)
    (a : A) (c : C) :
    behavior (compose n m) a c ↔ ∃ b, behavior n a b ∧ behavior m b c := by
  constructor
  · rintro ⟨⟨i, b, j⟩, hn, hm⟩
    exact ⟨b, ⟨i, hn⟩, ⟨j, hm⟩⟩
  · rintro ⟨b, ⟨i, hn⟩, ⟨j, hm⟩⟩
    exact ⟨⟨i, b, j⟩, hn, hm⟩

def wire (A : Type u) : Network A A where
  Internal := PUnit
  accepts a _ b := a = b

theorem behavior_wire (A : Type u) (a b : A) : behavior (wire A) a b ↔ a = b := by
  simp [behavior, wire]

theorem behavior_assoc {A B C D : Type u}
    (n : Network A B) (m : Network B C) (p : Network C D) (a : A) (d : D) :
    behavior (compose (compose n m) p) a d ↔
      behavior (compose n (compose m p)) a d := by
  simp only [behavior_compose]
  constructor
  · rintro ⟨c, ⟨b, hn, hm⟩, hp⟩
    exact ⟨b, hn, c, hm, hp⟩
  · rintro ⟨b, hn, c, hm, hp⟩
    exact ⟨c, ⟨b, hn, hm⟩, hp⟩

theorem behavior_wire_left {A B : Type u} (n : Network A B) (a : A) (b : B) :
    behavior (compose (wire A) n) a b ↔ behavior n a b := by
  simp [behavior_compose, behavior_wire]

theorem behavior_wire_right {A B : Type u} (n : Network A B) (a : A) (b : B) :
    behavior (compose n (wire B)) a b ↔ behavior n a b := by
  simp only [behavior_compose, behavior_wire, exists_eq_right]

def renameBoundary {A B C D : Type u} (n : Network A B) (e : C ≃ A) (f : D ≃ B) :
    Network C D where
  Internal := n.Internal
  accepts c i d := n.accepts (e c) i (f d)

theorem behavior_renameBoundary {A B C D : Type u} (n : Network A B)
    (e : C ≃ A) (f : D ≃ B) (c : C) (d : D) :
    behavior (renameBoundary n e f) c d ↔ behavior n (e c) (f d) := Iff.rfl

/-- Renaming internal variables does not discard solutions. -/
def renameInternal {A B I : Type u} (n : Network A B) (e : I ≃ n.Internal) :
    Network A B where
  Internal := I
  accepts a i b := n.accepts a (e i) b

theorem behavior_renameInternal {A B I : Type u} (n : Network A B)
    (e : I ≃ n.Internal) (a : A) (b : B) :
    behavior (renameInternal n e) a b ↔ behavior n a b := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨e i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨e.symm i, by simpa [renameInternal] using hi⟩

/-- The incumbent exact-square presentation decodes a network to its full relation. -/
def representation (A B : Type u) : Squares.Rep where
  R := Network A B
  S := ULift.{u + 1} (A → B → Prop)
  decode n := ⟨behavior n⟩

def composeSquare (A B C : Type u) :
    Squares.Square (Squares.product (representation A B) (representation B C))
      (representation A C) where
  impl ns := compose ns.1 ns.2
  spec rs := ⟨fun a c => ∃ b, rs.1.down a b ∧ rs.2.down b c⟩
  commutes ns := by
    apply congrArg ULift.up
    funext a c
    exact propext (behavior_compose ns.1 ns.2 a c)

/-- Boundary feasibility does not determine whether there are distinct solutions. -/
def ambiguous {A B : Type u} (n : Network A B) (a : A) (b : B) : Prop :=
  ∃ i j, n.accepts a i b ∧ n.accepts a j b ∧ i ≠ j

def one : Network Unit Unit := ⟨Bool, fun _ i _ => i = false⟩
def two : Network Unit Unit := ⟨Bool, fun _ _ _ => True⟩
def inconsistent : Network Unit Unit := ⟨Bool, fun _ _ _ => False⟩

theorem same_behavior : behavior one = behavior two := by
  funext a b
  apply propext
  constructor
  · intro _; exact ⟨false, trivial⟩
  · intro _; exact ⟨false, rfl⟩

theorem one_unambiguous : ¬ ambiguous one () () := by
  rintro ⟨i, j, hi, hj, hne⟩
  exact hne (hi.trans hj.symm)

theorem two_ambiguous : ambiguous two () () :=
  ⟨false, true, trivial, trivial, Bool.false_ne_true⟩

theorem inconsistent_empty (a b : Unit) : ¬ behavior inconsistent a b := by
  rintro ⟨_, h⟩
  exact h

/-- No observer of the possibility relation alone can recover multiplicity. -/
theorem no_ambiguity_factor :
    ¬ ∃ observe : (Unit → Unit → Prop) → Prop,
      ∀ n : Network Unit Unit, observe (behavior n) ↔ ambiguous n () () := by
  rintro ⟨observe, h⟩
  have ht := (h two).mpr two_ambiguous
  rw [← same_behavior] at ht
  exact one_unambiguous ((h one).mp ht)

end SquareKit.OpenConstraint
