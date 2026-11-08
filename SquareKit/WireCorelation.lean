import SquareKit.OpenConstraint

/-! Equality-wire cospans and their exact boundary black box. This is the
undecorated equality fragment, not arbitrary decorated corelations. -/
namespace SquareKit.WireCorelation
universe u

structure Cospan (A B : Type u) where
  Node : Type u
  left : A → Node
  right : B → Node

def boundary {A B : Type u} (n : Cospan A B) : A ⊕ B → n.Node :=
  Sum.elim n.left n.right

def network {A B V : Type u} (n : Cospan A B) :
    OpenConstraint.Network (A → V) (B → V) where
  Internal := n.Node → V
  accepts a v b := (∀ x, v (n.left x) = a x) ∧ (∀ y, v (n.right y) = b y)

/-- A boundary coloring is constant on each block of the kernel corelation. -/
def compatible {A B V : Type u} (n : Cospan A B) (a : A → V) (b : B → V) : Prop :=
  ∀ x y, boundary n x = boundary n y → Sum.elim a b x = Sum.elim a b y

/-- Unobserved nodes need a value. With a nonempty value domain, the kernel
partition determines exactly all extendable assignments. -/
theorem exact_blackbox {A B V : Type u} [Nonempty V] (n : Cospan A B)
    (a : A → V) (b : B → V) :
    OpenConstraint.behavior (network n) a b ↔ compatible n a b := by
  classical
  constructor
  · rintro ⟨v, ha, hb⟩ x y h
    have hv : ∀ z, v (boundary n z) = Sum.elim a b z := by
      intro z; cases z with
      | inl x => exact ha x
      | inr y => exact hb y
    rw [← hv x, ← hv y, h]
  · intro h
    let v : n.Node → V := fun z =>
      if hz : ∃ x, boundary n x = z then Sum.elim a b hz.choose else Classical.choice inferInstance
    have hv (x : A ⊕ B) : v (boundary n x) = Sum.elim a b x := by
      dsimp [v]
      split
      next hz => exact h hz.choose x hz.choose_spec
      next hz => exact False.elim (hz ⟨x, rfl⟩)
    exact ⟨v, (fun x => hv (.inl x)), (fun y => hv (.inr y))⟩

/-- The epi-image removes exactly the nodes absent from the boundary. -/
def reduce {A B : Type u} (n : Cospan A B) : Cospan A B where
  Node := {z : n.Node // ∃ x, boundary n x = z}
  left a := ⟨n.left a, ⟨.inl a, rfl⟩⟩
  right b := ⟨n.right b, ⟨.inr b, rfl⟩⟩

@[simp] theorem boundary_reduce_val {A B : Type u} (n : Cospan A B) (x : A ⊕ B) :
    (boundary (reduce n) x).val = boundary n x := by cases x <;> rfl

theorem reduce_surjective {A B : Type u} (n : Cospan A B) :
    Function.Surjective (boundary (reduce n)) := by
  rintro ⟨z, x, hx⟩
  exact ⟨x, Subtype.ext (by simpa using hx)⟩

theorem compatible_reduce {A B V : Type u} (n : Cospan A B) (a : A → V) (b : B → V) :
    compatible (reduce n) a b ↔ compatible n a b := by
  constructor
  · intro h x y he
    exact h x y (Subtype.ext (by simpa using he))
  · intro h x y he
    exact h x y (by simpa using congrArg Subtype.val he)

theorem behavior_reduce {A B V : Type u} [Nonempty V] (n : Cospan A B)
    (a : A → V) (b : B → V) :
    OpenConstraint.behavior (network (reduce n)) a b ↔
      OpenConstraint.behavior (network n) a b := by
  rw [exact_blackbox, exact_blackbox, compatible_reduce]

/-- The pushout relation identifies the two copies of every glued boundary. -/
inductive Join {A B C : Type u} (n : Cospan A B) (m : Cospan B C) :
    n.Node ⊕ m.Node → n.Node ⊕ m.Node → Prop where
  | glue (b : B) : Join n m (.inl (n.right b)) (.inr (m.left b))

def compose {A B C : Type u} (n : Cospan A B) (m : Cospan B C) : Cospan A C where
  Node := Quot (Join n m)
  left a := Quot.mk _ (.inl (n.left a))
  right c := Quot.mk _ (.inr (m.right c))

/-- Explicit pushout elimination, with the only local gluing obligation. -/
def descend {A B C V : Type u} (n : Cospan A B) (m : Cospan B C)
    (v : n.Node → V) (w : m.Node → V) (h : ∀ b, v (n.right b) = w (m.left b)) :
    (compose n m).Node → V :=
  Quot.lift (Sum.elim v w) (by intro x y r; cases r with | glue b => exact h b)

/-- Uniqueness on the quotient follows from both coprojections. -/
theorem descend_unique {A B C V : Type u} (n : Cospan A B) (m : Cospan B C)
    (v : n.Node → V) (w : m.Node → V) (h : ∀ b, v (n.right b) = w (m.left b))
    (f : (compose n m).Node → V)
    (hl : ∀ x, f (Quot.mk _ (.inl x)) = v x)
    (hr : ∀ y, f (Quot.mk _ (.inr y)) = w y) : f = descend n m v w h := by
  funext z
  induction z using Quot.ind with
  | _ z => cases z with
    | inl x => exact hl x
    | inr y => exact hr y

/-- Quotient elimination constructs the joint assignment. No global black-box
preservation law is an input. -/
theorem behavior_compose {A B C V : Type u} (n : Cospan A B) (m : Cospan B C)
    (a : A → V) (c : C → V) :
    OpenConstraint.behavior (network (compose n m)) a c ↔
      ∃ b, OpenConstraint.behavior (network n) a b ∧
        OpenConstraint.behavior (network m) b c := by
  constructor
  · rintro ⟨v, ha, hc⟩
    refine ⟨fun b => v (Quot.mk _ (.inl (n.right b))), ?_, ?_⟩
    · exact ⟨fun x => v (Quot.mk _ (.inl x)), ha, fun _ => rfl⟩
    · refine ⟨fun y => v (Quot.mk _ (.inr y)), ?_, hc⟩
      intro b
      exact congrArg v (Quot.sound (Join.glue b)).symm
  · rintro ⟨b, ⟨v, ha, hb⟩, ⟨w, hb', hc⟩⟩
    let f := descend n m v w (fun b => (hb b).trans (hb' b).symm)
    exact ⟨f, ha, hc⟩

/-- Corelation composition takes the image after the pushout. -/
theorem reduced_composition {A B C V : Type u} [Nonempty V]
    (n : Cospan A B) (m : Cospan B C) (a : A → V) (c : C → V) :
    OpenConstraint.behavior (network (reduce (compose (reduce n) (reduce m)))) a c ↔
      OpenConstraint.behavior (OpenConstraint.compose (network n) (network m)) a c := by
  rw [behavior_reduce, behavior_compose, OpenConstraint.behavior_compose]
  simp only [behavior_reduce]

end SquareKit.WireCorelation
