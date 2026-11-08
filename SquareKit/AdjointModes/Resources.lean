import Mathlib.Logic.Equiv.Defs
import Lean.Elab.Tactic.Omega

/-! A resource-sensitive shift model: sets embed as objects concentrated in
resource degree zero; the right adjoint takes the zero fiber. -/
namespace SquareKit.AdjointModes

inductive Mode where | linear | unrestricted
  deriving DecidableEq

/-- A conclusion at `k` can depend on a hypothesis at `m`. -/
def Above (m k : Mode) : Prop := m = .unrestricted ∨ k = .linear

inductive Permission where | weaken | contract
  deriving DecidableEq

def permits (m : Mode) (_ : Permission) : Prop := m = .unrestricted

theorem above_refl (m : Mode) : Above m m := by cases m <;> simp [Above]
theorem above_trans {m k j} (h : Above m k) (h' : Above k j) : Above m j := by
  cases m <;> cases k <;> cases j <;> simp_all [Above]
theorem permissions_monotone {m k} (h : Above m k) (p : Permission) :
    permits k p → permits m p := by cases m <;> cases k <;> simp_all [Above, permits]

def PolicyValid (order : Mode → Mode → Prop) (permission : Mode → Permission → Prop) : Prop :=
  ∀ m k, order m k → ∀ p, permission k p → permission m p

theorem reverse_order_invalid : ¬PolicyValid (fun _ _ => True) permits := by
  intro h
  have := h .linear .unrestricted trivial .contract rfl
  cases this

/-- The independence test rejects promotion of a linear dependency to U. -/
theorem no_linear_dependency : ¬Above .linear .unrestricted := by simp [Above]

structure Resource where
  Carrier : Type
  degree : Carrier → Nat

structure Map (A B : Resource) where
  run : A.Carrier → B.Carrier
  preserves : ∀ x, B.degree (run x) = A.degree x

namespace Map
@[ext] theorem ext {A B} {f g : Map A B} (h : ∀ x, f.run x = g.run x) : f = g := by
  cases f; cases g; congr; exact funext h
def identity (A) : Map A A := ⟨id, fun _ => rfl⟩
def comp {A B C} (g : Map B C) (f : Map A B) : Map A C :=
  ⟨g.run ∘ f.run, fun x => (g.preserves _).trans (f.preserves x)⟩
theorem comp_assoc {A B C D} (h : Map C D) (g : Map B C) (f : Map A B) :
    h.comp (g.comp f) = (h.comp g).comp f := rfl
theorem identity_comp {A B} (f : Map A B) : (identity B).comp f = f := by ext; rfl
theorem comp_identity {A B} (f : Map A B) : f.comp (identity A) = f := by ext; rfl
end Map

def tensor (A B : Resource) : Resource :=
  ⟨A.Carrier × B.Carrier, fun x => A.degree x.1 + B.degree x.2⟩
def one : Resource := ⟨Unit, fun _ => 0⟩
def down (X : Type) : Resource := ⟨X, fun _ => 0⟩
def up (A : Resource) : Type := {x : A.Carrier // A.degree x = 0}

def downMap {X Y : Type} (f : X → Y) : Map (down X) (down Y) := ⟨f, fun _ => rfl⟩
def upMap {A B} (f : Map A B) : up A → up B :=
  fun x => ⟨f.run x.val, (f.preserves _).trans x.property⟩

/-- The actual hom-set adjunction, not just maps in opposite directions. -/
def shiftAdjunction (X : Type) (A : Resource) : Map (down X) A ≃ (X → up A) where
  toFun f x := ⟨f.run x, f.preserves x⟩
  invFun f := ⟨fun x => (f x).val, fun x => (f x).property⟩
  left_inv _ := by ext; rfl
  right_inv _ := rfl

theorem shift_natural_left {X Y : Type} {A} (f : X → Y) (g : Map (down Y) A) :
    shiftAdjunction X A (g.comp (downMap f)) = shiftAdjunction Y A g ∘ f := rfl

theorem shift_natural_right {X : Type} {A B} (f : Map (down X) A) (g : Map A B) :
    shiftAdjunction X B (g.comp f) = upMap g ∘ shiftAdjunction X A f := rfl

def unit (X : Type) : X → up (down X) := fun x => ⟨x, rfl⟩
def counit (A : Resource) : Map (down (up A)) A := ⟨Subtype.val, Subtype.property⟩
theorem triangle_down (X : Type) : (counit (down X)).comp (downMap (unit X)) =
    Map.identity (down X) := by ext; rfl
theorem triangle_up (A : Resource) : upMap (counit A) ∘ unit (up A) = id := rfl

def atom : Resource := ⟨Nat, fun _ => 1⟩

theorem atom_no_copy : ¬Nonempty (Map atom (tensor atom atom)) := by
  rintro ⟨f⟩
  have h := f.preserves (0 : Nat)
  change 1 + 1 = 1 at h
  omega

theorem atom_no_discard : ¬Nonempty (Map atom one) := by
  rintro ⟨f⟩
  have h := f.preserves (0 : Nat)
  change 0 = 1 at h
  omega

/-- These operations are available on shifted unrestricted objects. -/
def copyDown (X : Type) : Map (down X) (tensor (down X) (down X)) :=
  ⟨fun x => (x,x), fun _ => rfl⟩
def discardDown (X : Type) : Map (down X) one := ⟨fun _ => (), fun _ => rfl⟩

/-- Keeping U above L while granting only L copying violates monotonicity. -/
theorem reversed_permissions_invalid :
    ¬PolicyValid Above (fun m _ => m = .linear) := by
  intro h
  have bad := h .unrestricted .linear (Or.inl rfl) .contract rfl
  cases bad

/-- The independence counterexample also fails semantically for the resource atom. -/
theorem atom_cannot_promote : ¬Nonempty (atom.Carrier → up atom) := by
  rintro ⟨f⟩
  have h := (f (0 : Nat)).property
  change 1 = 0 at h
  omega

end SquareKit.AdjointModes
