import Mathlib.Logic.Equiv.Basic

/-! Experimental extensional reconstruction of the designated mapping-square
argument from checkpoint 080, for #366. Identity is Lean equality in this module.
The quantified native theorem is not a source-calculus interpretation. -/
namespace SquareKit.Internal.DesignatedMap.Extensional
universe u

structure Contractible (A : Type u) where
  center : A
  contraction : ∀ a, center = a

abbrev Fiber {A B : Type u} (f : A → B) (b : B) := {a // f a = b}
abbrev IsEquiv {A B : Type u} (f : A → B) := (b : B) → Contractible (Fiber f b)

def fromEquiv {A B : Type u} (e : A ≃ B) : IsEquiv e := fun b =>
  ⟨⟨e.symm b, e.apply_symm_apply b⟩, fun a => Subtype.ext (e.injective
    ((e.apply_symm_apply b).trans a.property.symm))⟩

def toEquiv {A B : Type u} (f : A → B) (h : IsEquiv f) : A ≃ B where
  toFun := f
  invFun b := (h b).center.val
  left_inv a := congrArg Subtype.val ((h (f a)).contraction ⟨a, rfl⟩)
  right_inv b := (h b).center.property

/-- Transport contractible fibers along a pointwise equality of actual maps. -/
def homotopy {A B : Type u} (f g : A → B) (p : ∀ a, f a = g a)
    (h : IsEquiv f) : IsEquiv g := by
  have e : f = g := funext p
  exact e ▸ h

/-- Right cancellation constructs an inverse; no cancellation field is assumed. -/
def cancelRight {A B C : Type u} (f : A → B) (r : B → C)
    (h : IsEquiv (r ∘ f)) (hr : IsEquiv r) : IsEquiv f := by
  let composite := toEquiv (r ∘ f) h
  let outer := toEquiv r hr
  let e : A ≃ B := composite.trans outer.symm
  have he : ∀ a, e a = f a := fun a => outer.symm_apply_apply (f a)
  exact homotopy e f he (fromEquiv e)

structure Cocone {N L R : Type u} (north : N → L) (west : N → R) (Z : Type u) where
  left : L → Z
  right : R → Z
  glue : right ∘ west = left ∘ north

namespace Cocone
variable {N L R Z W : Type u} {north : N → L} {west : N → R}

def post (h : Z → W) (c : Cocone north west Z) : Cocone north west W where
  left := h ∘ c.left
  right := h ∘ c.right
  glue := congrArg (fun k => h ∘ k) c.glue

@[ext] theorem ext {c d : Cocone north west Z} (l : c.left = d.left)
    (r : c.right = d.right) : c = d := by cases c; cases d; cases l; cases r; rfl

theorem post_comp {X : Type u} (h : Z → W) (k : W → X) (c : Cocone north west Z) :
    post k (post h c) = post (k ∘ h) c := by apply ext <;> rfl
end Cocone

structure Boundary {N L R : Type u} (north : N → L) (west : N → R) where
  Carrier : Type u
  cocone : Cocone north west Carrier

namespace Boundary
variable {N L R S : Type u} {north : N → L} {west : N → R}

def restriction (b : Boundary north west) (Z : Type u) :
    (b.Carrier → Z) → Cocone north west Z := fun h => b.cocone.post h

/-- Quantification ranges over all native types at this level. -/
abbrev Universal (b : Boundary north west) := (Z : Type u) → IsEquiv (b.restriction Z)

def gap (b : Boundary north west) (universal : b.Universal)
    (c : Cocone north west S) : b.Carrier → S :=
  (toEquiv (b.restriction S) (universal S)).symm c

theorem gap_section (b : Boundary north west) (universal : b.Universal)
    (c : Cocone north west S) : b.restriction S (b.gap universal c) = c :=
  (toEquiv (b.restriction S) (universal S)).apply_symm_apply c

def mappingComparison (c : Cocone north west S) (Z : Type u) :
    (S → Z) → Cocone north west Z := fun h => c.post h

theorem comparison_computation (b : Boundary north west) (universal : b.Universal)
    (c : Cocone north west S) (Z : Type u) (h : S → Z) :
    b.restriction Z (h ∘ b.gap universal c) = mappingComparison c Z h := by
  change b.cocone.post (h ∘ b.gap universal c) = c.post h
  exact (Cocone.post_comp (b.gap universal c) h b.cocone).symm.trans
    (congrArg (Cocone.post h) (gap_section b universal c))

def mapping_square_local (b : Boundary north west) (universal : b.Universal)
    (c : Cocone north west S) (Z : Type u) (hm : IsEquiv (mappingComparison c Z)) :
    IsEquiv (fun h : S → Z => h ∘ b.gap universal c) :=
  cancelRight _ (b.restriction Z)
    (homotopy (mappingComparison c Z) _
      (fun h => (comparison_computation b universal c Z h).symm) hm) (universal Z)

/-- The identity span provides a constructed, nonempty pushout test. -/
def identitySpan (A : Type u) : Boundary (id : A → A) id :=
  ⟨A, ⟨id, id, rfl⟩⟩

def identityRestriction (A Z : Type u) : (A → Z) ≃ Cocone (id : A → A) id Z where
  toFun := (identitySpan A).restriction Z
  invFun c := c.left
  left_inv _ := rfl
  right_inv c := by
    apply Cocone.ext
    · rfl
    · exact c.glue.symm

def identityUniversal (A : Type u) : (identitySpan A).Universal :=
  fun Z => fromEquiv (identityRestriction A Z)

@[simp] theorem identity_gap (A : Type u) (c : Cocone (id : A → A) id S) :
    (identitySpan A).gap (identityUniversal A) c = c.left := rfl
end Boundary

/-- A family of actual experiments. Reindexing changes its carriers and all
selected data together; it does not choose fresh equivalence witnesses. -/
structure Experiment where
  N : Type u
  L : Type u
  R : Type u
  S : Type u
  Z : Type u
  north : N → L
  west : N → R
  boundary : Boundary north west
  universal : boundary.Universal
  target : Cocone north west S
  comparisonEquiv : IsEquiv (Boundary.mappingComparison target Z)

namespace Experiment

def result (e : Experiment) : IsEquiv
    (fun h : e.S → e.Z => h ∘ e.boundary.gap e.universal e.target) :=
  e.boundary.mapping_square_local e.universal e.target e.Z e.comparisonEquiv

/-- The dependent tail records a chosen input, its image and the selected
center of the actual fiber, not an arbitrary inhabitant of its type. -/
def selected (e : Experiment) (z : e.boundary.Carrier → e.Z) :
    Fiber (fun h : e.S → e.Z => h ∘ e.boundary.gap e.universal e.target) z :=
  (e.result z).center

end Experiment
end SquareKit.Internal.DesignatedMap.Extensional
