import SquareKit.SmoothAlgebra

/-!
Coordinate products and zero fibers of free smooth algebras. These universal
properties hold against every smooth algebra, including algebras with nilpotents.
-/
noncomputable section
namespace SquareKit.SmoothAlgebra.Coordinates

variable {A B : Type*} [CommRing A] [Algebra ℝ A] [Structure A]
  [CommRing B] [Algebra ℝ B] [Structure B] {n k : ℕ}

def left (n k : ℕ) : Hom (freeAlgebra n) (freeAlgebra (n+k)) :=
  evaluate (fun i => generator (Fin.castAdd k i))

def right (n k : ℕ) : Hom (freeAlgebra k) (freeAlgebra (n+k)) :=
  evaluate (fun i => generator (Fin.natAdd n i))

def zeroSection (n k : ℕ) : Hom (freeAlgebra (n+k)) (freeAlgebra n) :=
  evaluate (Fin.addCases generator (fun _ => 0))

def zero (k : ℕ) : Hom (freeAlgebra k) (freeAlgebra 0) := evaluate (fun _ => 0)

def constants (n : ℕ) : Hom (freeAlgebra 0) (freeAlgebra n) := evaluate Fin.elim0

/-- Concatenate the two specified tuples of images of generators. -/
def pair (u : Hom (freeAlgebra n) A) (v : Hom (freeAlgebra k) A) : Hom (freeAlgebra (n+k)) A :=
  evaluate (Fin.addCases (fun i => u (generator i)) (fun i => v (generator i)))

@[simp] theorem pair_left (u : Hom (freeAlgebra n) A) (v : Hom (freeAlgebra k) A) :
    (pair u v).comp (left n k) = u := by
  apply hom_ext_generators
  intro i
  simp [Hom.comp, left, pair]

@[simp] theorem pair_right (u : Hom (freeAlgebra n) A) (v : Hom (freeAlgebra k) A) :
    (pair u v).comp (right n k) = v := by
  apply hom_ext_generators
  intro i
  simp [Hom.comp, right, pair]

theorem pair_unique (u : Hom (freeAlgebra n) A) (v : Hom (freeAlgebra k) A)
    (w : Hom (freeAlgebra (n+k)) A) (hl : w.comp (left n k) = u)
    (hr : w.comp (right n k) = v) : w = pair u v := by
  apply hom_ext_generators
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have h := congrArg (fun f : Hom (freeAlgebra n) A => f (generator j)) hl
    simpa [Hom.comp, left, pair] using h
  · have h := congrArg (fun f : Hom (freeAlgebra k) A => f (generator j)) hr
    simpa [Hom.comp, right, pair] using h

theorem product_universal (u : Hom (freeAlgebra n) A) (v : Hom (freeAlgebra k) A) :
    ∃! w : Hom (freeAlgebra (n+k)) A, w.comp (left n k) = u ∧ w.comp (right n k) = v :=
  ⟨pair u v, ⟨pair_left u v, pair_right u v⟩, fun w hw => pair_unique u v w hw.1 hw.2⟩

theorem pair_natural (h : Hom A B) (u : Hom (freeAlgebra n) A) (v : Hom (freeAlgebra k) A) :
    h.comp (pair u v) = pair (h.comp u) (h.comp v) := by
  apply pair_unique
  · rw [← Hom.comp_assoc, pair_left]
  · rw [← Hom.comp_assoc, pair_right]

theorem constants_unique (u v : Hom (freeAlgebra 0) A) : u = v :=
  hom_ext_generators u v (fun i => Fin.elim0 i)

/-- The factor through the coordinate zero insertion keeps the free coordinates. -/
def fiberLift (u : Hom (freeAlgebra (n+k)) A) : Hom (freeAlgebra n) A := u.comp (left n k)

theorem fiberLift_zeroSection (u : Hom (freeAlgebra (n+k)) A) (v : Hom (freeAlgebra 0) A)
    (hc : u.comp (right n k) = v.comp (zero k)) :
    (fiberLift u).comp (zeroSection n k) = u := by
  apply hom_ext_generators
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [fiberLift, Hom.comp, zeroSection, left]
  · have h := congrArg (fun f : Hom (freeAlgebra k) A => f (generator j)) hc
    have hu : u 0 = 0 := u.toAlgHom.map_zero
    have hv : v 0 = 0 := v.toAlgHom.map_zero
    have hl : left n k 0 = 0 := (left n k).toAlgHom.map_zero
    simp only [Hom.comp, right, zero] at h
    simpa [fiberLift, Hom.comp, zeroSection, hl, hu, hv] using h.symm

theorem fiberLift_constants (u : Hom (freeAlgebra (n+k)) A) (v : Hom (freeAlgebra 0) A) :
    (fiberLift u).comp (constants n) = v := constants_unique _ _

theorem zeroSection_left (n k : ℕ) :
    (zeroSection n k).comp (left n k) = Hom.ident := by
  apply hom_ext_generators
  intro i
  simp [Hom.comp, zeroSection, left, Hom.ident]

theorem fiberLift_unique (u : Hom (freeAlgebra (n+k)) A) (w : Hom (freeAlgebra n) A)
    (hw : w.comp (zeroSection n k) = u) : w = fiberLift u := by
  rw [fiberLift, ← hw, ← Hom.comp_assoc, zeroSection_left, Hom.comp_ident]

theorem zero_fiber_universal (u : Hom (freeAlgebra (n+k)) A) (v : Hom (freeAlgebra 0) A)
    (hc : u.comp (right n k) = v.comp (zero k)) :
    ∃! w : Hom (freeAlgebra n) A, w.comp (zeroSection n k) = u ∧ w.comp (constants n) = v :=
  ⟨fiberLift u, ⟨fiberLift_zeroSection u v hc, fiberLift_constants u v⟩,
    fun w hw => fiberLift_unique u w hw.1⟩

theorem fiberLift_natural (h : Hom A B) (u : Hom (freeAlgebra (n+k)) A) :
    h.comp (fiberLift u) = fiberLift (h.comp u) := Hom.comp_assoc _ _ _

end SquareKit.SmoothAlgebra.Coordinates
