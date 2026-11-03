import SquareKit.SmoothQuotient
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-! Experimental finite smooth localization presentations. Principal and iterated
localizations share the finite list of inverse coordinates and its universal property. -/
noncomputable section
namespace SquareKit.SmoothAlgebra.Localization

variable {n k : ℕ}

def extend : Hom (Free n) (Free (n + k)) := pullback (fun i => projection (Fin.castAdd k i))
def relation (f : Fin k → Free n) (j : Fin k) : Free (n + k) :=
  extend (f j) * generator (Fin.natAdd n j) - 1

def ideal (f : Fin k → Free n) : Ideal (Free (n + k)) := Ideal.span (Set.range (relation f))
abbrev Carrier (f : Fin k → Free n) := Free (n + k) ⧸ ideal f

-- Direct inherited instances avoid repeated search through the presentation alias.
instance (f : Fin k → Free n) : CommRing (Carrier f) := inferInstance
instance (f : Fin k → Free n) : Algebra ℝ (Carrier f) := inferInstance
instance (f : Fin k → Free n) : Structure (Carrier f) := inferInstance
instance (f : Fin k → Free n) : IsDedekindFiniteMonoid (Carrier f) where
  mul_eq_one_symm {a b} h := (mul_comm b a).trans h

def base (f : Fin k → Free n) : Hom (Free n) (Carrier f) :=
  Hom.comp (Quotient.projection (ideal f)) extend

def inverseGenerator (f : Fin k → Free n) (j : Fin k) : Carrier f :=
  Quotient.projection (ideal f) (generator (Fin.natAdd n j))

theorem inverse_relation (f : Fin k → Free n) (j : Fin k) :
    base f (f j) * inverseGenerator f j = 1 := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk (ideal f) (extend (f j)) * Ideal.Quotient.mk (ideal f) (generator (Fin.natAdd n j)) - 1 = 0
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (ideal f)), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨j, rfl⟩

theorem base_isUnit (f : Fin k → Free n) (j : Fin k) : IsUnit (base f (f j)) :=
  ⟨⟨base f (f j), inverseGenerator f j, inverse_relation f j,
    (mul_comm (inverseGenerator f j) (base f (f j))).trans (inverse_relation f j)⟩, rfl⟩

variable {B C : Type*} [CommRing B] [Algebra ℝ B] [Structure B]
  [CommRing C] [Algebra ℝ C] [Structure C]

def coordinates (h : Hom (Free n) B) (f : Fin k → Free n) : Fin (n + k) → B :=
  Fin.append (fun i => h (generator i)) (fun j => Ring.inverse (h (f j)))

theorem evaluate_extend (h : Hom (Free n) B) (f : Fin k → Free n) (p : Free n) :
    evaluate (coordinates h f) (extend p) = h p := by
  have he := congrArg (fun g : Hom (Free n) B => g p)
    (evaluate_pullback (fun i => projection (Fin.castAdd k i)) (coordinates h f))
  change evaluate (coordinates h f) (extend p) =
    evaluate (fun i => act (projection (Fin.castAdd k i)) (coordinates h f)) p at he
  simpa only [Structure.projection, coordinates, Fin.append_left, evaluate_unique] using he

/-- The added inverses are forced by unitness, not supplied as free data. -/
def lift (f : Fin k → Free n) (h : Hom (Free n) B) (hu : ∀ j, IsUnit (h (f j))) : Hom (Carrier f) B :=
  Quotient.lift (ideal f) (evaluate (coordinates h f)) (by
    have hi : ideal f ≤ RingHom.ker (evaluate (coordinates h f)).toAlgHom := by
      apply Ideal.span_le.mpr
      rintro p ⟨j, rfl⟩
      change (evaluate (coordinates h f)).toAlgHom (extend (f j) * generator (Fin.natAdd n j) - 1) = 0
      rw [map_sub, map_mul, map_one]
      change evaluate (coordinates h f) (extend (f j)) * evaluate (coordinates h f) (generator (Fin.natAdd n j)) - 1 = 0
      rw [evaluate_extend, evaluate_generator]
      simp only [coordinates, Fin.append_right]
      rw [Ring.mul_inverse_cancel _ (hu j), sub_self]
    exact fun p hp => hi hp)

@[simp] theorem lift_base (f : Fin k → Free n) (h : Hom (Free n) B) (hu : ∀ j, IsUnit (h (f j))) :
    Hom.comp (lift f h hu) (base f) = h :=
  Hom.ext (evaluate_extend h f)

@[simp] theorem lift_inverse (f : Fin k → Free n) (h : Hom (Free n) B) (hu : ∀ j, IsUnit (h (f j))) (j : Fin k) :
    lift f h hu (inverseGenerator f j) = Ring.inverse (h (f j)) := by
  exact (evaluate_generator (coordinates h f) (Fin.natAdd n j)).trans (Fin.append_right _ _ j)

omit [Algebra ℝ B] [Structure B] in
theorem inverse_unique {a b c : B} (hb : a * b = 1) (hc : a * c = 1) : b = c := by
  calc
    b = b * (a * c) := by rw [hc, mul_one]
    _ = (a * b) * c := by ring
    _ = c := by rw [hb, one_mul]

theorem unique (f : Fin k → Free n) (h l : Hom (Carrier f) B)
    (he : Hom.comp h (base f) = Hom.comp l (base f)) : h = l := by
  apply Quotient.unique (ideal f)
  apply hom_ext_generators
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact congrArg (fun q : Hom (Free n) B => q (generator j)) he
  · change h (inverseGenerator f j) = l (inverseGenerator f j)
    apply inverse_unique (a := h (base f (f j)))
    · rw [← h.map_mul, inverse_relation]
      exact h.toAlgHom.map_one
    · have hh := congrArg (fun q : Hom (Free n) B => q (f j)) he
      change h (base f (f j)) = l (base f (f j)) at hh
      rw [hh, ← l.map_mul, inverse_relation]
      exact l.toAlgHom.map_one

def homEquiv (f : Fin k → Free n) :
    Hom (Carrier f) B ≃ {h : Hom (Free n) B // ∀ j, IsUnit (h (f j))} where
  toFun h := ⟨Hom.comp h (base f), fun j => (base_isUnit f j).map h.toAlgHom⟩
  invFun h := lift f h.val h.property
  left_inv h := unique f _ h (lift_base f _ _)
  right_inv h := Subtype.ext (lift_base f h.val h.property)

abbrev Principal (f : Free n) := Carrier (fun _ : Fin 1 => f)
abbrev principalBase (f : Free n) : Hom (Free n) (Principal f) := base (fun _ : Fin 1 => f)
abbrev inverse (f : Free n) : Principal f := inverseGenerator (fun _ : Fin 1 => f) 0
abbrev principalLift (f : Free n) (h : Hom (Free n) B) (hu : IsUnit (h f)) : Hom (Principal f) B :=
  lift (fun _ : Fin 1 => f) h (fun _ => hu)

def principalHomEquiv (f : Free n) : Hom (Principal f) B ≃ {h : Hom (Free n) B // IsUnit (h f)} :=
  (homEquiv (fun _ : Fin 1 => f)).trans {
    toFun := fun h => ⟨h.val, h.property 0⟩
    invFun := fun h => ⟨h.val, fun _ => h.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem principal_unique (f : Free n) (h l : Hom (Principal f) B)
    (he : Hom.comp h (principalBase f) = Hom.comp l (principalBase f)) : h = l := unique _ h l he

/-- Pullbacks of functions induce the contravariant geometric restriction map. -/
def map {m : ℕ} (f : Free n) (g : Free m) (h : Hom (Free n) (Free m)) (he : h f = g) :
    Hom (Principal f) (Principal g) :=
  principalLift f (Hom.comp (principalBase g) h) (by
    change IsUnit (principalBase g (h f))
    rw [he]
    exact base_isUnit _ 0)

@[simp] theorem map_base {m : ℕ} (f : Free n) (g : Free m) (h : Hom (Free n) (Free m)) (he : h f = g) :
    Hom.comp (map f g h he) (principalBase f) = Hom.comp (principalBase g) h := by
  unfold map
  apply lift_base

theorem map_ident (f : Free n) : map f f Hom.ident rfl = Hom.ident := by
  apply principal_unique f
  exact map_base f f Hom.ident rfl

theorem map_comp {m l : ℕ} (f : Free n) (g : Free m) (q : Free l)
    (h : Hom (Free n) (Free m)) (j : Hom (Free m) (Free l)) (he : h f = g) (je : j g = q) :
    Hom.comp (map g q j je) (map f g h he) =
      map f q (Hom.comp j h) (by change j (h f) = q; rw [he, je]) := by
  apply principal_unique f
  rw [← Hom.comp_assoc, map_base, Hom.comp_assoc, map_base, map_base, Hom.comp_assoc]

abbrev Iterated (f g : Free n) := Carrier ![f, g]
abbrev iteratedBase (f g : Free n) : Hom (Free n) (Iterated f g) := base ![f, g]

def first (f g : Free n) : Hom (Principal f) (Iterated f g) :=
  principalLift f (iteratedBase f g) (base_isUnit ![f, g] 0)

def iteratedLift (f g : Free n) (h : Hom (Principal f) B)
    (hg : IsUnit (h (principalBase f g))) : Hom (Iterated f g) B :=
  lift ![f, g] (Hom.comp h (principalBase f)) (fun j => by
    fin_cases j
    · exact (base_isUnit (fun _ : Fin 1 => f) 0).map h.toAlgHom
    · exact hg)

theorem first_base (f g : Free n) : Hom.comp (first f g) (principalBase f) = iteratedBase f g := by
  unfold first
  exact lift_base _ _ (fun _ => base_isUnit ![f, g] 0)

theorem iteratedLift_base (f g : Free n) (h : Hom (Principal f) B)
    (hg : IsUnit (h (principalBase f g))) :
    Hom.comp (iteratedLift f g h hg) (iteratedBase f g) = Hom.comp h (principalBase f) := by
  unfold iteratedLift
  apply lift_base

theorem iteratedLift_first (f g : Free n) (h : Hom (Principal f) B)
    (hg : IsUnit (h (principalBase f g))) : Hom.comp (iteratedLift f g h hg) (first f g) = h := by
  apply principal_unique f
  rw [← Hom.comp_assoc, first_base, iteratedLift_base]

theorem first_g_isUnit (f g : Free n) : IsUnit (first f g (principalBase f g)) := by
  have he := congrArg (fun h : Hom (Free n) (Iterated f g) => h g) (first_base f g)
  change first f g (principalBase f g) = iteratedBase f g g at he
  rw [he]
  exact base_isUnit ![f, g] 1

theorem iterated_unique (f g : Free n) (h l : Hom (Iterated f g) B)
    (he : Hom.comp h (first f g) = Hom.comp l (first f g)) : h = l := by
  apply unique ![f, g]
  have ht := congrArg (fun k => Hom.comp k (principalBase f)) he
  rw [← Hom.comp_assoc, ← Hom.comp_assoc, first_base] at ht
  exact ht

def productToIterated (f g : Free n) : Hom (Principal (f * g)) (Iterated f g) :=
  principalLift (f * g) (iteratedBase f g) (by
    rw [(iteratedBase f g).map_mul]
    exact (base_isUnit ![f, g] 0).mul (base_isUnit ![f, g] 1))

def iteratedToProduct (f g : Free n) : Hom (Iterated f g) (Principal (f * g)) :=
  lift ![f, g] (principalBase (f * g)) (by
    have hp := base_isUnit (fun _ : Fin 1 => f * g) 0
    change IsUnit (principalBase (f * g) (f * g)) at hp
    rw [(principalBase (f * g)).map_mul, IsUnit.mul_iff] at hp
    intro j
    fin_cases j
    · exact hp.1
    · exact hp.2)

theorem productToIterated_base (f g : Free n) :
    Hom.comp (productToIterated f g) (principalBase (f * g)) = iteratedBase f g := by
  unfold productToIterated
  apply lift_base

theorem iteratedToProduct_base (f g : Free n) :
    Hom.comp (iteratedToProduct f g) (iteratedBase f g) = principalBase (f * g) := by
  unfold iteratedToProduct
  apply lift_base

theorem product_iterated_inverse (f g : Free n) :
    Hom.comp (iteratedToProduct f g) (productToIterated f g) = Hom.ident := by
  apply principal_unique (f * g)
  rw [← Hom.comp_assoc, productToIterated_base, iteratedToProduct_base]
  rfl

theorem iterated_product_inverse (f g : Free n) :
    Hom.comp (productToIterated f g) (iteratedToProduct f g) = Hom.ident := by
  apply unique ![f, g]
  rw [← Hom.comp_assoc, iteratedToProduct_base, productToIterated_base]
  rfl

/-- Inverting zero gives the improper quotient, including in arity zero. -/
theorem zero_subsingleton : Subsingleton (Principal (0 : Free n)) := by
  apply subsingleton_of_zero_eq_one
  have h := inverse_relation (fun _ : Fin 1 => (0 : Free n)) 0
  change (principalBase (0 : Free n)).toAlgHom 0 * inverse (0 : Free n) = 1 at h
  rw [map_zero, zero_mul] at h
  exact h

/-- Inverting one changes no smooth algebra. -/
def oneRetraction : Hom (Principal (1 : Free n)) (Free n) :=
  principalLift 1 Hom.ident isUnit_one

theorem one_base_inverse : Hom.comp (oneRetraction (n := n)) (principalBase 1) = Hom.ident :=
  lift_base _ _ (fun _ => isUnit_one)

theorem one_inverse_base : Hom.comp (principalBase 1) (oneRetraction (n := n)) = Hom.ident := by
  apply principal_unique 1
  rw [← Hom.comp_assoc, one_base_inverse]
  rfl

end SquareKit.SmoothAlgebra.Localization
