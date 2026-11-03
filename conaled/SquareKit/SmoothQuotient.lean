import SquareKit.SmoothAlgebra
import SquareKit.SmoothHadamard
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Experimental ordinary-ideal quotients of smooth algebras. -/
noncomputable section
open scoped ContDiff
namespace SquareKit.SmoothAlgebra

/-- Joint coefficient as a finite-coordinate operation on the concatenated tuples. -/
def differenceCoefficient {n : ℕ} (f : Operation n) (i : Fin n) : Free (n+n) :=
  ⟨fun z => SmoothHadamard.coefficient f.val i
    (fun j => z (Fin.castAdd n j), fun j => z (Fin.natAdd n j)),
   (SmoothHadamard.coefficient_smooth f.property i).comp
     ((contDiff_pi.mpr fun j => contDiff_apply ℝ _ (Fin.castAdd n j)).prodMk
      (contDiff_pi.mpr fun j => contDiff_apply ℝ _ (Fin.natAdd n j)))⟩

variable {A B : Type*} [CommRing A] [Algebra ℝ A] [Structure A]
  [CommRing B] [Algebra ℝ B] [Structure B]

/-- The analytic identity transported by the free-algebra universal evaluation. -/
theorem act_difference {n : ℕ} (f : Operation n) (x y : Fin n → A) :
    act f x - act f y = ∑ i, (x i - y i) * evaluate (Fin.append x y) (differenceCoefficient f i) := by
  have h : (pullback (fun i => projection (Fin.castAdd n i)) (show Free n from f) -
      pullback (fun i => projection (Fin.natAdd n i)) (show Free n from f) : Free (n+n)) =
      ∑ i, (generator (Fin.castAdd n i) - generator (Fin.natAdd n i)) * differenceCoefficient f i := by
    apply Subtype.ext
    funext z
    simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Finset.sum_apply,
      AddSubmonoidClass.coe_finsetSum,
      Pi.sub_apply, Pi.mul_apply]
    exact SmoothHadamard.factorization f.property _ _
  have he := congrArg (evaluate (Fin.append x y)).toAlgHom h
  simp only [map_sub, map_sum, map_mul] at he
  change act (substitute f (fun i => projection (Fin.castAdd n i))) (Fin.append x y) -
    act (substitute f (fun i => projection (Fin.natAdd n i))) (Fin.append x y) =
    ∑ i, (act (projection (Fin.castAdd n i)) (Fin.append x y) -
      act (projection (Fin.natAdd n i)) (Fin.append x y)) *
      evaluate (Fin.append x y) (differenceCoefficient f i) at he
  simpa only [Structure.substitute, Structure.projection, Fin.append_left, Fin.append_right] using he


/-- Every ordinary ring ideal respects every smooth operation. -/
theorem ideal_stable (I : Ideal A) {n : ℕ} (f : Operation n) (x y : Fin n → A)
    (h : ∀ i, x i - y i ∈ I) : act f x - act f y ∈ I := by
  rw [act_difference]
  exact I.sum_mem fun i _ => I.mul_mem_right _ (h i)

namespace Quotient

variable (I : Ideal A)

private def representative (q : A ⧸ I) : A := (Ideal.Quotient.mk_surjective q).choose
omit [Algebra ℝ A] [Structure A] in
private theorem mk_representative (q : A ⧸ I) :
    Ideal.Quotient.mk I (representative I q) = q := (Ideal.Quotient.mk_surjective q).choose_spec

/-- Choose representatives, then use ordinary-ideal stability to remove the choice. -/
def operation {n : ℕ} (f : Operation n) (z : Fin n → A ⧸ I) : A ⧸ I :=
  Ideal.Quotient.mk I (act f (fun i => representative I (z i)))

theorem operation_mk {n : ℕ} (f : Operation n) (z : Fin n → A) :
    operation I f (fun i => Ideal.Quotient.mk I (z i)) = Ideal.Quotient.mk I (act f z) := by
  apply Ideal.Quotient.eq.mpr
  apply ideal_stable
  intro i
  exact Ideal.Quotient.eq.mp (mk_representative I _)

omit [Algebra ℝ A] [Structure A] in
private theorem tuple_surjective {n : ℕ} (z : Fin n → A ⧸ I) :
    ∃ x : Fin n → A, (fun i => Ideal.Quotient.mk I (x i)) = z :=
  ⟨fun i => representative I (z i), funext fun i => mk_representative I (z i)⟩

instance : Structure (A ⧸ I) where
  act := operation I
  projection i z := by
    obtain ⟨x, rfl⟩ := tuple_surjective I z
    rw [operation_mk, Structure.projection]
  substitute f g z := by
    obtain ⟨x, rfl⟩ := tuple_surjective I z
    simp only [operation_mk, Structure.substitute]
  constant n a z := by
    obtain ⟨x, rfl⟩ := tuple_surjective I z
    rw [operation_mk, Structure.constant]
    exact (Ideal.Quotient.mkₐ ℝ I).commutes a
  addition z := by
    obtain ⟨x, rfl⟩ := tuple_surjective I z
    rw [operation_mk, Structure.addition, map_add]
  multiplication z := by
    obtain ⟨x, rfl⟩ := tuple_surjective I z
    rw [operation_mk, Structure.multiplication, map_mul]

/-- The ordinary quotient projection preserves every smooth operation. -/
def projection : Hom A (A ⧸ I) :=
  ⟨Ideal.Quotient.mk I, fun f z => (operation_mk I f z).symm⟩

theorem projection_toAlgHom : (projection I).toAlgHom = Ideal.Quotient.mkₐ ℝ I := rfl

def lift (h : Hom A B) (hI : ∀ a ∈ I, h a = 0) : Hom (A ⧸ I) B where
  toFun := Ideal.Quotient.liftₐ I h.toAlgHom hI
  map_act f z := by
    obtain ⟨x, rfl⟩ := tuple_surjective I z
    change (Ideal.Quotient.liftₐ I h.toAlgHom hI) (operation I f _) = _
    rw [operation_mk]
    exact h.map_act f x

theorem lift_toAlgHom (h : Hom A B) (hI : ∀ a ∈ I, h a = 0) :
    (lift I h hI).toAlgHom = Ideal.Quotient.liftₐ I h.toAlgHom hI := by
  ext q
  rfl

@[simp] theorem lift_projection (h : Hom A B) (hI : ∀ a ∈ I, h a = 0) :
    Hom.comp (lift I h hI) (projection I) = h := Hom.ext fun _ => rfl

theorem unique (h k : Hom (A ⧸ I) B)
    (hk : Hom.comp h (projection I) = Hom.comp k (projection I)) : h = k := by
  apply Hom.ext
  intro q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact congrArg (fun f : Hom A B => f a) hk

/-- Maps out of the ordinary quotient are exactly smooth maps annihilating the ideal. -/
def homEquiv : Hom (A ⧸ I) B ≃ {h : Hom A B // ∀ a ∈ I, h a = 0} where
  toFun h := ⟨Hom.comp h (projection I), fun a ha => by
    change h (Ideal.Quotient.mk I a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact h.toAlgHom.map_zero⟩
  invFun h := lift I h.val h.property
  left_inv h := unique I _ _ (lift_projection I _ _)
  right_inv h := Subtype.ext (lift_projection I _ _)

/-- Presentations by ordinary ideals: generator tuples satisfying all relations. -/
def presentationEquiv {n : ℕ} (J : Ideal (Free n)) :
    Hom (Free n ⧸ J) B ≃ {a : Fin n → B // ∀ f ∈ J, evaluate a f = 0} :=
  (homEquiv J).trans {
    toFun := fun h => ⟨freeEquiv n h.val, by
      change ∀ f ∈ J, evaluate (fun i => h.val (generator i)) f = 0
      rw [evaluate_unique]
      exact h.property⟩
    invFun := fun a => ⟨evaluate a.val, a.property⟩
    left_inv := fun h => Subtype.ext (evaluate_unique h.val)
    right_inv := fun a => Subtype.ext ((freeEquiv n).right_inv a.val) }

end Quotient
end SquareKit.SmoothAlgebra
