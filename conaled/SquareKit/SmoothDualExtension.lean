import SquareKit.SmoothTaylor
import Mathlib.Algebra.DualNumber

/-!
Experimental dual extensions of arbitrary smooth algebras. The named structure
is installed locally: clients can select it explicitly without competing with
the previously constructed square-zero stage instances.
-/
noncomputable section
namespace SquareKit.SmoothAlgebra.DualExtension

variable {A B C : Type*} [CommRing A] [Algebra ℝ A] [Structure A]
  [CommRing B] [Algebra ℝ B] [Structure B]
  [CommRing C] [Algebra ℝ C] [Structure C]

def operation {n : ℕ} (f : Operation n) (z : Fin n → DualNumber A) : DualNumber A :=
  ⟨act f (fun i => (z i).fst), differential f (fun i => (z i).fst) (fun i => (z i).snd)⟩

@[instance_reducible] def smoothStructure : Structure (DualNumber A) where
  act := operation
  projection i z := by
    apply TrivSqZeroExt.ext
    · exact Structure.projection _ _
    · exact differential_projection _ _ _
  substitute f g z := by
    apply TrivSqZeroExt.ext
    · exact Structure.substitute _ _ _
    · exact differential_chain _ _ _ _
  constant n r z := by
    apply TrivSqZeroExt.ext
    · exact Structure.constant _ _ _
    · exact differential_constant _ _ _ _
  addition z := by
    apply TrivSqZeroExt.ext
    · exact Structure.addition _
    · exact differential_addition (fun i => (z i).fst) (fun i => (z i).snd)
  multiplication z := by
    apply TrivSqZeroExt.ext
    · exact Structure.multiplication _
    · simpa [operation, TrivSqZeroExt.snd_mul, smul_eq_mul, mul_comm] using
        differential_multiplication (fun i => (z i).fst) (fun i => (z i).snd)

attribute [local instance] smoothStructure

def inclusion : Hom A (DualNumber A) where
  toFun := TrivSqZeroExt.inl
  map_act f z := by
    apply TrivSqZeroExt.ext
    · rfl
    · change 0 = differential f z (fun _ => 0)
      simp [differential]

def lift (h : Hom A B) (d : B) (hd : d*d=0) : Hom (DualNumber A) B where
  toFun := DualNumber.lift ⟨(h.toAlgHom,d), hd, fun _ => Commute.all _ _⟩
  map_act f z := by
    change h (act f (fun i => (z i).fst)) + h (differential f (fun i => (z i).fst) (fun i => (z i).snd)) * d =
      act f (fun i => h (z i).fst + h (z i).snd * d)
    rw [h.map_act]
    have hv : h (differential f (fun i => (z i).fst) (fun i => (z i).snd)) =
        ∑ i, act (derivative f i) (fun j => h (z j).fst) * h (z i).snd := by
      change h.toAlgHom (∑ i, _) = _
      simp only [map_sum, map_mul]
      exact Finset.sum_congr rfl (fun i _ => congrArg (fun t => t * h (z i).snd) (h.map_act _ _))
    rw [hv, mul_comm]
    simpa only [mul_comm] using (nilsquare_taylor f (fun i => h (z i).fst)
      (fun i => h (z i).snd) d hd).symm

theorem lift_toAlgHom (h : Hom A B) (d : B) (hd : d*d=0) :
    (lift h d hd).toAlgHom = DualNumber.lift ⟨(h.toAlgHom,d), hd, fun _ => Commute.all _ _⟩ := by
  apply AlgHom.ext
  intro z
  rfl

@[simp] theorem lift_inclusion (h : Hom A B) (d : B) (hd : d*d=0) :
    Hom.comp (lift h d hd) inclusion = h := by
  apply Hom.ext
  intro a
  exact DualNumber.lift_apply_inl _ a

@[simp] theorem lift_eps (h : Hom A B) (d : B) (hd : d*d=0) :
    lift h d hd DualNumber.eps = d := DualNumber.lift_apply_eps _

/-- A smooth dual map is determined by its base map and its infinitesimal generator. -/
theorem unique (h k : Hom (DualNumber A) B)
    (hi : Hom.comp h inclusion = Hom.comp k inclusion)
    (he : h DualNumber.eps = k DualNumber.eps) : h=k := by
  have ha : h.toAlgHom = k.toAlgHom := DualNumber.lift.symm.injective
    (Subtype.ext (Prod.ext (congrArg Hom.toAlgHom hi) he))
  exact Hom.ext fun z => congrArg (fun f : DualNumber A →ₐ[ℝ] B => f z) ha

def homEquiv : Hom (DualNumber A) B ≃ (Hom A B × {d : B // d*d=0}) where
  toFun h := (Hom.comp h inclusion, ⟨h DualNumber.eps, by
    change h.toAlgHom DualNumber.eps * h.toAlgHom DualNumber.eps = 0
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]⟩)
  invFun p := lift p.1 p.2.val p.2.property
  left_inv h := unique _ _ (lift_inclusion _ _ _) (lift_eps _ _ _)
  right_inv p := Prod.ext (lift_inclusion _ _ _) (Subtype.ext (lift_eps p.1 p.2.val p.2.property))

theorem lift_natural (k : Hom B C) (h : Hom A B) (d : B) (hd : d*d=0) :
    Hom.comp k (lift h d hd) = lift (Hom.comp k h) (k d)
      (by change k.toAlgHom d * k.toAlgHom d = 0; rw [← map_mul, hd, map_zero]) := by
  apply Hom.ext
  intro z
  exact (k.map_add _ _).trans (congrArg (fun t => k (h z.fst) + t) (k.map_mul _ _))


/-- Scalar inclusion is smooth, derived from nullary constants and substitution. -/
def realHom : Hom ℝ B where
  toFun := algebraMap ℝ B
  map_act f z := by
    change algebraMap ℝ B (f.val z) = _
    have h : substitute f (fun i => constant 0 (z i)) = constant 0 (f.val z) := rfl
    have he := congrArg (fun g : Operation 0 => act (A := B) g Fin.elim0) h
    simpa only [Structure.substitute, Structure.constant] using he.symm

theorem realHom_unique (h : Hom ℝ B) : h = realHom := by
  apply Hom.ext
  intro r
  exact h.map_scalar r

def realHomEquiv : Hom (DualNumber ℝ) B ≃ {d : B // d*d=0} where
  toFun h := (homEquiv h).2
  invFun d := lift realHom d.val d.property
  left_inv h := unique _ _ (by rw [lift_inclusion, ← realHom_unique (Hom.comp h inclusion)])
    (lift_eps _ _ _)
  right_inv d := Subtype.ext (lift_eps realHom d.val d.property)

def rightInclusion : Hom (DualNumber ℝ) (DualNumber A) :=
  lift (Hom.comp inclusion realHom) DualNumber.eps DualNumber.eps_mul_eps

/-- The actual dual extension is the smooth coproduct with the real dual algebra. -/
def coproductEquiv : Hom (DualNumber A) B ≃ (Hom A B × Hom (DualNumber ℝ) B) :=
  homEquiv.trans (Equiv.prodCongr (Equiv.refl _) realHomEquiv.symm)

theorem coproduct_left (h : Hom (DualNumber A) B) :
    (coproductEquiv h).1 = Hom.comp h inclusion := rfl

theorem coproduct_right (h : Hom (DualNumber A) B) :
    (coproductEquiv h).2 = Hom.comp h rightInclusion := by
  apply realHomEquiv.injective
  apply Subtype.ext
  change lift realHom (h DualNumber.eps) (homEquiv h).2.property DualNumber.eps = h (rightInclusion DualNumber.eps)
  erw [lift_eps]
  congr 1
  exact (lift_eps _ _ _).symm

end SquareKit.SmoothAlgebra.DualExtension
