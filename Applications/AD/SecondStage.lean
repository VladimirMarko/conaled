import Applications.AD.SmoothDual
import Mathlib.Tactic.Ring

/-! Experimental second-order real stage, realized inside iterated dual numbers. -/
noncomputable section
namespace Applications.AD.SecondStage
abbrev Ambient := DualNumber (DualNumber ℝ)

/-- Equal first-order coordinates in the two dual directions. -/
def diagonal : Subalgebra ℝ Ambient where
  carrier := {z | z.fst.snd = z.snd.fst}
  zero_mem' := rfl
  one_mem' := rfl
  add_mem' ha hb := by simp only [Set.mem_ofPred_eq, TrivSqZeroExt.fst_add,
    TrivSqZeroExt.snd_add] at *; rw [ha, hb]
  mul_mem' {a b} ha hb := by
    change a.fst.snd = a.snd.fst at ha
    change b.fst.snd = b.snd.fst at hb
    change a.fst.fst * b.fst.snd + a.fst.snd * b.fst.fst =
      a.fst.fst * b.snd.fst + a.snd.fst * b.fst.fst
    rw [ha, hb]
  algebraMap_mem' _ := rfl

abbrev Stage := diagonal

def coeff (z : Stage) : ℝ × ℝ × ℝ := (z.val.fst.fst, z.val.fst.snd, z.val.snd.snd / 2)

def ofCoeff (x v w : ℝ) : Stage := ⟨⟨⟨x,v⟩,⟨v,2*w⟩⟩,rfl⟩

@[simp] theorem coeff_ofCoeff (x v w : ℝ) : coeff (ofCoeff x v w) = (x,v,w) := by
  change (x,v,2*w/2) = (x,v,w)
  simp

@[simp] theorem ofCoeff_coeff (z : Stage) : ofCoeff (coeff z).1 (coeff z).2.1 (coeff z).2.2 = z := by
  apply Subtype.ext
  apply TrivSqZeroExt.ext
  · rfl
  · apply TrivSqZeroExt.ext
    · exact z.property
    · change 2 * (z.val.snd.snd / 2) = _
      ring

@[ext] theorem ext {a b : Stage} (h : coeff a = coeff b) : a = b := by
  rw [← ofCoeff_coeff a, ← ofCoeff_coeff b, h]

theorem coeff_add (a b : Stage) : coeff (a+b) =
    ((coeff a).1+(coeff b).1, (coeff a).2.1+(coeff b).2.1, (coeff a).2.2+(coeff b).2.2) := by
  change (a.val.fst.fst+b.val.fst.fst, a.val.fst.snd+b.val.fst.snd,
    (a.val.snd.snd+b.val.snd.snd)/2) = _
  simp [coeff, add_div]

theorem coeff_mul (a b : Stage) : coeff (a*b) =
    ((coeff a).1*(coeff b).1, (coeff a).1*(coeff b).2.1+(coeff a).2.1*(coeff b).1,
      (coeff a).1*(coeff b).2.2+(coeff a).2.1*(coeff b).2.1+(coeff a).2.2*(coeff b).1) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  change ((a.val.fst.fst*b.val.snd.snd+a.val.fst.snd*b.val.snd.fst)+
    (a.val.snd.fst*b.val.fst.snd+a.val.snd.snd*b.val.fst.fst))/2 = _
  rw [← a.property, ← b.property]
  dsimp [coeff]
  ring

@[simp] theorem coeff_scalar (x : ℝ) : coeff (algebraMap ℝ Stage x) = (x,0,0) := by
  change (x,0,(0 : ℝ)/2) = (x,0,0)
  simp

@[simp] theorem coeff_zero : coeff (0 : Stage) = (0,0,0) := by simp [coeff]
@[simp] theorem coeff_one : coeff (1 : Stage) = (1,0,0) := by simp [coeff]

def epsilon : Stage := ofCoeff 0 1 0

theorem epsilon_sq : epsilon^2 = ofCoeff 0 0 1 := by
  apply ext
  rw [pow_two, coeff_mul]
  norm_num [epsilon]

theorem epsilon_cube : epsilon^3 = 0 := by
  rw [pow_succ, epsilon_sq]
  apply ext
  rw [coeff_mul]
  norm_num [epsilon]

theorem epsilon_sq_ne_zero : epsilon^2 ≠ 0 := by
  intro h
  have hh := congrArg (fun z => (coeff z).2.2) h
  rw [epsilon_sq] at hh
  norm_num at hh

/-- Unique truncated-polynomial normal form. -/
theorem normal_form (z : Stage) : z = algebraMap ℝ Stage (coeff z).1 +
    algebraMap ℝ Stage (coeff z).2.1 * epsilon +
    algebraMap ℝ Stage (coeff z).2.2 * epsilon^2 := by
  apply ext
  rw [epsilon_sq, coeff_add, coeff_add, coeff_mul, coeff_mul]
  simp [epsilon]

/-- Discard the quadratic coefficient, using the existing ambient algebra projection. -/
def project : Stage →ₐ[ℝ] DualNumber ℝ :=
  (TrivSqZeroExt.fstHom ℝ (DualNumber ℝ) (DualNumber ℝ)).comp diagonal.val

@[simp] theorem project_ofCoeff (x v w : ℝ) : project (ofCoeff x v w) = (⟨x,v⟩ : DualNumber ℝ) := rfl

/-- Universal evaluation at any cubically nilpotent element of a commutative real algebra. -/
def evaluate {A : Type*} [CommRing A] [Algebra ℝ A] (t : A) (ht : t^3 = 0) : Stage →ₐ[ℝ] A where
  toFun z := algebraMap ℝ A (coeff z).1 + algebraMap ℝ A (coeff z).2.1 * t +
    algebraMap ℝ A (coeff z).2.2 * t^2
  map_zero' := by simp
  map_one' := by simp
  map_add' a b := by simp only [coeff_add, map_add]; ring
  map_mul' a b := by
    simp only [coeff_mul, map_add, map_mul]
    have ht4 : t^4 = 0 := by rw [show (4 : ℕ) = 3+1 from rfl, pow_succ, ht, zero_mul]
    ring_nf
    simp [ht, ht4]
  commutes' a := by simp

@[simp] theorem evaluate_epsilon {A : Type*} [CommRing A] [Algebra ℝ A] (t : A) (ht : t^3 = 0) :
    evaluate t ht epsilon = t := by simp [evaluate, epsilon]

/-- A real algebra map out of this stage is uniquely determined by epsilon. -/
theorem hom_ext {A : Type*} [CommRing A] [Algebra ℝ A] (f g : Stage →ₐ[ℝ] A)
    (h : f epsilon = g epsilon) : f = g := by
  ext z
  rw [normal_form z]
  simp only [map_add, map_mul, map_pow, AlgHom.commutes, h]

theorem universal {A : Type*} [CommRing A] [Algebra ℝ A] (t : A) (ht : t^3 = 0) :
    ∃! h : Stage →ₐ[ℝ] A, h epsilon = t := by
  refine ⟨evaluate t ht, evaluate_epsilon t ht, ?_⟩
  intro h hh
  exact hom_ext h _ (hh.trans (evaluate_epsilon t ht).symm)

theorem nilpotent_cube (a b : ℝ) : (ofCoeff 0 a b)^3 = 0 := by
  apply ext
  simp only [pow_succ, pow_zero, coeff_mul, coeff_one, coeff_ofCoeff, coeff_zero]
  norm_num

/-- Every pair of real parameters is valid, including noninvertible changes. -/
def reparam (a b : ℝ) : Stage →ₐ[ℝ] Stage := evaluate (ofCoeff 0 a b) (nilpotent_cube a b)

theorem coeff_reparam (a b : ℝ) (z : Stage) : coeff (reparam a b z) =
    ((coeff z).1, a*(coeff z).2.1, b*(coeff z).2.1+a^2*(coeff z).2.2) := by
  change coeff (algebraMap ℝ Stage (coeff z).1 +
    algebraMap ℝ Stage (coeff z).2.1 * ofCoeff 0 a b +
    algebraMap ℝ Stage (coeff z).2.2 * (ofCoeff 0 a b)^2) = _
  simp only [pow_two, coeff_add, coeff_mul, coeff_scalar, coeff_ofCoeff]
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  apply Prod.ext
  · rfl
  apply Prod.ext <;> ring

theorem reparam_epsilon (a b : ℝ) : reparam a b epsilon =
    algebraMap ℝ Stage a * epsilon + algebraMap ℝ Stage b * epsilon^2 := by
  apply ext
  rw [coeff_reparam, epsilon_sq, coeff_add, coeff_mul, coeff_mul]
  simp [epsilon]

end Applications.AD.SecondStage
