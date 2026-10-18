import Applications.Linear.Matrix
import Applications.Orbifold.ProjectiveMotion

/-! Certified matrix realizations of positive similitudes in any finite basis.
Matrices store coordinates and preservation evidence, not a semantic function.
No addition operation is exposed on the certified carrier. -/
noncomputable section
open Matrix
namespace MatrixBackend
namespace Hermitian
variable {V ι : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
variable (β : Module.Basis ι ℂ V) (H : Orbifold.Form V)

abbrev formMatrix : Matrix ι ι ℂ := LinearMap.toMatrix₂ β β H

def linearEquiv : (Matrix ι ι ℂ)ˣ ≃* (V ≃ₗ[ℂ] V) :=
  (Units.mapEquiv (Matrix.toLinAlgEquiv β).toMulEquiv).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv ℂ V)

@[simp] theorem linearEquiv_apply (A : (Matrix ι ι ℂ)ˣ) (v : V) :
    linearEquiv β A v = Matrix.toLin β β A.val v := rfl

theorem coordinates (A : (Matrix ι ι ℂ)ˣ) (v : V) :
    β.equivFun (linearEquiv β A v) = A.val *ᵥ β.equivFun v := by
  ext i
  simp [linearEquiv_apply, Matrix.toLin_apply, Module.Basis.equivFun_apply,
    Finsupp.single_apply]

/-- The matrix identity is equivalent to preservation of the abstract form. -/
theorem preservation_iff (A : (Matrix ι ι ℂ)ˣ) (c : ℝ) :
    A.valᴴ * formMatrix β H * A.val = (c : ℂ) • formMatrix β H ↔
    ∀ v w, H (linearEquiv β A v) (linearEquiv β A w) = (c : ℂ) * H v w := by
  have eval (v w : V) : H (linearEquiv β A v) (linearEquiv β A w) =
      star (β.equivFun v) ⬝ᵥ (A.valᴴ * formMatrix β H * A.val) *ᵥ β.equivFun w := by
    rw [apply_eq_star_dotProduct_toMatrix₂_mulVec β]
    change star (β.equivFun (linearEquiv β A v)) ⬝ᵥ
      (formMatrix β H) *ᵥ β.equivFun (linearEquiv β A w) = _
    rw [coordinates, coordinates, Matrix.star_mulVec]
    simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  constructor
  · intro h v w
    rw [eval, h, apply_eq_star_dotProduct_toMatrix₂_mulVec β v w]
    simp [Matrix.smul_mulVec, dotProduct_smul]
  · intro h
    ext i j
    have hi := h (β i) (β j)
    rw [eval] at hi
    simpa [Module.Basis.equivFun_apply, Module.Basis.repr_self, formMatrix,
      LinearMap.toMatrix₂_apply, dotProduct, Matrix.mulVec, Finsupp.single_apply] using hi

/-- A matrix is certified by its positive preservation identity. -/
def certified : Subgroup (Matrix ι ι ℂ)ˣ :=
  (Orbifold.similitudes H).comap (linearEquiv β).toMonoidHom

abbrev Certified := ↥(certified β H)

theorem certified_iff (A : (Matrix ι ι ℂ)ˣ) : A ∈ certified β H ↔
    ∃ c : ℝ, 0 < c ∧ A.valᴴ * formMatrix β H * A.val = (c : ℂ) • formMatrix β H := by
  change (∃ c : ℝ, 0 < c ∧ _) ↔ _
  simp only [preservation_iff, MulEquiv.coe_toMonoidHom]

/-- Inverse coordinate conversions before the projective quotient. -/
def decodeEquiv : Certified β H ≃* Orbifold.Similitude H where
  toFun A := ⟨linearEquiv β A.val, A.property⟩
  invFun L := ⟨(linearEquiv β).symm L.val, by
    change linearEquiv β ((linearEquiv β).symm L.val) ∈ Orbifold.similitudes H
    simpa only [MulEquiv.apply_symm_apply] using L.property⟩
  left_inv A := Subtype.ext ((linearEquiv β).symm_apply_apply A.val)
  right_inv L := Subtype.ext ((linearEquiv β).apply_symm_apply L.val)
  map_mul' A B := Subtype.ext (map_mul (linearEquiv β) A.val B.val)

def decode : Certified β H →* Orbifold.Motion H :=
  Orbifold.Similitude.motion.comp (decodeEquiv β H).toMonoidHom

@[simp] theorem decode_encode (L : Orbifold.Similitude H) :
    decodeEquiv β H ((decodeEquiv β H).symm L) = L := (decodeEquiv β H).apply_symm_apply L

@[simp] theorem encode_decode (A : Certified β H) :
    (decodeEquiv β H).symm (decodeEquiv β H A) = A := (decodeEquiv β H).symm_apply_apply A

@[reducible] def representation : Squares.Rep :=
  ⟨Certified β H, Orbifold.Motion H, decode β H⟩

@[reducible] def linearRepresentation : Squares.Rep :=
  ⟨Certified β H, Orbifold.Similitude H, decodeEquiv β H⟩

def linearCompositionSquare : Squares.Square
    (Squares.product (linearRepresentation β H) (linearRepresentation β H))
    (linearRepresentation β H) where
  impl p := p.1 * p.2
  spec p := p.1 * p.2
  commutes p := (decodeEquiv β H).map_mul p.1 p.2

@[reducible] def quotientRepresentation : Squares.Rep :=
  ⟨Orbifold.Similitude H, Orbifold.Motion H, Orbifold.Similitude.motion⟩

def quotientCompositionSquare : Squares.Square
    (Squares.product (quotientRepresentation H) (quotientRepresentation H))
    (quotientRepresentation H) where
  impl p := p.1 * p.2
  spec p := p.1 * p.2
  commutes p := Orbifold.Similitude.motion.map_mul p.1 p.2

def compositionSquare : Squares.Square
    (Squares.product (representation β H) (representation β H)) (representation β H) where
  impl p := p.1 * p.2
  spec p := p.1 * p.2
  commutes p := (decode β H).map_mul p.1 p.2

/-- The matrix-to-linear and linear-to-projective layers paste exactly. -/
theorem composition_is_paste : compositionSquare β H =
    Squares.vertical
      (A := Squares.product (linearRepresentation β H) (linearRepresentation β H))
      (B := linearRepresentation β H)
      (AS := Orbifold.Motion H × Orbifold.Motion H) (BS := Orbifold.Motion H)
      (fun p => (Orbifold.Similitude.motion (H := H) p.1, Orbifold.Similitude.motion (H := H) p.2))
      (fun L => Orbifold.Similitude.motion (H := H) L) (linearCompositionSquare β H)
      (quotientCompositionSquare H) (fun _ => rfl) := rfl

def identitySquare : Squares.Square Squares.terminal (representation β H) where
  impl _ := 1
  spec _ := 1
  commutes _ := (decode β H).map_one

def inverseSquare : Squares.Square (representation β H) (representation β H) where
  impl := Inv.inv
  spec := Inv.inv
  commutes A := map_inv (decode β H) A

/-- Certified coordinates of a negative projective representative. -/
abbrev PointCoordinates := {x : ι → ℂ // (H (β.equivFun.symm x) (β.equivFun.symm x)).re < 0}

def pointDecode (x : PointCoordinates β H) : Orbifold.NegativeLine H := by
  have hn : β.equivFun.symm x.val ≠ 0 := by
    intro h
    have := x.property
    simp [h] at this
  exact ⟨Projectivization.mk ℂ _ hn, (Orbifold.negative_mk_iff _ _ _).mpr x.property⟩

@[reducible] def pointRepresentation : Squares.Rep :=
  ⟨PointCoordinates β H, Orbifold.NegativeLine H, pointDecode β H⟩

def applyCoordinates (A : Certified β H) (x : PointCoordinates β H) : PointCoordinates β H := by
  refine ⟨A.val.val *ᵥ x.val, ?_⟩
  have heq : β.equivFun.symm (A.val.val *ᵥ x.val) =
      linearEquiv β A.val (β.equivFun.symm x.val) := by
    apply β.equivFun.injective
    rw [coordinates]
    simp only [LinearEquiv.apply_symm_apply]
  rw [heq]
  obtain ⟨c, hc, hA⟩ := (decodeEquiv β H A).preserves
  rw [show H (linearEquiv β A.val (β.equivFun.symm x.val))
    (linearEquiv β A.val (β.equivFun.symm x.val)) =
    (c : ℂ) * H (β.equivFun.symm x.val) (β.equivFun.symm x.val) from hA _ _]
  simpa using mul_neg_of_pos_of_neg hc x.property

def applicationSquare : Squares.Square
    (Squares.product (representation β H) (pointRepresentation β H)) (pointRepresentation β H) where
  impl p := applyCoordinates β H p.1 p.2
  spec p := p.1 • p.2
  commutes p := by
    apply Subtype.ext
    change Projectivization.mk ℂ _ _ = Projectivization.mk ℂ _ _
    congr 1
    apply β.equivFun.injective
    change β.equivFun (β.equivFun.symm (p.1.val.val *ᵥ p.2.val)) =
      β.equivFun (linearEquiv β p.1.val (β.equivFun.symm p.2.val))
    rw [coordinates]
    simp only [LinearEquiv.apply_symm_apply]

@[simp] theorem encode_matrix (L : Orbifold.Similitude H) :
    ((decodeEquiv β H).symm L).val.val = LinearMap.toMatrix β β L.val.toLinearMap := rfl

variable (γ : Module.Basis ι ℂ V)

/-- Re-encode the same abstract similitude in another basis. -/
def changeBasis : Certified β H ≃* Certified γ H :=
  (decodeEquiv β H).trans (decodeEquiv γ H).symm

@[simp] theorem changeBasis_decode (A : Certified β H) :
    decode γ H (changeBasis β H γ A) = decode β H A := by
  simp [decode, changeBasis]

/-- C converts new coordinates to old; its inverse is the reverse conversion. -/
def basisMatrix : (Matrix ι ι ℂ)ˣ where
  val := LinearMap.toMatrix γ β LinearMap.id
  inv := LinearMap.toMatrix β γ LinearMap.id
  val_inv := by rw [← LinearMap.toMatrix_comp]; simp
  inv_val := by rw [← LinearMap.toMatrix_comp]; simp

theorem changeBasis_matrix (A : Certified β H) :
    (changeBasis β H γ A).val.val =
      (basisMatrix β γ).inv * A.val.val * (basisMatrix β γ).val := by
  change LinearMap.toMatrix γ γ (linearEquiv β A.val).toLinearMap = _
  have ha : A.val.val = LinearMap.toMatrix β β (linearEquiv β A.val).toLinearMap := by
    exact (LinearMap.toMatrix_toLin β β A.val.val).symm
  rw [ha]
  change _ = LinearMap.toMatrix β γ LinearMap.id * _ * LinearMap.toMatrix γ β LinearMap.id
  rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
  simp

theorem changeBasis_form : formMatrix γ H =
    (basisMatrix β γ).valᴴ * formMatrix β H * (basisMatrix β γ).val := by
  ext i j
  rw [show formMatrix γ H i j = H (γ i) (γ j) from LinearMap.toMatrix₂_apply γ γ H i j,
    apply_eq_star_dotProduct_toMatrix₂_mulVec β]
  simp only [basisMatrix, LinearMap.toMatrix_apply, LinearMap.id_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  simp [mul_assoc, mul_comm, mul_left_comm]

/-- Scalar rescaling changes raw matrices but preserves decoded motions. -/
def rescale (a : ℂˣ) (A : Certified β H) : Certified β H :=
  (decodeEquiv β H).symm (Orbifold.Similitude.scalar H a * decodeEquiv β H A)

@[simp] theorem rescale_decode (a : ℂˣ) (A : Certified β H) :
    decode β H (rescale β H a A) = decode β H A := by
  simp [decode, rescale]

theorem rescale_matrix (a : ℂˣ) (A : Certified β H) :
    (rescale β H a A).val.val = (a : ℂ) • A.val.val := by
  rw [rescale, encode_matrix]
  have h : (Orbifold.Similitude.scalar H a * decodeEquiv β H A).val.toLinearMap =
      (a : ℂ) • (linearEquiv β A.val).toLinearMap := by ext v; rfl
  rw [h, map_smul]
  congr 1
  exact LinearMap.toMatrix_toLin β β _

end Hermitian
end MatrixBackend
