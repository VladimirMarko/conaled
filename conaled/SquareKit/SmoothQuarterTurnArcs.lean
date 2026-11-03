import SquareKit.SmoothOpenArcs
import SquareKit.SmoothOrdinaryPullbackCover
import Applications.Orbifolds.QuarterTurn

/-! The open complex disk in the finite real-coordinate smooth model. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory Opposite
open scoped ContDiff Manifold
namespace SquareKit.SmoothQuarterTurnArcs
open SmoothAlgebra SmoothPresentationSite EuclideanOpen
open Orbifolds.QuarterTurn

def complexCoordinates : (Fin 2 → ℝ) ≃L[ℝ] ℂ :=
  (LinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearEquiv.trans Complex.equivRealProdCLM.symm

def diskOpen : Set (Fin 2 → ℝ) := complexCoordinates ⁻¹' (disk : Set ℂ)

theorem diskOpen_open : IsOpen diskOpen := disk.isOpen.preimage complexCoordinates.continuous

def diskDomain : Domain := ⟨2, openDefining diskOpen diskOpen_open⟩

theorem diskDomain_mem (x : Fin 2 → ℝ) :
    x ∈ Localization.locus diskDomain.defining ↔ complexCoordinates x ∈ (disk : Set ℂ) := by
  change x ∈ Localization.locus (openDefining diskOpen diskOpen_open) ↔ _
  rw [openDefining_locus]
  rfl

/-- The real-coordinate domain is exactly the previously checked complex disk. -/
def diskPoints : Points diskDomain ≃ Disk where
  toFun x := ⟨complexCoordinates x.val, (diskDomain_mem x.val).mp x.property⟩
  invFun z := ⟨complexCoordinates.symm z.val, (diskDomain_mem _).mpr (by simp)⟩
  left_inv x := Subtype.ext (complexCoordinates.symm_apply_apply x.val)
  right_inv z := Subtype.ext (complexCoordinates.apply_symm_apply z.val)

def diskLinear (g : C4) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  complexCoordinates.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.mul ℝ ℂ (g.val : ℂ)).comp complexCoordinates.toContinuousLinearMap)

@[simp] theorem diskLinear_complex (g : C4) (x : Fin 2 → ℝ) :
    complexCoordinates (diskLinear g x) = (g.val : ℂ) * complexCoordinates x := by
  simp [diskLinear]

def diskMap (g : C4) : diskDomain ⟶ diskDomain where
  toFun x := diskPoints.symm (g • diskPoints x)
  smooth i := by
    change (fun x : Points diskDomain => (diskPoints.symm (g • diskPoints x)).val i) ∈ OpenFunctions.algebra _
    apply (OpenFunctions.representative_iff _ (fun x => diskLinear g x i) (fun x => rfl)).mpr
    exact ((contDiff_apply ℝ (fun _ : Fin 2 => ℝ) i).comp (diskLinear g).contDiff).contDiffOn

theorem diskMap_one : diskMap 1 = 𝟙 diskDomain := by
  apply OpenFunctions.Map.ext
  intro x
  change diskPoints.symm ((1 : C4) • diskPoints x) = x
  simp

theorem diskMap_mul (g h : C4) : diskMap (g*h) = diskMap h ≫ diskMap g := by
  apply OpenFunctions.Map.ext
  intro x
  change diskPoints.symm ((g*h) • diskPoints x) =
    diskPoints.symm (g • diskPoints (diskPoints.symm (h • diskPoints x)))
  simp [mul_smul]

def diskSheaf : Sheaf SmoothOpenSite.topology Type := embedding.obj diskDomain

def diskAction (g : C4) : diskSheaf ⟶ diskSheaf := embedding.map (diskMap g)

theorem diskAction_one : diskAction 1 = 𝟙 diskSheaf := by
  change embedding.map (diskMap 1) = 𝟙 (embedding.obj diskDomain)
  rw [diskMap_one]
  exact embedding.map_id diskDomain

theorem diskAction_mul (g h : C4) : diskAction (g*h) = diskAction h ≫ diskAction g := by
  change embedding.map (diskMap (g*h)) = embedding.map (diskMap h) ≫ embedding.map (diskMap g)
  rw [diskMap_mul, Functor.map_comp]

def coefficientAction {B : Type} [CommRing B] [Algebra ℝ B]
    (g : C4) (v : Fin 2 → B) : Fin 2 → B :=
  ![algebraMap ℝ B (g.val : ℂ).re * v 0 + algebraMap ℝ B (-(g.val : ℂ).im) * v 1,
    algebraMap ℝ B (g.val : ℂ).im * v 0 + algebraMap ℝ B (g.val : ℂ).re * v 1]

@[simp] theorem coefficientAction_one {B : Type} [CommRing B] [Algebra ℝ B]
    (v : Fin 2 → B) : coefficientAction (1 : C4) v = v := by
  funext i
  fin_cases i <;> simp [coefficientAction]

theorem coefficientAction_mul {B : Type} [CommRing B] [Algebra ℝ B]
    (g h : C4) (v : Fin 2 → B) :
    coefficientAction (g*h) v = coefficientAction g (coefficientAction h v) := by
  funext i
  fin_cases i <;> simp [coefficientAction, Complex.mul_re, Complex.mul_im,
    map_add, map_mul, map_sub, map_neg] <;> ring

theorem coefficientAction_natural {B C : Type} [CommRing B] [Algebra ℝ B] [Structure B]
    [CommRing C] [Algebra ℝ C] [Structure C] (f : Hom B C)
    (g : C4) (v : Fin 2 → B) :
    (fun i => f (coefficientAction g v i)) = coefficientAction g (fun i => f (v i)) := by
  funext i
  fin_cases i
  · change f (_ * _ + _ * _) = _
    rw [f.map_add, f.map_mul, f.map_mul, f.map_scalar, f.map_scalar]
    rfl
  · change f (_ * _ + _ * _) = _
    rw [f.map_add, f.map_mul, f.map_mul, f.map_scalar, f.map_scalar]
    rfl

theorem diskLinear_coordinates (g : C4) (v : Fin 2 → ℝ) :
    diskLinear g v = coefficientAction g v := by
  funext i
  fin_cases i <;> simp [diskLinear, coefficientAction, complexCoordinates,
    Complex.mul_re, Complex.mul_im, sub_eq_add_neg]
  ring

def coordinatePolynomial (g : C4) (i : Fin 2) : Free 2 :=
  coefficientAction g (fun j => generator j) i

theorem diskMap_coordinate (g : C4) (i : Fin 2) :
    Localization.pullback (diskMap g)
      (Localization.principalBase diskDomain.defining (generator i)) =
    Localization.principalBase diskDomain.defining (coordinatePolynomial g i) := by
  apply (Localization.toOpen_bijective diskDomain.defining).injective
  apply OpenFunctions.ext
  intro x
  rw [Localization.pullback_apply, Localization.toOpen_base]
  exact (congrFun (diskLinear_coordinates g x.val) i).trans (by fin_cases i <;> rfl)


theorem coordinatePolynomial_eval {B : Type} [CommRing B] [Algebra ℝ B] [Structure B]
    (h : Hom (Localization.Principal diskDomain.defining) B) (g : C4) (i : Fin 2) :
    h (Localization.principalBase diskDomain.defining (coordinatePolynomial g i)) =
      coefficientAction g (fun j => h (Localization.principalBase diskDomain.defining (generator j))) i := by
  change (Hom.comp h (Localization.principalBase diskDomain.defining)) (coordinatePolynomial g i) = _
  let k : Hom (Free 2) B := Hom.comp h (Localization.principalBase diskDomain.defining)
  fin_cases i
  · change k (_ * _ + _ * _) = _
    rw [k.map_add, k.map_mul, k.map_mul, k.map_scalar, k.map_scalar]
    rfl
  · change k (_ * _ + _ * _) = _
    rw [k.map_add, k.map_mul, k.map_mul, k.map_scalar, k.map_scalar]
    rfl

attribute [local instance] DualExtension.smoothStructure

theorem coefficientAction_snd {B : Type} [CommRing B] [Algebra ℝ B]
    (g : C4) (v : Fin 2 → DualNumber B) (i : Fin 2) :
    (coefficientAction g v i).snd = coefficientAction g (fun j => (v j).snd) i := by
  have hf (r : ℝ) : (algebraMap ℝ (DualNumber B) r).fst = algebraMap ℝ B r := rfl
  have hs (r : ℝ) : (algebraMap ℝ (DualNumber B) r).snd = 0 := rfl
  fin_cases i <;> simp [coefficientAction, TrivSqZeroExt.snd_mul,
    hf, hs]

/-- The finite action acts on the velocity coordinate at every presentation,
not only at ordinary points. -/
theorem disk_coefficients_action (g : C4) (A : Code) (h : code diskDomain ⟶ dual A) :
    (SmoothOpenArcs.stageCoefficients diskDomain A
      (Localization.pullback (diskMap g) ≫ h)).2 =
      coefficientAction g (SmoothOpenArcs.stageCoefficients diskDomain A h).2 := by
  funext i
  change (dualToActual A (smoothMap h (Localization.pullback (diskMap g)
    (Localization.principalBase diskDomain.defining (generator i))))).snd = _
  rw [diskMap_coordinate]
  have he := coordinatePolynomial_eval (Hom.comp (dualToActual A) h) g i
  exact (congrArg TrivSqZeroExt.snd he).trans (coefficientAction_snd g _ i)

/-- The previous calculation is the action of the constructed disk sheaf,
read through the sheaf coefficient comparison. -/
theorem disk_sheaf_coefficients_action (g : C4) (A : Code)
    (h : diskSheaf.obj.obj (SmoothGeometricKL.atStage (dual A))) :
    ((SmoothOpenArcs.openCoefficientsIso diskDomain).hom.hom.app (SmoothGeometricKL.atStage A)
      ((diskAction g).hom.app (SmoothGeometricKL.atStage (dual A)) h)).2 =
      coefficientAction g
        ((SmoothOpenArcs.openCoefficientsIso diskDomain).hom.hom.app (SmoothGeometricKL.atStage A) h).2 :=
  disk_coefficients_action g A h.unop

/-- The checked classical derivative is precisely the real coefficient action. -/
theorem disk_coefficients_classical (g : C4) (z : Disk) (v : Fin 2 → ℝ) :
    complexCoordinates (coefficientAction g v) =
      mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) (fun w : Disk => g • w) z (complexCoordinates v) := by
  rw [← diskLinear_coordinates, diskLinear_complex, disk_tangent]

def coordinateOrigin : Points diskDomain := diskPoints.symm origin

theorem coordinateOrigin_fixed (g : C4) :
    (show Map diskDomain diskDomain from diskMap g).toFun coordinateOrigin = coordinateOrigin := by
  change diskPoints.symm (g • diskPoints (diskPoints.symm origin)) = diskPoints.symm origin
  rw [Equiv.apply_symm_apply]
  have h : g • origin = origin := (MulAction.mem_stabilizer_iff).mp (by
    rw [origin_stabilizer]; trivial)
  rw [h]

/-- All four distinct labels survive in the origin stabilizer. -/
def originLabelEquiv :
    {g : C4 // (show Map diskDomain diskDomain from diskMap g).toFun coordinateOrigin = coordinateOrigin} ≃ C4 where
  toFun := Subtype.val
  invFun g := ⟨g, coordinateOrigin_fixed g⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem origin_label_count :
    Nat.card {g : C4 // (show Map diskDomain diskDomain from diskMap g).toFun coordinateOrigin = coordinateOrigin} = 4 :=
  (Nat.card_congr originLabelEquiv).trans card_C4

theorem nonzero_label (x : Points diskDomain) (hx : (diskPoints x : ℂ) ≠ 0)
    (g : C4) (hg : (show Map diskDomain diskDomain from diskMap g).toFun x = x) : g = 1 := by
  have he : g • diskPoints x = diskPoints x := by
    have h := congrArg diskPoints hg
    simpa [diskMap] using h
  have hm : g ∈ MulAction.stabilizer C4 (diskPoints x) := he
  rw [nonzero_stabilizer _ hx] at hm
  exact hm

/-- A finite ineffective action keeps its labels while every scalar map is identity. -/
def ineffectiveScalarAction (_g : C4) : SmoothOpenSite.scalar ⟶ SmoothOpenSite.scalar := 𝟙 _

theorem ineffectiveScalarAction_one : ineffectiveScalarAction 1 = 𝟙 _ := rfl

theorem ineffectiveScalarAction_mul (g h : C4) :
    ineffectiveScalarAction (g*h) = ineffectiveScalarAction h ≫ ineffectiveScalarAction g := by
  simp [ineffectiveScalarAction]

theorem quarterTurn_ne_one : quarterTurn ≠ (1 : C4) := by
  intro h
  have hi := congrArg (fun g : C4 => (g.val : ℂ).im) h
  norm_num [quarterTurn] at hi

theorem ineffective_distinct_labels :
    quarterTurn ≠ (1 : C4) ∧ ineffectiveScalarAction quarterTurn = ineffectiveScalarAction 1 :=
  ⟨quarterTurn_ne_one, rfl⟩

theorem ineffective_coefficients (g : C4) (X : Sheaf SmoothOpenSite.topology Type)
    (h : SheafRelation.product SmoothOpenSite.infinitesimal X ⟶ SmoothOpenSite.scalar) :
    SmoothGeometricKL.coefficients (h ≫ ineffectiveScalarAction g) = SmoothGeometricKL.coefficients h := by
  simp [ineffectiveScalarAction]

end SquareKit.SmoothQuarterTurnArcs
