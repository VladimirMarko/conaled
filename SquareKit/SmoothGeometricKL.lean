import SquareKit.SmoothGeometricDual
import SquareKit.AffineExponential

/-! Experimental geometric KL: universal evaluation in the actual dual presentation
constructs an inverse to the affine map into the sheaf exponential. -/
noncomputable section
namespace SquareKit.SmoothGeometricKL
open CategoryTheory Opposite SmoothAlgebra SmoothPresentationSite SheafRelation SheafFunction
attribute [local instance] DualExtension.smoothStructure

variable {X : Sheaf topology Type}

theorem restrict_comp (F : Sheaf topology Type) {A B C : Code}
    (f : A ⟶ B) (g : B ⟶ C) (x : F.obj.obj (atStage A)) :
    F.obj.map (stageMap g) (F.obj.map (stageMap f) x) =
      F.obj.map (stageMap (f ≫ g)) x := by
  change (F.obj.map (stageMap f) ≫ F.obj.map (stageMap g)) x = _
  rw [← F.obj.map_comp]
  rfl

theorem operation_natural (h : product infinitesimal X ⟶ scalar)
    {A B : Code} (f : A ⟶ B) (d : infinitesimal.obj.obj (atStage A))
    (x : X.obj.obj (atStage A)) :
    h.hom.app (atStage B) (infinitesimal.obj.map (stageMap f) d,
      X.obj.map (stageMap f) x) = ringMap f (h.hom.app (atStage A) (d, x)) :=
  congrArg (fun k : (product infinitesimal X).obj.obj (atStage A) ⟶
    scalar.obj.obj (atStage B) => k (d, x)) (h.hom.naturality (stageMap f))

/-- Evaluate at the universal infinitesimal after extending the parameter. -/
def universalValue (h : product infinitesimal X ⟶ scalar) (A : Code)
    (x : X.obj.obj (atStage A)) : DualNumber (Carrier A) :=
  dualToActual A (h.hom.app (atStage (dual A)) (eps A, X.obj.map (stageMap (inl A)) x))

theorem universalValue_natural (h : product infinitesimal X ⟶ scalar)
    {A B : Code} (f : A ⟶ B) (x : X.obj.obj (atStage A)) :
    universalValue h B (X.obj.map (stageMap f) x) =
      (⟨ringMap f (universalValue h A x).fst,
        ringMap f (universalValue h A x).snd⟩ : DualNumber (Carrier B)) := by
  have h' := operation_natural h (dualMap f) (eps A)
    (X.obj.map (stageMap (inl A)) x)
  rw [dualMap_eps, restrict_comp, dualMap_inl, ← restrict_comp] at h'
  exact (congrArg (dualToActual B) h').trans (dualMap_actual f _)

/-- Coefficients are a natural pair, extracted without choosing external functions. -/
def coefficients (h : product infinitesimal X ⟶ scalar) : X ⟶ product scalar scalar :=
  ⟨{ app A := ↾fun x => ((universalValue h A.unop.unop x).fst,
       (universalValue h A.unop.unop x).snd)
     naturality A B f := by
       ext x
       apply Prod.ext
       · exact (congrArg TrivSqZeroExt.fst
           (universalValue_natural h f.unop.unop x))
       · exact (congrArg TrivSqZeroExt.snd
           (universalValue_natural h f.unop.unop x)) }⟩

theorem universal_reconstruction (h : product infinitesimal X ⟶ scalar)
    (A : Code) (d : infinitesimal.obj.obj (atStage A)) (x : X.obj.obj (atStage A)) :
    h.hom.app (atStage A) (d, x) =
      (universalValue h A x).fst + (universalValue h A x).snd * d.val := by
  let f : dual A ⟶ A := dualLift A A Hom.ident d
  have he : infinitesimal.obj.map (stageMap f) (eps A) = d :=
    Subtype.ext (dualLift_eps _ _ _ _)
  have hi : inl A ≫ f = 𝟙 A := dualLift_inl _ _ _ _
  have hx : X.obj.map (stageMap f) (X.obj.map (stageMap (inl A)) x) = x := by
    rw [restrict_comp, hi]
    change X.obj.map (𝟙 _) x = x
    simp
  have h' := operation_natural h f (eps A) (X.obj.map (stageMap (inl A)) x)
  rw [he, hx] at h'
  exact h'

/-- Reconstruction as an equality of sheaf arrows. -/
def rebuild (p : X ⟶ product scalar scalar) : product infinitesimal X ⟶ scalar :=
  parameterMap infinitesimal p ≫ affineBody

theorem rebuild_coefficients (h : product infinitesimal X ⟶ scalar) :
    rebuild (coefficients h) = h := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext A
  ext p
  exact (universal_reconstruction h A.unop.unop p.1 p.2).symm

theorem coefficients_rebuild (p : X ⟶ product scalar scalar) :
    coefficients (rebuild p) = p := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext A
  ext x
  have hp := congrArg (fun k : X.obj.obj A ⟶ (product scalar scalar).obj.obj
    (atStage (dual A.unop.unop)) => k x) (p.hom.naturality (stageMap (inl A.unop.unop)))
  change p.hom.app (atStage (dual A.unop.unop))
    (X.obj.map (stageMap (inl A.unop.unop)) x) =
    (ringMap (inl A.unop.unop) (p.hom.app A x).1,
      ringMap (inl A.unop.unop) (p.hom.app A x).2) at hp
  change ((universalValue (rebuild p) A.unop.unop x).fst,
    (universalValue (rebuild p) A.unop.unop x).snd) = _
  have hv : universalValue (rebuild p) A.unop.unop x =
      (⟨(p.hom.app A x).1, (p.hom.app A x).2⟩ : DualNumber (Carrier A.unop.unop)) := by
    unfold universalValue rebuild
    change dualToActual A.unop.unop ((p.hom.app _
      (X.obj.map (stageMap (inl A.unop.unop)) x)).1 +
      (p.hom.app _ (X.obj.map (stageMap (inl A.unop.unop)) x)).2 *
      (eps A.unop.unop).val) = _
    rw [hp, Hom.map_add, Hom.map_mul]
    have hi (a : Carrier A.unop.unop) :
        dualToActual A.unop.unop (ringMap (inl A.unop.unop) a) = TrivSqZeroExt.inl a :=
      congrArg (fun h : Hom (Carrier A.unop.unop) (DualNumber (Carrier A.unop.unop)) => h a)
        (Presentation.toDual_inclusion A.unop.unop.equations)
    rw [hi, hi]
    change _ + _ * (Presentation.toDual A.unop.unop.equations
      (Presentation.dualEps A.unop.unop.equations)) = _
    rw [Presentation.toDual_eps]
    exact AlgebraicKL.dual_reconstruct _ _
  exact congrArg (fun z => (z.fst, z.snd)) hv

theorem coefficients_parameter {Y : Sheaf topology Type}
    (h : product infinitesimal X ⟶ scalar) (p : Y ⟶ X) :
    coefficients (parameterMap infinitesimal p ≫ h) = p ≫ coefficients h := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext A
  ext y
  have hp := congrArg (fun k : Y.obj.obj A ⟶ X.obj.obj (atStage (dual A.unop.unop)) => k y)
    (p.hom.naturality (stageMap (inl A.unop.unop)))
  change p.hom.app _ (Y.obj.map _ y) = X.obj.map _ (p.hom.app A y) at hp
  change ((dualToActual _ (h.hom.app _ (eps _, p.hom.app _ (Y.obj.map _ y)))).fst,
    (dualToActual _ (h.hom.app _ (eps _, p.hom.app _ (Y.obj.map _ y)))).snd) = _
  rw [hp]
  rfl

abbrev functions := exponential infinitesimal scalar

def extract : functions ⟶ product scalar scalar := coefficients (evaluation infinitesimal scalar)

theorem extract_curry (h : product infinitesimal X ⟶ scalar) :
    curry h ≫ extract = coefficients h :=
  AffineExponential.extract_curry coefficients coefficients_parameter h

theorem affine_extract : affine ≫ extract = 𝟙 _ :=
  (AffineExponential.iso coefficients coefficients_parameter affineBody
    rebuild_coefficients coefficients_rebuild).hom_inv_id

theorem extract_affine : extract ≫ affine = 𝟙 _ :=
  (AffineExponential.iso coefficients coefficients_parameter affineBody
    rebuild_coefficients coefficients_rebuild).inv_hom_id

/-- First-order categorical KL for the original affine map. -/
def kl : product scalar scalar ≅ functions where
  hom := affine
  inv := extract
  hom_inv_id := affine_extract
  inv_hom_id := extract_affine

theorem coefficients_unique (h : product infinitesimal X ⟶ scalar)
    (p : X ⟶ product scalar scalar) (hp : rebuild p = h) : coefficients h = p := by
  calc
    coefficients h = curry h ≫ kl.inv := (extract_curry h).symm
    _ = curry (rebuild p) ≫ kl.inv := by rw [hp]
    _ = (p ≫ kl.hom) ≫ kl.inv := by rw [rebuild, affine_parameters]; rfl
    _ = p := by rw [Category.assoc, kl.hom_inv_id, Category.comp_id]

/-- Equation at all stages, for two natural coefficient maps. -/
def AffineEquation (h : product infinitesimal X ⟶ scalar) (a b : X ⟶ scalar) : Prop :=
  ∀ (A : Code) (d : infinitesimal.obj.obj (atStage A)) (x : X.obj.obj (atStage A)),
    h.hom.app (atStage A) (d, x) = a.hom.app (atStage A) x + b.hom.app (atStage A) x * d.val

theorem rebuild_eq_of_equation (h : product infinitesimal X ⟶ scalar)
    (a b : X ⟶ scalar) (he : AffineEquation h a b) : rebuild (lift a b) = h := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext A
  ext p
  exact (he A.unop.unop p.1 p.2).symm

/-- KL with arbitrary sheaf parameters and unique natural coefficients. -/
theorem allParameters (h : product infinitesimal X ⟶ scalar) :
    ∃! p : (X ⟶ scalar) × (X ⟶ scalar), AffineEquation h p.1 p.2 := by
  refine ⟨(coefficients h ≫ fst _ _, coefficients h ≫ snd _ _), ?_, ?_⟩
  · exact universal_reconstruction h
  · intro p hp
    have hc := coefficients_unique h (lift p.1 p.2) (rebuild_eq_of_equation h p.1 p.2 hp)
    apply Prod.ext
    · exact (congrArg (fun k => k ≫ fst scalar scalar) hc).symm
    · exact (congrArg (fun k => k ≫ snd scalar scalar) hc).symm

/-- Evaluation reconstruction uses the actual internal function object. -/
theorem evaluation_extract (A : Code) (d : infinitesimal.obj.obj (atStage A))
    (f : functions.obj.obj (atStage A)) :
    (evaluation infinitesimal scalar).hom.app (atStage A) (d, f) =
      (extract.hom.app (atStage A) f).1 + (extract.hom.app (atStage A) f).2 * d.val :=
  universal_reconstruction (evaluation infinitesimal scalar) A d f

end SquareKit.SmoothGeometricKL
