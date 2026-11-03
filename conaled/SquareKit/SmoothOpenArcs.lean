import SquareKit.SmoothDualSheaf
import SquareKit.SmoothOpenCoordinates

/-! D-arcs of ordinary principal opens, at every smooth presentation stage.
The open condition constrains the zero coefficient and leaves velocity free. -/
noncomputable section
open CategoryTheory Opposite
namespace SquareKit.SmoothOpenArcs
open SmoothAlgebra SmoothPresentationSite SmoothGeometricKL EuclideanOpen
attribute [local instance] DualExtension.smoothStructure

variable {B : Type} [CommRing B] [Algebra ℝ B] [Structure B]

def residue : Hom (DualNumber B) B where
  toFun := TrivSqZeroExt.fst
  map_act _ _ := rfl

/-- Localization in dual numbers requires exactly that the zero coefficient
lie in the localized open. This holds for any smooth coefficient algebra. -/
def localizationCoefficients (f : Free n) :
    Hom (Localization.Principal f) (DualNumber B) ≃
      Hom (Localization.Principal f) B × (Fin n → B) where
  toFun h := (Hom.comp residue h, fun i => (h (Localization.principalBase f (generator i))).snd)
  invFun p := (Localization.pointEquiv (B := DualNumber B) f).symm ⟨
    fun i => (⟨p.1 (Localization.principalBase f (generator i)), p.2 i⟩ : DualNumber B),
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ((Localization.pointEquiv f p.1).property)⟩
  left_inv h := by
    apply (Localization.pointEquiv (B := DualNumber B) f).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    funext i
    change (⟨(h (Localization.principalBase f (generator i))).fst,
      (h (Localization.principalBase f (generator i))).snd⟩ : DualNumber B) = _
    rfl
  right_inv p := by
    apply Prod.ext
    · apply (Localization.pointEquiv f).injective
      apply Subtype.ext
      funext i
      have h := congrArg (fun z => (z.val i).fst)
        ((Localization.pointEquiv (B := DualNumber B) f).apply_symm_apply ⟨
          fun j => (⟨p.1 (Localization.principalBase f (generator j)), p.2 j⟩ : DualNumber B),
          TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ((Localization.pointEquiv f p.1).property)⟩)
      exact h
    · funext i
      have h := congrArg (fun z => (z.val i).snd)
        ((Localization.pointEquiv (B := DualNumber B) f).apply_symm_apply ⟨
          fun j => (⟨p.1 (Localization.principalBase f (generator j)), p.2 j⟩ : DualNumber B),
          TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ((Localization.pointEquiv f p.1).property)⟩)
      exact h

/-- The dual presentation is compared with actual dual numbers before extracting
coordinates. All maps of smooth algebras remain available. -/
def stageCoefficients (U : Domain) (A : Code) :
    (code U ⟶ dual A) ≃ (code U ⟶ A) × (Fin U.dimension → Carrier A) :=
  (show (code U ⟶ dual A) ≃ Hom (Localization.Principal U.defining) (DualNumber (Carrier A)) from
    { toFun h := Hom.comp (dualToActual A) h
      invFun h := Hom.comp (dualFromActual A) h
      left_inv h := by
        change Hom.comp (dualFromActual A) (Hom.comp (dualToActual A) h) = h
        rw [Hom.comp_assoc, dual_comparison_inverse_rev, Hom.ident_comp]
      right_inv h := by
        change Hom.comp (dualToActual A) (Hom.comp (dualFromActual A) h) = h
        rw [Hom.comp_assoc, dual_comparison_inverse, Hom.ident_comp] }).trans
    (localizationCoefficients U.defining)

theorem stageCoefficients_zero (U : Domain) (A : Code) (h : code U ⟶ dual A) :
    (stageCoefficients U A h).1 = h ≫ SmoothOpenSite.dualZero A := by
  apply Hom.ext
  intro z
  exact (SmoothOpenSite.dualZero_actual A (smoothMap h z)).symm

theorem stageCoefficients_natural (U : Domain) {A B : Code}
    (f : A ⟶ B) (h : code U ⟶ dual A) :
    stageCoefficients U B (h ≫ dualMap f) =
      ((stageCoefficients U A h).1 ≫ f,
        fun i => smoothMap f ((stageCoefficients U A h).2 i)) := by
  apply Prod.ext
  · apply Hom.ext
    intro z
    exact congrArg TrivSqZeroExt.fst (dualMap_actual f (smoothMap h z))
  · funext i
    exact congrArg TrivSqZeroExt.snd
      (dualMap_actual f (smoothMap h (Localization.principalBase U.defining (generator i))))

/-- Every generalized arc in an ordinary open is its base point and a free
velocity vector. This is an isomorphism of sheaves, not just real points. -/
def openCoefficientsIso (U : Domain) :
    SmoothOpenSite.dualSheaf (embedding.obj U) ≅
      SheafRelation.product (embedding.obj U) (SmoothOpenSite.scalarPower U.dimension) :=
  let i := NatIso.ofComponents (fun A =>
    (show (SmoothOpenSite.dualSheaf (embedding.obj U)).obj.obj A ≃
      (SheafRelation.product (embedding.obj U) (SmoothOpenSite.scalarPower U.dimension)).obj.obj A from
      { toFun h := ((stageCoefficients U A.unop.unop h.unop).1.op,
          (stageCoefficients U A.unop.unop h.unop).2)
        invFun p := ((stageCoefficients U A.unop.unop).symm (p.1.unop,p.2)).op
        left_inv h := congrArg Quiver.Hom.op ((stageCoefficients U A.unop.unop).symm_apply_apply h.unop)
        right_inv p := by
          have h := (stageCoefficients U A.unop.unop).apply_symm_apply (p.1.unop,p.2)
          exact congrArg (fun q => (q.1.op,q.2)) h }).toIso) (by
    intro A B f
    ext h
    exact congrArg (fun q => (q.1.op,q.2))
      (stageCoefficients_natural U f.unop.unop h.unop))
  { hom := ⟨i.hom⟩
    inv := ⟨i.inv⟩
    hom_inv_id := by ext A h; exact congrArg (fun k => k.app A h) i.hom_inv_id
    inv_hom_id := by ext A h; exact congrArg (fun k => k.app A h) i.inv_hom_id }

/-- The actual exponential has the same coefficient comparison. -/
def arcCoefficientsIso (U : Domain) :
    SheafFunction.exponential SmoothOpenSite.infinitesimal (embedding.obj U) ≅
      SheafRelation.product (embedding.obj U) (SmoothOpenSite.scalarPower U.dimension) :=
  (show SheafFunction.exponential SmoothOpenSite.infinitesimal (embedding.obj U) ≅
      SmoothOpenSite.dualSheaf (embedding.obj U) from
    { hom := ⟨(SmoothOpenSite.dualSectionsIso (embedding.obj U)).hom⟩
      inv := ⟨(SmoothOpenSite.dualSectionsIso (embedding.obj U)).inv⟩
      hom_inv_id := by
        ext A x
        exact congrArg (fun k => k.app A x) (SmoothOpenSite.dualSectionsIso (embedding.obj U)).hom_inv_id
      inv_hom_id := by
        ext A x
        exact congrArg (fun k => k.app A x) (SmoothOpenSite.dualSectionsIso (embedding.obj U)).inv_hom_id }) ≪≫ openCoefficientsIso U

/-- In particular the comparison is available for every parameter sheaf. -/
def parameterCoefficients (U : Domain) (X : Sheaf SmoothOpenSite.topology Type) :
    (SheafRelation.product SmoothOpenSite.infinitesimal X ⟶ embedding.obj U) ≃
      (X ⟶ SheafRelation.product (embedding.obj U) (SmoothOpenSite.scalarPower U.dimension)) where
  toFun h := SheafFunction.curry h ≫ (arcCoefficientsIso U).hom
  invFun k := SheafFunction.uncurry (k ≫ (arcCoefficientsIso U).inv)
  left_inv h := by simp
  right_inv k := by simp

theorem parameterCoefficients_natural (U : Domain)
    {X Y : Sheaf SmoothOpenSite.topology Type} (f : Y ⟶ X)
    (h : SheafRelation.product SmoothOpenSite.infinitesimal X ⟶ embedding.obj U) :
    parameterCoefficients U Y (SheafFunction.parameterMap SmoothOpenSite.infinitesimal f ≫ h) =
      f ≫ parameterCoefficients U X h := by
  change SheafFunction.curry _ ≫ _ = _
  rw [SheafFunction.curry_parameter, Category.assoc]
  rfl

/-- Fixing the zero lift leaves precisely the velocity coordinate. -/
def fixedStageCoefficients (U : Domain) (A : Code) (x : code U ⟶ A) :
    {h : code U ⟶ dual A // h ≫ SmoothOpenSite.dualZero A = x} ≃
      (Fin U.dimension → Carrier A) where
  toFun h := (stageCoefficients U A h.val).2
  invFun v := ⟨(stageCoefficients U A).symm (x,v), by
    rw [← stageCoefficients_zero]
    exact congrArg Prod.fst ((stageCoefficients U A).apply_symm_apply (x,v))⟩
  left_inv h := by
    apply Subtype.ext
    apply (stageCoefficients U A).injective
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · exact (stageCoefficients_zero U A h.val |>.trans h.property).symm
    · rfl
  right_inv v := congrArg Prod.snd ((stageCoefficients U A).apply_symm_apply (x,v))

theorem openCoefficients_zero (U : Domain) :
    (openCoefficientsIso U).hom ≫ SheafRelation.fst _ _ =
      SmoothOpenSite.dualSheafZero (embedding.obj U) := by
  ext A h
  exact congrArg Quiver.Hom.op (stageCoefficients_zero U A.unop.unop h.unop)

/-- Exponential extraction is evaluation at the universal infinitesimal, with
the arbitrary parameter extended to the dual stage. -/
theorem dualSections_curry {X F : Sheaf SmoothOpenSite.topology Type}
    (h : SheafRelation.product SmoothOpenSite.infinitesimal X ⟶ F)
    (A : Code) (x : X.obj.obj (atStage A)) :
    SmoothOpenSite.dualSectionsEquiv F A ((SheafFunction.curry h).hom.app (atStage A) x) =
      h.hom.app (atStage (dual A)) (eps A, X.obj.map (stageMap (inl A)) x) := by
  let q : representable (J := SmoothOpenSite.topology) A ⟶ X :=
    (SmoothOpenSite.sheafYonedaEquiv A X).symm x
  have hq : (SmoothOpenSite.sheafYonedaEquiv A _).symm
      ((SheafFunction.curry h).hom.app (atStage A) x) = q ≫ SheafFunction.curry h := by
    apply Sheaf.hom_ext
    exact (yonedaEquiv_symm_naturality_right (op A) (SheafFunction.curry h).hom x).symm
  change yonedaEquiv (((dualRepresentable A).inv ≫ SheafFunction.uncurry
    ((SmoothOpenSite.sheafYonedaEquiv A _).symm
      ((SheafFunction.curry h).hom.app (atStage A) x))).hom) = _
  rw [hq, SmoothOpenSite.uncurry_parameter, SheafFunction.beta]
  rfl

/-- The arbitrary-parameter coefficient equivalence computes by the same
universal generalized point as the existing scalar KL map. -/
theorem parameterCoefficients_apply (U : Domain) {X : Sheaf SmoothOpenSite.topology Type}
    (h : SheafRelation.product SmoothOpenSite.infinitesimal X ⟶ embedding.obj U)
    (A : Code) (x : X.obj.obj (atStage A)) :
    ((parameterCoefficients U X h).hom.app (atStage A) x).2 =
      (stageCoefficients U A
        (h.hom.app (atStage (dual A)) (eps A, X.obj.map (stageMap (inl A)) x)).unop).2 := by
  change (stageCoefficients U A
    (SmoothOpenSite.dualSectionsEquiv _ A ((SheafFunction.curry h).hom.app (atStage A) x)).unop).2 = _
  rw [dualSections_curry]

end SquareKit.SmoothOpenArcs
