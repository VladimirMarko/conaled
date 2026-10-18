import SquareKit.AlgebraicStage

/-! Experimental categorical first-order KL on the small algebraic site.
Coefficients are extracted at the universal dual extension, using naturality
at all stages. No external-function KL assumption is made.
-/
noncomputable section
namespace SquareKit.AlgebraicKL
open CategoryTheory Opposite
open AlgebraicStage SheafRelation SheafFunction

abbrev atStage (A : Stage) : Siteᵒᵖ := op (op A)
abbrev stageMap {A B : Stage} (f : A ⟶ B) : atStage A ⟶ atStage B := f.op.op
abbrev inl (A : Stage) : A ⟶ .dual A := algebraMap (Carrier A) (DualNumber (Carrier A))
abbrev eps (A : Stage) : infinitesimal.obj.obj (atStage (.dual A)) :=
  ⟨DualNumber.eps, DualNumber.eps_mul_eps⟩

theorem dualLift_inl (A B : Stage) (f : Carrier A →+* Carrier B)
    (d : {d : Carrier B // d * d = 0}) : (dualLift A B (f, d)).comp (inl A) = f :=
  congrArg Prod.fst ((dualLift A B).symm_apply_apply (f, d))

theorem dualLift_eps (A B : Stage) (f : Carrier A →+* Carrier B)
    (d : {d : Carrier B // d * d = 0}) : dualLift A B (f, d) DualNumber.eps = d.val :=
  congrArg (fun p => p.2.val) ((dualLift A B).symm_apply_apply (f, d))

abbrev dualMap {A B : Stage} (f : A ⟶ B) : Stage.dual A ⟶ Stage.dual B :=
  dualLift A (.dual B) ((ringMap (inl B)).comp (ringMap f), eps B)

theorem dualMap_inl {A B : Stage} (f : A ⟶ B) :
    inl A ≫ dualMap f = f ≫ inl B := dualLift_inl _ _ _ _

theorem dualMap_eps {A B : Stage} (f : A ⟶ B) :
    infinitesimal.obj.map (stageMap (dualMap f)) (eps A) = eps B := by
  apply Subtype.ext
  exact dualLift_eps _ _ _ _

theorem dual_reconstruct {R : Type} [CommRing R] (a b : R) :
    (algebraMap R (DualNumber R) a +
      algebraMap R (DualNumber R) b * (DualNumber.eps : DualNumber R)) =
        (⟨a, b⟩ : DualNumber R) := by
  apply TrivSqZeroExt.ext <;>
    simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_coordinates {A B : Stage} (f : A ⟶ B) (z : DualNumber (Carrier A)) :
    (ringMap (dualMap f) z).fst = ringMap f z.fst ∧
    (ringMap (dualMap f) z).snd = ringMap f z.snd := by
  have h : ringMap (dualMap f) z =
      (⟨ringMap f z.fst, ringMap f z.snd⟩ : DualNumber (Carrier B)) :=
    dual_reconstruct _ _
  exact ⟨congrArg TrivSqZeroExt.fst h, congrArg TrivSqZeroExt.snd h⟩

abbrev representable (A : Stage) : Sheaf topology Type :=
  ⟨yoneda.obj (op A), Presheaf.isSheaf_bot _⟩

/-- The order is infinitesimal first, parameter second. -/
def dualRepresentable (A : Stage) :
    product infinitesimal (representable A) ≅ representable (.dual A) where
  hom := ⟨{
    app T := ↾fun p => (show A.dual ⟶ T.unop.unop from
      dualLift A T.unop.unop (ringMap p.2.unop, p.1)).op
    naturality T U g := by
      ext p
      exact congrArg Quiver.Hom.op (dualLift_natural A T.unop.unop U.unop.unop
        (ringMap p.2.unop) p.1 (ringMap g.unop.unop)).symm }⟩
  inv := ⟨{
    app T := ↾fun f => let p := (dualLift A T.unop.unop).symm (ringMap f.unop)
      (p.2, (show A ⟶ T.unop.unop from p.1).op)
    naturality T U g := by
      ext f
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · rfl }⟩
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext T
    ext p
    exact congrArg (fun q => (q.2, (show A ⟶ T.unop.unop from q.1).op))
      ((dualLift A T.unop.unop).symm_apply_apply (p.2.unop, p.1))
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext T
    ext f
    exact congrArg Quiver.Hom.op ((dualLift A T.unop.unop).apply_symm_apply f.unop)

abbrev representableMap {A B : Stage} (f : A ⟶ B) : representable B ⟶ representable A :=
  ⟨yoneda.map f.op⟩

theorem dualLift_source {A B T : Stage} (f : A ⟶ B)
    (g : Carrier B →+* Carrier T) (d : {d : Carrier T // d * d = 0}) :
    (dualLift B T (g, d)).comp (ringMap (dualMap f)) =
      dualLift A T (g.comp (ringMap f), d) := by
  ext z
  change g (ringMap (dualMap f) z).fst + g (ringMap (dualMap f) z).snd * d.val =
    g (ringMap f z.fst) + g (ringMap f z.snd) * d.val
  rw [(dualMap_coordinates f z).1, (dualMap_coordinates f z).2]

theorem dualRepresentable_parameter {A B : Stage} (f : A ⟶ B) :
    parameterMap infinitesimal (representableMap f) ≫ (dualRepresentable A).hom =
      (dualRepresentable B).hom ≫ representableMap (dualMap f) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext T
  ext p
  exact congrArg Quiver.Hom.op (dualLift_source f (ringMap p.2.unop) p.1).symm

variable {X : Sheaf topology Type}

theorem restrict_comp (F : Sheaf topology Type) {A B C : Stage}
    (f : A ⟶ B) (g : B ⟶ C) (x : F.obj.obj (atStage A)) :
    F.obj.map (stageMap g) (F.obj.map (stageMap f) x) =
      F.obj.map (stageMap (f ≫ g)) x := by
  change (F.obj.map (stageMap f) ≫ F.obj.map (stageMap g)) x = _
  rw [← F.obj.map_comp]
  rfl

theorem operation_natural (h : product infinitesimal X ⟶ scalar)
    {A B : Stage} (f : A ⟶ B) (d : infinitesimal.obj.obj (atStage A))
    (x : X.obj.obj (atStage A)) :
    h.hom.app (atStage B) (infinitesimal.obj.map (stageMap f) d,
      X.obj.map (stageMap f) x) = ringMap f (h.hom.app (atStage A) (d, x)) :=
  congrArg (fun k : (product infinitesimal X).obj.obj (atStage A) ⟶
    scalar.obj.obj (atStage B) => k (d, x)) (h.hom.naturality (stageMap f))

/-- Evaluate at the universal infinitesimal after extending the parameter. -/
def universalValue (h : product infinitesimal X ⟶ scalar) (A : Stage)
    (x : X.obj.obj (atStage A)) : DualNumber (Carrier A) :=
  h.hom.app (atStage (.dual A)) (eps A, X.obj.map (stageMap (inl A)) x)

theorem universalValue_natural (h : product infinitesimal X ⟶ scalar)
    {A B : Stage} (f : A ⟶ B) (x : X.obj.obj (atStage A)) :
    universalValue h B (X.obj.map (stageMap f) x) =
      ringMap (dualMap f) (universalValue h A x) := by
  have h' := operation_natural h (dualMap f) (eps A)
    (X.obj.map (stageMap (inl A)) x)
  rw [dualMap_eps, restrict_comp, dualMap_inl, ← restrict_comp] at h'
  exact h'

/-- Coefficients are a natural pair, extracted without choosing external functions. -/
def coefficients (h : product infinitesimal X ⟶ scalar) : X ⟶ product scalar scalar :=
  ⟨{ app A := ↾fun x => ((universalValue h A.unop.unop x).fst,
       (universalValue h A.unop.unop x).snd)
     naturality A B f := by
       ext x
       apply Prod.ext
       · exact (congrArg TrivSqZeroExt.fst
           (universalValue_natural h f.unop.unop x)).trans (dualMap_coordinates _ _).1
       · exact (congrArg TrivSqZeroExt.snd
           (universalValue_natural h f.unop.unop x)).trans (dualMap_coordinates _ _).2 }⟩

theorem universal_reconstruction (h : product infinitesimal X ⟶ scalar)
    (A : Stage) (d : infinitesimal.obj.obj (atStage A)) (x : X.obj.obj (atStage A)) :
    h.hom.app (atStage A) (d, x) =
      (universalValue h A x).fst + (universalValue h A x).snd * d.val := by
  let f : Stage.dual A ⟶ A := dualLift A A (RingHom.id _, d)
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
    (atStage (.dual A.unop.unop)) => k x) (p.hom.naturality (stageMap (inl A.unop.unop)))
  change p.hom.app (atStage (.dual A.unop.unop))
    (X.obj.map (stageMap (inl A.unop.unop)) x) =
    (ringMap (inl A.unop.unop) (p.hom.app A x).1,
      ringMap (inl A.unop.unop) (p.hom.app A x).2) at hp
  change ((universalValue (rebuild p) A.unop.unop x).fst,
    (universalValue (rebuild p) A.unop.unop x).snd) = _
  have hv : universalValue (rebuild p) A.unop.unop x =
      (⟨(p.hom.app A x).1, (p.hom.app A x).2⟩ : DualNumber (Carrier A.unop.unop)) := by
    unfold universalValue rebuild
    change (p.hom.app (atStage (.dual A.unop.unop))
      (X.obj.map (stageMap (inl A.unop.unop)) x)).1 +
      (p.hom.app (atStage (.dual A.unop.unop))
      (X.obj.map (stageMap (inl A.unop.unop)) x)).2 *
      (eps A.unop.unop).val = _
    rw [hp]
    exact dual_reconstruct _ _
  exact congrArg (fun z => (z.fst, z.snd)) hv

theorem coefficients_parameter {Y : Sheaf topology Type}
    (h : product infinitesimal X ⟶ scalar) (p : Y ⟶ X) :
    coefficients (parameterMap infinitesimal p ≫ h) = p ≫ coefficients h := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext A
  ext y
  have hp := congrArg (fun k : Y.obj.obj A ⟶ X.obj.obj (atStage (.dual A.unop.unop)) => k y)
    (p.hom.naturality (stageMap (inl A.unop.unop)))
  change p.hom.app _ (Y.obj.map _ y) = X.obj.map _ (p.hom.app A y) at hp
  change ((h.hom.app _ (eps _, p.hom.app _ (Y.obj.map _ y))).fst,
    (h.hom.app _ (eps _, p.hom.app _ (Y.obj.map _ y))).snd) = _
  rw [hp]
  rfl

/-- The universal value is exactly the Yoneda evaluation of the transposed
representable-parameter operation, through the constructed comparison. -/
theorem universalValue_yoneda (h : product infinitesimal X ⟶ scalar) (A : Stage)
    (x : X.obj.obj (atStage A)) :
    universalValue h A x = yonedaEquiv
      (((dualRepresentable A).inv ≫ parameterMap infinitesimal
        (show representable A ⟶ X from ⟨yonedaEquiv.symm x⟩) ≫ h).hom) := rfl

abbrev functions := exponential infinitesimal scalar

def extract : functions ⟶ product scalar scalar := coefficients (evaluation infinitesimal scalar)

theorem extract_curry (h : product infinitesimal X ⟶ scalar) :
    curry h ≫ extract = coefficients h := by
  rw [extract, ← coefficients_parameter, ← uncurry_evaluation, beta]

theorem affine_extract : affine ≫ extract = 𝟙 _ := by
  rw [affine, extract_curry]
  exact coefficients_rebuild (𝟙 (product scalar scalar))

theorem extract_affine : extract ≫ affine = 𝟙 _ := by
  rw [← affine_parameters, ← rebuild]
  change curry (rebuild (coefficients (evaluation infinitesimal scalar))) = _
  rw [rebuild_coefficients]
  exact eta (𝟙 functions)

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
  ∀ (A : Stage) (d : infinitesimal.obj.obj (atStage A)) (x : X.obj.obj (atStage A)),
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
theorem evaluation_extract (A : Stage) (d : infinitesimal.obj.obj (atStage A))
    (f : functions.obj.obj (atStage A)) :
    (evaluation infinitesimal scalar).hom.app (atStage A) (d, f) =
      (extract.hom.app (atStage A) f).1 + (extract.hom.app (atStage A) f).2 * d.val :=
  universal_reconstruction (evaluation infinitesimal scalar) A d f

end SquareKit.AlgebraicKL
