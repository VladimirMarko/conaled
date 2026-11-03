import SquareKit.SmoothGeometricDerivative

/-! Experimental comparison with the preceding smooth presheaf model.
Only the particular infinitesimal function object is compared. Its restriction
is a sheaf because the previous KL isomorphism identifies it with scalar pairs. -/
noncomputable section
namespace SquareKit.SmoothGeometricComparison
open CategoryTheory Opposite SmoothAlgebra SmoothPresentationSite SheafRelation SheafFunction
open SmoothGeometricKL

/-- Restrict a natural old scalar map to the common presentation category. -/
def scalarMap (f : SmoothStage.scalar ⟶ SmoothStage.scalar) : scalar ⟶ scalar :=
  ⟨Functor.whiskerLeft toStage.op.op f.hom⟩

/-- Arbitrary geometric parameters assigned naturally to a preceding presheaf. -/
def operation {X : Sheaf SmoothStage.topology Type} {Y : Sheaf topology Type}
    (h : product SmoothStage.infinitesimal X ⟶ SmoothStage.scalar)
    (p : Y.obj ⟶ toStage.op.op ⋙ X.obj) : product infinitesimal Y ⟶ scalar :=
  ⟨{app A := ↾fun q => h.hom.app (SmoothKL.atStage (toStage.obj A.unop.unop)) (q.1, p.app A q.2)
    naturality A B f := by
      ext q
      have hp := NatTrans.naturality_apply p f q.2
      change p.app B (Y.obj.map f q.2) = X.obj.map (toStage.op.op.map f) (p.app A q.2) at hp
      change h.hom.app _ (_, p.app B (Y.obj.map f q.2)) = _
      rw [hp]
      exact SmoothKL.operation_natural h (toStage.map f.unop.unop) q.1 (p.app A q.2)}⟩

theorem universalValue_comparison {X : Sheaf SmoothStage.topology Type} {Y : Sheaf topology Type}
    (h : product SmoothStage.infinitesimal X ⟶ SmoothStage.scalar)
    (p : Y.obj ⟶ toStage.op.op ⋙ X.obj) (A : Code) (x : Y.obj.obj (atStage A)) :
    universalValue (operation h p) A x =
      SmoothKL.universalValue h (toStage.obj A) (p.app (atStage A) x) := by
  let c : toStage.obj (dual A) ⟶ SmoothStage.Stage.dual (toStage.obj A) := dualToActual A
  have hc : (toStage.map (inl A)) ≫ c = SmoothKL.inl (toStage.obj A) :=
    Presentation.toDual_inclusion A.equations
  have he : SmoothStage.infinitesimal.obj.map (SmoothKL.stageMap c) (eps A) =
      SmoothKL.eps (toStage.obj A) := Subtype.ext (Presentation.toDual_eps A.equations)
  have hn := SmoothKL.operation_natural h c (eps A)
    (X.obj.map (SmoothKL.stageMap (toStage.map (inl A))) (p.app (atStage A) x))
  rw [he, SmoothKL.restrict_comp, hc] at hn
  have hp := NatTrans.naturality_apply p (stageMap (inl A)) x
  change p.app _ (Y.obj.map _ x) = X.obj.map _ (p.app _ x) at hp
  change dualToActual A (h.hom.app (SmoothKL.atStage (toStage.obj (dual A))) (eps A, p.app (atStage (dual A)) (Y.obj.map (stageMap (inl A)) x))) = _
  rw [hp]
  exact hn.symm

theorem coefficients_comparison {X : Sheaf SmoothStage.topology Type} {Y : Sheaf topology Type}
    (h : product SmoothStage.infinitesimal X ⟶ SmoothStage.scalar)
    (p : Y.obj ⟶ toStage.op.op ⋙ X.obj) (A : Code) (x : Y.obj.obj (atStage A)) :
    (coefficients (operation h p)).hom.app (atStage A) x =
      (SmoothKL.coefficients h).hom.app (SmoothKL.atStage (toStage.obj A)) (p.app (atStage A) x) :=
  congrArg (fun z : DualNumber (Carrier A) => (z.fst,z.snd)) (universalValue_comparison h p A x)

theorem derivative_comparison (f : SmoothStage.scalar ⟶ SmoothStage.scalar) :
    SmoothGeometricDerivative.derivative (scalarMap f) = scalarMap (SmoothDerivative.derivative f) := by
  apply SmoothGeometricDerivative.derivative_unique
  intro A x d
  exact SmoothDerivative.taylor f (toStage.obj A) x d

abbrev restrictedFunctionsData := toStage.op.op ⋙ SmoothKL.functions.obj

/-- A specific comparison, obtained from the already proved old KL inverse. -/
def restrictedPairIso : (product scalar scalar).obj ≅ restrictedFunctionsData :=
  NatIso.ofComponents (fun A => Equiv.toIso {
    toFun := SmoothStage.affine.hom.app (toStage.op.op.obj A)
    invFun := SmoothKL.extract.hom.app (toStage.op.op.obj A)
    left_inv := fun p => congrArg (fun k => k.hom.app (toStage.op.op.obj A) p) SmoothKL.affine_extract
    right_inv := fun p => congrArg (fun k => k.hom.app (toStage.op.op.obj A) p) SmoothKL.extract_affine })
    (fun f => (SmoothStage.affine.hom.naturality (toStage.op.op.map f)))

abbrev restrictedFunctions : Sheaf topology Type :=
  ⟨restrictedFunctionsData, (isSheaf_iff_isSheaf_of_type _ _).mpr
    (Presieve.isSheaf_iso topology restrictedPairIso (product_isSheaf scalar scalar))⟩

def functionComparison : SmoothGeometricKL.functions ≅ restrictedFunctions :=
  kl.symm ≪≫ (fullyFaithfulSheafToPresheaf topology Type).preimageIso
    (X := product scalar scalar) (Y := restrictedFunctions) restrictedPairIso

theorem evaluation_comparison :
    parameterMap infinitesimal functionComparison.hom ≫
      operation (Y := restrictedFunctions) (evaluation SmoothStage.infinitesimal SmoothStage.scalar) (𝟙 restrictedFunctionsData) =
      evaluation infinitesimal scalar := by
  ext A p
  change (evaluation SmoothStage.infinitesimal SmoothStage.scalar).hom.app (toStage.op.op.obj A)
    (p.1, SmoothStage.affine.hom.app (toStage.op.op.obj A) (extract.hom.app A p.2)) = _
  exact (SmoothStage.affine_evaluation (toStage.obj A.unop.unop) p.1.val p.1.property
    (extract.hom.app A p.2).1 (extract.hom.app A p.2).2).trans
      (evaluation_extract A.unop.unop p.1 p.2).symm

/-- Currying is compatible with this particular comparison, via evaluation. -/
theorem curry_comparison {X : Sheaf topology Type} (h : product infinitesimal X ⟶ scalar) :
    parameterMap infinitesimal (curry h ≫ functionComparison.hom) ≫
      operation (Y := restrictedFunctions) (evaluation SmoothStage.infinitesimal SmoothStage.scalar) (𝟙 restrictedFunctionsData) = h := by
  have he := congrArg (fun k => parameterMap infinitesimal (curry h) ≫ k) evaluation_comparison
  rw [← uncurry_evaluation, beta] at he
  exact he

end SquareKit.SmoothGeometricComparison
