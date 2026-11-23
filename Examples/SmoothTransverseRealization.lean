import Examples.SmoothTransversePullback
import Examples.SmoothCoordinatePullbacks
import SquareKit.SmoothTransverseLocalPullback
import SquareKit.SmoothTransverseRealization

/-! Concrete full-algebra controls for transverse realization. -/
noncomputable section
set_option autoImplicit false
namespace Examples.SmoothTransverseRealization
open CategoryTheory Opposite SquareKit SquareKit.SmoothAlgebra
open SmoothPresentationSite SmoothGeometricKL

/-- Pullback of functions along the nonlinear graph t ↦ (t,t²). -/
def graph : Hom (Free 2) (Free 1) := evaluate ![generator 0, generator 0 * generator 0]

/-- Pullback of functions along the regular equation y-x². -/
def equation : Hom (Free 1) (Free 2) := evaluate ![generator 1 - generator 0 * generator 0]

variable {B : Type*} [CommRing B] [Algebra ℝ B] [Structure B]

theorem graph_universal (w : Hom (Free 2) B)
    (hw : w (generator 1) = w (generator 0) * w (generator 0)) :
    ∃! v : Hom (Free 1) B, v.comp graph = w := by
  refine ⟨evaluate ![w (generator 0)], ?_, ?_⟩
  · apply hom_ext_generators
    intro i
    fin_cases i
    · simp [graph, Hom.comp, Function.comp_apply, evaluate_generator]
    · simp [graph, Hom.comp, Function.comp_apply, evaluate_generator, Hom.map_mul, hw]
  · intro v hv
    apply hom_ext_generators
    intro i
    fin_cases i
    have h := congrArg (fun k : Hom (Free 2) B => k (generator 0)) hv
    simpa [graph, Hom.comp, Function.comp_apply, evaluate_generator] using h

abbrev stage := SmoothCoordinatePullbacks.stage
abbrev d : Carrier stage := SmoothCoordinatePullbacks.d

def graphPoint : Hom (Free 2) (Carrier stage) := evaluate ![d, 0]
def graphParameter : Hom (Free 1) (Carrier stage) := evaluate ![d]

theorem graphPoint_on_level : graphPoint.comp equation = evaluate (fun _ : Fin 1 => 0) := by
  apply hom_ext_generators
  intro i
  fin_cases i
  rw [evaluate_generator]
  change graphPoint (equation (generator 0)) = 0
  simp only [equation, evaluate_generator, Matrix.cons_val_zero]
  change graphPoint.toAlgHom (_ - _ * _) = 0
  rw [map_sub, map_mul]
  simp [graphPoint, Hom.toAlgHom, evaluate_generator, SmoothCoordinatePullbacks.d_square]

theorem graphParameter_recovers : graphParameter.comp graph = graphPoint := by
  apply hom_ext_generators
  intro i
  fin_cases i <;>
    simp [graphParameter, graphPoint, graph, Hom.comp, Function.comp_apply, evaluate_generator,
      Hom.map_mul, SmoothCoordinatePullbacks.d_square]

theorem graphParameter_unique (v : Hom (Free 1) (Carrier stage))
    (hv : v.comp graph = graphPoint) : v = graphParameter := by
  have h := graph_universal graphPoint (by
    simp [graphPoint, evaluate_generator, SmoothCoordinatePullbacks.d_square])
  exact (h.unique hv graphParameter_recovers)

theorem graphParameter_nonzero : graphParameter (generator 0) ≠ 0 := by
  simpa [graphParameter, evaluate_generator] using SmoothCoordinatePullbacks.d_nonzero

/-- The two nonidentity restrictions from the coordinate control also act on
this nonlinear graph, and retain its full factorization equation. -/
theorem graph_restrict (r : stage ⟶ stage) :
    ((smoothMap r).comp graphParameter).comp graph = (smoothMap r).comp graphPoint := by
  rw [← Hom.comp_assoc, graphParameter_recovers]

theorem graph_double :
    ((smoothMap SmoothCoordinatePullbacks.doubleInfinitesimal).comp graphParameter)
      (generator 0) = d + d := by
  simpa [Hom.comp, Function.comp_apply, graphParameter, evaluate_generator] using
    SmoothCoordinatePullbacks.doubleInfinitesimal_d

theorem graph_kill :
    ((smoothMap SmoothCoordinatePullbacks.kill).comp graphParameter) (generator 0) = 0 := by
  simpa [Hom.comp, Function.comp_apply, graphParameter, evaluate_generator] using
    SmoothCoordinatePullbacks.kill_d

theorem graph_composite :
    ((smoothMap (SmoothCoordinatePullbacks.doubleInfinitesimal ≫ SmoothCoordinatePullbacks.kill)).comp
      graphParameter) (generator 0) = 0 := by
  change smoothMap (SmoothCoordinatePullbacks.doubleInfinitesimal ≫ SmoothCoordinatePullbacks.kill)
    (graphParameter (generator 0)) = 0
  simp only [graphParameter, evaluate_generator, Matrix.cons_val_zero]
  change smoothMap SmoothCoordinatePullbacks.kill
    (smoothMap SmoothCoordinatePullbacks.doubleInfinitesimal d) = 0
  rw [SmoothCoordinatePullbacks.doubleInfinitesimal_d, (smoothMap SmoothCoordinatePullbacks.kill).map_add,
    SmoothCoordinatePullbacks.kill_d, zero_add]

/-- Real points of x²=0 cannot detect the additional infinitesimal section. -/
theorem square_zero_real (x : ℝ) (hx : x*x = 0) : x = 0 :=
  (mul_self_eq_zero.mp hx)

theorem square_zero_infinitesimal : d*d = 0 ∧ d ≠ 0 :=
  ⟨SmoothCoordinatePullbacks.d_square, SmoothCoordinatePullbacks.d_nonzero⟩

open ManifoldRealization SmoothTransversality
open scoped Manifold ContDiff

def squareMap (x : Space 1) : Space 1 := fun _ => x 0 ^ 2

theorem squareMap_derivative_zero : HasFDerivAt squareMap (0 : Space 1 →L[ℝ] Space 1) 0 := by
  have h : ∀ i : Fin 1, HasFDerivAt (fun x : Space 1 => x 0 ^ 2)
      (0 : Space 1 →L[ℝ] ℝ) 0 := by
    intro i
    convert (hasFDerivAt_apply (𝕜 := ℝ) 0 (0 : Space 1)).pow 2 using 1
    simp
  have hpi := hasFDerivAt_pi.mpr h
  have hz : (ContinuousLinearMap.pi fun _ : Fin 1 => (0 : Space 1 →L[ℝ] ℝ)) = 0 := by
    ext x i
    rfl
  rw [hz] at hpi
  exact hpi

set_option backward.isDefEq.respectTransparency false in
theorem squareMap_not_transverse : ¬ TransverseAt (m := 1) (n := 0) (p := 1)
    squareMap (fun _ : Space 0 => (0 : Space 1)) 0 0 (by ext; simp [squareMap]) := by
  intro ht
  obtain ⟨v, hv⟩ := ht (fun _ => 1)
  simp only [tangentDifference, sub_apply, ContinuousLinearMap.comp_apply,
    mfderiv_const, zero_apply, ContinuousLinearEquiv.coe_coe,
    tangentTransport_apply] at hv
  rw [show Model 1 = 𝓘(ℝ, Space 1) from rfl, mfderiv_eq_fderiv,
    squareMap_derivative_zero.fderiv] at hv
  have h := congrFun hv 0
  simp only [ContinuousLinearMap.comp_apply, zero_apply, map_zero, sub_self] at h
  change (0 : ℝ) = 1 at h
  exact zero_ne_one h

/-- The algebraic graph equation is the ordinary transverse parabola equation. -/
theorem equation_real (x : Space 2) :
    evaluate x (equation (generator 0)) = SmoothTransversePullback.parabola x 0 := by
  simp only [equation, evaluate_generator, Matrix.cons_val_zero]
  change (evaluate x).toAlgHom (_ - _ * _) = _
  rw [map_sub, map_mul]
  simp [Hom.toAlgHom, evaluate_generator, SmoothTransversePullback.parabola, pow_two]

/-- The nilpotent solution of x²=0 does not factor through its ordinary singleton
zero locus. This is the obstruction excluded by transversality. -/
theorem square_zero_no_point_factor :
    ¬ ∃ v : Hom (Free 0) (Carrier stage),
      v.comp (evaluate (fun _ : Fin 1 => (0 : Free 0))) = graphParameter := by
  rintro ⟨v, hv⟩
  have h := congrArg (fun k : Hom (Free 1) (Carrier stage) => k (generator 0)) hv
  change v (evaluate (fun _ : Fin 1 => (0 : Free 0)) (generator 0)) =
    graphParameter (generator 0) at h
  rw [evaluate_generator] at h
  have hz : v 0 = 0 := v.toAlgHom.map_zero
  rw [hz] at h
  exact graphParameter_nonzero h.symm

open EuclideanOpen

def toFull (n : ℕ) (x : Space n) : ordinaryOpen (full n) := ⟨x, one_ne_zero⟩

theorem toFull_smooth (n : ℕ) : ContMDiff (Model n) (Model n) ∞ (toFull n) := by
  apply (ContMDiff.subtypeVal_comp_iff (ordinaryOpen (full n)) _).mp
  exact contMDiff_id

/-- This example adapter identifies the actual whole-space manifold with its
principal presentation; it does not assume preservation of pullbacks. -/
def fullSpacePrincipalIso (n : ℕ) : object n (Space n) ≅ embedding.obj (full n) :=
  (show object n (Space n) ≅ object n (ordinaryOpen (full n)) from {
    hom := ManifoldRealization.map (toFull n) (toFull_smooth n)
    inv := ManifoldRealization.map Subtype.val (contMDiff_subtype_val (U := ordinaryOpen (full n)))
    hom_inv_id := by
      rw [← ManifoldRealization.map_comp]
      exact ManifoldRealization.map_id
    inv_hom_id := by
      rw [← ManifoldRealization.map_comp]
      have h : toFull n ∘ (Subtype.val : ordinaryOpen (full n) → Space n) = id := by
        funext x
        exact Subtype.ext rfl
      simpa only [h] using (ManifoldRealization.map_id (M := ordinaryOpen (full n)) (n := n)) }) ≪≫
    principalIso (full n)

def fullSpaceIso (n : ℕ) : object n (Space n) ≅ SmoothOpenSite.scalarPower n :=
  fullSpacePrincipalIso n ≪≫ fullPowerIso n

theorem fullSpacePrincipal_naturality {n m : ℕ} (f : Space n → Space m)
    (hf : ContMDiff (Model n) (Model m) ∞ f) (g : full n ⟶ full m)
    (h : ∀ x, ((show EuclideanOpen.Map _ _ from g) (toFull n x)).val = f x) :
    ManifoldRealization.map f hf ≫ (fullSpacePrincipalIso m).hom =
      (fullSpacePrincipalIso n).hom ≫ embedding.map g := by
  change ManifoldRealization.map f hf ≫
    (ManifoldRealization.map (toFull m) (toFull_smooth m) ≫ (principalIso (full m)).hom) =
    (ManifoldRealization.map (toFull n) (toFull_smooth n) ≫ (principalIso (full n)).hom) ≫ embedding.map g
  rw [← Category.assoc, ← ManifoldRealization.map_comp]
  have he : toFull m ∘ f = (fun y : ordinaryOpen (full n) => (show ordinaryOpen (full m) from (show EuclideanOpen.Map _ _ from g) y)) ∘ toFull n := by
    funext x
    exact Subtype.ext (h x).symm
  simp only [he]
  rw [ManifoldRealization.map_comp (toFull n)
    (fun y : ordinaryOpen (full n) => (show ordinaryOpen (full m) from (show EuclideanOpen.Map _ _ from g) y))
    (toFull_smooth n) (openMap_contMDiff g)]
  rw [Category.assoc, principalIso_naturality, Category.assoc]

/-- A translated infinitesimal exhibits the nonconstant square coordinate. -/
def shiftedGraphParameter : Hom (Free 1) (Carrier stage) := evaluate ![1+d]

def shiftedGraphPoint : Hom (Free 2) (Carrier stage) := evaluate ![1+d, 1+(d+d)]

theorem shiftedGraph_recovers : shiftedGraphParameter.comp graph = shiftedGraphPoint := by
  apply hom_ext_generators
  intro i
  fin_cases i
  · simp [shiftedGraphParameter, shiftedGraphPoint, graph, Hom.comp, evaluate_generator]
  · have hs : (1+d)*(1+d) = 1+(d+d) := by
      calc
        (1+d)*(1+d) = 1+(d+d)+d*d := by ring
        _ = _ := by rw [SmoothCoordinatePullbacks.d_square, add_zero]
    simpa [shiftedGraphParameter, shiftedGraphPoint, graph, Hom.comp,
      evaluate_generator, Hom.map_mul] using hs

theorem shiftedGraph_second_nonconstant : shiftedGraphPoint (generator 1) ≠ 1 := by
  simp only [shiftedGraphPoint, evaluate_generator, Matrix.cons_val_one, Matrix.cons_val_zero, ne_eq, add_eq_left]
  intro h
  have hs : (2 : ℝ) • d = 0 := by simpa only [two_smul] using h
  exact SmoothCoordinatePullbacks.d_nonzero ((smul_eq_zero.mp hs).resolve_left two_ne_zero)

local instance parabolaCharted : ChartedSpace (Space 1) SmoothTransversePullback.ParabolaFiber :=
  SquareKit.SmoothTransversePullback.chartedSpace SmoothTransversePullback.parabola_smooth
    contMDiff_const SmoothTransversePullback.parabola_transverse_all

local instance parabolaManifold : IsManifold (Model 1) ∞ SmoothTransversePullback.ParabolaFiber :=
  SquareKit.SmoothTransversePullback.isManifold SmoothTransversePullback.parabola_smooth
    contMDiff_const SmoothTransversePullback.parabola_transverse_all

def firstCoordinate : Space 2 →L[ℝ] Space 1 :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.proj 0

def fiberCoordinate (q : SmoothTransversePullback.ParabolaFiber) : Space 1 := firstCoordinate q.val.1

theorem fiberCoordinate_smooth : ContMDiff (Model 1) (Model 1) ∞ fiberCoordinate :=
  firstCoordinate.contDiff.contMDiff.comp
    (SquareKit.SmoothTransversePullback.smooth_fst SmoothTransversePullback.parabola_smooth
      contMDiff_const SmoothTransversePullback.parabola_transverse_all)

def parabolaFamily : object 1 (Space 1) ⟶ object 1 SmoothTransversePullback.ParabolaFiber :=
  ManifoldRealization.map SmoothTransversePullback.parabolaPoint SmoothTransversePullback.parabolaPoint_smooth

def readParameter : object 1 SmoothTransversePullback.ParabolaFiber ⟶ SmoothOpenSite.scalarPower 1 :=
  ManifoldRealization.map fiberCoordinate fiberCoordinate_smooth ≫ (fullSpaceIso 1).hom

theorem parabolaFamily_parameter : parabolaFamily ≫ readParameter = (fullSpaceIso 1).hom := by
  unfold parabolaFamily readParameter
  rw [← Category.assoc, ← ManifoldRealization.map_comp]
  have h : fiberCoordinate ∘ SmoothTransversePullback.parabolaPoint = id := by
    funext x i
    fin_cases i
    simp [fiberCoordinate, firstCoordinate, SmoothTransversePullback.parabolaPoint,
      SmoothTransversePullback.parabolaCurve]
  simp only [h, ManifoldRealization.map_id, Category.id_comp]

/-- An actual section of the realized ordinary parabola, at the nonreduced stage. -/
def realizedNilpotent : (object 1 SmoothTransversePullback.ParabolaFiber).obj.obj (atStage stage) :=
  parabolaFamily.hom.app (atStage stage)
    ((fullSpaceIso 1).inv.hom.app (atStage stage) (fun _ => 1+d))

theorem realizedNilpotent_parameter :
    readParameter.hom.app (atStage stage) realizedNilpotent = (fun _ => 1+d) := by
  have h := congrArg (fun k : object 1 (Space 1) ⟶ SmoothOpenSite.scalarPower 1 =>
    k.hom.app (atStage stage) ((fullSpaceIso 1).inv.hom.app (atStage stage) (fun _ => 1+d)))
    parabolaFamily_parameter
  exact h.trans (congrArg (fun k : SmoothOpenSite.scalarPower 1 ⟶ SmoothOpenSite.scalarPower 1 =>
    k.hom.app (atStage stage) (fun _ => 1+d)) (fullSpaceIso 1).inv_hom_id)

theorem realizedNilpotent_not_real_base :
    readParameter.hom.app (atStage stage) realizedNilpotent 0 ≠ 1 := by
  rw [realizedNilpotent_parameter]
  exact fun h => SmoothCoordinatePullbacks.d_nonzero (add_left_cancel (h.trans (add_zero 1).symm))

theorem realizedNilpotent_restrict (r : stage ⟶ stage) :
    readParameter.hom.app (atStage stage)
      ((object 1 SmoothTransversePullback.ParabolaFiber).obj.map (stageMap r) realizedNilpotent) 0 =
        1 + smoothMap r d := by
  have h := congrFun (NatTrans.naturality_apply readParameter.hom (stageMap r) realizedNilpotent) 0
  rw [realizedNilpotent_parameter] at h
  change _ = smoothMap r (1+d) at h
  rw [(smoothMap r).map_add] at h
  exact h.trans (congrArg (fun z => z + smoothMap r d) (smoothMap r).toAlgHom.map_one)

def squareOp : Operation 1 := substitute multiplication (fun _ : Fin 2 => projection 0)

def squareSheaf : SmoothOpenSite.scalarPower 1 ⟶ SmoothOpenSite.scalarPower 1 :=
  SmoothOpenSite.tuple (fun _ => SmoothOpenSite.operation squareOp)

theorem squareMap_smooth : ContMDiff (Model 1) (Model 1) ∞ squareMap := by
  apply ContDiff.contMDiff
  unfold squareMap
  fun_prop

theorem squareMap_comparison :
    ManifoldRealization.map squareMap squareMap_smooth ≫ (fullSpaceIso 1).hom =
      (fullSpaceIso 1).hom ≫ squareSheaf := by
  have h := fullSpacePrincipal_naturality squareMap squareMap_smooth
    (EuclideanOpen.Coordinates.coordinateMap (fun _ : Fin 1 => squareOp)) (by
      intro x
      ext i
      simp [EuclideanOpen.Coordinates.coordinateMap, squareOp, substitute, multiplication,
        SmoothAlgebra.projection, squareMap, pow_two, toFull])
  change ManifoldRealization.map squareMap squareMap_smooth ≫
    ((fullSpacePrincipalIso 1).hom ≫ (fullPowerIso 1).hom) = _
  rw [← Category.assoc, h, Category.assoc, EuclideanOpen.Coordinates.coordinateMap_comparison]
  rfl

def secondCoordinate : Space 2 →L[ℝ] Space 1 :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.proj 1

def fiberSecond (q : SmoothTransversePullback.ParabolaFiber) : Space 1 := secondCoordinate q.val.1

theorem fiberSecond_smooth : ContMDiff (Model 1) (Model 1) ∞ fiberSecond :=
  secondCoordinate.contDiff.contMDiff.comp
    (SquareKit.SmoothTransversePullback.smooth_fst SmoothTransversePullback.parabola_smooth
      contMDiff_const SmoothTransversePullback.parabola_transverse_all)

theorem fiberSecond_eq : fiberSecond = squareMap ∘ fiberCoordinate := by
  funext q i
  have h := congrFun q.property 0
  change q.val.1 1 - q.val.1 0 ^ 2 = 0 at h
  exact sub_eq_zero.mp h

def readSecond : object 1 SmoothTransversePullback.ParabolaFiber ⟶ SmoothOpenSite.scalarPower 1 :=
  ManifoldRealization.map fiberSecond fiberSecond_smooth ≫ (fullSpaceIso 1).hom

theorem readSecond_parameter : readSecond = readParameter ≫ squareSheaf := by
  unfold readSecond readParameter
  have hm : ManifoldRealization.map fiberSecond fiberSecond_smooth =
      ManifoldRealization.map (squareMap ∘ fiberCoordinate) (squareMap_smooth.comp fiberCoordinate_smooth) := by
    congr 1
    exact fiberSecond_eq
  rw [hm, ManifoldRealization.map_comp fiberCoordinate squareMap
    fiberCoordinate_smooth squareMap_smooth, Category.assoc, squareMap_comparison, Category.assoc]

theorem realizedNilpotent_second :
    readSecond.hom.app (atStage stage) realizedNilpotent 0 = 1+(d+d) := by
  rw [readSecond_parameter]
  change squareSheaf.hom.app (atStage stage)
    (readParameter.hom.app (atStage stage) realizedNilpotent) 0 = _
  rw [realizedNilpotent_parameter]
  change act squareOp (fun _ => 1+d) = _
  rw [squareOp, Structure.substitute, Structure.multiplication]
  simp only [Structure.projection]
  calc
    (1+d)*(1+d) = 1+(d+d)+d*d := by ring
    _ = _ := by rw [SmoothCoordinatePullbacks.d_square, add_zero]

theorem realizedNilpotent_second_nonconstant :
    readSecond.hom.app (atStage stage) realizedNilpotent 0 ≠ 1 := by
  rw [realizedNilpotent_second]
  simpa only [shiftedGraphPoint, evaluate_generator, Matrix.cons_val_one, Matrix.cons_val_zero] using
    shiftedGraph_second_nonconstant

theorem realizedNilpotent_double :
    readParameter.hom.app (atStage stage)
      ((object 1 SmoothTransversePullback.ParabolaFiber).obj.map
        (stageMap SmoothCoordinatePullbacks.doubleInfinitesimal) realizedNilpotent) 0 = 1+(d+d) := by
  rw [realizedNilpotent_restrict, SmoothCoordinatePullbacks.doubleInfinitesimal_d]

theorem realizedNilpotent_kill :
    readParameter.hom.app (atStage stage)
      ((object 1 SmoothTransversePullback.ParabolaFiber).obj.map
        (stageMap SmoothCoordinatePullbacks.kill) realizedNilpotent) 0 = 1 := by
  rw [realizedNilpotent_restrict, SmoothCoordinatePullbacks.kill_d, add_zero]

theorem realizedNilpotent_composite :
    readParameter.hom.app (atStage stage)
      ((object 1 SmoothTransversePullback.ParabolaFiber).obj.map
        (stageMap (SmoothCoordinatePullbacks.doubleInfinitesimal ≫ SmoothCoordinatePullbacks.kill))
        realizedNilpotent) 0 = 1 := by
  rw [realizedNilpotent_restrict]
  change 1 + smoothMap SmoothCoordinatePullbacks.kill
    (smoothMap SmoothCoordinatePullbacks.doubleInfinitesimal d) = 1
  rw [SmoothCoordinatePullbacks.doubleInfinitesimal_d, (smoothMap SmoothCoordinatePullbacks.kill).map_add,
    SmoothCoordinatePullbacks.kill_d, zero_add, add_zero]

theorem realizedNilpotent_kill_changes :
    (object 1 SmoothTransversePullback.ParabolaFiber).obj.map
      (stageMap SmoothCoordinatePullbacks.kill) realizedNilpotent ≠ realizedNilpotent := by
  intro h
  have hp := realizedNilpotent_kill
  rw [h] at hp
  exact realizedNilpotent_not_real_base hp

open SquareKit.SmoothTransversePullback

/-- The general theorem applies to the nonlinear positive-dimensional fiber. -/
theorem parabola_preserved : CategoryTheory.IsPullback
    (Realization.first SmoothTransversePullback.parabola_smooth contMDiff_const
      SmoothTransversePullback.parabola_transverse_all)
    (Realization.second SmoothTransversePullback.parabola_smooth contMDiff_const
      SmoothTransversePullback.parabola_transverse_all)
    (ManifoldRealization.map SmoothTransversePullback.parabola SmoothTransversePullback.parabola_smooth)
    (ManifoldRealization.map (fun _ : Space 0 => (0 : Space 1)) contMDiff_const) :=
  Realization.isPullback SmoothTransversePullback.parabola_smooth contMDiff_const
    SmoothTransversePullback.parabola_transverse_all

/-- The actual intersection of the two transverse coordinate axes is covered too. -/
theorem axes_preserved : CategoryTheory.IsPullback
    (Realization.first SmoothTransversePullback.axisX_smooth SmoothTransversePullback.axisY_smooth
      SmoothTransversePullback.axes_transverse_all)
    (Realization.second SmoothTransversePullback.axisX_smooth SmoothTransversePullback.axisY_smooth
      SmoothTransversePullback.axes_transverse_all)
    (ManifoldRealization.map SmoothTransversePullback.axisX SmoothTransversePullback.axisX_smooth)
    (ManifoldRealization.map SmoothTransversePullback.axisY SmoothTransversePullback.axisY_smooth) :=
  Realization.isPullback SmoothTransversePullback.axisX_smooth SmoothTransversePullback.axisY_smooth
    SmoothTransversePullback.axes_transverse_all

/-- Empty transverse fibers are allowed even when p > m+n. -/
theorem empty_preserved : CategoryTheory.IsPullback
    (Realization.first (f := SmoothTransversePullback.emptyLeft) (g := SmoothTransversePullback.emptyRight)
      contMDiff_const contMDiff_const SmoothTransversePullback.empty_transverse_all)
    (Realization.second (f := SmoothTransversePullback.emptyLeft) (g := SmoothTransversePullback.emptyRight)
      contMDiff_const contMDiff_const SmoothTransversePullback.empty_transverse_all)
    (ManifoldRealization.map (n := 0) (m := 2) SmoothTransversePullback.emptyLeft contMDiff_const)
    (ManifoldRealization.map (n := 1) (m := 2) SmoothTransversePullback.emptyRight contMDiff_const) :=
  Realization.isPullback contMDiff_const contMDiff_const SmoothTransversePullback.empty_transverse_all

abbrev parabolaPairs (V : Site) :=
  Realization.stagePairs (m := 2) (n := 0) (p := 1) SmoothTransversePullback.parabola_smooth
    (g := fun _ : Space 0 => (0 : Space 1)) contMDiff_const V

abbrev parabolaLift (V : Site) :=
  Realization.stageLift SmoothTransversePullback.parabola_smooth contMDiff_const
    SmoothTransversePullback.parabola_transverse_all V

/-- The compatible target pair is specified by the actual ordinary projections. -/
def nilpotentPair : parabolaPairs (op stage) :=
  ⟨((Realization.first SmoothTransversePullback.parabola_smooth contMDiff_const
      SmoothTransversePullback.parabola_transverse_all).hom.app (atStage stage) realizedNilpotent,
    (Realization.second SmoothTransversePullback.parabola_smooth contMDiff_const
      SmoothTransversePullback.parabola_transverse_all).hom.app (atStage stage) realizedNilpotent),
    congrArg (fun k => k.hom.app (atStage stage) realizedNilpotent)
      (Realization.square SmoothTransversePullback.parabola_smooth contMDiff_const
        SmoothTransversePullback.parabola_transverse_all)⟩

theorem nilpotentPair_recovers : parabolaLift (op stage) nilpotentPair = realizedNilpotent :=
  (Realization.stageLift_unique SmoothTransversePullback.parabola_smooth contMDiff_const
    SmoothTransversePullback.parabola_transverse_all (op stage) nilpotentPair realizedNilpotent rfl rfl).symm

theorem recovered_nilpotent_second :
    readSecond.hom.app (atStage stage) (parabolaLift (op stage) nilpotentPair) 0 = 1+(d+d) := by
  rw [nilpotentPair_recovers, realizedNilpotent_second]

theorem recovered_nilpotent_restrict (r : stage ⟶ stage) :
    parabolaLift (op stage)
      (Realization.stagePairs_restrict SmoothTransversePullback.parabola_smooth contMDiff_const r.op nilpotentPair) =
    (object 1 SmoothTransversePullback.ParabolaFiber).obj.map (stageMap r) realizedNilpotent := by
  have h := Realization.stageLift_restrict SmoothTransversePullback.parabola_smooth contMDiff_const
    SmoothTransversePullback.parabola_transverse_all r.op nilpotentPair
  change (object 1 SmoothTransversePullback.ParabolaFiber).obj.map (stageMap r)
    (parabolaLift (op stage) nilpotentPair) = _ at h
  rw [nilpotentPair_recovers] at h
  exact h.symm

theorem recovered_nilpotent_composite :
    readParameter.hom.app (atStage stage)
      (parabolaLift (op stage)
        (Realization.stagePairs_restrict SmoothTransversePullback.parabola_smooth contMDiff_const
          (SmoothCoordinatePullbacks.doubleInfinitesimal ≫ SmoothCoordinatePullbacks.kill).op
          nilpotentPair)) 0 = 1 := by
  rw [recovered_nilpotent_restrict, realizedNilpotent_composite]

end Examples.SmoothTransverseRealization
