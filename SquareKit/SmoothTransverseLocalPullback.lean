import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import SquareKit.SmoothTransverseStageCover
import SquareKit.SmoothOpenCoordinatePullbacks
import SquareKit.SmoothNormalFormPrincipal

/-! Ordinary principal products and their full-algebra coordinate lifts. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.EuclideanOpen.Product
open CategoryTheory SmoothAlgebra SmoothPresentationSite Localization

variable (U V : Domain)

def defining : Free (U.dimension + V.dimension) :=
  SmoothAlgebra.Coordinates.left U.dimension V.dimension U.defining *
    SmoothAlgebra.Coordinates.right U.dimension V.dimension V.defining

def domain : Domain := ⟨U.dimension + V.dimension, defining U V⟩

def fst : domain U V ⟶ U where
  toFun x := ⟨fun i => x.val (Fin.castAdd V.dimension i), left_ne_zero_of_mul x.property⟩
  smooth i := (OpenFunctions.representative_iff _
    (fun x => x (Fin.castAdd V.dimension i)) (fun _ => rfl)).mpr
    (contDiff_apply ℝ (fun _ : Fin (U.dimension + V.dimension) => ℝ)
      (Fin.castAdd V.dimension i)).contDiffOn

def snd : domain U V ⟶ V where
  toFun x := ⟨fun i => x.val (Fin.natAdd U.dimension i), right_ne_zero_of_mul x.property⟩
  smooth i := (OpenFunctions.representative_iff _
    (fun x => x (Fin.natAdd U.dimension i)) (fun _ => rfl)).mpr
    (contDiff_apply ℝ (fun _ : Fin (U.dimension + V.dimension) => ℝ)
      (Fin.natAdd U.dimension i)).contDiffOn

theorem fst_base (i : Fin U.dimension) :
    Localization.pullback (fst U V) (principalBase U.defining (generator i)) =
      principalBase (defining U V) (generator (Fin.castAdd V.dimension i)) := by
  apply (toOpen_bijective _).injective
  apply OpenFunctions.ext
  intro x
  rw [Localization.pullback_apply, toOpen_base]
  exact (toOpen_base (defining U V) (generator (Fin.castAdd V.dimension i)) x).symm

theorem snd_base (i : Fin V.dimension) :
    Localization.pullback (snd U V) (principalBase V.defining (generator i)) =
      principalBase (defining U V) (generator (Fin.natAdd U.dimension i)) := by
  apply (toOpen_bijective _).injective
  apply OpenFunctions.ext
  intro x
  rw [Localization.pullback_apply, toOpen_base]
  exact (toOpen_base (defining U V) (generator (Fin.natAdd U.dimension i)) x).symm

variable {B : Type*} [CommRing B] [Algebra ℝ B] [Structure B]
  (a : Hom (Principal U.defining) B) (b : Hom (Principal V.defining) B)

def coordinates : Hom (Free (U.dimension + V.dimension)) B :=
  SmoothAlgebra.Coordinates.pair (a.comp (principalBase U.defining))
    (b.comp (principalBase V.defining))

theorem coordinates_unit : IsUnit (coordinates U V a b (defining U V)) := by
  have hl := congrArg (fun h : Hom (Free U.dimension) B => h U.defining)
    (SmoothAlgebra.Coordinates.pair_left (a.comp (principalBase U.defining))
      (b.comp (principalBase V.defining)))
  have hr := congrArg (fun h : Hom (Free V.dimension) B => h V.defining)
    (SmoothAlgebra.Coordinates.pair_right (a.comp (principalBase U.defining))
      (b.comp (principalBase V.defining)))
  change IsUnit ((coordinates U V a b).toAlgHom (_ * _))
  rw [map_mul]
  change IsUnit (coordinates U V a b _ * coordinates U V a b _)
  change coordinates U V a b _ = a (principalBase U.defining U.defining) at hl
  change coordinates U V a b _ = b (principalBase V.defining V.defining) at hr
  rw [hl, hr]
  exact ((base_isUnit (fun _ : Fin 1 => U.defining) 0).map a.toAlgHom).mul
    ((base_isUnit (fun _ : Fin 1 => V.defining) 0).map b.toAlgHom)

def pair : Hom (Principal (defining U V)) B :=
  principalLift (defining U V) (coordinates U V a b) (coordinates_unit U V a b)

theorem pair_base : (pair U V a b).comp (principalBase (defining U V)) =
    coordinates U V a b := lift_base _ _ (fun _ => coordinates_unit U V a b)

theorem pair_fst : (pair U V a b).comp (Localization.pullback (fst U V)) = a := by
  apply principal_unique U.defining
  apply hom_ext_generators
  intro i
  change pair U V a b (Localization.pullback (fst U V) (principalBase U.defining (generator i))) = _
  rw [fst_base]
  have h := congrArg (fun k : Hom (Free (U.dimension + V.dimension)) B =>
    k (generator (Fin.castAdd V.dimension i))) (pair_base U V a b)
  simpa only [Hom.comp, Function.comp_apply, coordinates, SmoothAlgebra.Coordinates.pair,
    evaluate_generator, Fin.addCases_left] using h

theorem pair_snd : (pair U V a b).comp (Localization.pullback (snd U V)) = b := by
  apply principal_unique V.defining
  apply hom_ext_generators
  intro i
  change pair U V a b (Localization.pullback (snd U V) (principalBase V.defining (generator i))) = _
  rw [snd_base]
  have h := congrArg (fun k : Hom (Free (U.dimension + V.dimension)) B =>
    k (generator (Fin.natAdd U.dimension i))) (pair_base U V a b)
  simpa only [Hom.comp, Function.comp_apply, coordinates, SmoothAlgebra.Coordinates.pair,
    evaluate_generator, Fin.addCases_right] using h

theorem pair_unique (w : Hom (Principal (defining U V)) B)
    (hl : w.comp (Localization.pullback (fst U V)) = a)
    (hr : w.comp (Localization.pullback (snd U V)) = b) : w = pair U V a b := by
  apply principal_unique (defining U V)
  rw [pair_base]
  apply hom_ext_generators
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have h := congrArg (fun k : Hom (Principal U.defining) B =>
      k (principalBase U.defining (generator j))) hl
    change w (Localization.pullback (fst U V) (principalBase U.defining (generator j))) = _ at h
    rw [fst_base] at h
    simpa only [Hom.comp, Function.comp_apply, coordinates, SmoothAlgebra.Coordinates.pair,
      evaluate_generator, Fin.addCases_left] using h
  · have h := congrArg (fun k : Hom (Principal V.defining) B =>
      k (principalBase V.defining (generator j))) hr
    change w (Localization.pullback (snd U V) (principalBase V.defining (generator j))) = _ at h
    rw [snd_base] at h
    simpa only [Hom.comp, Function.comp_apply, coordinates, SmoothAlgebra.Coordinates.pair,
      evaluate_generator, Fin.addCases_right] using h

theorem universal : ∃! w : Hom (Principal (defining U V)) B,
    w.comp (Localization.pullback (fst U V)) = a ∧
      w.comp (Localization.pullback (snd U V)) = b :=
  ⟨pair U V a b, ⟨pair_fst U V a b, pair_snd U V a b⟩,
    fun w hw => pair_unique U V a b w hw.1 hw.2⟩

theorem pair_comp {C : Type*} [CommRing C] [Algebra ℝ C] [Structure C] (c : Hom B C) :
    c.comp (pair U V a b) = pair U V (c.comp a) (c.comp b) := by
  apply pair_unique
  · rw [← Hom.comp_assoc, pair_fst]
  · rw [← Hom.comp_assoc, pair_snd]

end SquareKit.EuclideanOpen.Product



namespace SquareKit.EuclideanOpen.Product
open CategoryTheory CategoryTheory.Limits Opposite SmoothAlgebra SmoothPresentationSite Localization

def toPoint (U : Domain) : U ⟶ full 0 where
  toFun _ := ⟨Fin.elim0, one_ne_zero⟩
  smooth i := Fin.elim0 i

theorem point_unique {U : Domain} (a b : U ⟶ full 0) : a = b := by
  apply OpenFunctions.Map.ext
  intro x
  apply Subtype.ext
  funext i
  exact Fin.elim0 i

theorem site_isPullback (U V : Domain) :
    IsPullback (toSite.map (fst U V)) (toSite.map (snd U V))
      (toSite.map (toPoint U)) (toSite.map (toPoint V)) := by
  have h : IsPushout
      (show code (full 0) ⟶ code U from Localization.pullback (toPoint U))
      (show code (full 0) ⟶ code V from Localization.pullback (toPoint V))
      (show code U ⟶ code (domain U V) from Localization.pullback (fst U V))
      (show code V ⟶ code (domain U V) from Localization.pullback (snd U V)) := by
    apply IsPushout.of_isColimit
      (PushoutCocone.IsColimit.mk
        (inl := show code U ⟶ code (domain U V) from Localization.pullback (fst U V))
        (inr := show code V ⟶ code (domain U V) from Localization.pullback (snd U V))
        ?_ (fun c => pair U V (smoothMap c.inl) (smoothMap c.inr))
        (fun c => pair_fst U V (smoothMap c.inl) (smoothMap c.inr))
        (fun c => pair_snd U V (smoothMap c.inl) (smoothMap c.inr))
        (fun c w hl hr => pair_unique U V (smoothMap c.inl) (smoothMap c.inr)
          (smoothMap w) hl hr))
    exact (Localization.pullback_comp (fst U V) (toPoint U)).symm.trans
      ((congrArg (fun k : EuclideanOpen.Map _ _ => Localization.pullback k)
        (point_unique (fst U V ≫ toPoint U) (snd U V ≫ toPoint V))).trans
        (Localization.pullback_comp (snd U V) (toPoint V)))
  exact h.op.flip

/-- The ordinary principal product represents the product at every sheaf test. -/
theorem isPullback (U V : Domain) :
    IsPullback (embedding.map (fst U V)) (embedding.map (snd U V))
      (embedding.map (toPoint U)) (embedding.map (toPoint V)) :=
  SmoothOpenSite.topology.yoneda.map_isPullback (site_isPullback U V)

theorem sheaf_point_unique {F : Sheaf SmoothOpenSite.topology Type}
    (a b : F ⟶ embedding.obj (full 0)) : a = b := by
  apply (cancel_mono (fullPowerIso 0).hom).mp
  exact SmoothOpenSite.Coordinates.point_unique _ _

variable (U V : Domain) {F G : Sheaf SmoothOpenSite.topology Type}

def sheafPair (a : F ⟶ embedding.obj U) (b : F ⟶ embedding.obj V) :
    F ⟶ embedding.obj (domain U V) :=
  (isPullback U V).lift a b (sheaf_point_unique _ _)

@[reassoc (attr := simp)] theorem sheafPair_fst
    (a : F ⟶ embedding.obj U) (b : F ⟶ embedding.obj V) :
    sheafPair U V a b ≫ embedding.map (fst U V) = a := (isPullback U V).lift_fst _ _ _

@[reassoc (attr := simp)] theorem sheafPair_snd
    (a : F ⟶ embedding.obj U) (b : F ⟶ embedding.obj V) :
    sheafPair U V a b ≫ embedding.map (snd U V) = b := (isPullback U V).lift_snd _ _ _

theorem sheafPair_unique (a : F ⟶ embedding.obj U) (b : F ⟶ embedding.obj V)
    (w : F ⟶ embedding.obj (domain U V))
    (hl : w ≫ embedding.map (fst U V) = a)
    (hr : w ≫ embedding.map (snd U V) = b) : w = sheafPair U V a b :=
  (isPullback U V).hom_ext (hl.trans (sheafPair_fst U V a b).symm)
    (hr.trans (sheafPair_snd U V a b).symm)

theorem sheafPair_precomp (a : F ⟶ embedding.obj U) (b : F ⟶ embedding.obj V) (r : G ⟶ F) :
    r ≫ sheafPair U V a b = sheafPair U V (r ≫ a) (r ≫ b) := by
  apply sheafPair_unique <;> simp

/-- Evaluation of the categorical pairing is the full smooth-algebra pairing. -/
theorem sheafPair_apply (a : F ⟶ embedding.obj U) (b : F ⟶ embedding.obj V)
    (B : Code) (x : F.obj.obj (op (op B))) :
    ((sheafPair U V a b).hom.app (op (op B)) x).unop =
      pair U V (smoothMap (a.hom.app (op (op B)) x).unop)
        (smoothMap (b.hom.app (op (op B)) x).unop) := by
  apply pair_unique
  · exact congrArg (fun k : F ⟶ embedding.obj U => (k.hom.app (op (op B)) x).unop)
      (sheafPair_fst U V a b)
  · exact congrArg (fun k : F ⟶ embedding.obj V => (k.hom.app (op (op B)) x).unop)
      (sheafPair_snd U V a b)

theorem sheafPair_stage (a : F ⟶ embedding.obj U) (b : F ⟶ embedding.obj V)
    {B C : Code} (r : B ⟶ C) (x : F.obj.obj (op (op B))) :
    ((sheafPair U V a b).hom.app (op (op C)) (F.obj.map r.op.op x)).unop =
      (smoothMap r).comp ((sheafPair U V a b).hom.app (op (op B)) x).unop :=
  congrArg Quiver.Hom.unop (NatTrans.naturality_apply (sheafPair U V a b).hom r.op.op x)

end SquareKit.EuclideanOpen.Product

namespace SquareKit.SmoothTransversePullback.LocalModel
open CategoryTheory ManifoldRealization SmoothTransversality SmoothNormalFormPrincipal IsManifold
open EuclideanOpen SmoothAlgebra
open scoped ContDiff Manifold

variable {m n p : ℕ} {M N P : Type}
  [TopologicalSpace M] [ChartedSpace (Space m) M]
  [TopologicalSpace N] [ChartedSpace (Space n) N]
  [TopologicalSpace P] [ChartedSpace (Space p) P]
  {f : M → P} {g : N → P} {q : Pullback f g}
  (A : LocalModel (m := m) (n := n) (p := p) q)

theorem ambient_mem (x : Points (sourceDomain A.finiteChart)) :
    split m n x.val ∈ coordinateNeighborhood (m := m) (n := n) (p := p) f g q.val.1 q.val.2 := by
  apply A.normal.source_subset
  have hx : x.val ∈ A.finiteChart.source := (sourceDomain_points _) ▸ x.property
  rw [A.finiteChart_source] at hx
  exact hx

def ambientFirst : sourceDomain A.finiteChart ⟶ chartDomain (chartAt (Space m) q.val.1) where
  toFun x := ⟨(split m n x.val).1, by
    change (split m n x.val).1 ∈ Points (chartDomain (chartAt (Space m) q.val.1))
    rw [chartDomain_locus]
    exact (A.ambient_mem x).1.1⟩
  smooth i := (OpenFunctions.representative_iff _ (fun x => x (Fin.castAdd n i))
    (fun _ => rfl)).mpr (contDiff_apply ℝ (fun _ : Fin (m+n) => ℝ) (Fin.castAdd n i)).contDiffOn

def ambientSecond : sourceDomain A.finiteChart ⟶ chartDomain (chartAt (Space n) q.val.2) where
  toFun x := ⟨(split m n x.val).2, by
    change (split m n x.val).2 ∈ Points (chartDomain (chartAt (Space n) q.val.2))
    rw [chartDomain_locus]
    exact (A.ambient_mem x).2.1⟩
  smooth i := (OpenFunctions.representative_iff _ (fun x => x (Fin.natAdd m i))
    (fun _ => rfl)).mpr (contDiff_apply ℝ (fun _ : Fin (m+n) => ℝ) (Fin.natAdd m i)).contDiffOn

@[simp] theorem ambientFirst_apply (x : Points (sourceDomain A.finiteChart)) :
    ((show EuclideanOpen.Map _ _ from A.ambientFirst) x).val = (split m n x.val).1 := rfl

@[simp] theorem ambientSecond_apply (x : Points (sourceDomain A.finiteChart)) :
    ((show EuclideanOpen.Map _ _ from A.ambientSecond) x).val = (split m n x.val).2 := rfl

theorem ambientFirst_base (i : Fin m) :
    Localization.pullback A.ambientFirst
      (Localization.principalBase (chartDomain (chartAt (Space m) q.val.1)).defining (generator i)) =
    Localization.principalBase (sourceDomain A.finiteChart).defining (generator (Fin.castAdd n i)) := by
  apply (Localization.toOpen_bijective _).injective
  apply OpenFunctions.ext
  intro x
  rw [Localization.pullback_apply, Localization.toOpen_base, Localization.toOpen_base]
  rfl

theorem ambientSecond_base (i : Fin n) :
    Localization.pullback A.ambientSecond
      (Localization.principalBase (chartDomain (chartAt (Space n) q.val.2)).defining (generator i)) =
    Localization.principalBase (sourceDomain A.finiteChart).defining (generator (Fin.natAdd m i)) := by
  apply (Localization.toOpen_bijective _).injective
  apply OpenFunctions.ext
  intro x
  rw [Localization.pullback_apply, Localization.toOpen_base, Localization.toOpen_base]
  rfl

theorem ambient_joint_cancel {B : Type*} [CommRing B] [Algebra ℝ B] [Structure B]
    (a b : Hom (Localization.Principal (sourceDomain A.finiteChart).defining) B)
    (hl : a.comp (Localization.pullback A.ambientFirst) = b.comp (Localization.pullback A.ambientFirst))
    (hr : a.comp (Localization.pullback A.ambientSecond) = b.comp (Localization.pullback A.ambientSecond)) :
    a = b := by
  apply Localization.unique
  apply hom_ext_generators
  intro i
  change a (Localization.principalBase _ (generator i)) = b (Localization.principalBase _ (generator i))
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [← A.ambientFirst_base j]
    exact congrArg (fun k : Hom (Localization.Principal
      (chartDomain (chartAt (Space m) q.val.1)).defining) B =>
        k (Localization.principalBase _ (generator j))) hl
  · rw [← A.ambientSecond_base j]
    exact congrArg (fun k : Hom (Localization.Principal
      (chartDomain (chartAt (Space n) q.val.2)).defining) B =>
        k (Localization.principalBase _ (generator j))) hr

theorem normalParameterMap_first_agreement (v : Points (chartDomain A.chart)) :
    chartPoint (chartAt (Space m) q.val.1)
        ((show EuclideanOpen.Map _ _ from A.normalParameterMap ≫ A.ambientFirst) v) =
      (chartPoint A.chart v).val.1 := by
  have hv : v.val ∈ A.chart.target := by
    rw [← chartDomain_locus A.chart]
    exact v.property
  change v.val ∈ A.target at hv
  change (chartAt (Space m) q.val.1).symm
    (split m n ((show EuclideanOpen.Map _ _ from A.normalParameterMap) v).val).1 =
      (A.inverse v.val).val.1
  rw [A.normalParameterMap_apply, (split m n).apply_symm_apply, A.inverse_val hv]
  rfl

theorem normalParameterMap_second_agreement (v : Points (chartDomain A.chart)) :
    chartPoint (chartAt (Space n) q.val.2)
        ((show EuclideanOpen.Map _ _ from A.normalParameterMap ≫ A.ambientSecond) v) =
      (chartPoint A.chart v).val.2 := by
  have hv : v.val ∈ A.chart.target := by
    rw [← chartDomain_locus A.chart]
    exact v.property
  change v.val ∈ A.target at hv
  change (chartAt (Space n) q.val.2).symm
    (split m n ((show EuclideanOpen.Map _ _ from A.normalParameterMap) v).val).2 =
      (A.inverse v.val).val.2
  rw [A.normalParameterMap_apply, (split m n).apply_symm_apply, A.inverse_val hv]
  rfl

variable [IsManifold (Model m) ∞ M] [IsManifold (Model n) ∞ N] [IsManifold (Model p) ∞ P]
  (hf : ContMDiff (Model m) (Model p) ∞ f) (hg : ContMDiff (Model n) (Model p) ∞ g)

def ambientFirstRestriction : sourceDomain A.finiteChart ⟶
    subdomain (chartDomain (chartAt (Space m) q.val.1))
      (coordinateDefining (e := chartAt (Space m) q.val.1) (chartAt (Space p) (f q.val.1)) f hf.continuous) :=
  restrictCodomain A.ambientFirst _ (fun x =>
    (coordinateDefining_iff (chartAt (Space p) (f q.val.1)) f hf.continuous _).mpr (A.ambient_mem x).1)

def ambientSecondRestriction : sourceDomain A.finiteChart ⟶
    subdomain (chartDomain (chartAt (Space n) q.val.2))
      (coordinateDefining (e := chartAt (Space n) q.val.2) (chartAt (Space p) (f q.val.1)) g hg.continuous) :=
  restrictCodomain A.ambientSecond _ (fun x =>
    (coordinateDefining_iff (chartAt (Space p) (f q.val.1)) g hg.continuous _).mpr (A.ambient_mem x).2)

def ambientTargetFirst : sourceDomain A.finiteChart ⟶ chartDomain (chartAt (Space p) (f q.val.1)) :=
  A.ambientFirstRestriction hf ≫ coordinateMap (chartAt (Space p) (f q.val.1)) f
    (IsManifold.chart_mem_maximalAtlas q.val.1) (IsManifold.chart_mem_maximalAtlas (f q.val.1)) hf

def ambientTargetSecond : sourceDomain A.finiteChart ⟶ chartDomain (chartAt (Space p) (f q.val.1)) :=
  A.ambientSecondRestriction hg ≫ coordinateMap (chartAt (Space p) (f q.val.1)) g
    (IsManifold.chart_mem_maximalAtlas q.val.2) (IsManifold.chart_mem_maximalAtlas (f q.val.1)) hg

omit [IsManifold (Model n) ∞ N] in
theorem ambientTargetFirst_agreement (x : Points (sourceDomain A.finiteChart)) :
    f (chartPoint (chartAt (Space m) q.val.1) ((show EuclideanOpen.Map _ _ from A.ambientFirst) x)) =
      chartPoint (chartAt (Space p) (f q.val.1)) ((show EuclideanOpen.Map _ _ from A.ambientTargetFirst hf) x) :=
  coordinateMap_agreement (chartAt (Space p) (f q.val.1)) f
    (IsManifold.chart_mem_maximalAtlas q.val.1) (IsManifold.chart_mem_maximalAtlas (f q.val.1)) hf
    ((show EuclideanOpen.Map _ _ from A.ambientFirstRestriction hf) x)

omit [IsManifold (Model m) ∞ M] in
theorem ambientTargetSecond_agreement (x : Points (sourceDomain A.finiteChart)) :
    g (chartPoint (chartAt (Space n) q.val.2) ((show EuclideanOpen.Map _ _ from A.ambientSecond) x)) =
      chartPoint (chartAt (Space p) (f q.val.1)) ((show EuclideanOpen.Map _ _ from A.ambientTargetSecond hg) x) :=
  coordinateMap_agreement (chartAt (Space p) (f q.val.1)) g
    (IsManifold.chart_mem_maximalAtlas q.val.2) (IsManifold.chart_mem_maximalAtlas (f q.val.1)) hg
    ((show EuclideanOpen.Map _ _ from A.ambientSecondRestriction hg) x)

/-- The difference coordinate is an equality in the full principal algebra. -/
theorem normalDifference_base (i : Fin p) :
    Localization.pullback A.normalDifferenceMap (Localization.principalBase 1 (generator i)) =
      Localization.pullback (A.ambientTargetFirst hf)
          (Localization.principalBase (chartDomain (chartAt (Space p) (f q.val.1))).defining (generator i)) -
        Localization.pullback (A.ambientTargetSecond hg)
          (Localization.principalBase (chartDomain (chartAt (Space p) (f q.val.1))).defining (generator i)) := by
  apply (Localization.toOpen_bijective _).injective
  rw [show Localization.toOpen (sourceDomain A.finiteChart).defining (_ - _) =
      Localization.toOpen (sourceDomain A.finiteChart).defining _ -
        Localization.toOpen (sourceDomain A.finiteChart).defining _ from
    map_sub (Localization.toOpen (sourceDomain A.finiteChart).defining).toAlgHom _ _]
  apply OpenFunctions.ext
  intro x
  change (Localization.toOpen _ (Localization.pullback A.normalDifferenceMap _)).val x =
    (Localization.toOpen _ (Localization.pullback (A.ambientTargetFirst hf) _)).val x -
      (Localization.toOpen _ (Localization.pullback (A.ambientTargetSecond hg) _)).val x
  rw [Localization.pullback_apply, Localization.pullback_apply, Localization.pullback_apply,
    Localization.toOpen_base, Localization.toOpen_base, Localization.toOpen_base]
  change ((show EuclideanOpen.Map _ _ from A.normalDifferenceMap) x).val i = _
  rw [A.normalDifferenceMap_apply]
  rfl

theorem normalDifference_zero_coordinates {B : Type*} [CommRing B] [Algebra ℝ B] [Structure B]
    (w : Hom (Localization.Principal (sourceDomain A.finiteChart).defining) B)
    (hc : w.comp (Localization.pullback (A.ambientTargetFirst hf)) =
      w.comp (Localization.pullback (A.ambientTargetSecond hg))) (i : Fin p) :
    w (Localization.pullback A.normalDifferenceMap (Localization.principalBase 1 (generator i))) = 0 := by
  rw [A.normalDifference_base hf hg]
  change w.toAlgHom (_ - _) = 0
  rw [map_sub, sub_eq_zero]
  exact congrArg (fun k : Hom (Localization.Principal
    (chartDomain (chartAt (Space p) (f q.val.1))).defining) B =>
      k (Localization.principalBase _ (generator i))) hc

theorem normalDifference_zero {B : Type*} [CommRing B] [Algebra ℝ B] [Structure B]
    (w : Hom (Localization.Principal (sourceDomain A.finiteChart).defining) B)
    (hc : w.comp (Localization.pullback (A.ambientTargetFirst hf)) =
      w.comp (Localization.pullback (A.ambientTargetSecond hg))) :
    w.comp (Localization.pullback A.normalDifferenceMap) =
      (w.comp (Localization.pullback (Product.toPoint (sourceDomain A.finiteChart)))).comp
        (Localization.pullback (Coordinates.zero p)) := by
  apply Localization.unique
  apply hom_ext_generators
  intro i
  change w (Localization.pullback A.normalDifferenceMap (Localization.principalBase 1 (generator i))) = _
  rw [A.normalDifference_zero_coordinates hf hg w hc i]
  have hz : Localization.pullback (Coordinates.zero p)
      (Localization.principalBase 1 (generator i)) = 0 := by
    apply (Localization.toOpen_bijective _).injective
    apply OpenFunctions.ext
    intro x
    rw [Localization.pullback_apply, Localization.toOpen_base]
    rfl
  change 0 = w (Localization.pullback (Product.toPoint (sourceDomain A.finiteChart))
    (Localization.pullback (Coordinates.zero p) (Localization.principalBase 1 (generator i))))
  rw [hz]
  change 0 = w.toAlgHom ((Localization.pullback (Product.toPoint (sourceDomain A.finiteChart))).toAlgHom 0)
  rw [map_zero, map_zero]

omit [IsManifold (Model m) ∞ M] [IsManifold (Model n) ∞ N]
    [IsManifold (Model p) ∞ P] in
theorem normalParameterMap_cancel {B : SmoothPresentationSite.Code}
    (a b : Hom (Localization.Principal (chartDomain A.chart).defining)
      (SmoothPresentationSite.Carrier B))
    (h : a.comp (Localization.pullback A.normalParameterMap) =
      b.comp (Localization.pullback A.normalParameterMap)) : a = b := by
  have hp := ((sheafToPresheaf SmoothOpenSite.topology Type) ⋙
    (evaluation _ Type).obj (Opposite.op (Opposite.op B))).map_isPullback A.normal_isPullback
  have hpoint : a.comp (Localization.pullback A.levelToPoint) =
      b.comp (Localization.pullback A.levelToPoint) := by
    apply Localization.unique
    apply hom_ext_generators
    intro i
    exact Fin.elim0 i
  have hh := Limits.Types.ext_of_isPullback hp
    (x₁ := (show code (chartDomain A.chart) ⟶ B from a).op)
    (y₁ := (show code (chartDomain A.chart) ⟶ B from b).op) (congrArg Quiver.Hom.op h) (congrArg Quiver.Hom.op hpoint)
  exact congrArg Quiver.Hom.unop hh

theorem normalFactorization (B : SmoothPresentationSite.Code)
    (w : Hom (Localization.Principal (sourceDomain A.finiteChart).defining)
      (SmoothPresentationSite.Carrier B))
    (hc : w.comp (Localization.pullback (A.ambientTargetFirst hf)) =
      w.comp (Localization.pullback (A.ambientTargetSecond hg))) :
    ∃! v : Hom (Localization.Principal (chartDomain A.chart).defining)
      (SmoothPresentationSite.Carrier B),
      v.comp (Localization.pullback A.normalParameterMap) = w := by
  have hp := ((sheafToPresheaf SmoothOpenSite.topology Type) ⋙
    (evaluation _ Type).obj (Opposite.op (Opposite.op B))).map_isPullback A.normal_isPullback
  obtain ⟨v, hv, _⟩ := Limits.Types.exists_of_isPullback hp
    (show code (sourceDomain A.finiteChart) ⟶ B from w).op
    (show code (full 0) ⟶ B from
      w.comp (Localization.pullback (Product.toPoint (sourceDomain A.finiteChart)))).op
    (congrArg Quiver.Hom.op (A.normalDifference_zero hf hg w hc))
  refine ⟨v.unop, congrArg Quiver.Hom.unop hv, ?_⟩
  intro y hy
  exact A.normalParameterMap_cancel y v.unop (hy.trans (congrArg Quiver.Hom.unop hv).symm)

end SquareKit.SmoothTransversePullback.LocalModel
