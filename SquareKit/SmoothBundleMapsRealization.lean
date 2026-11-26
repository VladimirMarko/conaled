import SquareKit.SmoothBundleMorphisms
import SquareKit.SmoothBundleRecovery
import SquareKit.SmoothManifoldFullFaithfulness
import SquareKit.SplitSheafCategory

/-! Ordinary bundle maps on the preferred realization of their common base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SmoothPrincipalBundle.Bundle
open CategoryTheory ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {n : ℕ} {G B E : Type} [Group G] [MulAction G E]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E]
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))

/-- The chosen atlas is transported to the preferred realization of the base. -/
def realizedTorsor := SheafTorsor.reindex P.descendedObject.torsor (atlasIso P.baseCharts).hom

def realizedTotalIso : SplitSheaf.extension P.realizedTorsor.family ≅ object n E := by
  let l := SplitSheaf.lift P.descendedObject.torsor.family (atlasIso P.baseCharts).hom
  letI : IsIso l := (SplitSheaf.extension_pullback P.descendedObject.torsor.family
    (atlasIso P.baseCharts).hom).isIso_fst_of_isIso
  exact asIso l ≪≫ P.totalSpaceIso

theorem realizedTotalIso_projection :
    P.realizedTotalIso.hom ≫ ManifoldRealization.map P.projection P.smooth_projection =
      SplitSheaf.p P.realizedTorsor.family := by
  change SplitSheaf.lift _ _ ≫ P.totalSpaceIso.hom ≫ _ = _
  rw [P.totalSpaceIso_projection, ← Category.assoc, SplitSheaf.lift_p, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  rfl

theorem realizedTotalIso_equivariant (x : (object n B).obj.Elements)
    (g : (locallyConstantGroup G).obj.obj x.obj) (p : P.realizedTorsor.family.family.obj x) :
    P.realizedTotalIso.hom.hom.app x.obj ⟨x.val, P.realizedTorsor.act x g p⟩ =
      (representation P.smooth_action).act x.obj g
        (P.realizedTotalIso.hom.hom.app x.obj ⟨x.val, p⟩) :=
  P.totalSpaceIso_equivariant ((atlasIso P.baseCharts).hom.hom.mapElements.obj x) g p

end SquareKit.SmoothPrincipalBundle.Bundle


namespace SquareKit.SmoothPrincipalBundle.Map
open CategoryTheory ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {n : ℕ} {G B E E' : Type} [Group G] [MulAction G E] [MulAction G E']
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace E']
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E] [ChartedSpace (Space n) E']
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E] [IsManifold (modelWithCorners n) ∞ E']
variable {P : Bundle (n := n) (G := G) (B := B) (E := E)}
  {Q : Bundle (n := n) (G := G) (B := B) (E := E')} (f : Map P Q)

def realizedTotalMap : SplitSheaf.extension P.realizedTorsor.family ⟶
    SplitSheaf.extension Q.realizedTorsor.family :=
  P.realizedTotalIso.hom ≫ ManifoldRealization.map f.toFun f.smooth ≫ Q.realizedTotalIso.inv

theorem realizedTotalMap_projection :
    f.realizedTotalMap ≫ SplitSheaf.p Q.realizedTorsor.family =
      SplitSheaf.p P.realizedTorsor.family := by
  rw [← Q.realizedTotalIso_projection]
  simp only [realizedTotalMap, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← ManifoldRealization.map_comp]
  have h : Q.projection ∘ f.toFun = P.projection := funext f.projection
  simp only [h]
  exact P.realizedTotalIso_projection

def realizedFiberMap : P.realizedTorsor.family.family ⟶ Q.realizedTorsor.family.family := SplitSheaf.mapOfTotal f.realizedTotalMap f.realizedTotalMap_projection

theorem realizedFiberMap_total : SplitSheaf.totalMap f.realizedFiberMap = f.realizedTotalMap :=
  SplitSheaf.totalMap_mapOfTotal _ _

theorem realizedFiberMap_value (x : (object n B).obj.Elements)
    (p : P.realizedTorsor.family.family.obj x) :
    Q.realizedTotalIso.hom.hom.app x.obj ⟨x.val, f.realizedFiberMap.app x p⟩ =
      (ManifoldRealization.map f.toFun f.smooth).hom.app x.obj
        (P.realizedTotalIso.hom.hom.app x.obj ⟨x.val, p⟩) := by
  have h : SplitSheaf.totalMap f.realizedFiberMap ≫ Q.realizedTotalIso.hom =
      P.realizedTotalIso.hom ≫ ManifoldRealization.map f.toFun f.smooth := by
    rw [f.realizedFiberMap_total]
    simp [realizedTotalMap]
  exact SplitSheaf.totalMap_value _ _ _ _ h x p

theorem realizedFiberMap_equivariant (x : (object n B).obj.Elements)
    (g : (locallyConstantGroup G).obj.obj x.obj) (p : P.realizedTorsor.family.family.obj x) :
    f.realizedFiberMap.app x (P.realizedTorsor.act x g p) =
      Q.realizedTorsor.act x g (f.realizedFiberMap.app x p) := by
  have hinj := ((CategoryTheory.isIso_iff_bijective
    (Q.realizedTotalIso.hom.hom.app x.obj)).mp inferInstance).injective
  have h : Q.realizedTotalIso.hom.hom.app x.obj
      ⟨x.val, f.realizedFiberMap.app x (P.realizedTorsor.act x g p)⟩ =
      Q.realizedTotalIso.hom.hom.app x.obj
      ⟨x.val, Q.realizedTorsor.act x g (f.realizedFiberMap.app x p)⟩ := by
    rw [f.realizedFiberMap_value, P.realizedTotalIso_equivariant,
      Q.realizedTotalIso_equivariant, f.realizedFiberMap_value]
    apply SmoothConstantAction.Representation.intertwines
    intro a
    exact Bundle.target_intertwines P Q.smooth_action f.toFun f.smooth f.equivariant a
  exact eq_of_heq (Sigma.mk.inj_iff.mp (hinj h)).2

def realizedEquivariantMap : SheafTorsor.EquivariantMap P.realizedTorsor Q.realizedTorsor where
  hom := f.realizedFiberMap
  equivariant := f.realizedFiberMap_equivariant

def realizedArrow : SheafTorsor.Arrow P.realizedTorsor Q.realizedTorsor :=
  f.realizedEquivariantMap.toArrow

end SquareKit.SmoothPrincipalBundle.Map

namespace SquareKit.SmoothPrincipalBundle
open CategoryTheory ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {n : ℕ} {G B E E' : Type} [Group G] [MulAction G E] [MulAction G E']
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace E']
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E] [ChartedSpace (Space n) E']
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E] [IsManifold (modelWithCorners n) ∞ E']
variable {P : Bundle (n := n) (G := G) (B := B) (E := E)}
  {Q : Bundle (n := n) (G := G) (B := B) (E := E')}

namespace RealizedArrow
variable (h : SheafTorsor.Arrow P.realizedTorsor Q.realizedTorsor)

def totalMap : object n E ⟶ object n E' :=
  P.realizedTotalIso.inv ≫ SplitSheaf.totalMap h.iso.hom ≫ Q.realizedTotalIso.hom

theorem totalMap_projection :
    totalMap h ≫ ManifoldRealization.map Q.projection Q.smooth_projection =
      ManifoldRealization.map P.projection P.smooth_projection := by
  simp only [totalMap, Category.assoc, Q.realizedTotalIso_projection]
  have hp : SplitSheaf.totalMap h.iso.hom ≫ SplitSheaf.p Q.realizedTorsor.family =
      SplitSheaf.p P.realizedTorsor.family := SplitSheaf.totalMap_projection _
  rw [hp, ← P.realizedTotalIso_projection, Iso.inv_hom_id_assoc]

theorem totalMap_equivariant (g : G) :
    (representation P.smooth_action).map g ≫ totalMap h =
      totalMap h ≫ (representation Q.smooth_action).map g := by
  apply (cancel_epi P.realizedTotalIso.hom).mp
  ext U z
  rcases z with ⟨b, p⟩
  let x := (object n B).obj.elementsMk U b
  let a := (constantLabel G).app U g
  have he := P.realizedTotalIso_equivariant x a p
  rw [SmoothConstantAction.Representation.act_constant] at he
  change (totalMap h).hom.app U
      (((representation P.smooth_action).map g).hom.app U
        (P.realizedTotalIso.hom.hom.app U ⟨b,p⟩)) =
    ((representation Q.smooth_action).map g).hom.app U
      ((totalMap h).hom.app U (P.realizedTotalIso.hom.hom.app U ⟨b,p⟩))
  rw [← he]
  rw [show (totalMap h).hom.app U
      (P.realizedTotalIso.hom.hom.app U ⟨b, P.realizedTorsor.act x a p⟩) =
      Q.realizedTotalIso.hom.hom.app U ⟨b, h.iso.hom.app x (P.realizedTorsor.act x a p)⟩ from
      SplitSheaf.conjugate_value P.realizedTotalIso Q.realizedTotalIso h.iso.hom x _]
  rw [show (totalMap h).hom.app U (P.realizedTotalIso.hom.hom.app U ⟨b,p⟩) =
      Q.realizedTotalIso.hom.hom.app U ⟨b,h.iso.hom.app x p⟩ from
      SplitSheaf.conjugate_value P.realizedTotalIso Q.realizedTotalIso h.iso.hom x p]
  rw [h.equivariant]
  exact (Q.realizedTotalIso_equivariant x a (h.iso.hom.app x p)).trans
    ((representation Q.smooth_action).act_constant U g _)

/-- Recover the ordinary smooth map from its action at all smooth stages. -/
def ordinaryMap : Map P Q where
  toFun := reconstruct (totalMap h)
  smooth := reconstruct_smooth _
  projection e := by
    have he : Q.projection ∘ reconstruct (totalMap h) = P.projection := by
      apply ManifoldRealization.map_injective
        (Q.smooth_projection.comp (reconstruct_smooth (totalMap h))) P.smooth_projection
      rw [ManifoldRealization.map_comp _ _ (reconstruct_smooth (totalMap h)) Q.smooth_projection,
        map_reconstruct]
      exact totalMap_projection h
    exact congrFun he e
  equivariant g e := by
    have he : reconstruct (totalMap h) ∘ (fun e : E => g • e) =
        (fun e : E' => g • e) ∘ reconstruct (totalMap h) := by
      apply ManifoldRealization.map_injective
        ((reconstruct_smooth (totalMap h)).comp (P.smooth_action g))
        ((Q.smooth_action g).comp (reconstruct_smooth (totalMap h)))
      rw [ManifoldRealization.map_comp _ _ (P.smooth_action g) (reconstruct_smooth (totalMap h)),
        ManifoldRealization.map_comp _ _ (reconstruct_smooth (totalMap h)) (Q.smooth_action g),
        map_reconstruct]
      exact totalMap_equivariant h g
    exact congrFun he e

end RealizedArrow
end SquareKit.SmoothPrincipalBundle

namespace SquareKit.SmoothPrincipalBundle
open CategoryTheory ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {n : ℕ} {G B E E' : Type} [Group G] [MulAction G E] [MulAction G E']
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace E']
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E] [ChartedSpace (Space n) E']
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E] [IsManifold (modelWithCorners n) ∞ E']
variable {P : Bundle (n := n) (G := G) (B := B) (E := E)}
  {Q : Bundle (n := n) (G := G) (B := B) (E := E')}

theorem Map.realizedArrow_total (f : Map P Q) :
    RealizedArrow.totalMap f.realizedArrow = ManifoldRealization.map f.toFun f.smooth := by
  change P.realizedTotalIso.inv ≫ SplitSheaf.totalMap f.realizedFiberMap ≫ Q.realizedTotalIso.hom = _
  rw [f.realizedFiberMap_total]
  simp [Map.realizedTotalMap]

theorem RealizedArrow.ordinaryMap_map (h : SheafTorsor.Arrow P.realizedTorsor Q.realizedTorsor) :
    ManifoldRealization.map (RealizedArrow.ordinaryMap h).toFun (RealizedArrow.ordinaryMap h).smooth =
      RealizedArrow.totalMap h := map_reconstruct _

@[simp] theorem Map.ordinary_realized (f : Map P Q) :
    RealizedArrow.ordinaryMap f.realizedArrow = f := by
  apply Map.ext
  change reconstruct (RealizedArrow.totalMap f.realizedArrow) = f.toFun
  rw [f.realizedArrow_total, reconstruct_map]

@[simp] theorem RealizedArrow.realized_ordinary
    (h : SheafTorsor.Arrow P.realizedTorsor Q.realizedTorsor) :
    (RealizedArrow.ordinaryMap h).realizedArrow = h := by
  apply SheafTorsor.Arrow.ext
  apply SplitSheaf.totalMap_injective
  change SplitSheaf.totalMap (RealizedArrow.ordinaryMap h).realizedFiberMap = _
  rw [Map.realizedFiberMap_total]
  simp only [Map.realizedTotalMap, RealizedArrow.ordinaryMap_map, RealizedArrow.totalMap,
    Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- Every equivariant ordinary smooth map, and every sheaf torsor arrow, is retained. -/
def mapEquiv : Map P Q ≃ SheafTorsor.Arrow P.realizedTorsor Q.realizedTorsor where
  toFun := Map.realizedArrow
  invFun := RealizedArrow.ordinaryMap
  left_inv := Map.ordinary_realized
  right_inv := RealizedArrow.realized_ordinary

namespace RealizedArrow

theorem totalMap_injective : Function.Injective
    (totalMap (P := P) (Q := Q)) := by
  intro h k he
  apply SheafTorsor.Arrow.ext
  apply SplitSheaf.totalMap_injective
  apply (cancel_epi P.realizedTotalIso.inv).mp
  apply (cancel_mono Q.realizedTotalIso.hom).mp
  simpa only [totalMap, Category.assoc] using he

end RealizedArrow
end SquareKit.SmoothPrincipalBundle


namespace SquareKit.SmoothPrincipalBundle
open CategoryTheory ManifoldRealization
open scoped Manifold ContDiff
variable {n : ℕ} {G B E E' E'' : Type} [Group G]
  [MulAction G E] [MulAction G E'] [MulAction G E'']
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace E'']
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E] [ChartedSpace (Space n) E']
  [ChartedSpace (Space n) E'']
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E]
  [IsManifold (modelWithCorners n) ∞ E'] [IsManifold (modelWithCorners n) ∞ E'']
variable {P : Bundle (n := n) (G := G) (B := B) (E := E)}
  {Q : Bundle (n := n) (G := G) (B := B) (E := E')}
  {R : Bundle (n := n) (G := G) (B := B) (E := E'')}

@[simp] theorem RealizedArrow.totalMap_ident :
    totalMap (SheafTorsor.Arrow.ident P.realizedTorsor) = 𝟙 (object n E) := by
  simp [totalMap, SheafTorsor.Arrow.ident]

theorem RealizedArrow.totalMap_comp
    (h : SheafTorsor.Arrow P.realizedTorsor Q.realizedTorsor)
    (k : SheafTorsor.Arrow Q.realizedTorsor R.realizedTorsor) :
    totalMap (h.comp k) = totalMap h ≫ totalMap k := by
  change P.realizedTotalIso.inv ≫ SplitSheaf.totalMap (h.iso.hom ≫ k.iso.hom) ≫
      R.realizedTotalIso.hom = _
  rw [SplitSheaf.totalMap_comp (A := P.realizedTorsor.family)
    (B := Q.realizedTorsor.family) (D := R.realizedTorsor.family)]
  simp [totalMap, Category.assoc]

@[simp] theorem Map.realizedArrow_ident :
    (Map.ident P).realizedArrow = SheafTorsor.Arrow.ident P.realizedTorsor := by
  apply RealizedArrow.totalMap_injective
  rw [Map.realizedArrow_total, RealizedArrow.totalMap_ident]
  exact ManifoldRealization.map_id

theorem Map.realizedArrow_comp (f : Map P Q) (g : Map Q R) :
    (f.comp g).realizedArrow = f.realizedArrow.comp g.realizedArrow := by
  apply RealizedArrow.totalMap_injective
  rw [Map.realizedArrow_total, RealizedArrow.totalMap_comp,
    f.realizedArrow_total, g.realizedArrow_total]
  exact ManifoldRealization.map_comp f.toFun g.toFun f.smooth g.smooth

/-- Inverse and its smoothness are derived through full faithfulness, not supplied. -/
def Map.inverse (f : Map P Q) : Map Q P :=
  RealizedArrow.ordinaryMap f.realizedArrow.inverse

@[simp] theorem Map.realizedArrow_inverse (f : Map P Q) :
    f.inverse.realizedArrow = f.realizedArrow.inverse := RealizedArrow.realized_ordinary _

@[simp] theorem Map.comp_inverse (f : Map P Q) : f.comp f.inverse = Map.ident P := by
  apply mapEquiv.injective
  change (f.comp f.inverse).realizedArrow = (Map.ident P).realizedArrow
  rw [Map.realizedArrow_comp, Map.realizedArrow_inverse, Map.realizedArrow_ident]
  apply SheafTorsor.Arrow.ext
  exact f.realizedArrow.iso.hom_inv_id

@[simp] theorem Map.inverse_comp (f : Map P Q) : f.inverse.comp f = Map.ident Q := by
  apply mapEquiv.injective
  change (f.inverse.comp f).realizedArrow = (Map.ident Q).realizedArrow
  rw [Map.realizedArrow_comp, Map.realizedArrow_inverse, Map.realizedArrow_ident]
  apply SheafTorsor.Arrow.ext
  exact f.realizedArrow.iso.inv_hom_id

@[simp] theorem Map.inverse_apply_apply (f : Map P Q) (e : E) : f.inverse.toFun (f.toFun e) = e :=
  congrArg (fun k : Map P P => k.toFun e) f.comp_inverse

@[simp] theorem Map.apply_inverse_apply (f : Map P Q) (e : E') : f.toFun (f.inverse.toFun e) = e :=
  congrArg (fun k : Map Q Q => k.toFun e) f.inverse_comp

end SquareKit.SmoothPrincipalBundle

namespace SquareKit.SmoothPrincipalBundle
open CategoryTheory ManifoldRealization
open scoped Manifold ContDiff
variable {n : ℕ} {G B E E' : Type} [Group G] [MulAction G E] [MulAction G E']
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace E']
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E] [ChartedSpace (Space n) E']
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E] [IsManifold (modelWithCorners n) ∞ E']
variable {P : Bundle (n := n) (G := G) (B := B) (E := E)}
  {Q : Bundle (n := n) (G := G) (B := B) (E := E')}

/-- The ordinary equivariant map is a genuine smooth bundle isomorphism. -/
def Map.diffeomorph (f : Map P Q) : E ≃ₘ⟮modelWithCorners n, modelWithCorners n⟯ E' where
  toEquiv := {
    toFun := f.toFun
    invFun := f.inverse.toFun
    left_inv := f.inverse_apply_apply
    right_inv := f.apply_inverse_apply }
  contMDiff_toFun := f.smooth
  contMDiff_invFun := f.inverse.smooth

@[simp] theorem Map.diffeomorph_apply (f : Map P Q) (e : E) : f.diffeomorph e = f.toFun e := rfl

/-- Returning to any original chart base is explicit reindexing along its atlas iso. -/
theorem Bundle.realizedTorsor_chart (P : Bundle (n := n) (G := G) (B := B) (E := E))
    (A : ChartFamily n B) :
    SheafTorsor.reindex P.realizedTorsor (atlasIso A).inv =
      SheafTorsor.reindex P.descendedObject.torsor (A.comparison P.baseCharts).hom := by
  change SheafTorsor.reindex P.descendedObject.torsor
      ((atlasIso A).inv ≫ (atlasIso P.baseCharts).hom) = _
  have he : (atlasIso A).inv ≫ (atlasIso P.baseCharts).hom =
      (A.comparison P.baseCharts).hom :=
    congrArg Iso.hom (A.comparison_trans .preferred P.baseCharts)
  rw [he]

/-- Recovering the original selected base needs no equality of chart choices. -/
theorem Bundle.realizedTorsor_original (P : Bundle (n := n) (G := G) (B := B) (E := E)) :
    SheafTorsor.reindex P.realizedTorsor (atlasIso P.baseCharts).inv = P.descendedObject.torsor := by
  rw [P.realizedTorsor_chart, ChartFamily.comparison_refl]
  rfl

end SquareKit.SmoothPrincipalBundle
