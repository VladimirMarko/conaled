import SquareKit.SmoothTorsorAtlas
import SquareKit.SmoothBundleRealization

/-! Consumers of Čech recovery on derived section atlases. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SquareKit.SmoothCech
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothManifoldAction ManifoldRealization
open scoped Manifold ContDiff
variable {d n : ℕ} {G M N : Type} [Group G] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
  [TopologicalSpace N] [ChartedSpace (Space n) N]
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))
variable (A : ChartFamily n N)
  (P : SheafActionQuotient.Object (representation smoothAction).action A.realization)

abbrev derivedDatum := (trivializedOnManifold smoothAction A P).extractedDatum

/-- Selected recovery retains the whole torsor and target-valued map. -/
def derivedRecovery : SheafActionQuotient.Arrow
    ((derivedDatum smoothAction A P).interpreted smoothAction) P :=
  (trivializedOnManifold smoothAction A P).extractedRecovery

end SquareKit.SmoothCech

namespace SquareKit.SmoothPrincipalBundle.Bundle
open CategoryTheory ManifoldRealization EuclideanOpen SmoothManifoldAction
open scoped Manifold ContDiff
variable {n : ℕ} {G B E : Type} [Group G] [MulAction G E]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E]
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))

/-- The ordinary bundle determines its smooth Čech datum before interpretation. -/
def ordinaryDatum : SmoothCech.Datum (d := n) (G := G) (M := E) P.baseCharts.representedAtlas where
  localMap i := ⟨P.ordinarySheet i 1, P.ordinarySheet_smooth i 1⟩
  transition i j := ⟨P.transitionLabel i j, P.transitionLabel_action i j⟩
  diagonal i x := by
    change B at i
    let A := P.baseCharts.representedAtlas
    have hl := congrArg (fun f : A.domain i ⟶ A.domain i => (show Map _ _ from f) x) (A.diagonal_left i)
    have hr := congrArg (fun f : A.domain i ⟶ A.domain i => (show Map _ _ from f) x) (A.diagonal_right i)
    apply P.action_free _ _ (P.ordinarySheet i 1 x)
    have h := P.transitionLabel_action i i ((show Map _ _ from A.diagonal i) x)
    change _ • P.ordinarySheet i 1 ((show Map _ _ from A.left i i) ((show Map _ _ from A.diagonal i) x)) =
      P.ordinarySheet i 1 ((show Map _ _ from A.right i i) ((show Map _ _ from A.diagonal i) x)) at h
    change (show Map _ _ from A.left i i) ((show Map _ _ from A.diagonal i) x) = x at hl
    change (show Map _ _ from A.right i i) ((show Map _ _ from A.diagonal i) x) = x at hr
    dsimp only [A] at h hl hr
    rw [hl, hr] at h
    exact h.trans (one_smul G _).symm
  cocycle i j k x := by
    change B at i j k
    let A := P.baseCharts.representedAtlas
    have hfl := congrArg (fun f : A.triple i j k ⟶ A.domain i => (show Map _ _ from f) x) (A.firstThird_left i j k)
    have hfr := congrArg (fun f : A.triple i j k ⟶ A.domain k => (show Map _ _ from f) x) (A.firstThird_right i j k)
    have hsl := congrArg (fun f : A.triple i j k ⟶ A.domain j => (show Map _ _ from f) x) (A.secondThird_left i j k)
    have hsr := congrArg (fun f : A.triple i j k ⟶ A.domain k => (show Map _ _ from f) x) (A.secondThird_right i j k)
    let y := (show Map _ _ from A.firstSecond i j k) x
    let z := (show Map _ _ from A.firstThird i j k) x
    let w := (show Map _ _ from A.secondThird i j k) x
    change (show Map _ _ from A.left i k) z = (show Map _ _ from A.left i j) y at hfl
    change (show Map _ _ from A.right i k) z = (show Map _ _ from A.third i j k) x at hfr
    change (show Map _ _ from A.left j k) w = (show Map _ _ from A.right i j) y at hsl
    change (show Map _ _ from A.right j k) w = (show Map _ _ from A.third i j k) x at hsr
    apply P.action_free _ _ (P.ordinarySheet i 1 ((show Map _ _ from A.left i j) y))
    change P.transitionLabel i k z • _ = (P.transitionLabel j k w * P.transitionLabel i j y) • _
    dsimp only [A, ChartFamily.representedAtlas] at hfl hfr hsl hsr ⊢
    rw [mul_smul, P.transitionLabel_action i j y, ← hfl,
      P.transitionLabel_action i k z, ← hsl, P.transitionLabel_action j k w, hfr, hsr]

/-- Effective descent of the derived ordinary datum. The comparison with the
ordinary total-space realization is a separate theorem obligation. -/
def descendedObject := P.ordinaryDatum.interpreted P.smooth_action
end SquareKit.SmoothPrincipalBundle.Bundle

namespace SquareKit.SmoothCech
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothManifoldAction ManifoldRealization
open scoped Manifold ContDiff
variable {d n : ℕ} {G M N : Type} [Group G] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
  [TopologicalSpace N] [ChartedSpace (Space n) N]
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))
variable (A : ChartFamily n N)
  (P Q : SheafActionQuotient.Object (representation smoothAction).action A.realization)

abbrev commonSectionAtlas := A.commonRepresented
  (ChartFamily.TorsorAtlas.charts A P.torsor) (ChartFamily.TorsorAtlas.charts A Q.torsor)

def commonTrivializedLeft : TrivializedOn (commonSectionAtlas smoothAction A P Q) smoothAction P :=
  (trivializedOnManifold smoothAction A P).restrict
    (A.commonRepresentedLeft (ChartFamily.TorsorAtlas.charts A P.torsor)
      (ChartFamily.TorsorAtlas.charts A Q.torsor))

def commonTrivializedRight : TrivializedOn (commonSectionAtlas smoothAction A P Q) smoothAction Q :=
  (trivializedOnManifold smoothAction A Q).restrict
    (A.commonRepresentedRight (ChartFamily.TorsorAtlas.charts A P.torsor)
      (ChartFamily.TorsorAtlas.charts A Q.torsor))

/-- Complete arrows, with both local section atlases and their common refinement
constructed from the two objects. No compatibility datum is an input. -/
def derivedArrowEquiv :
    Hom (commonTrivializedLeft smoothAction A P Q).extractedDatum
      (commonTrivializedRight smoothAction A P Q).extractedDatum ≃ SheafActionQuotient.Arrow P Q :=
  (commonTrivializedLeft smoothAction A P Q).arrowEquiv (commonTrivializedRight smoothAction A P Q)

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem derivedArrow_roundtrip (f : SheafActionQuotient.Arrow P Q) :
    derivedArrowEquiv smoothAction A P Q ((derivedArrowEquiv smoothAction A P Q).symm f) = f :=
  (derivedArrowEquiv smoothAction A P Q).apply_symm_apply f

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem derivedExternalArrow_roundtrip
    (f : Hom (commonTrivializedLeft smoothAction A P Q).extractedDatum
      (commonTrivializedRight smoothAction A P Q).extractedDatum) :
    (derivedArrowEquiv smoothAction A P Q).symm (derivedArrowEquiv smoothAction A P Q f) = f :=
  (derivedArrowEquiv smoothAction A P Q).symm_apply_apply f
end SquareKit.SmoothCech

namespace SquareKit.SmoothCech
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothManifoldAction ManifoldRealization
open scoped Manifold ContDiff
variable {d n m : ℕ} {G M N L : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
  [TopologicalSpace N] [ChartedSpace (Space n) N]
  [TopologicalSpace L] [ChartedSpace (Space m) L]
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))
variable (A : ChartFamily n N) (B : ChartFamily m L)
  (f : N → L) (hf : ContMDiff (modelWithCorners n) (modelWithCorners m) ∞ f)
  (p : Datum (d := d) (G := G) (M := M) B.representedAtlas)

/-- Base change through the represented atlas of actual chart inverse images. -/
def derivedBaseChange : SheafActionQuotient.Arrow
    (SheafActionQuotient.reindex (p.interpreted smoothAction) (A.interpret B f hf))
    ((p.restrict (A.inverseTarget B f hf)).interpreted smoothAction) :=
  p.restrictComparison (A.inverseTarget B f hf) smoothAction

theorem derivedBaseChange_naturality
    {q : Datum (d := d) (G := G) (M := M) B.representedAtlas} (h : Hom p q) :
    ((h.interpreted smoothAction).reindex (A.interpret B f hf)).comp
      (derivedBaseChange smoothAction A B f hf q) =
    (derivedBaseChange smoothAction A B f hf p).comp
      ((h.restrict (A.inverseTarget B f hf)).interpreted smoothAction) :=
  h.restrictComparison_naturality (A.inverseTarget B f hf) smoothAction
end SquareKit.SmoothCech

namespace SquareKit.SmoothCech.Datum
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothRepresentedCover
open SmoothManifoldAction ManifoldRealization SheafActionQuotient
open scoped Manifold ContDiff
variable {X : Sheaf topology Type} {I : Type} {A : Atlas X I}
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
variable (p : Datum (d := d) (G := G) (M := M) A)
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))

def displayChart (i : I) : embedding.obj (A.domain i) ⟶ SplitSheaf.extension (SplitSheaf.ofDisplay A.cover) :=
  A.inclusion i ≫ (SplitSheaf.displayIso A.cover).inv
theorem displayChart_projection (i : I) :
    displayChart (A := A) i ≫ SplitSheaf.p (SplitSheaf.ofDisplay A.cover) = A.chart i := by
  rw [displayChart, Category.assoc, ← SplitSheaf.displayIso_projection]
  simp only [Iso.inv_hom_id_assoc, A.inclusion_cover]
theorem displayChart_localMap (i : I) :
    displayChart (A := A) i ≫ p.splitLocalMap = hat (p.localMap i).val (p.localMap i).property := by
  simp only [displayChart, splitLocalMap, Category.assoc, Iso.inv_hom_id_assoc, localMapSheaf_fac]

/-- The selected descent comparison supplies local arrows on the actual charts. -/
def interpretedLocalArrow (i : I) : Arrow
    (chart (representation smoothAction).action (hat (p.localMap i).val (p.localMap i).property))
    (reindex (p.interpreted smoothAction) (A.chart i)) := by
  have e := ((p.cech smoothAction).toDescent.comparison).inverse.reindex (displayChart (A := A) i)
  change Arrow (chart (representation smoothAction).action (displayChart (A := A) i ≫ p.splitLocalMap))
    (reindex (p.interpreted smoothAction)
      (displayChart (A := A) i ≫ SplitSheaf.p (SplitSheaf.ofDisplay A.cover))) at e
  rw [displayChart_projection (A := A), p.displayChart_localMap] at e
  exact e

def interpretedTrivialization : TrivializedOn A smoothAction (p.interpreted smoothAction) where
  trivialization i := (p.interpretedLocalArrow smoothAction i).torsorArrow
end SquareKit.SmoothCech.Datum

namespace SquareKit.SmoothCech.Datum
open CategoryTheory Opposite EuclideanOpen SmoothOpenSite SmoothRepresentedCover
open SmoothManifoldAction ManifoldRealization SheafActionQuotient
open scoped Manifold ContDiff
variable {X : Sheaf topology Type} {I : Type} {A : Atlas X I}
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
variable (p : Datum (d := d) (G := G) (M := M) A)
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))

def interpretedLift (i : I) (g : embedding.obj (A.domain i) ⟶ locallyConstantGroupSheaf G) :
    embedding.obj (A.domain i) ⟶ SplitSheaf.extension (p.interpreted smoothAction).torsor.family :=
  SplitSheaf.pair _ (A.chart i) (SheafTorsor.sectionOfArrow
    ((SheafTorsor.regularArrow g).comp (p.interpretedLocalArrow smoothAction i).torsorArrow))

theorem interpretedLift_projection (i : I)
    (g : embedding.obj (A.domain i) ⟶ locallyConstantGroupSheaf G) :
    p.interpretedLift smoothAction i g ≫ SplitSheaf.p (p.interpreted smoothAction).torsor.family =
      A.chart i := SplitSheaf.pair_p _ _ _

theorem interpretedLift_value (i : I)
    (g : embedding.obj (A.domain i) ⟶ locallyConstantGroupSheaf G) :
    p.interpretedLift smoothAction i g ≫ (p.interpreted smoothAction).totalMap =
      (representation smoothAction).action.onMap g (hat (p.localMap i).val (p.localMap i).property) := by
  ext U x
  change (p.interpreted smoothAction).value _
    ((p.interpretedLocalArrow smoothAction i).torsorArrow.iso.hom.app
      ((embedding.obj (A.domain i)).obj.elementsMk U x)
      ((1 : (locallyConstantGroup G).obj.obj U) *
        (show (locallyConstantGroup G).obj.obj U from g.hom.app U x))) = _
  rw [one_mul]
  exact (p.interpretedLocalArrow smoothAction i).preserves _ _
end SquareKit.SmoothCech.Datum

namespace SquareKit.SmoothOpenSite
open CategoryTheory Opposite SmoothAlgebra SmoothPresentationSite

/-- A stage without real points has the empty covering sieve. This statement
is about covering existence, not detection of arbitrary infinitesimal maps. -/
theorem empty_cover_of_no_real_points (U : Site)
    (h : ¬ Nonempty (op (free 0) ⟶ U)) : (⊥ : Sieve U) ∈ topology U := by
  have hc : OpenCover.Covers (fun i : Fin 0 => (0 : Carrier U.unop)) := by
    intro p
    exact (h ⟨(show U.unop ⟶ free 0 from Hom.comp DualExtension.realHom p).op⟩).elim
  have hs := principal_covering U.unop (fun i : Fin 0 => (0 : Carrier U.unop)) hc
  have he : principalPresieve U.unop (fun i : Fin 0 => (0 : Carrier U.unop)) = ⊥ := by
    funext V
    funext f
    apply propext
    constructor
    · rintro ⟨i⟩
      exact Fin.elim0 i
    · simp
  simpa only [principalSieve, he, Sieve.generate_bot] using hs

/-- Constants can be distinguished at every nonempty real locus; empty stages
have unique sheaf sections. No such claim is made for general smooth sections. -/
theorem constantLabel_eq_of_real_points {G : Type} [Group G] (U : Site) (g h : G)
    (he : ∀ _x : op (free 0) ⟶ U, g = h) :
    (constantLabel G).app (op U) g = (constantLabel G).app (op U) h := by
  by_cases hx : Nonempty (op (free 0) ⟶ U)
  · obtain ⟨x⟩ := hx
    rw [he x]
  · apply (((isSheaf_iff_isSheaf_of_type _ _).mp (locallyConstantGroupSheaf G).property)
      (⊥ : Sieve U) (empty_cover_of_no_real_points U hx)).isSeparatedFor.ext
    intro V f hf
    cases hf
end SquareKit.SmoothOpenSite

namespace SquareKit.SmoothManifoldAction
open CategoryTheory Opposite SmoothOpenSite ManifoldRealization
open scoped Manifold ContDiff
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))

/-- Ordinary freeness lifts to every stage. Only locally constant group labels
are detected at real points; manifold-valued infinitesimal sections are retained. -/
theorem act_free (hf : ∀ (g : G) (x : M), g • x = x → g = 1)
    (U : SmoothPresentationSite.Siteᵒᵖ) (g : (locallyConstantGroup G).obj.obj U)
    (m : (object d M).obj.obj U) (he : (representation smoothAction).act U g m = m) : g = 1 := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp (locallyConstantGroupSheaf G).property)
    (Presheaf.imageSieve (constantLabel G) g)
    (Presheaf.imageSieve_mem topology (constantLabel G) g)).isSeparatedFor.ext
  intro V k hk
  obtain ⟨c,hc⟩ := hk
  change G at c
  change (locallyConstantGroup G).obj.map k.op g = (locallyConstantGroup G).obj.map k.op 1
  rw [((locallyConstantGroup G).obj.map k.op).hom.map_one, ← hc,
    ← ((constantLabel G).app (op V)).hom.map_one]
  apply constantLabel_eq_of_real_points V c 1
  intro x
  have hv := ((representation smoothAction).act_natural k.op g m).symm.trans
    (congrArg (fun z => (object d M).obj.map k.op z) he)
  rw [← hc] at hv
  have hx := ((representation smoothAction).act_natural x.op
    ((constantLabel G).app (op V) c) ((object d M).obj.map k.op m)).symm.trans
    (congrArg (fun z => (object d M).obj.map x.op z) hv)
  rw [← NatTrans.naturality_apply (constantLabel G) x.op c,
    (representation smoothAction).act_constant] at hx
  apply hf c (pointEquiv ((object d M).obj.map x.op ((object d M).obj.map k.op m)))
  exact (map_eval (fun z : M => c • z) (smoothAction c) _).symm.trans (congrArg pointEquiv hx)
end SquareKit.SmoothManifoldAction

namespace SquareKit.SmoothConstantAction.Representation
open CategoryTheory Opposite SmoothOpenSite
variable {G : Type} [Group G] {M N : Sheaf topology Type}
variable (r : SmoothConstantAction.Representation G M) (f : M ⟶ N)

/-- Invariance for ordinary constant labels extends to the whole group sheaf. -/
theorem invariant (hf : ∀ g, r.map g ≫ f = f) (U : SmoothPresentationSite.Siteᵒᵖ)
    (g : (locallyConstantGroup G).obj.obj U) (m : M.obj.obj U) :
    f.hom.app U (r.act U g m) = f.hom.app U m := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp N.property)
    (Presheaf.imageSieve (constantLabel G) g)
    (Presheaf.imageSieve_mem topology (constantLabel G) g)).isSeparatedFor.ext
  intro V k hk
  obtain ⟨c,hc⟩ := hk
  rw [← NatTrans.naturality_apply f.hom, r.act_natural,
    ← NatTrans.naturality_apply f.hom, ← hc, r.act_constant]
  exact congrArg (fun h : M ⟶ N => h.hom.app (op V) (M.obj.map k.op m)) (hf c)
end SquareKit.SmoothConstantAction.Representation

namespace SquareKit.SmoothCech.Datum
open CategoryTheory Opposite EuclideanOpen SmoothOpenSite SmoothRepresentedCover
open SmoothManifoldAction ManifoldRealization SheafActionQuotient
open scoped Manifold ContDiff
variable {X : Sheaf topology Type} {I : Type} {A : Atlas X I}
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
variable (p : Datum (d := d) (G := G) (M := M) A)
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))

/-- Descent retains an invariant ordinary projection as an equality of sheaf maps. -/
theorem interpreted_projection (q : object d M ⟶ X)
    (hq : ∀ g, (representation smoothAction).map g ≫ q = q)
    (hm : p.localMapSheaf ≫ q = A.cover) :
    (p.interpreted smoothAction).totalMap ≫ q = SplitSheaf.p (p.interpreted smoothAction).torsor.family := by
  have hs : p.splitLocalMap ≫ q = SplitSheaf.p (SplitSheaf.ofDisplay A.cover) := by
    rw [splitLocalMap, Category.assoc, hm]
    exact SplitSheaf.displayIso_projection A.cover
  let D := (p.cech smoothAction).toDescent
  apply (cancel_epi D.cover).mp
  ext U z
  rcases z with ⟨⟨x,b⟩,t⟩
  change q.hom.app U (D.value (X.obj.elementsMk U x) t) = x
  rw [D.value_at_lift (X.obj.elementsMk U x) b]
  change q.hom.app U ((representation smoothAction).act U _
    (p.splitLocalMap.hom.app U ⟨x,b⟩)) = x
  rw [(representation smoothAction).invariant q hq]
  exact congrArg (fun h => h.hom.app U ⟨x,b⟩) hs
end SquareKit.SmoothCech.Datum

namespace SquareKit.SmoothPrincipalBundle.Bundle
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothManifoldAction ManifoldRealization
open scoped Manifold ContDiff
variable {n : ℕ} {G B E : Type} [Group G] [MulAction G E]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E]
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))

def projectionMap : object n E ⟶ P.baseCharts.realization :=
  ManifoldRealization.map P.projection P.smooth_projection ≫ (atlasIso P.baseCharts).hom

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem projectionMap_invariant (g : G) :
    (representation P.smooth_action).map g ≫ P.projectionMap = P.projectionMap := by
  change ManifoldRealization.map (fun e : E => g • e) (P.smooth_action g) ≫
    (ManifoldRealization.map P.projection P.smooth_projection ≫ (atlasIso P.baseCharts).hom) = _
  rw [← Category.assoc, ← ManifoldRealization.map_comp]
  have he : P.projection ∘ (fun e : E => g • e) = P.projection := funext (P.invariant g)
  simp only [he]
  rfl

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem ordinarySheet_projectionMap (b : B) :
    hat (P.ordinarySheet b 1) (P.ordinarySheet_smooth b 1) ≫ P.projectionMap = P.baseCharts.charts.chart b := by
  have he : P.projection ∘ P.ordinarySheet b 1 =
      (fun x : ordinaryOpen (chartDomain (P.baseChart b)) => chartPoint (P.baseChart b) x) :=
    funext (P.ordinarySheet_projection b 1)
  change ((principalIso _).inv ≫ ManifoldRealization.map _ _) ≫
    (ManifoldRealization.map _ _ ≫ (atlasIso P.baseCharts).hom) = _
  rw [Category.assoc, ← Category.assoc (ManifoldRealization.map _ _), ← ManifoldRealization.map_comp]
  simp only [he]
  rw [← Category.assoc]
  exact (congrArg (fun h => h ≫ (atlasIso P.baseCharts).hom)
    (P.baseCharts.chart_hat b)).trans (by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

theorem descended_projection :
    P.descendedObject.totalMap ≫ P.projectionMap = SplitSheaf.p P.descendedObject.torsor.family := by
  apply P.ordinaryDatum.interpreted_projection P.smooth_action P.projectionMap P.projectionMap_invariant
  apply CategoryTheory.Limits.colimit.hom_ext
  intro ⟨b⟩
  change P.baseCharts.representedAtlas.inclusion b ≫ _ = _
  rw [← Category.assoc, SmoothCech.Datum.localMapSheaf_fac]
  exact (P.ordinarySheet_projectionMap b).trans (P.baseCharts.representedAtlas.inclusion_cover b).symm
end SquareKit.SmoothPrincipalBundle.Bundle

namespace SquareKit.SmoothCech
open CategoryTheory Opposite SmoothOpenSite SmoothManifoldAction ManifoldRealization SheafActionQuotient
open scoped Manifold ContDiff
variable {X : Sheaf topology Type} {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))

/-- A projection-preserving equivariant map into a free ordinary action is
injective at every stage, including stages with no real points. -/
theorem totalMap_injective_of_free (P : Object (representation smoothAction).action X)
    (q : object d M ⟶ X) (hq : P.totalMap ≫ q = SplitSheaf.p P.torsor.family)
    (hf : ∀ (g : G) (x : M), g • x = x → g = 1)
    (U : SmoothPresentationSite.Siteᵒᵖ) : Function.Injective (P.totalMap.hom.app U) := by
  rintro ⟨x,p⟩ ⟨y,t⟩ he
  have hb : x = y := by
    have hp := congrArg (fun f => f.hom.app U ⟨x,p⟩) hq
    have ht := congrArg (fun f => f.hom.app U ⟨y,t⟩) hq
    exact hp.symm.trans ((congrArg (q.hom.app U) he).trans ht)
  subst y
  obtain ⟨g,hg,_⟩ := P.torsor.principal (X.obj.elementsMk U x) p t
  have hfree : (representation smoothAction).act U g (P.value (X.obj.elementsMk U x) p) =
      P.value (X.obj.elementsMk U x) p := by
    exact (P.equivariant (X.obj.elementsMk U x) g p).symm.trans
      ((congrArg (P.value (X.obj.elementsMk U x)) hg).trans he.symm)
  have hgone := SmoothManifoldAction.act_free smoothAction hf U g _ hfree
  rw [hgone, P.torsor.one_act] at hg
  exact congrArg (Sigma.mk x) hg

theorem totalMap_mono_of_free (P : Object (representation smoothAction).action X)
   (q : object d M ⟶ X) (hq : P.totalMap ≫ q = SplitSheaf.p P.torsor.family)
   (hf : ∀ (g : G) (x : M), g • x = x → g = 1) : Mono P.totalMap where
 right_cancellation {Z} f g he := by
   ext U z
   exact totalMap_injective_of_free smoothAction P q hq hf U
     (congrArg (fun h => h.hom.app U z) he)
end SquareKit.SmoothCech

namespace SquareKit.SmoothPrincipalBundle.Bundle
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothManifoldAction ManifoldRealization
open scoped Manifold ContDiff
variable {n : ℕ} {G B E : Type} [Group G] [MulAction G E]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E]
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))

theorem interpretedLift_sheet (b : B) (g : G) :
    P.ordinaryDatum.interpretedLift P.smooth_action b (constantSection _ g) ≫ P.descendedObject.totalMap =
      hat (P.ordinarySheet b g) (P.ordinarySheet_smooth b g) := by
  dsimp only [descendedObject]
  rw [SmoothCech.Datum.interpretedLift_value]
  apply (onMap_iff P.smooth_action _ _ (P.ordinarySheet b g) (P.ordinarySheet b 1) _ _).mpr
  intro x
  have hl : ordinaryHomLabelEquiv G _ (constantSection _ g) x = g := ordinaryLabel_constant G _ g x
  apply (congrArg (fun h : G => h • P.ordinarySheet b 1 x) hl).trans
  exact ((P.localAt b).equivariant g 1 (chartPoint (P.baseChart b) x)
    (P.baseChart_source b _ (chartPoint_source _ _))).symm.trans
      (congrArg (fun h => ((P.localAt b).sheet h).symm (chartPoint (P.baseChart b) x)) (mul_one g))

def totalChartLift (bg : B × G) : embedding.obj (P.totalCharts.charts.domain bg) ⟶
    SplitSheaf.extension P.descendedObject.torsor.family :=
  embedding.map (P.sheetDomainIso bg.1 bg.2).hom ≫
    P.ordinaryDatum.interpretedLift P.smooth_action bg.1 (constantSection _ bg.2)

theorem totalChartLift_value (bg : B × G) :
    P.totalChartLift bg ≫ P.descendedObject.totalMap =
      P.totalCharts.charts.chart bg ≫ (atlasIso P.totalCharts).inv := by
  rw [totalChartLift, Category.assoc, P.interpretedLift_sheet]
  rw [External.hat_restrict (⟨P.ordinarySheet bg.1 bg.2, P.ordinarySheet_smooth bg.1 bg.2⟩ :
    External.SmoothMap (chartDomain (P.baseChart bg.1)) n E)]
  exact P.totalCharts.chart_hat bg
end SquareKit.SmoothPrincipalBundle.Bundle

namespace SquareKit.SmoothPrincipalBundle.Bundle
open CategoryTheory Opposite EuclideanOpen SmoothOpenSite SmoothManifoldAction ManifoldRealization
open scoped Manifold ContDiff
variable {n : ℕ} {G B E : Type} [Group G] [MulAction G E]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E]
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))

instance totalMap_locallySurjective : Presheaf.IsLocallySurjective topology P.descendedObject.totalMap.hom where
  imageSieve_mem {U} x := by
    let A := P.totalCharts.representedAtlas.transport (atlasIso P.totalCharts).symm
    apply topology.superset_covering _ (A.covering U x)
    intro V r hr
    obtain ⟨bg,z,hz⟩ := hr
    refine ⟨(P.totalChartLift bg).hom.app (op V) z, ?_⟩
    exact (congrArg (fun h => h.hom.app (op V) z) (P.totalChartLift_value bg)).trans hz

instance totalMap_mono : Mono P.descendedObject.totalMap :=
  SmoothCech.totalMap_mono_of_free P.smooth_action P.descendedObject P.projectionMap
    P.descended_projection (fun g e h => P.action_free g 1 e (h.trans (one_smul G e).symm))

/-- The ordinary total space is recovered from the derived bundle cocycle.
The inverse is supplied by the proved mono and local-surjectivity results. -/
def totalSpaceIso : SplitSheaf.extension P.descendedObject.torsor.family ≅ object n E := by
  letI : IsIso P.descendedObject.totalMap := isIso_of_mono_of_epi _
  exact asIso P.descendedObject.totalMap

theorem totalSpaceIso_projection :
    P.totalSpaceIso.hom ≫ ManifoldRealization.map P.projection P.smooth_projection =
      SplitSheaf.p P.descendedObject.torsor.family ≫ (atlasIso P.baseCharts).inv := by
  apply (cancel_mono (atlasIso P.baseCharts).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact P.descended_projection
end SquareKit.SmoothPrincipalBundle.Bundle

namespace SquareKit.SmoothConstantAction.Representation
open CategoryTheory Opposite SmoothOpenSite
variable {G : Type} [Group G] {M N : Sheaf topology Type}
variable (r : SmoothConstantAction.Representation G M) (s : SmoothConstantAction.Representation G N)
  (f : M ⟶ N)

/-- Constant-label equivariance extends to all locally constant labels. -/
theorem intertwines (hf : ∀ g, r.map g ≫ f = f ≫ s.map g) (U : SmoothPresentationSite.Siteᵒᵖ)
    (g : (locallyConstantGroup G).obj.obj U) (m : M.obj.obj U) :
    f.hom.app U (r.act U g m) = s.act U g (f.hom.app U m) := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp N.property)
    (Presheaf.imageSieve (constantLabel G) g)
    (Presheaf.imageSieve_mem topology (constantLabel G) g)).isSeparatedFor.ext
  intro V k hk
  obtain ⟨c,hc⟩ := hk
  rw [← NatTrans.naturality_apply f.hom, r.act_natural, s.act_natural,
    ← NatTrans.naturality_apply f.hom, ← hc, r.act_constant, s.act_constant]
  exact congrArg (fun h : M ⟶ N => h.hom.app (op V) (M.obj.map k.op m)) (hf c)
end SquareKit.SmoothConstantAction.Representation

namespace SquareKit.SmoothPrincipalBundle.Bundle
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothManifoldAction ManifoldRealization SheafActionQuotient
open scoped Manifold ContDiff
variable {n d : ℕ} {G B E M : Type} [Group G] [MulAction G E] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace M]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E] [ChartedSpace (Space d) M]
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E] [IsManifold (modelWithCorners d) ∞ M]
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))
variable (F : E → M) (hF : ContMDiff (modelWithCorners n) (modelWithCorners d) ∞ F)
  (hG : ∀ (g : G) (e : E), F (g • e) = g • F e)

omit [TopologicalSpace G] [DiscreteTopology G] [IsManifold (modelWithCorners n) ∞ B] in
include hG in
theorem target_intertwines (g : G) :
    (representation P.smooth_action).map g ≫ ManifoldRealization.map F hF =
      ManifoldRealization.map F hF ≫ (representation smoothAction).map g := by
  change ManifoldRealization.map (fun e : E => g • e) _ ≫ ManifoldRealization.map F _ =
    ManifoldRealization.map F _ ≫ ManifoldRealization.map (fun m : M => g • m) _
  rw [← ManifoldRealization.map_comp, ← ManifoldRealization.map_comp]
  congr 1
  exact funext (hG g)

/-- The ordinary bundle and an independent smooth equivariant target map
produce the full quotient object. No sheaf torsor or comparison is an input. -/
def quotientObject : Object (representation smoothAction).action P.baseCharts.realization where
  torsor := P.descendedObject.torsor
  value x t := (ManifoldRealization.map F hF).hom.app x.obj (P.descendedObject.value x t)
  natural k t := by
    rw [← NatTrans.naturality_apply (ManifoldRealization.map F hF).hom, P.descendedObject.natural]
  equivariant x g t := by
    rw [P.descendedObject.equivariant]
    exact (representation P.smooth_action).intertwines (representation smoothAction)
      (ManifoldRealization.map F hF) (P.target_intertwines smoothAction F hF hG) x.obj g _

theorem quotientObject_totalMap :
    (P.quotientObject smoothAction F hF hG).totalMap = P.totalSpaceIso.hom ≫ ManifoldRealization.map F hF := rfl

def quotientTrivialization : SmoothCech.TrivializedOn P.baseCharts.representedAtlas smoothAction
    (P.quotientObject smoothAction F hF hG) where
  trivialization := (P.ordinaryDatum.interpretedTrivialization P.smooth_action).trivialization

def quotientRecovery : Arrow
    ((P.quotientTrivialization smoothAction F hF hG).extractedDatum.interpreted smoothAction)
    (P.quotientObject smoothAction F hF hG) :=
  (P.quotientTrivialization smoothAction F hF hG).extractedRecovery
end SquareKit.SmoothPrincipalBundle.Bundle

namespace SquareKit.SmoothCech
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothManifoldAction ManifoldRealization
open scoped Manifold ContDiff
variable {d n : ℕ} {G M N : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
  [TopologicalSpace N] [ChartedSpace (Space n) N]
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))
variable (A : ChartFamily n N)
  (P Q : SheafActionQuotient.Object (representation smoothAction).action A.realization)

theorem common_identity :
    (commonTrivializedLeft smoothAction A P Q).extractArrow
      (commonTrivializedLeft smoothAction A P Q) (SheafActionQuotient.Arrow.ident P) =
      Hom.ident (commonTrivializedLeft smoothAction A P Q).extractedDatum :=
  (commonTrivializedLeft smoothAction A P Q).extractArrow_ident

theorem common_composition (f : SheafActionQuotient.Arrow P Q) (g : SheafActionQuotient.Arrow Q P) :
    (commonTrivializedLeft smoothAction A P Q).extractArrow (commonTrivializedLeft smoothAction A P Q)
      (f.comp g) =
    ((commonTrivializedLeft smoothAction A P Q).extractArrow (commonTrivializedRight smoothAction A P Q) f).comp
      ((commonTrivializedRight smoothAction A P Q).extractArrow (commonTrivializedLeft smoothAction A P Q) g) :=
  (commonTrivializedLeft smoothAction A P Q).extractArrow_comp
    (commonTrivializedRight smoothAction A P Q) (commonTrivializedLeft smoothAction A P Q) f g

theorem common_inverse (f : SheafActionQuotient.Arrow P Q) :
    (commonTrivializedRight smoothAction A P Q).extractArrow (commonTrivializedLeft smoothAction A P Q) f.inverse =
      ((commonTrivializedLeft smoothAction A P Q).extractArrow (commonTrivializedRight smoothAction A P Q) f).inverse :=
  (commonTrivializedLeft smoothAction A P Q).extractArrow_inverse (commonTrivializedRight smoothAction A P Q) f

theorem common_recovery_naturality (f : SheafActionQuotient.Arrow P Q) :
    (interpretedHomEquiv smoothAction _ _
      ((commonTrivializedLeft smoothAction A P Q).extractArrow (commonTrivializedRight smoothAction A P Q) f)).comp
        (commonTrivializedRight smoothAction A P Q).extractedRecovery =
      (commonTrivializedLeft smoothAction A P Q).extractedRecovery.comp f :=
  (commonTrivializedLeft smoothAction A P Q).recovery_naturality (commonTrivializedRight smoothAction A P Q) f

/-- The two projections of the derived self-intersection atlas give an overlap
gauge from the identity of the original object. -/
def derivedGauge := (commonTrivializedLeft smoothAction A P P).changeOfTrivialization smoothAction
  (commonTrivializedRight smoothAction A P P)

theorem derivedGauge_recovery :
    (interpretedHomEquiv smoothAction _ _ (derivedGauge smoothAction A P)).comp
      (commonTrivializedRight smoothAction A P P).extractedRecovery =
      (commonTrivializedLeft smoothAction A P P).extractedRecovery :=
  (commonTrivializedLeft smoothAction A P P).change_recovery smoothAction (commonTrivializedRight smoothAction A P P)
end SquareKit.SmoothCech

namespace SquareKit.SmoothCech
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothManifoldAction ManifoldRealization
open scoped Manifold ContDiff
variable {d n : ℕ} {G M N J : Type} [Group G] [MulAction G M] [Fintype J]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
  [TopologicalSpace N] [ChartedSpace (Space n) N]
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))
variable (A : ChartFamily n N)
  (P : J → SheafActionQuotient.Object (representation smoothAction).action A.realization)

def jointTrivialized (j : J) :
    TrivializedOn (ChartFamily.JointTorsorAtlas.atlas A (fun j => (P j).torsor)) smoothAction (P j) where
  trivialization := ChartFamily.JointTorsorAtlas.trivialization A (fun j => (P j).torsor) j

def jointArrowEquiv (i j : J) :=
  (jointTrivialized smoothAction A P i).arrowEquiv (jointTrivialized smoothAction A P j)

theorem joint_composition (i j k : J)
    (f : Hom (jointTrivialized smoothAction A P i).extractedDatum (jointTrivialized smoothAction A P j).extractedDatum)
    (g : Hom (jointTrivialized smoothAction A P j).extractedDatum (jointTrivialized smoothAction A P k).extractedDatum) :
    jointArrowEquiv smoothAction A P i k (f.comp g) =
      (jointArrowEquiv smoothAction A P i j f).comp (jointArrowEquiv smoothAction A P j k g) :=
  (jointTrivialized smoothAction A P i).arrowEquiv_comp
    (jointTrivialized smoothAction A P j) (jointTrivialized smoothAction A P k) f g
end SquareKit.SmoothCech

namespace SquareKit.SmoothCech
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothManifoldAction ManifoldRealization
open scoped Manifold ContDiff
variable {d n : ℕ} {G M N : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
  [TopologicalSpace N] [ChartedSpace (Space n) N]
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))
variable (A : ChartFamily n N) (p : Datum (d := d) (G := G) (M := M) A.representedAtlas)

/-- Two chart choices on the actual intersection cover give isomorphic selected
descents, without identifying the selected objects by definitional equality. -/
def chartChoiceComparison := p.commonComparison (A.inverseSource A id contMDiff_id) A.selfCommonRight smoothAction

theorem chartChoice_naturality {q : Datum (d := d) (G := G) (M := M) A.representedAtlas} (h : Hom p q) :
    ((h.restrict (A.inverseSource A id contMDiff_id)).interpreted smoothAction).comp
      (chartChoiceComparison smoothAction A q) =
    (chartChoiceComparison smoothAction A p).comp ((h.restrict A.selfCommonRight).interpreted smoothAction) :=
  h.commonComparison_naturality (A.inverseSource A id contMDiff_id) A.selfCommonRight smoothAction
end SquareKit.SmoothCech

namespace SquareKit.SmoothPrincipalBundle.Bundle
open CategoryTheory SmoothOpenSite SmoothManifoldAction ManifoldRealization
open scoped Manifold ContDiff
variable {n : ℕ} {G B E : Type} [Group G] [MulAction G E]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E]
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))

/-- The comparison retains the full group-sheaf action, not only constant labels. -/
theorem totalSpaceIso_equivariant (x : P.baseCharts.realization.obj.Elements)
    (g : (locallyConstantGroup G).obj.obj x.obj) (t : P.descendedObject.torsor.family.family.obj x) :
    P.totalSpaceIso.hom.hom.app x.obj ⟨x.val,P.descendedObject.torsor.act x g t⟩ =
      (representation P.smooth_action).act x.obj g (P.totalSpaceIso.hom.hom.app x.obj ⟨x.val,t⟩) :=
  P.descendedObject.equivariant x g t
end SquareKit.SmoothPrincipalBundle.Bundle

namespace SquareKit.SmoothCech
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothManifoldAction ManifoldRealization
open scoped Manifold ContDiff
variable {d n : ℕ} {G M N : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
  [TopologicalSpace N] [ChartedSpace (Space n) N]
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))
variable (A : ChartFamily n N)
  (P : SheafActionQuotient.Object (representation smoothAction).action A.realization)

/-- Independent section choices on the already constructed section cover.
These are comparison parameters; admission supplies `selectedSections` without them. -/
abbrev LocalSections := ∀ i, SplitSheaf.Tm
  (SheafTorsor.reindex P.torsor ((ChartFamily.TorsorAtlas.atlas A P.torsor).chart i)).family

def selectedSections : LocalSections smoothAction A P := ChartFamily.TorsorAtlas.localSection A P.torsor

def sectionsTrivialized (s : LocalSections smoothAction A P) :
    TrivializedOn (ChartFamily.TorsorAtlas.atlas A P.torsor) smoothAction P where
  trivialization i := SheafTorsor.ofSection _ (s i)

def sectionsCommonLeft (s : LocalSections smoothAction A P) :
    TrivializedOn (commonSectionAtlas smoothAction A P P) smoothAction P :=
  (sectionsTrivialized smoothAction A P s).restrict
    (A.commonRepresentedLeft (ChartFamily.TorsorAtlas.charts A P.torsor)
      (ChartFamily.TorsorAtlas.charts A P.torsor))

def sectionsCommonRight (s : LocalSections smoothAction A P) :
    TrivializedOn (commonSectionAtlas smoothAction A P P) smoothAction P :=
  (sectionsTrivialized smoothAction A P s).restrict
    (A.commonRepresentedRight (ChartFamily.TorsorAtlas.charts A P.torsor)
      (ChartFamily.TorsorAtlas.charts A P.torsor))

/-- The comparison is extracted, not supplied, for arbitrary independent choices. -/
def sectionsGauge (s t : LocalSections smoothAction A P) :=
  (sectionsCommonLeft smoothAction A P s).changeOfTrivialization smoothAction
    (sectionsCommonRight smoothAction A P t)

theorem sectionsGauge_datum (s t : LocalSections smoothAction A P) :
    (sectionsCommonLeft smoothAction A P s).extractedDatum.gauge
      (sectionsCommonRight smoothAction A P t).extractedDatum.localMap
      (sectionsGauge smoothAction A P s t).labels =
    (sectionsCommonRight smoothAction A P t).extractedDatum :=
  (sectionsCommonLeft smoothAction A P s).changed_datum smoothAction
    (sectionsCommonRight smoothAction A P t)

theorem sectionsGauge_recovery (s t : LocalSections smoothAction A P) :
    (interpretedHomEquiv smoothAction _ _ (sectionsGauge smoothAction A P s t)).comp
      (sectionsCommonRight smoothAction A P t).extractedRecovery =
    (sectionsCommonLeft smoothAction A P s).extractedRecovery :=
  (sectionsCommonLeft smoothAction A P s).change_recovery smoothAction
    (sectionsCommonRight smoothAction A P t)
end SquareKit.SmoothCech
