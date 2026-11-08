import SquareKit.SheafActionQuotientLabels
import SquareKit.SmoothConstantComparison
import SquareKit.SmoothQuarterTurnQuotient

/-! Ordinary quotient chart arrows with locally constant labels. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory Opposite

namespace SquareKit.EuclideanOpen
open SmoothOpenSite SmoothPresentationSite SmoothAlgebra

/-- Ordinary representable targets are point detected by the proved full faithfulness. -/
theorem ordinary_hom_ext {U V : Domain} (f g : embedding.obj U ⟶ embedding.obj V)
    (h : ∀ x : Points U, f.hom.app (op (op (free 0))) (ordinaryPoint U x) =
      g.hom.app (op (op (free 0))) (ordinaryPoint U x)) : f = g := by
  rw [← forward_inverse f, ← forward_inverse g]
  congr 1
  apply OpenFunctions.Map.ext
  intro x
  have hf := realSectionEquiv_naturality ((homEquiv U V).symm f) (ordinaryPoint U x)
  have hg := realSectionEquiv_naturality ((homEquiv U V).symm g) (ordinaryPoint U x)
  rw [forward_inverse] at hf hg
  have hx : realSectionEquiv U (ordinaryPoint U x) = x := (realSectionEquiv U).apply_symm_apply x
  rw [hx] at hf hg
  exact hf.symm.trans ((congrArg (realSectionEquiv V) (h x)).trans hg)

end SquareKit.EuclideanOpen
namespace SquareKit.SmoothOrdinaryQuotient
open SmoothOpenSite SmoothPresentationSite EuclideanOpen SheafActionQuotient
open SmoothQuarterTurnQuotient SmoothQuarterTurnArcs Orbifolds.QuarterTurn

/-- Evaluation of the actual Yoneda/section comparison at an ordinary point. -/
theorem homLabel_point {G : Type} [Group G] (U : Domain)
    (g : embedding.obj U ⟶ locallyConstantGroupSheaf G) (x : Points U) :
    (constantLabelRealEquiv G) (ordinaryHomLabelEquiv G U g x) =
      g.hom.app (op (op (free 0))) (ordinaryPoint U x) := by
  change (constantLabelRealEquiv G) ((constantLabelRealEquiv G).symm _) = _
  rw [Equiv.apply_symm_apply]
  exact SmoothOpenSite.topology.yonedaEquiv_naturality g (ordinaryPoint U x)

/-- The equation is reflected using the ordinary target's full faithfulness. -/
theorem disk_onMap_iff (U : Domain) (g : embedding.obj U ⟶ locallyConstantGroupSheaf C4)
    (m n : U ⟶ diskDomain) :
    diskRepresentation.action.onMap g (embedding.map n) = embedding.map m ↔
      ∀ x : Points U, (show Map _ _ from diskMap (ordinaryHomLabelEquiv C4 U g x))
        ((show Map _ _ from n) x) = (show Map _ _ from m) x := by
  have eval (x : Points U) :
      realSectionEquiv diskDomain
        ((diskRepresentation.action.onMap g (embedding.map n)).hom.app (op (op (free 0))) (ordinaryPoint U x)) =
      (show Map _ _ from diskMap (ordinaryHomLabelEquiv C4 U g x)) ((show Map _ _ from n) x) := by
    change realSectionEquiv diskDomain (diskRepresentation.act _ (g.hom.app _ _) _) = _
    rw [← homLabel_point U g x]
    change realSectionEquiv diskDomain (diskRepresentation.act _ ((constantLabel C4).app _ _) _) = _
    rw [diskRepresentation.act_constant]
    change realSectionEquiv diskDomain
      (realSections.map (embedding.map (diskMap _)) (realSections.map (embedding.map n) (ordinaryPoint U x))) = _
    rw [realSectionEquiv_naturality, realSectionEquiv_naturality]
    exact congrArg (fun z => (show Map _ _ from diskMap (ordinaryHomLabelEquiv C4 U g x))
      ((show Map _ _ from n) z)) ((realSectionEquiv U).apply_symm_apply x)
  have em (x : Points U) : realSectionEquiv diskDomain
      ((embedding.map m).hom.app (op (op (free 0))) (ordinaryPoint U x)) = (show Map _ _ from m) x :=
    (realSectionEquiv_naturality m _).trans
      (congrArg (show Map _ _ from m) ((realSectionEquiv U).apply_symm_apply x))
  constructor
  · intro h x
    rw [← eval x, h]
    exact em x
  · intro h
    apply ordinary_hom_ext
    intro x
    apply (realSectionEquiv diskDomain).injective
    exact (eval x).trans ((h x).trans (em x).symm)

/-- Ordinary chart arrows retain precisely their locally constant action labels. -/
def diskChartArrowEquiv (U : Domain) (m n : U ⟶ diskDomain) :
    Arrow (chart diskRepresentation.action (embedding.map m))
      (chart diskRepresentation.action (embedding.map n)) ≃
    {k : LocallyConstant (Points U) C4 // ∀ x, (show Map _ _ from diskMap (k x))
      ((show Map _ _ from n) x) = (show Map _ _ from m) x} :=
  (chartArrowEquiv (embedding.map m) (embedding.map n)).trans {
    toFun g := ⟨ordinaryHomLabelEquiv C4 U g.val, (disk_onMap_iff U g.val m n).mp g.property⟩
    invFun k := ⟨(ordinaryHomLabelEquiv C4 U).symm k.val, (disk_onMap_iff U _ m n).mpr (by
      rw [Equiv.apply_symm_apply]; exact k.property)⟩
    left_inv g := Subtype.ext ((ordinaryHomLabelEquiv C4 U).symm_apply_apply g.val)
    right_inv k := Subtype.ext ((ordinaryHomLabelEquiv C4 U).apply_symm_apply k.val) }

/-- Generic ordinary labels expose group order independently of the C4 example. -/
def ordinaryArrowLabel {G : Type} [Group G] {M : Sheaf SmoothOpenSite.topology Type}
    {a : Action (locallyConstantGroup G) M} {U : Domain}
    {m n : embedding.obj U ⟶ M} (f : Arrow (chart a m) (chart a n)) :
    LocallyConstant (Points U) G := ordinaryHomLabelEquiv G U (arrowLabel f)

theorem ordinaryArrowLabel_comp {G : Type} [Group G] {M : Sheaf SmoothOpenSite.topology Type}
    {a : Action (locallyConstantGroup G) M} {U : Domain}
    {m n p : embedding.obj U ⟶ M}
    (f : Arrow (chart a m) (chart a n)) (g : Arrow (chart a n) (chart a p)) (x : Points U) :
    ordinaryArrowLabel (Arrow.comp f g) x = ordinaryArrowLabel f x * ordinaryArrowLabel g x := by
  apply (constantLabelRealEquiv G).injective
  change (constantLabelRealEquiv G) (ordinaryHomLabelEquiv G U (arrowLabel (Arrow.comp f g)) x) =
    (constantLabel G).app _ (ordinaryArrowLabel f x * ordinaryArrowLabel g x)
  rw [homLabel_point, ((constantLabel G).app _).hom.map_mul]
  exact (arrowLabel_comp_apply f g _ _).trans
    (congrArg₂ (fun a b : (locallyConstantGroup G).obj.obj (op (op (free 0))) => a * b)
      (homLabel_point U (arrowLabel f) x).symm (homLabel_point U (arrowLabel g) x).symm)

theorem ordinaryArrowLabel_ident {G : Type} [Group G] {M : Sheaf SmoothOpenSite.topology Type}
    (a : Action (locallyConstantGroup G) M) {U : Domain} (m : embedding.obj U ⟶ M) (x : Points U) :
    ordinaryArrowLabel (Arrow.ident (chart a m)) x = (1 : G) := by
  apply (constantLabelRealEquiv G).injective
  exact (homLabel_point U (arrowLabel (Arrow.ident (chart a m))) x).trans
    (((constantLabel G).app _).hom.map_one.symm)

theorem ordinaryArrowLabel_reindex {G : Type} [Group G] {M : Sheaf SmoothOpenSite.topology Type}
    {a : Action (locallyConstantGroup G) M} {U V : Domain}
    {m n : embedding.obj V ⟶ M} (f : Arrow (chart a m) (chart a n)) (r : U ⟶ V) (x : Points U) :
    ordinaryArrowLabel (m := embedding.map r ≫ m) (n := embedding.map r ≫ n)
      (f.reindex (embedding.map r)) x = ordinaryArrowLabel f ((show Map _ _ from r) x) := by
  change ordinaryLabel G U (SmoothOpenSite.topology.yonedaEquiv (embedding.map r ≫ arrowLabel f)) x = _
  change ordinaryLabel G U (SmoothOpenSite.topology.yonedaEquiv (SmoothOpenSite.topology.yoneda.map (toSite.map r) ≫ arrowLabel f)) x = _
  rw [← SmoothOpenSite.topology.yonedaEquiv_naturality]
  exact ordinaryLabel_natural G r _ x

theorem ordinaryArrowLabel_inverse {G : Type} [Group G] {M : Sheaf SmoothOpenSite.topology Type}
    {a : Action (locallyConstantGroup G) M} {U : Domain}
    {m n : embedding.obj U ⟶ M} (f : Arrow (chart a m) (chart a n)) (x : Points U) :
    ordinaryArrowLabel f.inverse x = (ordinaryArrowLabel f x)⁻¹ := by
  apply (constantLabelRealEquiv G).injective
  change (constantLabelRealEquiv G) (ordinaryHomLabelEquiv G U (arrowLabel f.inverse) x) =
    (constantLabel G).app _ ((ordinaryArrowLabel f x)⁻¹)
  rw [homLabel_point, ((constantLabel G).app _).hom.map_inv]
  exact (arrowLabel_inverse_apply f _ _).trans (congrArg (fun z : (locallyConstantGroup G).obj.obj (op (op (free 0))) => z⁻¹)
    (homLabel_point U (arrowLabel f) x).symm)

theorem diskChartArrowEquiv_label (U : Domain) (m n : U ⟶ diskDomain)
    (f : Arrow (chart diskRepresentation.action (embedding.map m))
      (chart diskRepresentation.action (embedding.map n))) :
    (diskChartArrowEquiv U m n f).val = ordinaryArrowLabel f := rfl

@[simp] theorem diskChartArrowEquiv_ident (U : Domain) (m : U ⟶ diskDomain) :
    (diskChartArrowEquiv U m m (Arrow.ident _)).val = LocallyConstant.const _ 1 :=
  DFunLike.ext _ _ (ordinaryArrowLabel_ident diskRepresentation.action (embedding.map m))

theorem diskChartArrowEquiv_comp (U : Domain) (m n p : U ⟶ diskDomain)
    (f : Arrow (chart diskRepresentation.action (embedding.map m))
      (chart diskRepresentation.action (embedding.map n)))
    (g : Arrow (chart diskRepresentation.action (embedding.map n))
      (chart diskRepresentation.action (embedding.map p))) :
    (diskChartArrowEquiv U m p (f.comp g)).val =
      (diskChartArrowEquiv U m n f).val * (diskChartArrowEquiv U n p g).val :=
  DFunLike.ext _ _ (ordinaryArrowLabel_comp f g)

theorem diskChartArrowEquiv_inverse (U : Domain) (m n : U ⟶ diskDomain)
    (f : Arrow (chart diskRepresentation.action (embedding.map m))
      (chart diskRepresentation.action (embedding.map n))) :
    (diskChartArrowEquiv U n m f.inverse).val = (diskChartArrowEquiv U m n f).val⁻¹ :=
  DFunLike.ext _ _ (ordinaryArrowLabel_inverse f)

/-- Restriction uses the actual reindexed chart arrow. Its endpoints agree with
embedded composite maps by the embedding functor's composition law. -/
theorem diskChartArrowEquiv_restriction {U V : Domain} (r : U ⟶ V) (m n : V ⟶ diskDomain)
    (f : Arrow (chart diskRepresentation.action (embedding.map m))
      (chart diskRepresentation.action (embedding.map n))) (x : Points U) :
    ordinaryArrowLabel (m := embedding.map r ≫ embedding.map m) (n := embedding.map r ≫ embedding.map n)
      (f.reindex (embedding.map r)) x = (diskChartArrowEquiv V m n f).val ((show Map _ _ from r) x) :=
  ordinaryArrowLabel_reindex f r x

end SquareKit.SmoothOrdinaryQuotient

namespace SquareKit.SmoothConstantAction.Representation
open SmoothOpenSite
variable {G : Type} [Group G] {M : Sheaf topology Type}

/-- A trivial representation remains trivial for all sheafified labels. -/
theorem act_of_trivial (r : SmoothConstantAction.Representation G M)
    (hr : ∀ g, r.map g = 𝟙 M) (U : SmoothPresentationSite.Siteᵒᵖ)
    (g : (locallyConstantGroup G).obj.obj U) (m : M.obj.obj U) : r.act U g m = m := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp M.property)
    (Presheaf.imageSieve (constantLabel G) g)
    (Presheaf.imageSieve_mem topology (constantLabel G) g)).isSeparatedFor.ext
  intro V f hf
  obtain ⟨k, hk⟩ := hf
  rw [r.act_natural, ← hk, r.act_constant, hr]
  rfl

end SquareKit.SmoothConstantAction.Representation
