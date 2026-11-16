import SquareKit.SmoothCechDescent

/-! Complete arrow comparisons for independent smooth cocycles. -/
noncomputable section
open scoped Manifold ContDiff
namespace SquareKit.SmoothCech
open CategoryTheory CategoryTheory.Limits Opposite EuclideanOpen SmoothOpenSite
open SmoothRepresentedCover SmoothManifoldAction ManifoldRealization SheafActionQuotient
variable {X : Sheaf topology Type} {I : Type} {A : Atlas X I}
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (Model d) ∞ M]
variable (smoothAction : ∀ g : G, ContMDiff (Model d) (Model d) ∞ (fun x : M => g • x))
namespace Hom
variable {p q : Datum (d := d) (G := G) (M := M) A} (f : Hom p q)

def chartArrow (i : I) :=
  (External.chartLabelsEquiv smoothAction (p.localMap i) (q.localMap i)).symm (f.labels i)

def localLabel : A.total ⟶ locallyConstantGroupSheaf G :=
  SheafCoproductLocal.desc A.family (fun i => arrowLabel (f.chartArrow smoothAction i))

omit [TopologicalSpace G] [DiscreteTopology G] in
@[simp, reassoc] theorem localLabel_fac (i : I) :
    A.inclusion i ≫ f.localLabel smoothAction = arrowLabel (f.chartArrow smoothAction i) :=
  SheafCoproductLocal.inclusion_desc _ _ _

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem localLabel_relation :
    (representation smoothAction).action.onMap (f.localLabel smoothAction) q.localMapSheaf =
      p.localMapSheaf := by
  apply colimit.hom_ext
  intro ⟨i⟩
  change A.inclusion i ≫ _ = A.inclusion i ≫ _
  rw [Datum.onMap_precomp, localLabel_fac, Datum.localMapSheaf_fac, Datum.localMapSheaf_fac]
  exact arrowLabel_relation (f.chartArrow smoothAction i)

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem chartArrow_label (i : I) (x : Points (A.domain i)) :
    ordinaryHomLabelEquiv G (A.domain i) (arrowLabel (f.chartArrow smoothAction i)) x =
      ((f.labels i).val x)⁻¹ := by
  have h := congrArg (fun z => z.val x)
    ((External.chartLabelsEquiv smoothAction (p.localMap i) (q.localMap i)).apply_symm_apply (f.labels i))
  change (ordinaryHomLabelEquiv G (A.domain i)
    (arrowLabel (f.chartArrow smoothAction i)) x)⁻¹ = _ at h
  exact inv_eq_iff_eq_inv.mp h

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem localLabel_commutes :
    labelMul (SheafCoverCech.first A.cover ≫ f.localLabel smoothAction) (q.overlapLabel smoothAction) =
      labelMul (p.overlapLabel smoothAction) (SheafCoverCech.second A.cover ≫ f.localLabel smoothAction) := by
  apply A.pairHom_ext
  intro i j
  simp only [labelMul_precomp, A.pairMap_first_assoc, A.pairMap_second_assoc,
    localLabel_fac, Datum.overlapLabel_fac]
  apply (ordinaryHomLabelEquiv G (A.pair i j)).injective
  apply LocallyConstant.ext
  intro x
  simp only [ordinary_labelMul, ordinaryHomLabelEquiv_natural, chartArrow_label,
    Datum.transitionArrow_label]
  simpa only [mul_inv_rev] using congrArg Inv.inv (f.commutes i j x)

/-- The entire local arrow on the split cover, retaining its right label. -/
def splitLabel : SplitSheaf.Ext (SplitSheaf.ofDisplay A.cover) ⟶ locallyConstantGroupSheaf G :=
  (SplitSheaf.displayIso A.cover).hom ≫ f.localLabel smoothAction

theorem splitLabel_relation :
    (representation smoothAction).action.onMap (f.splitLabel smoothAction) q.splitLocalMap =
      p.splitLocalMap := by
  exact congrArg (fun h => (SplitSheaf.displayIso A.cover).hom ≫ h)
    (f.localLabel_relation smoothAction)

def localArrow : SheafActionQuotient.Arrow
    (p.cech smoothAction).localObject (q.cech smoothAction).localObject :=
  chartArrowOfRelation (f.splitLabel smoothAction) p.splitLocalMap q.splitLocalMap
    (f.splitLabel_relation smoothAction)

theorem splitLabel_commutes :
    labelMul (SplitSheaf.Cech.first (SplitSheaf.ofDisplay A.cover) ≫ f.splitLabel smoothAction)
      (q.splitLabel smoothAction) =
    labelMul (p.splitLabel smoothAction)
      (SplitSheaf.Cech.second (SplitSheaf.ofDisplay A.cover) ≫ f.splitLabel smoothAction) := by
  have h := congrArg (fun h => (SheafCoverCech.splitDoubleIso A.cover).hom ≫ h)
    (f.localLabel_commutes smoothAction)
  simp only [labelMul_precomp, ← Category.assoc, SheafCoverCech.splitDouble_first,
    SheafCoverCech.splitDouble_second] at h
  simpa only [splitLabel, Datum.splitLabel, Category.assoc] using h

/-- Compatible external families yield the full commuting quotient arrow. -/
def cechMap : SheafActionQuotient.Cech.Map (p.cech smoothAction) (q.cech smoothAction) where
  localArrow := f.localArrow smoothAction
  commutes := by
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    ext x z
    change (locallyConstantGroup G).obj.obj x.obj at z
    change (z * (show (locallyConstantGroup G).obj.obj x.obj from
      (SplitSheaf.Cech.first (SplitSheaf.ofDisplay A.cover) ≫ f.splitLabel smoothAction).hom.app x.obj x.val)) *
      (show (locallyConstantGroup G).obj.obj x.obj from (q.splitLabel smoothAction).hom.app x.obj x.val) =
      (z * (show (locallyConstantGroup G).obj.obj x.obj from (p.splitLabel smoothAction).hom.app x.obj x.val)) *
      (show (locallyConstantGroup G).obj.obj x.obj from
      (SplitSheaf.Cech.second (SplitSheaf.ofDisplay A.cover) ≫ f.splitLabel smoothAction).hom.app x.obj x.val)
    rw [mul_assoc, mul_assoc]
    exact congrArg (z * ·) (congrArg (fun h => h.hom.app x.obj x.val)
      (f.splitLabel_commutes smoothAction))

/-- The interpreted arrow uses the same effective descent functor as objects. -/
def interpreted : SheafActionQuotient.Arrow (p.interpreted smoothAction) (q.interpreted smoothAction) :=
  (Descent.displayDescentEquivalence (representation smoothAction).action A.cover).functor.map
    (f.cechMap smoothAction).toDescent

end Hom
/-- Internal coordinates on a compatible complete arrow, before quotienting anything. -/
structure LabelMap (p q : Datum (d := d) (G := G) (M := M) A) where
  label : A.total ⟶ locallyConstantGroupSheaf G
  relation : (representation smoothAction).action.onMap label q.localMapSheaf = p.localMapSheaf
  commutes : labelMul (SheafCoverCech.first A.cover ≫ label) (q.overlapLabel smoothAction) =
    labelMul (p.overlapLabel smoothAction) (SheafCoverCech.second A.cover ≫ label)

namespace LabelMap
variable {p q : Datum (d := d) (G := G) (M := M) A}

omit [TopologicalSpace G] [DiscreteTopology G] in
@[ext] theorem ext (f g : LabelMap smoothAction p q) (h : f.label = g.label) : f = g := by
  cases f
  cases g
  cases h
  rfl

def ofHom (f : Hom p q) : LabelMap smoothAction p q where
  label := f.localLabel smoothAction
  relation := f.localLabel_relation smoothAction
  commutes := f.localLabel_commutes smoothAction

variable (f : LabelMap smoothAction p q)

def chartArrow (i : I) : External.ChartArrow smoothAction (p.localMap i) (q.localMap i) :=
  chartArrowOfRelation (A.inclusion i ≫ f.label)
    (hat (p.localMap i).val (p.localMap i).property)
    (hat (q.localMap i).val (q.localMap i).property) (by
      have h := congrArg (fun h => A.inclusion i ≫ h) f.relation
      simpa only [Datum.onMap_precomp, Datum.localMapSheaf_fac] using h)

def labels (i : I) := External.chartLabelsEquiv smoothAction (p.localMap i) (q.localMap i)
  (f.chartArrow smoothAction i)

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem labels_apply (i : I) (x : Points (A.domain i)) :
    (f.labels smoothAction i).val x =
      (ordinaryHomLabelEquiv G (A.domain i) (A.inclusion i ≫ f.label) x)⁻¹ := by
  change (ordinaryHomLabelEquiv G (A.domain i)
    (arrowLabel (f.chartArrow smoothAction i)) x)⁻¹ = _
  apply congrArg Inv.inv
  apply congrArg (fun h => ordinaryHomLabelEquiv G (A.domain i) h x)
  ext U x
  exact one_mul (show (locallyConstantGroup G).obj.obj U from (A.inclusion i ≫ f.label).hom.app U x)

def toHom : Hom p q where
  labels := f.labels smoothAction
  commutes i j x := by
    have h := congrArg (fun h => ordinaryHomLabelEquiv G (A.pair i j)
      (A.pairMap i j ≫ h) x) f.commutes
    simp only [labelMul_precomp, A.pairMap_first_assoc, A.pairMap_second_assoc,
      Datum.overlapLabel_fac, ordinary_labelMul, ordinaryHomLabelEquiv_natural,
      Datum.transitionArrow_label] at h
    have hi := congrArg Inv.inv h
    simpa only [labels_apply, mul_inv_rev, inv_inv] using hi

theorem ofHom_toHom : ofHom smoothAction (f.toHom smoothAction) = f := by
  apply LabelMap.ext
  apply colimit.hom_ext
  intro ⟨i⟩
  change A.inclusion i ≫ (f.toHom smoothAction).localLabel smoothAction = _
  rw [Hom.localLabel_fac]
  apply (ordinaryHomLabelEquiv G (A.domain i)).injective
  apply LocallyConstant.ext
  intro x
  rw [Hom.chartArrow_label]
  change ((f.labels smoothAction i).val x)⁻¹ = _
  rw [labels_apply, inv_inv]

theorem toHom_ofHom (f : Hom p q) : (ofHom smoothAction f).toHom smoothAction = f := by
  apply Hom.ext
  funext i
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  change ((ofHom smoothAction f).labels smoothAction i).val x = _
  rw [labels_apply]
  change (ordinaryHomLabelEquiv G (A.domain i) (A.inclusion i ≫ f.localLabel smoothAction) x)⁻¹ = _
  rw [Hom.localLabel_fac, Hom.chartArrow_label, inv_inv]

/-- Both inverse equations retain the entire local family, not only point values. -/
def homEquiv : Hom p q ≃ LabelMap smoothAction p q where
  toFun := ofHom smoothAction
  invFun := toHom smoothAction
  left_inv := toHom_ofHom smoothAction
  right_inv := ofHom_toHom smoothAction

/-- Read the label of an arbitrary compatible quotient arrow; no reconstruction
or trivialization hypothesis is added to the already regular local objects. -/
def ofCechMap (f : SheafActionQuotient.Cech.Map (p.cech smoothAction) (q.cech smoothAction)) :
    LabelMap smoothAction p q where
  label := (SplitSheaf.displayIso A.cover).inv ≫ arrowLabel f.localArrow
  relation := by
    have h := congrArg (fun h => (SplitSheaf.displayIso A.cover).inv ≫ h)
      (arrowLabel_relation f.localArrow)
    simp only [Datum.onMap_precomp, Datum.cech, Datum.splitLocalMap,
      Iso.inv_hom_id_assoc] at h
    exact h
  commutes := by
    apply (cancel_epi (SheafCoverCech.splitDoubleIso A.cover).hom).mp
    simp only [labelMul_precomp, ← Category.assoc, SheafCoverCech.splitDouble_first,
      SheafCoverCech.splitDouble_second]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    ext U x
    have h := congrArg (fun a => a.torsorArrow.iso.hom.app
      ((SplitSheaf.Cech.double (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U x)
      (1 : (locallyConstantGroup G).obj.obj U)) f.commutes
    change (show (locallyConstantGroup G).obj.obj U from
      (arrowLabel f.localArrow).hom.app U ((SplitSheaf.Cech.first _).hom.app U x)) *
      (show (locallyConstantGroup G).obj.obj U from (q.splitLabel smoothAction).hom.app U x) =
      _ at h
    change _ = f.localArrow.torsorArrow.iso.hom.app
      ((SplitSheaf.Ext (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U
        ((SplitSheaf.Cech.second _).hom.app U x))
      ((1 : (locallyConstantGroup G).obj.obj U) *
        (show (locallyConstantGroup G).obj.obj U from (p.splitLabel smoothAction).hom.app U x)) at h
    rw [one_mul] at h
    have he := f.localArrow.torsorArrow.equivariant
      ((SplitSheaf.Ext (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U
        ((SplitSheaf.Cech.second _).hom.app U x))
      (show (locallyConstantGroup G).obj.obj U from (p.splitLabel smoothAction).hom.app U x)
      (1 : (locallyConstantGroup G).obj.obj U)
    change f.localArrow.torsorArrow.iso.hom.app
      ((SplitSheaf.Ext (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U
        ((SplitSheaf.Cech.second (SplitSheaf.ofDisplay A.cover)).hom.app U x))
      ((show (locallyConstantGroup G).obj.obj U from (p.splitLabel smoothAction).hom.app U x) *
        (1 : (locallyConstantGroup G).obj.obj U)) =
      (show (locallyConstantGroup G).obj.obj U from (p.splitLabel smoothAction).hom.app U x) *
      (show (locallyConstantGroup G).obj.obj U from (arrowLabel f.localArrow).hom.app U
        ((SplitSheaf.Cech.second _).hom.app U x)) at he
    rw [mul_one] at he
    exact h.trans he

theorem ofCechMap_ofHom (f : Hom p q) :
    ofCechMap smoothAction (f.cechMap smoothAction) = ofHom smoothAction f := by
  apply LabelMap.ext
  have h : arrowLabel (f.localArrow smoothAction) = f.splitLabel smoothAction := by
    ext U x
    exact one_mul (show (locallyConstantGroup G).obj.obj U from (f.splitLabel smoothAction).hom.app U x)
  change (SplitSheaf.displayIso A.cover).inv ≫ arrowLabel (f.localArrow smoothAction) = _
  rw [h]
  exact Iso.inv_hom_id_assoc _ _

theorem ofCechMap_injective : Function.Injective
    (ofCechMap smoothAction (p := p) (q := q)) := by
  intro f g h
  apply SheafActionQuotient.Cech.Map.ext
  apply (chartArrowEquiv p.splitLocalMap q.splitLocalMap).injective
  apply Subtype.ext
  apply (cancel_epi (SplitSheaf.displayIso A.cover).inv).mp
  exact congrArg LabelMap.label h

theorem cechMap_toHom_ofCechMap
    (f : SheafActionQuotient.Cech.Map (p.cech smoothAction) (q.cech smoothAction)) :
    ((ofCechMap smoothAction f).toHom smoothAction).cechMap smoothAction = f := by
  apply ofCechMap_injective smoothAction
  rw [ofCechMap_ofHom, ofHom_toHom]

/-- Complete external families classify all compatible quotient Čech arrows. -/
def cechHomEquiv : Hom p q ≃
    SheafActionQuotient.Cech.Map (p.cech smoothAction) (q.cech smoothAction) where
  toFun := Hom.cechMap smoothAction
  invFun f := (ofCechMap smoothAction f).toHom smoothAction
  left_inv f := by
    change (ofCechMap smoothAction (f.cechMap smoothAction)).toHom smoothAction = f
    rw [ofCechMap_ofHom, toHom_ofHom]
  right_inv := cechMap_toHom_ofCechMap smoothAction

end LabelMap

namespace Hom
variable {p q r : Datum (d := d) (G := G) (M := M) A}

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem localLabel_ident (p : Datum (d := d) (G := G) (M := M) A) :
    (Hom.ident p).localLabel smoothAction = labelOne A.total := by
  apply colimit.hom_ext
  intro ⟨i⟩
  change A.inclusion i ≫ _ = A.inclusion i ≫ _
  rw [localLabel_fac, labelOne_precomp]
  apply (ordinaryHomLabelEquiv G (A.domain i)).injective
  apply LocallyConstant.ext
  intro x
  rw [chartArrow_label, ordinary_labelOne]
  exact inv_one

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem localLabel_comp (f : Hom p q) (g : Hom q r) :
    (f.comp g).localLabel smoothAction = labelMul (f.localLabel smoothAction) (g.localLabel smoothAction) := by
  apply colimit.hom_ext
  intro ⟨i⟩
  change A.inclusion i ≫ _ = A.inclusion i ≫ _
  rw [localLabel_fac, labelMul_precomp, localLabel_fac, localLabel_fac]
  apply (ordinaryHomLabelEquiv G (A.domain i)).injective
  apply LocallyConstant.ext
  intro x
  rw [ordinary_labelMul, chartArrow_label, chartArrow_label, chartArrow_label]
  exact mul_inv_rev _ _

theorem cechMap_ident (p : Datum (d := d) (G := G) (M := M) A) :
    (Hom.ident p).cechMap smoothAction = 𝟙 (p.cech smoothAction) := by
  apply SheafActionQuotient.Cech.Map.ext
  apply SheafActionQuotient.Arrow.ext
  apply SheafTorsor.Arrow.ext
  ext x z
  change (locallyConstantGroup G).obj.obj x.obj at z
  change z * (show (locallyConstantGroup G).obj.obj x.obj from
    ((Hom.ident p).localLabel smoothAction).hom.app x.obj
      ((SplitSheaf.displayIso A.cover).hom.hom.app x.obj x.val)) = z
  rw [localLabel_ident]
  exact mul_one z

theorem cechMap_comp (f : Hom p q) (g : Hom q r) :
    (f.comp g).cechMap smoothAction = SheafActionQuotient.Cech.Map.comp (f.cechMap smoothAction) (g.cechMap smoothAction) := by
  apply SheafActionQuotient.Cech.Map.ext
  apply SheafActionQuotient.Arrow.ext
  apply SheafTorsor.Arrow.ext
  ext x z
  change (locallyConstantGroup G).obj.obj x.obj at z
  change z * (show (locallyConstantGroup G).obj.obj x.obj from
    ((f.comp g).localLabel smoothAction).hom.app x.obj
      ((SplitSheaf.displayIso A.cover).hom.hom.app x.obj x.val)) =
    (z * (show (locallyConstantGroup G).obj.obj x.obj from
    (f.localLabel smoothAction).hom.app x.obj
      ((SplitSheaf.displayIso A.cover).hom.hom.app x.obj x.val))) *
    (show (locallyConstantGroup G).obj.obj x.obj from
    (g.localLabel smoothAction).hom.app x.obj
      ((SplitSheaf.displayIso A.cover).hom.hom.app x.obj x.val))
  rw [localLabel_comp]
  exact (mul_assoc _ _ _).symm

end Hom

/-- Interpretation preserves the complete groupoid of external objects and arrows. -/
def cechFunctor : Datum (d := d) (G := G) (M := M) A ⥤
    SheafActionQuotient.Cech.Datum (a := (representation smoothAction).action)
      (SplitSheaf.ofDisplay A.cover) where
  obj p := p.cech smoothAction
  map f := f.cechMap smoothAction
  map_id := Hom.cechMap_ident smoothAction
  map_comp := Hom.cechMap_comp smoothAction

def interpretation : Datum (d := d) (G := G) (M := M) A ⥤
    SheafActionQuotient.Object (representation smoothAction).action X :=
  cechFunctor smoothAction ⋙ SheafActionQuotient.Cech.equivalence.functor ⋙
    (Descent.displayDescentEquivalence (representation smoothAction).action A.cover).functor

/-- The full external arrow family is equivalent to every arrow between the
interpreted objects. Existing Čech equivalence and effective descent supply
the final two steps, after the represented-cover comparison. -/
def interpretedHomEquiv (p q : Datum (d := d) (G := G) (M := M) A) :
    Hom p q ≃ SheafActionQuotient.Arrow (p.interpreted smoothAction) (q.interpreted smoothAction) :=
  (LabelMap.cechHomEquiv smoothAction).trans
    ((SheafActionQuotient.Cech.equivalence.fullyFaithfulFunctor.homEquiv).trans
      (Descent.arrowEquiv (p.cech smoothAction).toDescent (q.cech smoothAction).toDescent))

end SquareKit.SmoothCech
