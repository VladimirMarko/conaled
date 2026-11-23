import SquareKit.SheafAssociatedBundleCocycle
import Examples.SheafTorsorCocycle

/-! Associated quotients retain nontrivial torsors, stabilizers and noninvertible fiber maps. -/
noncomputable section
namespace Examples.SheafAssociatedBundle
open CategoryTheory Opposite SquareKit SquareKit.SheafAssociatedBundle
open SquareKit.SmoothOpenSite SquareKit.ManifoldRealization

abbrev S3 := Equiv.Perm (Fin 3)
abbrev group := locallyConstantGroup S3
abbrev base := Examples.SheafTorsorCocycle.base
abbrev torsor := SheafTorsor.trivial group base

/-- Conjugation is an action with stabilizers on a noncommutative group. -/
def conjugation : SheafActionQuotient.Action group (SheafTorsor.groupSheaf group) where
  act U g m := g * (show group.obj.obj U from m) * g⁻¹
  one_act U m := by
    change group.obj.obj U at m
    change (1 : group.obj.obj U) * m * 1⁻¹ = m
    simp
  mul_act U g h m := by
    change group.obj.obj U at m
    change (g * h) * (show group.obj.obj U from m) * (g * h)⁻¹ = g * (h * m * h⁻¹) * g⁻¹
    simp [mul_assoc]
  natural {U V} f g m := by
    change group.obj.obj U at m
    change group.obj.map f (g * m * g⁻¹) =
      group.obj.map f g * group.obj.map f m * (group.obj.map f g)⁻¹
    rw [(group.obj.map f).hom.map_mul, (group.obj.map f).hom.map_mul, (group.obj.map f).hom.map_inv]

/-- The constant-one map is equivariant but is not required to be invertible. -/
def collapseFiber : ActionMap (𝟙 group) conjugation conjugation where
  hom := ⟨{
    app U := ↾fun _ => (1 : group.obj.obj U)
    naturality {U V} f := by ext m; exact ((group.obj.map f).hom.map_one).symm }⟩
  equivariant U g m := by
    change (1 : group.obj.obj U) = g * 1 * g⁻¹
    simp

def collapse : associated torsor conjugation ⟶ associated torsor conjugation :=
  map (SheafTorsor.SemilinearMap.ident torsor) collapseFiber

def realStage := op (op (SmoothPresentationSite.free 0))
def basePoint : base.obj.obj realStage :=
  (SquareKit.SmoothManifoldAction.pointEquiv (d := 1) (M := Space 1)).symm 0

def x : base.obj.Elements := base.obj.elementsMk realStage basePoint
def p : torsor.family.family.obj x := (1 : group.obj.obj realStage)
def swap : S3 := Equiv.swap 0 1
def label : group.obj.obj realStage := (constantLabel S3).app realStage swap

theorem swap_ne_one : swap ≠ 1 := by
  intro h
  have he := congrArg (fun g : S3 => g 0) h
  norm_num [swap, Equiv.swap_apply_def] at he

theorem label_ne_one : label ≠ 1 := by
  intro h
  apply swap_ne_one
  apply constantLabel_injective S3 (SmoothPresentationSite.free 0) (𝟙 _)
  exact h.trans (((constantLabel S3).app realStage).hom.map_one).symm

/-- A nonidentity group section fixes the identity fiber point. -/
theorem nontrivial_stabilizer :
    label ≠ 1 ∧ conjugation.act realStage label (1 : group.obj.obj realStage) =
      (1 : group.obj.obj realStage) := by
  refine ⟨label_ne_one, ?_⟩
  change label * 1 * label⁻¹ = 1
  simp

theorem classes_distinct : classOf torsor conjugation x p label ≠
    classOf torsor conjugation x p (1 : group.obj.obj realStage) := by
  intro h
  have he := congrArg (evaluate torsor conjugation x p) h
  exact label_ne_one ((evaluate_classOf torsor conjugation x p label).symm.trans
    (he.trans (evaluate_classOf torsor conjugation x p (1 : group.obj.obj realStage))))

/-- The constructed map actually identifies distinct associated points. -/
theorem collapse_identifies :
    collapse.app x (classOf torsor conjugation x p label) =
    collapse.app x (classOf torsor conjugation x p (1 : group.obj.obj realStage)) :=
  (map_classOf (SheafTorsor.SemilinearMap.ident torsor) collapseFiber x p label).trans
    (map_classOf (SheafTorsor.SemilinearMap.ident torsor) collapseFiber x p
      (1 : group.obj.obj realStage)).symm

theorem collapse_not_injective : ¬ Function.Injective (collapse.app x) :=
  fun h => classes_distinct (h collapse_identifies)

/-- Original stabilizer/gauge arrows remain distinct even when a fiber map forgets information. -/
theorem retained_gauges : Function.Injective Examples.SheafTorsorCocycle.gauge :=
  Examples.SheafTorsorCocycle.gauge_injective

namespace Nontrivial
abbrev c := Examples.SheafTorsorCocycle.Clutching.datum
abbrev P := c.glue.obj

/-- The regular associated fiber preserves the nontrivial torsor's actual display. -/
def recovery : associated P (regularAction _) ≅ P.family := regularIso P

theorem no_section : ¬ Nonempty (SplitSheaf.Tm (associated P (regularAction _))) := by
  rintro ⟨s⟩
  apply Examples.SheafTorsorCocycle.Clutching.no_section
  refine ⟨{ val x := recovery.hom.app x (s.val x), natural := ?_ }⟩
  intro x y f
  exact (NatTrans.naturality_apply recovery.hom f (s.val x)).symm.trans
    (congrArg (recovery.hom.app y) (s.natural f))

/-- Independently specified nontrivial cocycle transitions recover the same associated display. -/
def cocycle_recovery := cocycleComparison (regularAction _) c

end Nontrivial
namespace EdgeCases
open Examples.SheafFamilyCover Examples.SheafFamilyDescent

abbrev P := SheafTorsor.trivial finiteGroup (constant Bool)
abbrev emptyAction := trivialAction finiteGroup (constant Empty)

/-- On this bottom-topology site the empty fiber gives an actual initial total sheaf. -/
def emptyFiberInitial : Limits.IsInitial (SplitSheaf.Ext (associated P emptyAction)) :=
  Limits.IsInitial.ofUniqueHom
    (fun F => ⟨{
      app U := ↾fun z => Empty.elim
        ((trivialRecoveryMap P (constant Empty)).app ((constant Bool).obj.elementsMk U z.1) z.2)
      naturality {U V} f := by
        ext z
        exact Empty.elim ((trivialRecoveryMap P (constant Empty)).app
          ((constant Bool).obj.elementsMk U z.1) z.2) }⟩)
    (by
      intro F h
      ext U z
      exact Empty.elim ((trivialRecoveryMap P (constant Empty)).app
        ((constant Bool).obj.elementsMk U z.1) z.2))

/-- Empty bases are handled without choosing any section or cover index. -/
def emptyBaseInitial (T : SheafTorsor.Torsor finiteGroup (constant Empty))
    {M : Sheaf Examples.SheafFamilyCover.topology Type} (a : SheafActionQuotient.Action finiteGroup M) :
    Limits.IsInitial (SplitSheaf.Ext (associated T a)) :=
  Limits.IsInitial.ofUniqueHom (fun F => ⟨{
    app U := ↾fun z => Empty.elim z.1
    naturality := by intros; ext z; exact Empty.elim z.1 }⟩)
    (by intro F h; ext U z; exact Empty.elim z.1)

def unitGroup : Sheaf Examples.SheafFamilyCover.topology GrpCat :=
  ⟨(Functor.const Siteᵒᵖ).obj (GrpCat.of PUnit), Presheaf.isSheaf_bot _⟩

/-- The trivial group case retains the whole two-point fiber. -/
def trivialGroupRecovery : associated (SheafTorsor.trivial unitGroup (constant Bool))
    (trivialAction unitGroup (constant Bool)) ≅ SplitSheaf.constant (constant Bool) (constant Bool) :=
  trivialIso _ _

/-- Two nonidentity restrictions agree with their composite on the full associated display. -/
theorem twice_negation :
    reindexIso P (regularAction finiteGroup) (negation ≫ negation) =
      (SplitSheaf.restriction negation).mapIso (reindexIso P (regularAction finiteGroup) negation) ≪≫
        reindexIso (SheafTorsor.reindex P negation) (regularAction finiteGroup) negation :=
  reindexIso_comp P (regularAction finiteGroup) negation negation

theorem negation_nonidentity : negation ≠ 𝟙 (constant Bool) := by
  intro h
  have he := congrArg (fun f => f.hom.app (op (Discrete.mk PUnit.unit)) true) h
  change false = true at he
  cases he

end EdgeCases

namespace ProperCover
open Examples.SheafTorsorCocycle.ProperCover Examples.SheafFamilyDescent
local instance : Presheaf.IsLocallySurjective SmoothOpenSite.topology aggregate.hom :=
  (SheafFamilyCover.jointlyLocallySurjective_iff_sigmaDesc charts).mp charts_joint
local instance : Presheaf.IsLocallySurjective SmoothOpenSite.topology (Limits.Sigma.desc swappedCharts).hom :=
  (SheafFamilyCover.jointlyLocallySurjective_iff_sigmaDesc swappedCharts).mp swappedCharts_joint

/-- Named inputs keep concrete smooth algebra and gluing internals out of comparison elaboration. -/
def scalingTorsor :=
  Examples.SmoothTorsors.nontrivialTorsor

/-- The checked equality keeps the concrete scaling maps available without expanding
smooth-algebra implementation terms during comparison specialization. -/
private opaque scalingMaps : { maps : (SmoothClutching.base ⟶ SmoothClutching.base) ×
    (SmoothClutching.base ⟶ SmoothClutching.base) // maps = (scale2,scale3) } :=
  ⟨(scale2,scale3),rfl⟩

def firstRestriction := scalingMaps.val.1
def secondRestriction := scalingMaps.val.2

theorem firstRestriction_eq : firstRestriction = scale2 := congrArg Prod.fst scalingMaps.property
theorem secondRestriction_eq : secondRestriction = scale3 := congrArg Prod.snd scalingMaps.property

theorem firstRestriction_nonidentity : firstRestriction ≠ 𝟙 SmoothClutching.base := by
  rw [firstRestriction_eq]
  exact SmoothClutching.baseScale_ne_identity 2 (by norm_num) (by norm_num)
theorem secondRestriction_nonidentity : secondRestriction ≠ 𝟙 SmoothClutching.base := by
  rw [secondRestriction_eq]
  exact SmoothClutching.baseScale_ne_identity 3 (by norm_num) (by norm_num)

/-- Two nonidentity scalings preserve every full arbitrary-stage section of
association to the independently glued nontrivial torsor. -/
theorem twice_scaling : type_of%
    (reindexMap_comp_apply scalingTorsor (regularAction _) firstRestriction secondRestriction) :=
  reindexMap_comp_apply scalingTorsor (regularAction _) firstRestriction secondRestriction

/-- The proper two-chart presentation can be exchanged, with the same associated sheaf. -/
def swappedComparison : associated (Examples.SheafTorsorCocycle.ProperCover.swap.pull datum).glue.obj (regularAction _) ≅
    associated datum.glue.obj (regularAction _) :=
  cocycleRefinementComparison (regularAction _) datum Examples.SheafTorsorCocycle.ProperCover.swap

end ProperCover


namespace Target
/-- An actual target object with nonfree conjugation action and a constant fixed point. -/
def fixedObject : SheafActionQuotient.Object conjugation base where
  torsor := torsor
  value y _ := (1 : group.obj.obj y.obj)
  natural f _ := (group.obj.map f.hom).hom.map_one
  equivariant y g _ := by
    change (1 : group.obj.obj y.obj) = g * 1 * g⁻¹
    simp

def fixedSection := objectSection fixedObject

theorem fixedSection_value : evaluate torsor conjugation x p (fixedSection.val x) =
    (1 : group.obj.obj realStage) := objectSection_value fixedObject x p

/-- The noninjective fiber map also preserves the target-to-section construction. -/
theorem collapse_section : mapSection collapse fixedSection = fixedSection :=
  targetSection_natural (SheafTorsor.SemilinearMap.ident torsor) collapseFiber
    ⟨fixedObject.totalMap,fixedObject.equivariant⟩ ⟨fixedObject.totalMap,fixedObject.equivariant⟩
    (fun _ _ => rfl)

theorem recover_target : sectionTarget fixedSection =
    (⟨fixedObject.totalMap,fixedObject.equivariant⟩ : EquivariantTarget torsor conjugation) :=
  (targetSectionEquiv (P := torsor) (a := conjugation)).left_inv _

/-- Every actual target arrow, without a preferred gauge, preserves its associated section. -/
theorem all_arrows (T : SheafActionQuotient.Object conjugation base) (h : fixedObject ⟶ T) :
    type_of% (objectSection_natural h) := objectSection_natural h

/-- Restriction of the actual target is comparison of the associated sections. -/
theorem restriction (f : base ⟶ base) : type_of% (objectSection_reindex conjugation fixedObject f) :=
  objectSection_reindex conjugation fixedObject f
end Target

namespace GroupChange
open SquareKit.SheafStructureGroupExtension

def diagonalHom : S3 →* S3 × S3 := (MonoidHom.id S3).prod (MonoidHom.id S3)
def firstHom : S3 × S3 →* S3 := MonoidHom.fst S3 S3
def secondHom : S3 × S3 →* S3 := MonoidHom.snd S3 S3
abbrev productGroup := locallyConstantGroup (S3 × S3)
def diagonal : group ⟶ productGroup := locallyConstantGroupMap diagonalHom
def first : productGroup ⟶ group := locallyConstantGroupMap firstHom
def second : productGroup ⟶ group := locallyConstantGroupMap secondHom

theorem diagonal_first : diagonal ≫ first = 𝟙 group := by
  change locallyConstantGroupMap diagonalHom ≫ locallyConstantGroupMap firstHom = _
  rw [← locallyConstantGroupMap_comp]
  exact locallyConstantGroupMap_id S3

theorem diagonal_second : diagonal ≫ second = 𝟙 group := by
  change locallyConstantGroupMap diagonalHom ≫ locallyConstantGroupMap secondHom = _
  rw [← locallyConstantGroupMap_comp]
  exact locallyConstantGroupMap_id S3

local instance (U : SmoothPresentationSite.Site) :
    Limits.HasColimitsOfShape (topology.Cover U)ᵒᵖ GrpCat.{0} where
  has_colimit F := ⟨⟨_, GrpCat.FilteredColimits.colimitCoconeIsColimit F⟩⟩

set_option backward.isDefEq.respectTransparency false in
theorem map_constant {G H : Type} [Group G] [Group H] (f : G →* H)
    (U : SmoothPresentationSite.Siteᵒᵖ) (g : G) :
    (locallyConstantGroupMap f).hom.app U ((constantLabel G).app U g) =
      (constantLabel H).app U (f g) := by
  have h := CategoryTheory.toSheafify_naturality topology
    ((Functor.const SmoothPresentationSite.Siteᵒᵖ).map (GrpCat.ofHom f))
  exact (congrArg (fun k => k.app U g) h).symm

/-- The chosen homomorphism is not surjective even at a concrete represented stage. -/
theorem diagonal_not_surjective : ¬ Function.Surjective (diagonal.hom.app realStage) := by
  intro h
  obtain ⟨u,hu⟩ := h ((constantLabel (S3 × S3)).app realStage (1,swap))
  have h₁ := congrArg (first.hom.app realStage) hu
  have h₂ := congrArg (second.hom.app realStage) hu
  have e₁ := congrArg (fun k : group ⟶ group => k.hom.app realStage u) diagonal_first
  have e₂ := congrArg (fun k : group ⟶ group => k.hom.app realStage u) diagonal_second
  change first.hom.app realStage (diagonal.hom.app realStage u) = u at e₁
  change second.hom.app realStage (diagonal.hom.app realStage u) = u at e₂
  rw [e₁, show first = locallyConstantGroupMap firstHom from rfl, map_constant] at h₁
  rw [e₂, show second = locallyConstantGroupMap secondHom from rfl, map_constant] at h₂
  apply swap_ne_one
  apply constantLabel_injective S3 (SmoothPresentationSite.free 0) (𝟙 _)
  exact h₂.symm.trans h₁

/-- The composite comparison is specialized to a proper group extension and its retraction. -/
def twice := compositionComparison diagonal first torsor

def otherSwap : S3 := Equiv.swap 1 2
def k : group.obj.obj realStage := (constantLabel S3).app realStage otherSwap
def h : productGroup.obj.obj realStage := (constantLabel (S3 × S3)).app realStage (swap,1)

set_option backward.isDefEq.respectTransparency false in
theorem order_control : k * first.hom.app realStage h ≠ first.hom.app realStage h * k := by
  change k * (locallyConstantGroupMap firstHom).hom.app realStage h ≠
    (locallyConstantGroupMap firstHom).hom.app realStage h * k
  rw [show h = (constantLabel (S3 × S3)).app realStage (swap,1) from rfl, map_constant]
  intro he
  have he' : (constantLabel S3).app realStage (otherSwap * swap) =
      (constantLabel S3).app realStage (swap * otherSwap) := by
    change (constantLabel S3).app realStage otherSwap * (constantLabel S3).app realStage swap =
      (constantLabel S3).app realStage swap * (constantLabel S3).app realStage otherSwap at he
    exact (((constantLabel S3).app realStage).hom.map_mul otherSwap swap).trans
      (he.trans (((constantLabel S3).app realStage).hom.map_mul swap otherSwap).symm)
  have hp := congrArg (fun q : S3 => q 0)
    (constantLabel_injective S3 (SmoothPresentationSite.free 0) (𝟙 _) he')
  norm_num [otherSwap, swap, Equiv.Perm.mul_apply, Equiv.swap_apply_def] at hp

theorem twice_value : twice.iso.hom.app x
    (classOf (extension diagonal torsor) (rightInverseAction first) x
      (classOf torsor (rightInverseAction diagonal) x p h) k) =
    classOf torsor (rightInverseAction (diagonal ≫ first)) x p (k * first.hom.app realStage h) :=
  compositionComparison_classOf diagonal first torsor x p h k

/-- Applied cocycle labels give the actual extension torsor, including all gauge arrows. -/
def changedCocycle := cocycleExtensionComparison diagonal Examples.SheafTorsorCocycle.datum

theorem changedGauge : type_of%
    (cocycleExtensionComparison_natural diagonal (Examples.SheafTorsorCocycle.gauge swap)) :=
  cocycleExtensionComparison_natural diagonal (Examples.SheafTorsorCocycle.gauge swap)

end GroupChange

end Examples.SheafAssociatedBundle
