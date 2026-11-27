import Examples.ProperLocalBranches
import SquareKit.SmoothBranchRestriction
import SquareKit.SmoothManifoldOpenRectangle
import SquareKit.SmoothOpenCoordinatePullbacks

/-! Empty fibers and proper endpoint restrictions on complete sheaf sections. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped Manifold ContDiff
namespace Examples.SmoothBranchRestriction
open SquareKit SquareKit.ManifoldRealization SquareKit.SmoothPresentationSite
open SquareKit.SmoothBranchRealization Orbifolds.LocalBranches
open SquareKit.EuclideanOpen
abbrev stageAt (A : Code) := op (op A)

abbrev emptyDomain : Domain := ⟨1, 0⟩

/-- The empty principal stage has a section of every sheaf, including the initial one. -/
def emptyStageSection (F : Sheaf SmoothOpenSite.topology Type) :
    F.obj.obj (stageAt (code emptyDomain)) :=
  ((emptyDomainIsInitial emptyDomain ⟨fun z => z.property rfl⟩).to F).hom.app
    (stageAt (code emptyDomain)) (𝟙 (op (code emptyDomain)))

private theorem diagonal_proper : IsProperMap (fun x : Space 1 => (x,x)) := by
  apply isProperMap_of_comp_of_t2 (continuous_id.prodMk continuous_id) continuous_fst
  exact isProperMap_id

private theorem unequal_centers : (0 : Space 1) ≠ 1 := by
  intro h
  have := congrFun h 0
  norm_num at this

/-- An actual empty central fiber produces an initial branch sheaf, which still
has a section on the empty principal stage. -/
theorem empty_fiber_sheaf :
    ∃ U V : Opens (Space 1), (0 : Space 1) ∈ U ∧ (1 : Space 1) ∈ V ∧
      ∃ D : Diagram (modelWithCorners 1) (modelWithCorners 1) id id U V
          {a : Space 1 // a = 0 ∧ a = 1},
        D.region = ⊥ ∧ Nonempty (IsInitial (branches D)) ∧
          Nonempty (IsInitial (arrowObject D)) ∧
          ∃ b : (branches D).obj.obj (stageAt (code emptyDomain)),
            stageEquiv D (op (code emptyDomain))
              ((assembly D).hom.app (stageAt (code emptyDomain)) b) = b := by
  have he : ∀ a : Space 1, ¬(id a = 0 ∧ id a = 1) :=
    fun _ h => unequal_centers (h.1.symm.trans h.2)
  let : IsEmpty {a : Space 1 // id a = 0 ∧ id a = 1} := ⟨fun a => he a.val a.property⟩
  have hs : IsLocalDiffeomorph (modelWithCorners 1) (modelWithCorners 1) ∞
      (id : Space 1 → Space 1) :=
    (Diffeomorph.refl (modelWithCorners 1) (Space 1) ∞).isLocalDiffeomorph
  obtain ⟨U,V,hU,hV,D,hD⟩ := exists_empty_diagram hs
    (IY := modelWithCorners 1) contMDiff_id diagonal_proper 0 1 he
  exact ⟨U,V,hU,hV,D,hD,⟨branchesIsInitial D⟩,⟨emptyArrowIsInitial D⟩,
    emptyStageSection (branches D),(stageEquiv D _).apply_symm_apply _⟩

abbrev puncturedDomain : Domain := ⟨1, SmoothAlgebra.generator 0⟩
abbrev punctured : Opens (Space 1) := ordinaryOpen puncturedDomain

def whole := ProperLocalBranches.unitDiagram (modelWithCorners 1)
  (⊤ : Opens (Space 1)) ⊤

def restricted := whole.restrict contMDiff_id contMDiff_id ⊤ punctured le_rfl le_top

theorem partial_domain : restricted.domain () = punctured := by
  ext z
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ha.2.2
  · intro hz
    exact ⟨z,⟨⟨Set.mem_univ _,Set.mem_univ _⟩,Set.mem_univ _,hz⟩,rfl⟩

theorem partial_domain_nonempty : Nonempty (restricted.domain ()) := by
  rw [partial_domain]
  exact ⟨⟨1,by change (1 : ℝ) ≠ 0; norm_num⟩⟩

theorem partial_domain_proper : restricted.domain () ≠ (⊤ : Opens (Space 1)) := by
  rw [partial_domain]
  intro h
  have hz : (0 : Space 1) ∈ punctured := h ▸ Set.mem_univ _
  exact hz rfl

/-- The endpoint window really is pulled back on full interpreted sections. -/
theorem partial_isPullback :
    IsPullback (arrowRestriction whole contMDiff_id contMDiff_id ⊤ punctured le_rfl le_top)
      (prod.lift (source restricted contMDiff_id) (target restricted contMDiff_id))
      (prod.lift (source whole contMDiff_id) (target whole contMDiff_id))
      (prod.map (map (Opens.inclusion (le_rfl : (⊤ : Opens (Space 1)) ≤ ⊤))
          (contMDiff_inclusion le_rfl))
        (map (Opens.inclusion (le_top : punctured ≤ ⊤)) (contMDiff_inclusion le_top))) :=
  OpenRectangle.restriction_isPullback (id : Space 1 → Space 1) contMDiff_id
    id contMDiff_id le_rfl le_top

/-- The principal punctured stage supplies a nonconstant complete arrow section. -/
def principalArrow : embedding.obj puncturedDomain ⟶ arrowObject restricted :=
  (principalIso puncturedDomain).inv ≫ map
    (fun z : punctured => (⟨z.val, Set.mem_univ _,z.property⟩ : restricted.region))
    ((ContMDiff.subtypeVal_comp_iff restricted.region _).mp contMDiff_subtype_val)

/-- The target of the section is the universal punctured coordinate itself. -/
theorem principalArrow_target :
    principalArrow ≫ target restricted contMDiff_id = (principalIso puncturedDomain).inv := by
  rw [principalArrow, target, Category.assoc, ← map_comp]
  change (principalIso puncturedDomain).inv ≫
    map (id : punctured → punctured) contMDiff_id = _
  rw [map_id, Category.comp_id]

def partialArrow : (arrowObject restricted).obj.obj (stageAt (code puncturedDomain)) :=
  principalArrow.hom.app (stageAt (code puncturedDomain)) (𝟙 (op (code puncturedDomain)))

def partialBranch : (branches restricted).obj.obj (stageAt (code puncturedDomain)) :=
  stageEquiv restricted (op (code puncturedDomain)) partialArrow

theorem partial_assembly :
    (assembly restricted).hom.app (stageAt (code puncturedDomain)) partialBranch = partialArrow :=
  (stageEquiv restricted _).symm_apply_apply _

/-- Restricting the actual punctured section commutes with its branch assembly. -/
theorem partial_assembly_restriction :
    (arrowRestriction whole contMDiff_id contMDiff_id ⊤ punctured le_rfl le_top).hom.app
      (stageAt (code puncturedDomain)) partialArrow =
    (assembly whole).hom.app (stageAt (code puncturedDomain))
      ((branchRestriction whole contMDiff_id contMDiff_id ⊤ punctured le_rfl le_top).hom.app
        (stageAt (code puncturedDomain)) partialBranch) := by
  rw [← partial_assembly]
  exact congrArg (fun f => f.hom.app (stageAt (code puncturedDomain)) partialBranch)
    (assembly_restriction whole contMDiff_id contMDiff_id ⊤ punctured le_rfl le_top)

end Examples.SmoothBranchRestriction
