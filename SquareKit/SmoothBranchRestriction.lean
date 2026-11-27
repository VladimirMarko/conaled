import Applications.Orbifolds.LocalBranchRestriction
import SquareKit.SmoothBranchRealization
import SquareKit.SmoothManifoldOpenRectangle

/-! Canonical assembly respects restriction of both endpoint neighborhoods. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped Manifold ContDiff
namespace SquareKit.SmoothBranchRealization
open ManifoldRealization Orbifolds.LocalBranches

variable {a x y : ℕ} {A X Y J : Type}
  [TopologicalSpace A] [ChartedSpace (Space a) A] [IsManifold (modelWithCorners a) ∞ A]
  [TopologicalSpace X] [ChartedSpace (Space x) X] [IsManifold (modelWithCorners x) ∞ X]
  [TopologicalSpace Y] [ChartedSpace (Space y) Y] [IsManifold (modelWithCorners y) ∞ Y]
  {s : A → X} {t : A → Y} {U : Opens X} {V : Opens Y}
  (D : Diagram (modelWithCorners a) (modelWithCorners x) s t U V J)
  (hs : ContMDiff (modelWithCorners a) (modelWithCorners x) ∞ s)
  (ht : ContMDiff (modelWithCorners a) (modelWithCorners y) ∞ t)
  (U' : Opens X) (V' : Opens Y) (hU : U' ≤ U) (hV : V' ≤ V)

/-- Inclusion of the actual smaller arrow region. -/
def arrowRestriction : arrowObject (D.restrict hs ht U' V' hU hV) ⟶ arrowObject D :=
  map (Opens.inclusion (D.restrict_region_le hs ht U' V' hU hV))
    (contMDiff_inclusion (D.restrict_region_le hs ht U' V' hU hV))

omit [IsManifold (modelWithCorners a) ∞ A] [IsManifold (modelWithCorners x) ∞ X]
  [IsManifold (modelWithCorners y) ∞ Y] in
theorem restrictionDomain_le (i : J) :
    (D.restrict hs ht U' V' hU hV).domain i ≤ D.domain i :=
  D.restrictedDomain_le i _ (D.restrictedPiece_le hs ht U' V' i)

/-- Each smaller source domain enters the original summand with the same label. -/
def branchRestriction : branches (D.restrict hs ht U' V' hU hV) ⟶ branches D :=
  SheafCoproductLocal.desc _ (fun i =>
    map (Opens.inclusion (restrictionDomain_le D hs ht U' V' hU hV i))
      (contMDiff_inclusion (restrictionDomain_le D hs ht U' V' hU hV i)) ≫
        SheafCoproductLocal.inclusion (fun i => object x (D.domain i)) i)

omit [IsManifold (modelWithCorners y) ∞ Y] in
@[reassoc] theorem assembly_restriction :
    assembly (D.restrict hs ht U' V' hU hV) ≫ arrowRestriction D hs ht U' V' hU hV =
      branchRestriction D hs ht U' V' hU hV ≫ assembly D := by
  apply colimit.hom_ext
  rintro ⟨i⟩
  change SheafCoproductLocal.inclusion _ i ≫
    (assembly (D.restrict hs ht U' V' hU hV) ≫ arrowRestriction D hs ht U' V' hU hV) =
    SheafCoproductLocal.inclusion _ i ≫ (branchRestriction D hs ht U' V' hU hV ≫ assembly D)
  rw [← Category.assoc, inclusion_assembly, ← Category.assoc, branchRestriction,
    SheafCoproductLocal.inclusion_desc, Category.assoc, inclusion_assembly]
  rw [arrowRestriction, ← map_comp, ← map_comp]
  rfl

omit [IsManifold (modelWithCorners y) ∞ Y] in
@[reassoc] theorem decompose_restriction :
    arrowRestriction D hs ht U' V' hU hV ≫ decompose D =
      decompose (D.restrict hs ht U' V' hU hV) ≫ branchRestriction D hs ht U' V' hU hV := by
  have h := congrArg (fun f => decompose (D.restrict hs ht U' V' hU hV) ≫ f ≫ decompose D)
    (assembly_restriction D hs ht U' V' hU hV)
  simpa only [Category.assoc, decompose_assembly_assoc, assembly_decompose, Category.comp_id] using h

omit [IsManifold (modelWithCorners y) ∞ Y] in
@[reassoc] theorem arrowRestriction_source :
    arrowRestriction D hs ht U' V' hU hV ≫ source D hs =
      source (D.restrict hs ht U' V' hU hV) hs ≫ map (Opens.inclusion hU)
        (contMDiff_inclusion hU) := by
  rw [arrowRestriction, source, source, ← map_comp, ← map_comp]
  rfl

omit [IsManifold (modelWithCorners x) ∞ X] in
@[reassoc] theorem arrowRestriction_target :
    arrowRestriction D hs ht U' V' hU hV ≫ target D ht =
      target (D.restrict hs ht U' V' hU hV) ht ≫ map (Opens.inclusion hV)
        (contMDiff_inclusion hV) := by
  rw [arrowRestriction, target, target, ← map_comp, ← map_comp]
  rfl

omit [IsManifold (modelWithCorners y) ∞ Y] in
@[reassoc] theorem branchRestriction_source :
    branchRestriction D hs ht U' V' hU hV ≫ branchSource D =
      branchSource (D.restrict hs ht U' V' hU hV) ≫ map (Opens.inclusion hU)
        (contMDiff_inclusion hU) := by
  rw [← assembly_source D hs, ← Category.assoc, ← assembly_restriction,
    Category.assoc, arrowRestriction_source, ← Category.assoc, assembly_source]

@[reassoc] theorem branchRestriction_target :
    branchRestriction D hs ht U' V' hU hV ≫ branchTarget D ht =
      branchTarget (D.restrict hs ht U' V' hU hV) ht ≫ map (Opens.inclusion hV)
        (contMDiff_inclusion hV) := by
  rw [← assembly_target D ht, ← Category.assoc, ← assembly_restriction,
    Category.assoc, arrowRestriction_target, ← Category.assoc, assembly_target]

/-- Smaller endpoint neighborhoods pull back the complete arrow sheaf. -/
theorem arrowRestriction_isPullback :
    IsPullback (arrowRestriction D hs ht U' V' hU hV)
      (prod.lift (source (D.restrict hs ht U' V' hU hV) hs)
        (target (D.restrict hs ht U' V' hU hV) ht))
      (prod.lift (source D hs) (target D ht))
      (prod.map (map (Opens.inclusion hU) (contMDiff_inclusion hU))
        (map (Opens.inclusion hV) (contMDiff_inclusion hV))) :=
  OpenRectangle.restriction_isPullback s hs t ht hU hV

/-- The same pullback on the genuine coproduct of source domains. -/
theorem branchRestriction_isPullback :
    IsPullback (branchRestriction D hs ht U' V' hU hV)
      (prod.lift (branchSource (D.restrict hs ht U' V' hU hV))
        (branchTarget (D.restrict hs ht U' V' hU hV) ht))
      (prod.lift (branchSource D) (branchTarget D ht))
      (prod.map (map (Opens.inclusion hU) (contMDiff_inclusion hU))
        (map (Opens.inclusion hV) (contMDiff_inclusion hV))) := by
  apply (arrowRestriction_isPullback D hs ht U' V' hU hV).of_iso'
    (assemblyIso (D.restrict hs ht U' V' hU hV)) (assemblyIso D) (Iso.refl _) (Iso.refl _)
  · simp only [assemblyIso_hom]
    exact assembly_restriction D hs ht U' V' hU hV
  · apply prod.hom_ext <;>
      simp only [assemblyIso_hom, Iso.refl_hom, Category.comp_id, Category.assoc,
        prod.lift_fst, prod.lift_snd, assembly_source, assembly_target]
  · apply prod.hom_ext <;>
      simp only [assemblyIso_hom, Iso.refl_hom, Category.comp_id, Category.assoc,
        prod.lift_fst, prod.lift_snd, assembly_source, assembly_target]
  · simp

end SquareKit.SmoothBranchRealization
