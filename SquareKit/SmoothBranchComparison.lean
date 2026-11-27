import SquareKit.SmoothBranchRestriction

/-! Independent branch diagrams compare through the actual arrow sheaf.
No common index type or fixed permutation of indices is required. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace Opposite
open scoped Manifold ContDiff
namespace SquareKit.SmoothBranchComparison
open ManifoldRealization Orbifolds.LocalBranches SmoothBranchRealization

variable {a x y : ℕ} {A X Y J K L : Type}
  [TopologicalSpace A] [ChartedSpace (Space a) A] [IsManifold (modelWithCorners a) ∞ A]
  [TopologicalSpace X] [ChartedSpace (Space x) X] [IsManifold (modelWithCorners x) ∞ X]
  [TopologicalSpace Y] [ChartedSpace (Space y) Y] [IsManifold (modelWithCorners y) ∞ Y]
  {s : A → X} {t : A → Y} {U : Opens X} {V : Opens Y}
  (D : Diagram (modelWithCorners a) (modelWithCorners x) s t U V J)
  (E : Diagram (modelWithCorners a) (modelWithCorners x) s t U V K)
  (F : Diagram (modelWithCorners a) (modelWithCorners x) s t U V L)

/-- The source domain where one old branch meets one independently chosen branch. -/
def overlapDomain (i : J) (j : K) : Opens X :=
  D.restrictedDomain i (D.piece i ⊓ E.piece j) inf_le_left

/-- The overlap uses the original source coordinate on the actual arrow intersection. -/
def overlapSourceEquiv (i : J) (j : K) :
    Diffeomorph (modelWithCorners a) (modelWithCorners x)
      (D.piece i ⊓ E.piece j : Opens A) (overlapDomain D E i j) ∞ :=
  D.restrictedSourceEquiv i (D.piece i ⊓ E.piece j) inf_le_left

omit [IsManifold (modelWithCorners a) ∞ A] [IsManifold (modelWithCorners x) ∞ X] in
theorem overlapDomain_cover (i : J) (z : D.domain i) :
    ∃ j, z.val ∈ overlapDomain D E i j := by
  let b := (D.sourceEquiv i).symm z
  obtain ⟨j, hj⟩ := (E.covers b.val).mp (D.piece_le_region i b.property)
  refine ⟨j, b.val, ⟨b.property, hj⟩, ?_⟩
  exact (D.source_eq i b).symm.trans
    (congrArg Subtype.val ((D.sourceEquiv i).apply_symm_apply z))

/-- Reconstruct the actual arrow before choosing its coordinates in the other diagram. -/
def comparisonIso : branches D ≅ branches E := assemblyIso D ≪≫ (assemblyIso E).symm

theorem comparisonIso_hom : (comparisonIso D E).hom = assembly D ≫ decompose E := by
  simp only [comparisonIso, Iso.trans_hom, Iso.symm_hom, assemblyIso_hom]
  rfl

@[reassoc (attr := simp)] theorem comparison_assembly :
    (comparisonIso D E).hom ≫ assembly E = assembly D := by
  rw [comparisonIso_hom, Category.assoc, decompose_assembly]
  exact Category.comp_id (assembly D)

@[simp] theorem comparison_refl : (comparisonIso D D).hom = 𝟙 _ := by
  rw [comparisonIso_hom, assembly_decompose]

@[reassoc (attr := simp)] theorem comparison_trans :
    (comparisonIso D E).hom ≫ (comparisonIso E F).hom = (comparisonIso D F).hom := by
  rw [comparisonIso_hom, comparisonIso_hom, comparisonIso_hom]
  simp only [Category.assoc, decompose_assembly_assoc]

@[simp] theorem comparison_symm : (comparisonIso D E).inv = (comparisonIso E D).hom := by
  simp only [comparisonIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv]

variable (hs : ContMDiff (modelWithCorners a) (modelWithCorners x) ∞ s)
  (ht : ContMDiff (modelWithCorners a) (modelWithCorners y) ∞ t)

include hs in
@[reassoc] theorem comparison_source :
    (comparisonIso D E).hom ≫ branchSource E = branchSource D := by
  rw [comparisonIso_hom, Category.assoc, decompose_source E hs]
  exact assembly_source D hs

@[reassoc] theorem comparison_target :
    (comparisonIso D E).hom ≫ branchTarget E ht = branchTarget D ht := by
  rw [comparisonIso_hom, Category.assoc, decompose_target E ht]
  exact assembly_target D ht

/-- All generalized sections, including locally varying choices of branch. -/
def stageComparison (T : SmoothPresentationSite.Site) :
    (branches D).obj.obj (op T) ≃ (branches E).obj.obj (op T) where
  toFun := (comparisonIso D E).hom.hom.app (op T)
  invFun := (comparisonIso D E).inv.hom.app (op T)
  left_inv z := congrArg (fun f : branches D ⟶ branches D => f.hom.app (op T) z)
    (comparisonIso D E).hom_inv_id
  right_inv z := congrArg (fun f : branches E ⟶ branches E => f.hom.app (op T) z)
    (comparisonIso D E).inv_hom_id

theorem stageComparison_restrict {T W : SmoothPresentationSite.Site} (r : W ⟶ T)
    (z : (branches D).obj.obj (op T)) :
    stageComparison D E W ((branches D).obj.map r.op z) =
      (branches E).obj.map r.op (stageComparison D E T z) :=
  NatTrans.naturality_apply (comparisonIso D E).hom.hom r.op z

theorem stageComparison_symm_restrict {T W : SmoothPresentationSite.Site} (r : W ⟶ T)
    (z : (branches E).obj.obj (op T)) :
    (stageComparison D E W).symm ((branches E).obj.map r.op z) =
      (branches D).obj.map r.op ((stageComparison D E T).symm z) :=
  NatTrans.naturality_apply (comparisonIso D E).inv.hom r.op z

omit [IsManifold (modelWithCorners y) ∞ Y] in
/-- Changing coordinates commutes with shrinking both endpoint windows. -/
@[reassoc] theorem comparison_restriction
    (U' : Opens X) (V' : Opens Y) (hU : U' ≤ U) (hV : V' ≤ V) :
    (comparisonIso (D.restrict hs ht U' V' hU hV)
      (E.restrict hs ht U' V' hU hV)).hom ≫ branchRestriction E hs ht U' V' hU hV =
    branchRestriction D hs ht U' V' hU hV ≫ (comparisonIso D E).hom := by
  let D' := D.restrict hs ht U' V' hU hV
  let E' := E.restrict hs ht U' V' hU hV
  change (comparisonIso D' E').hom ≫ _ = _
  rw [comparisonIso_hom D' E', Category.assoc,
    ← decompose_restriction E hs ht U' V' hU hV]
  change assembly D' ≫ (arrowRestriction D hs ht U' V' hU hV ≫ decompose E) = _
  rw [← Category.assoc, assembly_restriction D hs ht U' V' hU hV,
    Category.assoc, ← comparisonIso_hom D E]

section DifferentRectangles
variable {U₁ U₂ U₃ : Opens X} {V₁ V₂ V₃ : Opens Y}
  (D₁ : Diagram (modelWithCorners a) (modelWithCorners x) s t U₁ V₁ J)
  (D₂ : Diagram (modelWithCorners a) (modelWithCorners x) s t U₂ V₂ K)
  (D₃ : Diagram (modelWithCorners a) (modelWithCorners x) s t U₃ V₃ L)

/-- Any common endpoint refinement compares the two independent diagrams. -/
def commonComparisonIso (W : Opens X) (Z : Opens Y)
    (h₁ : W ≤ U₁) (k₁ : Z ≤ V₁) (h₂ : W ≤ U₂) (k₂ : Z ≤ V₂) :
    branches (D₁.restrict hs ht W Z h₁ k₁) ≅
      branches (D₂.restrict hs ht W Z h₂ k₂) :=
  comparisonIso (D₁.restrict hs ht W Z h₁ k₁) (D₂.restrict hs ht W Z h₂ k₂)

/-- Comparison on the actual intersection of the endpoint rectangles. -/
def overlapComparisonIso :
    branches (D₁.restrict hs ht (U₁ ⊓ U₂) (V₁ ⊓ V₂) inf_le_left inf_le_left) ≅
      branches (D₂.restrict hs ht (U₁ ⊓ U₂) (V₁ ⊓ V₂) inf_le_right inf_le_right) :=
  commonComparisonIso hs ht D₁ D₂ _ _ inf_le_left inf_le_left inf_le_right inf_le_right

omit [IsManifold (modelWithCorners y) ∞ Y] in
/-- Triple compatibility is stated on one actual common rectangle. -/
theorem commonComparison_trans (W : Opens X) (Z : Opens Y)
    (h₁ : W ≤ U₁) (k₁ : Z ≤ V₁) (h₂ : W ≤ U₂) (k₂ : Z ≤ V₂)
    (h₃ : W ≤ U₃) (k₃ : Z ≤ V₃) :
    (commonComparisonIso hs ht D₁ D₂ W Z h₁ k₁ h₂ k₂).hom ≫
      (commonComparisonIso hs ht D₂ D₃ W Z h₂ k₂ h₃ k₃).hom =
    (commonComparisonIso hs ht D₁ D₃ W Z h₁ k₁ h₃ k₃).hom :=
  comparison_trans _ _ _

omit [IsManifold (modelWithCorners y) ∞ Y] in
theorem commonComparison_refl (W : Opens X) (Z : Opens Y)
    (h₁ : W ≤ U₁) (k₁ : Z ≤ V₁) :
    (commonComparisonIso hs ht D₁ D₁ W Z h₁ k₁ h₁ k₁).hom = 𝟙 _ :=
  comparison_refl _

omit [IsManifold (modelWithCorners y) ∞ Y] in
theorem commonComparison_symm (W : Opens X) (Z : Opens Y)
    (h₁ : W ≤ U₁) (k₁ : Z ≤ V₁) (h₂ : W ≤ U₂) (k₂ : Z ≤ V₂) :
    (commonComparisonIso hs ht D₁ D₂ W Z h₁ k₁ h₂ k₂).inv =
      (commonComparisonIso hs ht D₂ D₁ W Z h₂ k₂ h₁ k₁).hom :=
  comparison_symm _ _

end DifferentRectangles
end SquareKit.SmoothBranchComparison
