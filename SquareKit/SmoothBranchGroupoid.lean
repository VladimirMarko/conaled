import SquareKit.SheafGroupoidChart
import SquareKit.SmoothBranchComparison

/-! Smooth branch diagrams give complete coordinate charts for represented
sheaf groupoids, retaining the actual arrows and both lifted endpoints. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped Manifold ContDiff
namespace SquareKit.SmoothBranchGroupoid
open ManifoldRealization Orbifolds.LocalBranches SmoothBranchRealization
open SmoothBranchComparison SmoothOpenSite

variable {a x : ℕ} {A X J K : Type}
  [TopologicalSpace A] [ChartedSpace (Space a) A] [IsManifold (modelWithCorners a) ∞ A]
  [TopologicalSpace X] [ChartedSpace (Space x) X] [IsManifold (modelWithCorners x) ∞ X]
  {s t : A → X} {U V : Opens X}
  (D : Diagram (modelWithCorners a) (modelWithCorners x) s t U V J)
  (hs : ContMDiff (modelWithCorners a) (modelWithCorners x) ∞ s)
  (ht : ContMDiff (modelWithCorners a) (modelWithCorners x) ∞ t)

/-- Reconstruct an arrow in the full geometric arrow space. -/
def geometricAssembly : branches D ⟶ object a A :=
  assembly D ≫ map (Subtype.val : D.region → A) contMDiff_subtype_val

/-- Open endpoint restriction and canonical assembly supply the complete pullback. -/
theorem geometric_isPullback :
    IsPullback (geometricAssembly D) (prod.lift (branchSource D) (branchTarget D ht))
      (prod.lift (map s hs) (map t ht))
      (prod.map (map (Subtype.val : U → X) contMDiff_subtype_val)
        (map (Subtype.val : V → X) contMDiff_subtype_val)) := by
  apply (OpenRectangle.isPullback s hs t ht U V).of_iso'
    (assemblyIso D) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [assemblyIso_hom, geometricAssembly, Iso.refl_hom, Category.comp_id]
    rfl
  · apply prod.hom_ext
    · simp only [assemblyIso_hom, Iso.refl_hom, Category.comp_id, Category.assoc, prod.lift_fst]
      change assembly D ≫ source D hs = branchSource D
      exact assembly_source D hs
    · simp only [assemblyIso_hom, Iso.refl_hom, Category.comp_id, Category.assoc, prod.lift_snd]
      change assembly D ≫ target D ht = branchTarget D ht
      exact assembly_target D ht
  · simp
  · simp

variable (G : SheafGroupoid.Operations topology)
  (objectsIso : object x X ≅ G.objects) (arrowsIso : object a A ≅ G.arrows)
  (source_eq : map s hs ≫ objectsIso.hom = arrowsIso.hom ≫ G.source)
  (target_eq : map t ht ≫ objectsIso.hom = arrowsIso.hom ≫ G.target)

/-- The adapter asks only how the supplied source and target maps are represented.
The pullback and all coordinate recovery are proved from the smooth diagram. -/
def chart : SheafGroupoid.Chart G
    (map (Subtype.val : U → X) contMDiff_subtype_val ≫ objectsIso.hom)
    (map (Subtype.val : V → X) contMDiff_subtype_val ≫ objectsIso.hom) where
  coordinates := branches D
  source := branchSource D
  target := branchTarget D ht
  assembly := geometricAssembly D ≫ arrowsIso.hom
  isPullback := by
    apply (geometric_isPullback D hs ht).of_iso' (Iso.refl _) arrowsIso.symm
      (Iso.refl _) (prod.mapIso objectsIso.symm objectsIso.symm)
    · simp
    · simp
    · apply prod.hom_ext
      · simp only [Category.assoc, prod.lift_fst, prod.mapIso_hom, Iso.symm_hom,
          prod.map_fst, prod.lift_fst_assoc]
        apply (cancel_mono objectsIso.hom).mp
        simp [Category.assoc, source_eq]
      · simp only [Category.assoc, prod.lift_snd, prod.mapIso_hom, Iso.symm_hom,
          prod.map_snd, prod.lift_snd_assoc]
        apply (cancel_mono objectsIso.hom).mp
        simp [Category.assoc, target_eq]
    · apply prod.hom_ext <;> simp


/-- The generic coordinate arrow reconstructs the original smooth assembly. -/
@[simp] theorem chart_assembly :
    (chart D hs ht G objectsIso arrowsIso source_eq target_eq).assembly =
      assembly D ≫ map (Subtype.val : D.region → A) contMDiff_subtype_val ≫ arrowsIso.hom := rfl

@[reassoc] theorem chart_decompose_assembly :
    decompose D ≫ (chart D hs ht G objectsIso arrowsIso source_eq target_eq).assembly =
      map (Subtype.val : D.region → A) contMDiff_subtype_val ≫ arrowsIso.hom := by
  rw [chart_assembly, decompose_assembly_assoc]

/-- The original stage endpoint-fiber comparison is the coordinate fiber of this chart. -/
def stageFiberEquiv (T : SmoothPresentationSite.Site)
    (u : (object x U).obj.obj (op T)) (v : (object x V).obj.obj (op T)) :
    ArrowFiber D hs ht T u v ≃
      {z : (chart D hs ht G objectsIso arrowsIso source_eq target_eq).coordinates.obj.obj (op T) //
        (chart D hs ht G objectsIso arrowsIso source_eq target_eq).source.hom.app (op T) z = u ∧
        (chart D hs ht G objectsIso arrowsIso source_eq target_eq).target.hom.app (op T) z = v} :=
  fiberEquiv D hs ht T u v

/-- Endpoint-fiber recovery reconstructs the same full arrow, at every site stage. -/
theorem stageFiberEquiv_recovery (T : SmoothPresentationSite.Site)
    (u : (object x U).obj.obj (op T)) (v : (object x V).obj.obj (op T))
    (z : ArrowFiber D hs ht T u v) :
    (chart D hs ht G objectsIso arrowsIso source_eq target_eq).assembly.hom.app (op T)
      (stageFiberEquiv D hs ht G objectsIso arrowsIso source_eq target_eq T u v z).val =
      arrowsIso.hom.hom.app (op T)
        ((map (Subtype.val : D.region → A) contMDiff_subtype_val).hom.app (op T) z.val) :=
  congrArg (fun f : arrowObject D ⟶ G.arrows => f.hom.app (op T) z.val)
    (chart_decompose_assembly D hs ht G objectsIso arrowsIso source_eq target_eq)

variable (E : Diagram (modelWithCorners a) (modelWithCorners x) s t U V K)
  {T : Sheaf topology Type} (m : T ⟶ object x U) (n : T ⟶ object x V)

/-- The generic reconstructed coordinate change is the independent smooth-chart comparison. -/
theorem comparison_map
    (f : (chart D hs ht G objectsIso arrowsIso source_eq target_eq).Arrow m n) :
    ((chart D hs ht G objectsIso arrowsIso source_eq target_eq).comparison
      (chart E hs ht G objectsIso arrowsIso source_eq target_eq) m n f).val =
      f.val ≫ (comparisonIso D E).hom := by
  let g : (chart E hs ht G objectsIso arrowsIso source_eq target_eq).Arrow m n :=
    ⟨f.val ≫ (comparisonIso D E).hom, by
      constructor
      · change (f.val ≫ (comparisonIso D E).hom) ≫ branchSource E = m
        rw [Category.assoc, comparison_source D E hs]
        exact f.property.1
      · change (f.val ≫ (comparisonIso D E).hom) ≫ branchTarget E ht = n
        rw [Category.assoc, comparison_target D E ht]
        exact f.property.2⟩
  have he : (chart D hs ht G objectsIso arrowsIso source_eq target_eq).comparison
      (chart E hs ht G objectsIso arrowsIso source_eq target_eq) m n f = g := by
    apply ((chart E hs ht G objectsIso arrowsIso source_eq target_eq).arrowEquiv m n).injective
    rw [SheafGroupoid.Chart.comparison_recovery]
    apply SheafGroupoid.Operations.Arrow.ext
    change f.val ≫ (assembly D ≫ _ ≫ _) =
      (f.val ≫ (comparisonIso D E).hom) ≫ (assembly E ≫ _ ≫ _)
    simp only [Category.assoc, comparison_assembly_assoc]
    rfl
  exact congrArg Subtype.val he


/-- Smaller endpoint rectangles retain the actual full-arrow assembly. -/
@[reassoc] theorem chart_restriction (U' V' : Opens X) (hU : U' ≤ U) (hV : V' ≤ V) :
    branchRestriction D hs ht U' V' hU hV ≫
      (chart D hs ht G objectsIso arrowsIso source_eq target_eq).assembly =
    (chart (D.restrict hs ht U' V' hU hV) hs ht G objectsIso arrowsIso source_eq target_eq).assembly := by
  let D' := D.restrict hs ht U' V' hU hV
  have hi : arrowRestriction D hs ht U' V' hU hV ≫
      map (Subtype.val : D.region → A) contMDiff_subtype_val =
      map (Subtype.val : D'.region → A) contMDiff_subtype_val := by
    rw [arrowRestriction, ← map_comp]
    rfl
  rw [chart_assembly, chart_assembly, ← Category.assoc,
    ← assembly_restriction, Category.assoc]
  exact congrArg (fun k => assembly D' ≫ k ≫ arrowsIso.hom) hi |>.trans (by rfl)

/-- The chart restriction square is the original complete branch pullback. -/
theorem chart_restriction_isPullback (U' V' : Opens X) (hU : U' ≤ U) (hV : V' ≤ V) :
    IsPullback (branchRestriction D hs ht U' V' hU hV)
      (prod.lift
        (chart (D.restrict hs ht U' V' hU hV) hs ht G objectsIso arrowsIso source_eq target_eq).source
        (chart (D.restrict hs ht U' V' hU hV) hs ht G objectsIso arrowsIso source_eq target_eq).target)
      (prod.lift (chart D hs ht G objectsIso arrowsIso source_eq target_eq).source
        (chart D hs ht G objectsIso arrowsIso source_eq target_eq).target)
      (prod.map (map (Opens.inclusion hU) (contMDiff_inclusion hU))
        (map (Opens.inclusion hV) (contMDiff_inclusion hV))) :=
  branchRestriction_isPullback D hs ht U' V' hU hV

end SquareKit.SmoothBranchGroupoid
