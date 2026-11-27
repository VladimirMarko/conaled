import SquareKit.SmoothManifoldOpenPullback
import SquareKit.RectanglePullback

/-! Open rectangles retain both endpoint maps at every sheaf stage. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Set
open scoped Manifold ContDiff
namespace SquareKit.ManifoldRealization.OpenRectangle

variable {a m n : ℕ} {A M N : Type}
  [TopologicalSpace A] [ChartedSpace (Space a) A] [IsManifold (modelWithCorners a) ∞ A]
  [TopologicalSpace M] [ChartedSpace (Space m) M] [IsManifold (modelWithCorners m) ∞ M]
  [TopologicalSpace N] [ChartedSpace (Space n) N] [IsManifold (modelWithCorners n) ∞ N]
  (f : A → M) (hf : ContMDiff (modelWithCorners a) (modelWithCorners m) ∞ f)
  (g : A → N) (hg : ContMDiff (modelWithCorners a) (modelWithCorners n) ∞ g)
  (U : Opens M) (V : Opens N)

def domain : Opens A := ⟨{x | f x ∈ U ∧ g x ∈ V},
  (U.isOpen.preimage hf.continuous).inter (V.isOpen.preimage hg.continuous)⟩

def first (x : domain f hf g hg U V) : U := ⟨f x.val, x.property.1⟩
def second (x : domain f hf g hg U V) : V := ⟨g x.val, x.property.2⟩

omit [IsManifold (modelWithCorners a) ∞ A] [IsManifold (modelWithCorners m) ∞ M]
  [IsManifold (modelWithCorners n) ∞ N] in
theorem first_smooth : ContMDiff (modelWithCorners a) (modelWithCorners m) ∞
    (first f hf g hg U V) :=
  (ContMDiff.subtypeVal_comp_iff U _).mp (hf.comp contMDiff_subtype_val)

omit [IsManifold (modelWithCorners a) ∞ A] [IsManifold (modelWithCorners m) ∞ M]
  [IsManifold (modelWithCorners n) ∞ N] in
theorem second_smooth : ContMDiff (modelWithCorners a) (modelWithCorners n) ∞
    (second f hf g hg U V) :=
  (ContMDiff.subtypeVal_comp_iff V _).mp (hg.comp contMDiff_subtype_val)

private abbrev nested := OpenPullback.domain
  (g ∘ (Subtype.val : OpenPullback.domain f hf U → A))
  (hg.comp contMDiff_subtype_val) V

private def nestedEquiv : Diffeomorph (modelWithCorners a) (modelWithCorners a)
    (domain f hf g hg U V) (nested f hf g hg U V) ∞ where
  toFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  invFun x := ⟨x.val.val, x.val.property, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    exact contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (domain f hf g hg U V) _).mp
    exact (contMDiff_subtype_val (U := OpenPullback.domain f hf U)).comp
      (contMDiff_subtype_val (U := nested f hf g hg U V))

/-- This pullback compares full sections; the endpoint map needs no transversality premise. -/
theorem isPullback :
    IsPullback (map (Subtype.val : domain f hf g hg U V → A) contMDiff_subtype_val)
      (prod.lift (map (first f hf g hg U V) (first_smooth f hf g hg U V))
        (map (second f hf g hg U V) (second_smooth f hf g hg U V)))
      (prod.lift (map f hf) (map g hg))
      (prod.map (map (Subtype.val : U → M) contMDiff_subtype_val)
        (map (Subtype.val : V → N) contMDiff_subtype_val)) := by
  have h₁ := OpenPullback.isPullback (m := a) (n := m) f hf U
  have h₂ := OpenPullback.isPullback (m := a) (n := n)
    (g ∘ (Subtype.val : OpenPullback.domain f hf U → A))
    (hg.comp (contMDiff_subtype_val (I := modelWithCorners a)
      (U := OpenPullback.domain f hf U))) V
  rw [map_comp (n := a) (m := a) (p := n)
    (Subtype.val : OpenPullback.domain f hf U → A) g contMDiff_subtype_val hg] at h₂
  apply (rectangle_isPullback h₁ h₂).of_iso'
    (diffeomorphIso (nestedEquiv f hf g hg U V))
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [diffeomorphIso, ← map_comp, Iso.refl_hom, Category.comp_id]
    rfl
  · apply prod.hom_ext <;>
      simp only [Iso.refl_hom, Category.comp_id, Category.assoc,
        prod.lift_fst, prod.lift_snd, diffeomorphIso, ← map_comp] <;> rfl
  · simp
  · simp

variable {U V} {U' : Opens M} {V' : Opens N} (hU : U' ≤ U) (hV : V' ≤ V)

def inclusion : domain f hf g hg U' V' → domain f hf g hg U V :=
  Opens.inclusion (fun _ h => ⟨hU h.1, hV h.2⟩)

omit [IsManifold (modelWithCorners a) ∞ A] [IsManifold (modelWithCorners m) ∞ M]
  [IsManifold (modelWithCorners n) ∞ N] in
theorem inclusion_smooth : ContMDiff (modelWithCorners a) (modelWithCorners a) ∞
    (inclusion f hf g hg hU hV) :=
  contMDiff_inclusion (U := domain f hf g hg U' V') (V := domain f hf g hg U V)
    (fun _ h => ⟨hU h.1, hV h.2⟩)

/-- Shrinking either endpoint window is a pullback of complete interpreted sections. -/
theorem restriction_isPullback :
    IsPullback (map (inclusion f hf g hg hU hV) (inclusion_smooth f hf g hg hU hV))
      (prod.lift (map (first f hf g hg U' V') (first_smooth f hf g hg U' V'))
        (map (second f hf g hg U' V') (second_smooth f hf g hg U' V')))
      (prod.lift (map (first f hf g hg U V) (first_smooth f hf g hg U V))
        (map (second f hf g hg U V) (second_smooth f hf g hg U V)))
      (prod.map (map (Opens.inclusion hU) (contMDiff_inclusion hU))
        (map (Opens.inclusion hV) (contMDiff_inclusion hV))) := by
  apply IsPullback.of_right (h₁₂ := map
    (Subtype.val : domain f hf g hg U V → A) contMDiff_subtype_val)
    (h₂₂ := prod.map (map (Subtype.val : U → M) contMDiff_subtype_val)
      (map (Subtype.val : V → N) contMDiff_subtype_val))
  · simpa only [prod.map_map, ← map_comp, inclusion, Opens.inclusion, Function.comp_def] using
      isPullback f hf g hg U' V'
  · apply prod.hom_ext <;>
      simp only [Category.assoc, prod.lift_fst, prod.lift_snd, prod.map_fst,
        prod.map_snd, prod.lift_fst_assoc, prod.lift_snd_assoc, ← map_comp] <;> rfl
  · exact isPullback f hf g hg U V

end SquareKit.ManifoldRealization.OpenRectangle
