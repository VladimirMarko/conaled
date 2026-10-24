import SquareKit.Internal.PresheafSetting
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! Universal properties of the experimental finite presheaf presentation.
The representing object lies in the presheaf slice over the original context. -/
namespace SquareKit.Internal.PresheafSetting
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite Limits
universe v
variable {J : Type v} [SmallCategory J]
variable {X Y Z W : Jᵒᵖ ⥤ Type}

/-- Equality in the chosen pullback retains both projections. -/
theorem pullback_ext {T : Presentation X} {σ : Y ⟶ X} {j : Jᵒᵖ}
    {a b : (pullback T σ).obj j} (hb : a.base = b.base)
    (ho : a.original = b.original) : a = b := by
  cases a; cases b; cases hb; cases ho; rfl

/-- The universal lift uses the existing equality-bearing pullback. -/
def pullbackLift (T : Presentation X) (σ : Y ⟶ X)
    (a : Z ⟶ total T) (b : Z ⟶ Y) (h : a ≫ projection T = b ≫ σ) :
    Z ⟶ pullback T σ where
  app j := ↾fun z => ⟨b.app j z, a.app j z, congrArg (fun f => f.app j z) h⟩
  naturality j k f := by
    ext z
    apply pullback_ext
    · exact NatTrans.naturality_apply b f z
    · change (a.app k (Z.map f z)) = ((pullback T σ).map f _).original
      rw [pullback_original_map]
      exact NatTrans.naturality_apply a f z

@[simp] theorem pullbackLift_original (T : Presentation X) (σ : Y ⟶ X)
    (a : Z ⟶ total T) (b : Z ⟶ Y) (h : a ≫ projection T = b ≫ σ) :
    pullbackLift T σ a b h ≫ pullbackOriginal T σ = a := by
  ext j z
  exact pullback_original T σ j _

@[simp] theorem pullbackLift_projection (T : Presentation X) (σ : Y ⟶ X)
    (a : Z ⟶ total T) (b : Z ⟶ Y) (h : a ≫ projection T = b ≫ σ) :
    pullbackLift T σ a b h ≫ pullbackProjection T σ = b := rfl

theorem pullback_hom_ext (T : Presentation X) (σ : Y ⟶ X)
    {a b : Z ⟶ pullback T σ}
    (ho : a ≫ pullbackOriginal T σ = b ≫ pullbackOriginal T σ)
    (hb : a ≫ pullbackProjection T σ = b ≫ pullbackProjection T σ) : a = b := by
  ext j z
  apply pullback_ext
  · exact congrArg (fun f => f.app j z) hb
  · have h := congrArg (fun f => f.app j z) ho
    change (pullbackOriginal T σ).app j (a.app j z) =
      (pullbackOriginal T σ).app j (b.app j z) at h
    rw [pullback_original, pullback_original] at h
    exact h

/-- Mathlib's limit interface for this chosen square, rather than a replacement limit. -/
theorem chosen_isPullback (T : Presentation X) (σ : Y ⟶ X) :
    IsPullback (pullbackOriginal T σ) (pullbackProjection T σ) (projection T) σ :=
  IsPullback.mk' (pullback_square T σ) (fun {_} {_ _} => pullback_hom_ext T σ)
    (fun {_} a b h => ⟨pullbackLift T σ a b h,
      pullbackLift_original T σ a b h, pullbackLift_projection T σ a b h⟩)

/-- Transport the universal property through the formation/substitution comparison. -/
theorem formed_isPullback (T : Presentation X) (σ : Y ⟶ X) :
    IsPullback (totalMap T σ) (projection (subst T σ)) (projection T) σ := by
  exact (chosen_isPullback T σ).of_iso (comparison T σ)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [pullbackOriginal])
    (by simp [pullbackProjection]) (by simp) (by simp)

/-- A classifying map is an actual morphism in the presheaf slice. -/
abbrev ClassifyingMap (T : Presentation X) (σ : Y ⟶ X) :=
  Over.mk σ ⟶ Over.mk (projection T)

noncomputable def classify (T : Presentation X) (σ : Y ⟶ X)
    (M : Model (subst T σ)) : ClassifyingMap T σ :=
  Over.homMk (M.toSection.graph ≫ totalMap T σ) (by
    change (M.toSection.graph ≫ totalMap T σ) ≫ projection T = σ
    rw [Category.assoc, totalMap_projection, ← Category.assoc, Section.graph_projection]
    simp)

/-- Pull back both actual generic predicates. The equation over X discharges
presentation transport once, inside the interface. -/
def representedModel (T : Presentation X) (σ : Y ⟶ X)
    (f : ClassifyingMap T σ) : Model (subst T σ) where
  P := (genericModel T).P.preimage f.left
  Q := (genericModel T).Q.preimage f.left
  satisfies j := by
    apply (FiniteSetting.satisfies_iff _ _ _).mpr
    have h := (FiniteSetting.satisfies_iff _ _ _).mp
      (((genericModel T).subst f.left).satisfies j)
    refine ⟨h.1, h.2.1, ?_⟩
    intro y hy
    have hw := congrArg (fun g => g.app j y) (Over.w f)
    change (f.left.app j y).1 = σ.app j y at hw
    change T.obj j (σ.app j y)
    rw [← hw]
    exact h.2.2 y hy

/-- Transport a model's presentation without changing either predicate. -/
def Model.cast {S T : Presentation X} (h : S = T) (M : Model S) : Model T := h ▸ M

@[simp] theorem Model.cast_P {S T : Presentation X} (h : S = T) (M : Model S) :
    (M.cast h).P = M.P := by cases h; rfl

@[simp] theorem Model.cast_Q {S T : Presentation X} (h : S = T) (M : Model S) :
    (M.cast h).Q = M.Q := by cases h; rfl

/-- Pullback of the generic model with its dependent presentation equality explicit. -/
theorem represented_generic (T : Presentation X) (σ : Y ⟶ X)
    (f : ClassifyingMap T σ) :
    representedModel T σ f = ((genericModel T).subst f.left).cast
      (congrArg (subst T) (Over.w f)) := by
  apply Model.ext; intro j
  apply FiniteSetting.Model.ext
  · change _ = (Model.cast _ _).P.obj j
    rw [Model.cast_P]; rfl
  · change _ = (Model.cast _ _).Q.obj j
    rw [Model.cast_Q]; rfl

@[simp] theorem represented_classify (T : Presentation X) (σ : Y ⟶ X)
    (M : Model (subst T σ)) : representedModel T σ (classify T σ M) = M := by
  apply Model.ext; intro j
  exact (M.stage j).toSection_toModel

/-- Uniqueness uses the complete model equality, together with the equation over X. -/
theorem represented_injective (T : Presentation X) (σ : Y ⟶ X) :
    Function.Injective (representedModel T σ) := by
  intro f g h
  apply Over.OverMorphism.ext
  ext j y
  apply total_ext
  · exact (congrArg (fun k => k.app j y) (Over.w f)).trans
      (congrArg (fun k => k.app j y) (Over.w g)).symm
  · apply Bool.eq_iff_iff.mpr
    exact iff_of_eq (congrArg (fun M => M.P.obj j y) h)

@[simp] theorem classify_represented (T : Presentation X) (σ : Y ⟶ X)
    (f : ClassifyingMap T σ) : classify T σ (representedModel T σ f) = f :=
  represented_injective T σ (represented_classify T σ _)

noncomputable def modelOverEquiv (T : Presentation X) (σ : Y ⟶ X) :
    Model (subst T σ) ≃ ClassifyingMap T σ where
  toFun := classify T σ
  invFun := representedModel T σ
  left_inv := represented_classify T σ
  right_inv := classify_represented T σ

/-- Reindex along any arrow over X, hiding its presentation equality. -/
def reindex (T : Presentation X) {A B : Over X} (u : A ⟶ B)
    (M : Model (subst T B.hom)) : Model (subst T A.hom) :=
  (M.subst u.left).cast (congrArg (subst T) (Over.w u))

@[simp] theorem reindex_id (T : Presentation X) (A : Over X)
    (M : Model (subst T A.hom)) : reindex T (𝟙 A) M = M := rfl

@[simp] theorem reindex_comp (T : Presentation X) {A B C : Over X}
    (u : A ⟶ B) (w : B ⟶ C) (M : Model (subst T C.hom)) :
    reindex T u (reindex T w M) = reindex T (u ≫ w) M := by
  apply Model.ext; intro j
  apply FiniteSetting.Model.ext <;>
    simp only [Model.stage, reindex, Model.cast_P, Model.cast_Q,
      Model.subst, Subfunctor.preimage_obj] <;> rfl

/-- Contravariant naturality on the whole presheaf slice. -/
theorem represented_natural (T : Presentation X) {A B : Over X}
    (u : A ⟶ B) (f : B ⟶ Over.mk (projection T)) :
    representedModel T A.hom (u ≫ f) = reindex T u (representedModel T B.hom f) := by
  apply Model.ext; intro j
  apply FiniteSetting.Model.ext <;>
    simp only [Model.stage, reindex, Model.cast_P, Model.cast_Q,
      Model.subst, representedModel, Subfunctor.preimage_obj] <;> rfl

theorem classify_natural (T : Presentation X) {A B : Over X}
    (u : A ⟶ B) (M : Model (subst T B.hom)) :
    classify T A.hom (reindex T u M) = u ≫ classify T B.hom M := by
  apply represented_injective T A.hom
  rw [represented_classify, represented_natural, represented_classify]

/-- The usual composable substitution needs no presentation transports from callers. -/
theorem classify_subst (T : Presentation X) (σ : Y ⟶ X) (τ : Z ⟶ Y)
    (M : Model (subst T σ)) :
    (classify T (τ ≫ σ) (M.subst τ)).left = τ ≫ (classify T σ M).left := by
  have h := classify_natural T (A := Over.mk (τ ≫ σ)) (B := Over.mk σ)
    (Over.homMk τ rfl) M
  exact congrArg (fun f => f.left) h

/-- The equivalence extends the existing model/section correspondence. -/
theorem classify_section (T : Presentation X) (σ : Y ⟶ X)
    (M : Model (subst T σ)) :
    (modelOverEquiv T σ M).left = (modelSectionEquiv (subst T σ) M).graph ≫ totalMap T σ := rfl

/-- Universal lifting recovers the formed section through the original comparison. -/
theorem classify_comparison (T : Presentation X) (σ : Y ⟶ X)
    (M : Model (subst T σ)) :
    pullbackLift T σ (classify T σ M).left (𝟙 Y) (by simpa using Over.w (classify T σ M)) ≫
      (comparison T σ).hom = M.toSection.graph := by
  apply (cancel_mono (comparison T σ).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply pullback_hom_ext T σ
  · rw [pullbackLift_original]
    simp [pullbackOriginal, classify]
  · rw [pullbackLift_projection]
    simp [pullbackProjection, Section.graph_projection]

/-- The generic model classifies the identity of the representing slice object. -/
theorem classify_generic (T : Presentation X) :
    classify T (projection T) (genericModel T) = 𝟙 (Over.mk (projection T)) := by
  apply represented_injective T (projection T)
  rw [represented_classify]
  rfl

/-- Graph soundness over the represented model uses the existing source derivations. -/
theorem represented_graph (T : Presentation X) (σ : Y ⟶ X)
    (M : Model (subst T σ)) :
    (Presheaf.graphModel (classify T σ M).left (tag T)).formula
      (Graph.composite .first .second) =
    (Presheaf.graphModel (classify T σ M).left (tag T)).formula
      (Graph.result .first .second) := Presheaf.graph_valid _ _

/-- Its true observation is precisely the represented P predicate. -/
theorem represented_graph_P (T : Presentation X) (σ : Y ⟶ X)
    (M : Model (subst T σ)) (j : Jᵒᵖ) (y : Y.obj j) :
    (∃ a : (total T).obj j, a = (classify T σ M).left.app j y ∧
      true = (tag T).app j a) ↔ M.P.obj j y := by
  have h := Presheaf.graph_evaluation (classify T σ M).left (tag T) j y true
  apply h.trans
  have hm := congrArg (fun N => N.P.obj j y) (represented_classify T σ M)
  exact eq_comm.trans (iff_of_eq hm)

end SquareKit.Internal.PresheafSetting
