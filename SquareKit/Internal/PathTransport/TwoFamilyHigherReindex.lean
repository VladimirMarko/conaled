import SquareKit.Internal.PathTransport.TwoFamilyHigher

/-!
# Higher reindexing of two-families

Reindexing retains each fiber 2-cell and applies the substitution functor to its base
cell. The horizontal laws use the substitution's whiskering laws and equality
transports of the total composition boundaries.
-/
open CategoryTheory Bicategory
namespace SquareKit.Internal.PathTransport.TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000
universe u v w u' v' w'
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Bicategory.Strict Γ]
variable {Δ : Type*} [Bicategory Δ] [Bicategory.Strict Δ]
private theorem cell_comp_base (F : Family Γ) {x y : Total F}
    {p q r : x ⟶ y} (α : p ⟶ q) (β : q ⟶ r) :
    (α ≫ β).base = α.base ≫ β.base := rfl
private theorem cell_eqToHom_base (F : Family Γ) {x y : Total F}
    {p q : x ⟶ y} (h : p = q) :
    (eqToHom h).base = eqToHom (congrArg (fun r : x ⟶ y => r.base) h) := by
  cases h
  rfl

omit [Bicategory.Strict Γ] in
private theorem cell_transport_fiber_heq (F : Family Γ) {x y : Total F}
    {p p' q q' : Hom F x y} (hp : p = p') (hq : q = q') (α : p' ⟶ q') :
    HEq ((eqToHom hp ≫ α ≫ eqToHom hq.symm).fiber) α.fiber := by
  cases hp
  cases hq
  simp only [eqToHom_refl]
  rw [Category.comp_id α, Category.id_comp α]

/-- Reindexing preserves left whiskering, with its exact composition boundaries. -/
theorem reindex_whiskerLeft (F : Family Γ) (σ : StrictPseudofunctor Δ Γ)
    {x y z : Total (reindex σ F)} (p : Hom (reindex σ F) x y)
    {q r : Hom (reindex σ F) y z} (α : q ⟶ r) :
    (reindexHom σ F x z).map (TwoFamily.whiskerLeft (reindex σ F) p α) =
      eqToHom ((reindexFunctor F σ).map_comp p q) ≫
        TwoFamily.whiskerLeft F ((reindexFunctor F σ).map p) ((reindexHom σ F y z).map α) ≫
          eqToHom ((reindexFunctor F σ).map_comp p r).symm := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
  · simp only [cell_comp_base F, cell_eqToHom_base F]
    change σ.map₂ (p.base ◁ α.base) =
      eqToHom (σ.map_comp p.base q.base) ≫ σ.map p.base ◁ σ.map₂ α.base ≫
        eqToHom (σ.map_comp p.base r.base).symm
    simpa only [σ.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv] using
      σ.map₂_whisker_left p.base α.base
  · apply eq_of_heq
    apply HEq.trans (b := (F.map (σ.map q.base)).map p.fiber ◁ α.fiber)
    · change HEq ((compBoundary (reindex σ F) p.base q.base x.fiber ◁
        (F.map (σ.map q.base)).map p.fiber ◁ α.fiber) ≫ eqToHom _) _
      apply HEq.trans (comp_eqToHom_heq _ _)
      exact eqToHom_left_heq _ _
    · apply HEq.symm
      apply HEq.trans (comp_eqToHom_heq _ _)
      apply HEq.trans (cell_transport_fiber_heq F
        ((reindexFunctor F σ).map_comp p q) ((reindexFunctor F σ).map_comp p r) _)
      change HEq ((compBoundary F (σ.map p.base) (σ.map q.base) x.fiber ◁
        (F.map (σ.map q.base)).map p.fiber ◁ α.fiber) ≫ eqToHom _) _
      apply HEq.trans (comp_eqToHom_heq _ _)
      exact eqToHom_left_heq _ _
private theorem boundary_whiskerRight_heq {B : Type*} [Bicategory B] [Bicategory.Strict B]
    {a b c d : B} (h : a = b) {f g : b ⟶ c} (α : f ⟶ g) (q : c ⟶ d) :
    HEq ((eqToHom h ◁ α) ▷ q) (α ▷ q) := by
  rw [Bicategory.whisker_assoc]
  simp only [Bicategory.Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv]
  apply HEq.trans (eqToHom_comp_heq _ _)
  apply HEq.trans (comp_eqToHom_heq _ _)
  exact eqToHom_left_heq _ _

/-- Reindexing preserves right whiskering of genuine fiber cells. -/
theorem reindex_whiskerRight (F : Family Γ) (σ : StrictPseudofunctor Δ Γ)
    {x y z : Total (reindex σ F)} {p q : Hom (reindex σ F) x y}
    (α : p ⟶ q) (r : Hom (reindex σ F) y z) :
    (reindexHom σ F x z).map (TwoFamily.whiskerRight (reindex σ F) α r) =
      eqToHom ((reindexFunctor F σ).map_comp p r) ≫
        TwoFamily.whiskerRight F ((reindexHom σ F x y).map α) ((reindexFunctor F σ).map r) ≫
          eqToHom ((reindexFunctor F σ).map_comp q r).symm := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
  · simp only [cell_comp_base F, cell_eqToHom_base F]
    change σ.map₂ (α.base ▷ r.base) =
      eqToHom (σ.map_comp p.base r.base) ≫ σ.map₂ α.base ▷ σ.map r.base ≫
        eqToHom (σ.map_comp q.base r.base).symm
    simpa only [σ.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv] using
      σ.map₂_whisker_right α.base r.base
  · apply eq_of_heq
    apply HEq.trans (b := (F.map (σ.map r.base)).map₂ α.fiber ▷ r.fiber)
    · change HEq (eqToHom _ ≫
        (compBoundary (reindex σ F) p.base r.base x.fiber ◁
          (F.map (σ.map r.base)).map₂ α.fiber) ▷ r.fiber ≫ eqToHom _) _
      apply HEq.trans (eqToHom_comp_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _)
      exact boundary_whiskerRight_heq _ _ _
    · apply HEq.symm
      apply HEq.trans (comp_eqToHom_heq _ _)
      apply HEq.trans (cell_transport_fiber_heq F
        ((reindexFunctor F σ).map_comp p r) ((reindexFunctor F σ).map_comp q r) _)
      change HEq (eqToHom _ ≫
        (compBoundary F (σ.map p.base) (σ.map r.base) x.fiber ◁
          (F.map (σ.map r.base)).map₂ α.fiber) ▷ r.fiber ≫ eqToHom _) _
      apply HEq.trans (eqToHom_comp_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _)
      exact boundary_whiskerRight_heq _ _ _
/-- Substitution on context extensions preserves the full higher structure. -/
def reindexHigher (F : Family.{u,v,w,u',v',w'} Γ) (σ : StrictPseudofunctor Δ Γ) :
    StrictPseudofunctor (Total (reindex σ F)) (Total F) :=
  StrictPseudofunctor.mk'' {
    obj := (reindexFunctor F σ).obj
    map := (reindexFunctor F σ).map
    map₂ := fun {x y f g} α => (reindexHom σ F x y).map α
    map₂_id := fun p => (reindexHom σ F _ _).map_id p
    map₂_comp := fun α β => (reindexHom σ F _ _).map_comp α β
    map_id := (reindexFunctor F σ).map_id
    map_comp := (reindexFunctor F σ).map_comp
    map₂_whisker_left := by
      intro x y z p q r α
      exact reindex_whiskerLeft F σ p α
    map₂_whisker_right := by
      intro x y z p q α r
      exact reindex_whiskerRight F σ α r
  }

/-- Higher reindexing commutes strictly with extension projection. -/
theorem reindexHigher_projection (F : Family Γ) (σ : StrictPseudofunctor Δ Γ) :
    (reindexHigher F σ).comp (projectionHigher F) =
      (projectionHigher (reindex σ F)).comp σ :=
  StrictTwoTransformation.functor_ext rfl

end SquareKit.Internal.PathTransport.TwoFamily
