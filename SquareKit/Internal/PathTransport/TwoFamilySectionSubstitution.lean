import SquareKit.Internal.PathTransport.TwoFamilySections
/-! Substitution of arbitrary higher sections through the actual total construction. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w'
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Bicategory.Strict Γ]
variable {Δ : Type*} [Bicategory Δ] [Bicategory.Strict Δ]
variable (F : Family.{u,v,w,u',v',w'} Γ)
lemma reindex_reflects {σ : StrictPseudofunctor Δ Γ} {x y : Total (reindex σ F)}
    (p q : Hom (reindex σ F) x y) (hb : p.base = q.base)
    (h : (reindexFunctor F σ).map p = (reindexFunctor F σ).map q) : p = q := by
  apply Pseudofunctor.CoGrothendieck.ext
  · exact hb
  · exact congr_arg_heq (fun r => r.fiber) h

omit [Bicategory.Strict Γ] in
lemma reindex_reflects₂ {σ : StrictPseudofunctor Δ Γ} {x y : Total (reindex σ F)}
    {p q : Hom (reindex σ F) x y} (α β : p ⟶ q) (hb : α.base = β.base)
    (h : (reindexHom σ F x y).map α = (reindexHom σ F x y).map β) : α = β := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ hb ?_
  apply eq_of_heq
  exact HEq.trans (congr_arg_heq (fun γ => γ.fiber) h) (comp_eqToHom_heq _ _).symm

variable (h : StrictPseudofunctor Δ (Total F))
abbrev factorBase := h.comp (projectionHigher F)
abbrev factorObj (x : Δ) : Total (reindex (factorBase F h) F) := ⟨x,(h.obj x).fiber⟩
abbrev factorMap {x y : Δ} (p : x ⟶ y) : Hom (reindex (factorBase F h) F) (factorObj F h x) (factorObj F h y) :=
  ⟨p,(h.map p).fiber⟩
abbrev factorCell {x y : Δ} {p q : x ⟶ y} (α : p ⟶ q) : factorMap F h p ⟶ factorMap F h q :=
  ⟨α,(h.map₂ α).fiber⟩
lemma factorMap_id (x : Δ) : factorMap F h (𝟙 x) = identity _ (factorObj F h x) := by
  refine reindex_reflects F _ _ ?_ ?_
  · rfl
  · exact (h.map_id x).trans ((reindexFunctor F (factorBase F h)).map_id (factorObj F h x)).symm
lemma factorMap_comp {x y z : Δ} (p : x ⟶ y) (q : y ⟶ z) :
    factorMap F h (p ≫ q) = compose _ (factorMap F h p) (factorMap F h q) := by
  refine reindex_reflects F _ _ ?_ ?_
  · rfl
  · exact (h.map_comp p q).trans ((reindexFunctor F (factorBase F h)).map_comp (factorMap F h p) (factorMap F h q)).symm
lemma factorCell_id {x y : Δ} (p : x ⟶ y) :
    factorCell F h (𝟙 p) = 𝟙 (factorMap F h p) := by
  refine reindex_reflects₂ F _ _ ?_ ?_
  · rfl
  · exact (h.map₂_id p).trans ((reindexHom (factorBase F h) F _ _).map_id (factorMap F h p)).symm
lemma factorCell_comp {x y : Δ} {p q r : x ⟶ y} (α : p ⟶ q) (β : q ⟶ r) :
    factorCell F h (α ≫ β) = factorCell F h α ≫ factorCell F h β := by
  refine reindex_reflects₂ F _ _ ?_ ?_
  · rfl
  · exact (h.map₂_comp α β).trans ((reindexHom (factorBase F h) F _ _).map_comp
      (factorCell F h α) (factorCell F h β)).symm
private theorem cell_transport_fiber_heq {C B : Type*} [Category C] [Bicategory B]
    [Bicategory.Strict B] {E : C ⥤ B} {b : B}
    {p p' q q' : TwoGroupoidHom.Total E b} (hp : p = p') (hq : q = q') (α : p' ⟶ q) :
    HEq ((eqToHom hp ≫ α ≫ eqToHom hq).fiber) α.fiber := by
  cases hp
  cases hq
  simp only [eqToHom_refl]
  rw [Category.comp_id α, Category.id_comp α]

lemma factorCell_whiskerLeft {x y z : Δ} (p : x ⟶ y) {q r : y ⟶ z} (α : q ⟶ r) :
    factorCell F h (p ◁ α) = eqToHom (factorMap_comp F h p q) ≫
      TwoFamily.whiskerLeft _ (factorMap F h p) (factorCell F h α) ≫
        eqToHom (factorMap_comp F h p r).symm := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
  · simp [total_eqToHom_base, TwoFamily.whiskerLeft, TwoGroupoidHom.cell]
  · have h0 := h.map₂_whisker_left p α
    simp only [h.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv] at h0
    apply eq_of_heq
    refine HEq.trans (congr_arg_heq (fun β => β.fiber) h0) ?_
    refine HEq.trans (cell_transport_fiber_heq (h.map_comp p q) (h.map_comp p r).symm _) ?_
    refine HEq.trans ?_ ((HEq.trans (comp_eqToHom_heq _ _)
      (cell_transport_fiber_heq (factorMap_comp F h p q) (factorMap_comp F h p r).symm _)).symm)
    apply HEq.trans (b := (F.map (h.map q).base).map (h.map p).fiber ◁ (h.map₂ α).fiber)
    · change HEq ((compBoundary F (h.map p).base (h.map q).base (h.obj x).fiber ◁
        (F.map (h.map q).base).map (h.map p).fiber ◁ (h.map₂ α).fiber) ≫ eqToHom _) _
      exact HEq.trans (comp_eqToHom_heq _ _) (eqToHom_left_heq _ _)
    · apply HEq.symm
      change HEq ((compBoundary (reindex (factorBase F h) F) p q (h.obj x).fiber ◁
        (F.map (h.map q).base).map (h.map p).fiber ◁ (h.map₂ α).fiber) ≫ eqToHom _) _
      exact HEq.trans (comp_eqToHom_heq _ _) (eqToHom_left_heq _ _)
private theorem boundary_whiskerRight_heq {B : Type*} [Bicategory B] [Bicategory.Strict B]
    {a b c d : B} (e : a = b) {f g : b ⟶ c} (α : f ⟶ g) (q : c ⟶ d) :
    HEq ((eqToHom e ◁ α) ▷ q) (α ▷ q) := by
  rw [Bicategory.whisker_assoc]
  simp only [Bicategory.Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv]
  exact HEq.trans (eqToHom_comp_heq _ _) (HEq.trans (comp_eqToHom_heq _ _) (eqToHom_left_heq _ _))

lemma factorCell_whiskerRight {x y z : Δ} {p q : x ⟶ y} (α : p ⟶ q) (r : y ⟶ z) :
    factorCell F h (α ▷ r) = eqToHom (factorMap_comp F h p r) ≫
      TwoFamily.whiskerRight _ (factorCell F h α) (factorMap F h r) ≫
        eqToHom (factorMap_comp F h q r).symm := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
  · simp [total_eqToHom_base, TwoFamily.whiskerRight, TwoGroupoidHom.cell]
  · have h0 := h.map₂_whisker_right α r
    simp only [h.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv] at h0
    apply eq_of_heq
    refine HEq.trans (congr_arg_heq (fun β => β.fiber) h0) ?_
    refine HEq.trans (cell_transport_fiber_heq (h.map_comp p r) (h.map_comp q r).symm _) ?_
    refine HEq.trans ?_ ((HEq.trans (comp_eqToHom_heq _ _)
      (cell_transport_fiber_heq (factorMap_comp F h p r) (factorMap_comp F h q r).symm _)).symm)
    apply HEq.trans (b := (F.map (h.map r).base).map₂ (h.map₂ α).fiber ▷ (h.map r).fiber)
    · change HEq (eqToHom _ ≫ (compBoundary F (h.map p).base (h.map r).base (h.obj x).fiber ◁
        (F.map (h.map r).base).map₂ (h.map₂ α).fiber) ▷ (h.map r).fiber ≫ eqToHom _) _
      exact HEq.trans (eqToHom_comp_heq _ _) (HEq.trans (comp_eqToHom_heq _ _) (boundary_whiskerRight_heq _ _ _))
    · apply HEq.symm
      change HEq (eqToHom _ ≫ (compBoundary (reindex (factorBase F h) F) p r (h.obj x).fiber ◁
        (F.map (h.map r).base).map₂ (h.map₂ α).fiber) ▷ (h.map r).fiber ≫ eqToHom _) _
      exact HEq.trans (eqToHom_comp_heq _ _) (HEq.trans (comp_eqToHom_heq _ _) (boundary_whiskerRight_heq _ _ _))

/-- Factor a higher lift through its projected family, retaining every fiber cell. -/
def factorHigher : StrictPseudofunctor Δ (Total (reindex (factorBase F h) F)) :=
  StrictPseudofunctor.mk'' {
    obj := factorObj F h
    map := factorMap F h
    map₂ := factorCell F h
    map_id := factorMap_id F h
    map_comp := factorMap_comp F h
    map₂_id := factorCell_id F h
    map₂_comp := factorCell_comp F h
    map₂_whisker_left := factorCell_whiskerLeft F h
    map₂_whisker_right := factorCell_whiskerRight F h
  }
/-- Every higher lift supplies a section of its projected pullback family. -/
def sectionOfLift : Section (reindex (factorBase F h) F) where
  lift := factorHigher F h
  over := StrictTwoTransformation.functor_ext rfl

/-- Recombining the factorization recovers the original higher lift exactly. -/
theorem factorHigher_reindex : (factorHigher F h).comp (reindexHigher F (factorBase F h)) = h :=
  StrictTwoTransformation.functor_ext rfl
theorem Section.reindex_base (s : Section F) (σ : StrictPseudofunctor Δ Γ) :
    factorBase F (σ.comp s.lift) = σ := by
  calc
    factorBase F (σ.comp s.lift) = σ.comp (s.lift.comp (projectionHigher F)) :=
      StrictTwoTransformation.functor_ext rfl
    _ = σ.comp (StrictPseudofunctor.id Γ) := congrArg (fun k => σ.comp k) s.over
    _ = σ := StrictTwoTransformation.functor_comp_id σ

/-- Transport a section along equality of its structural family. -/
def Section.cast {F G : Family.{u,v,w,u',v',w'} Γ} (e : F = G) (s : Section F) : Section G := e ▸ s

/-- Substitute any higher section, using only its structural projection equation. -/
def Section.reindex (s : Section F) (σ : StrictPseudofunctor Δ Γ) : Section (TwoFamily.reindex σ F) :=
  Section.cast (congrArg (fun k => TwoFamily.reindex k F) (s.reindex_base F σ))
    (sectionOfLift F (σ.comp s.lift))

theorem Section.cast_cell_fiber {F G : Family.{u,v,w,u',v',w'} Γ} (e : F = G)
    (s : Section F) {x y : Γ} {p q : x ⟶ y} (α : p ⟶ q) :
    HEq (((Section.cast e s).lift.map₂ α).fiber) ((s.lift.map₂ α).fiber) := by
  cases e
  rfl

end SquareKit.Internal.PathTransport.TwoFamily
