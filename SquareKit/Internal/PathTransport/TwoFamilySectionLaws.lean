import SquareKit.Internal.PathTransport.TwoFamilySectionSubstitution
/-! Extensionality and identity substitution for arbitrary higher sections. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w'
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Bicategory.Strict Γ]
variable {Δ : Type*} [Bicategory Δ] [Bicategory.Strict Δ]
variable (F : Family.{u,v,w,u',v',w'} Γ)
private theorem prelax_ext {A B : Type*} [Bicategory A] [Bicategory B]
    (H K : PrelaxFunctor A B) (ho : ∀ x, H.obj x = K.obj x)
    (hm : ∀ {x y} (p : x ⟶ y), HEq (H.map p) (K.map p))
    (hc : ∀ {x y} {p q : x ⟶ y} (α : p ⟶ q), HEq (H.map₂ α) (K.map₂ α)) : H = K := by
  rcases H with ⟨⟨⟨Ho,Hm⟩,Hc⟩,_,_⟩
  rcases K with ⟨⟨⟨Ko,Km⟩,Kc⟩,_,_⟩
  have hO : Ho = Ko := funext ho
  subst Ko
  have hM : @Hm = @Km := by
    funext x y p
    exact eq_of_heq (hm p)
  subst Km
  have hC : @Hc = @Kc := by
    funext x y p q α
    exact eq_of_heq (hc α)
  subst Kc
  rfl
omit [Bicategory.Strict Γ] in
private theorem total_ext {x y : Total F} (hb : x.base = y.base)
    (hf : HEq x.fiber y.fiber) : x = y := by
  rcases x with ⟨x,a⟩
  rcases y with ⟨y,b⟩
  dsimp at hb hf
  subst y
  cases eq_of_heq hf
  rfl
omit [Bicategory.Strict Γ] in
private theorem hom_hext {x x' y y' : Total F} (hx : x = x') (hy : y = y')
    (p : Hom F x y) (q : Hom F x' y') (hb : HEq p.base q.base)
    (hf : HEq p.fiber q.fiber) : HEq p q := by
  subst x'
  subst y'
  apply heq_of_eq
  exact Pseudofunctor.CoGrothendieck.ext (eq_of_heq hb) hf
omit [Bicategory.Strict Γ] in
private theorem cell_hext {x x' y y' : Total F} (hx : x = x') (hy : y = y')
    {p q : Hom F x y} {p' q' : Hom F x' y'} (hp : HEq p p') (hq : HEq q q')
    (α : p ⟶ q) (β : p' ⟶ q') (hb : HEq α.base β.base)
    (hf : HEq α.fiber β.fiber) : HEq α β := by
  subst x'
  subst y'
  cases eq_of_heq hp
  cases eq_of_heq hq
  apply heq_of_eq
  apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ (eq_of_heq hb)
  exact eq_of_heq (HEq.trans hf (comp_eqToHom_heq _ _).symm)

theorem Section.ext_fiber (s t : Section F)
    (ho : ∀ x, HEq (s.lift.obj x).fiber (t.lift.obj x).fiber)
    (hm : ∀ {x y} (p : x ⟶ y), HEq (s.lift.map p).fiber (t.lift.map p).fiber)
    (hc : ∀ {x y} {p q : x ⟶ y} (α : p ⟶ q),
      HEq (s.lift.map₂ α).fiber (t.lift.map₂ α).fiber) : s = t := by
  have hobj (x : Γ) : s.lift.obj x = t.lift.obj x := by
    apply total_ext F _ (ho x)
    exact (congrArg (fun H => H.obj x) s.over).trans
      (congrArg (fun H => H.obj x) t.over).symm
  have hmap {x y : Γ} (p : x ⟶ y) : HEq (s.lift.map p) (t.lift.map p) := by
    apply hom_hext F (hobj x) (hobj y) _ _ _ (hm p)
    exact HEq.trans (congr_arg_heq (fun H => H.map p) s.over)
      (congr_arg_heq (fun H => H.map p) t.over).symm
  have hcell {x y : Γ} {p q : x ⟶ y} (α : p ⟶ q) : HEq (s.lift.map₂ α) (t.lift.map₂ α) := by
    apply cell_hext F (hobj x) (hobj y) (hmap p) (hmap q) _ _ _ (hc α)
    exact HEq.trans (congr_arg_heq (fun H => H.map₂ α) s.over)
      (congr_arg_heq (fun H => H.map₂ α) t.over).symm
  have hl : s.lift = t.lift := StrictTwoTransformation.functor_ext
    (prelax_ext _ _ hobj (fun p => hmap p) (fun α => hcell α))
  cases s
  cases t
  cases hl
  rfl
theorem Section.cast_obj_fiber {F G : Family.{u,v,w,u',v',w'} Γ} (e : F = G)
    (s : Section F) (x : Γ) :
    HEq ((Section.cast e s).lift.obj x).fiber (s.lift.obj x).fiber := by
  cases e
  rfl

theorem Section.cast_map_fiber {F G : Family.{u,v,w,u',v',w'} Γ} (e : F = G)
    (s : Section F) {x y : Γ} (p : x ⟶ y) :
    HEq ((Section.cast e s).lift.map p).fiber (s.lift.map p).fiber := by
  cases e
  rfl

set_option maxHeartbeats 1000000 in
theorem Section.reindex_obj_fiber (s : Section F) (σ : StrictPseudofunctor Δ Γ) (x : Δ) :
    HEq ((s.reindex F σ).lift.obj x).fiber (s.lift.obj (σ.obj x)).fiber := by
  exact Section.cast_obj_fiber _ (sectionOfLift F (σ.comp s.lift)) x

set_option maxHeartbeats 1000000 in
theorem Section.reindex_map_fiber (s : Section F) (σ : StrictPseudofunctor Δ Γ)
    {x y : Δ} (p : x ⟶ y) :
    HEq ((s.reindex F σ).lift.map p).fiber (s.lift.map (σ.map p)).fiber := by
  exact Section.cast_map_fiber _ (sectionOfLift F (σ.comp s.lift)) p

theorem reindex_id : reindex (StrictPseudofunctor.id Γ) F = F :=
  StrictTwoTransformation.functor_ext rfl

set_option maxHeartbeats 1000000 in
theorem Section.reindex_id (s : Section F) :
    Section.cast (reindex_id F) (s.reindex F (StrictPseudofunctor.id Γ)) = s := by
  apply Section.ext_fiber F
  · intro x
    exact HEq.trans (Section.cast_obj_fiber _ _ x) (s.reindex_obj_fiber F _ x)
  · intro x y p
    exact HEq.trans (Section.cast_map_fiber _ _ p) (s.reindex_map_fiber F _ p)
  · intro x y p q α
    exact HEq.trans (Section.cast_cell_fiber _ _ α) (s.reindex_cell_fiber F _ α)

variable {Θ : Type*} [Bicategory Θ] [Bicategory.Strict Θ]
omit [Bicategory.Strict Γ] in
theorem reindex_comp (σ : StrictPseudofunctor Δ Γ) (τ : StrictPseudofunctor Θ Δ) :
    reindex τ (reindex σ F) = reindex (τ.comp σ) F :=
  StrictTwoTransformation.functor_ext rfl

end SquareKit.Internal.PathTransport.TwoFamily
