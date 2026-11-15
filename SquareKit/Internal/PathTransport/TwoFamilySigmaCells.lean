import SquareKit.Internal.PathTransport.TwoFamilySigmaAction

namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w uΓ vΓ wΓ uB vB wB
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable (B : Family.{max uΓ u,max vΓ v,max wΓ w,uB,vB,wB} (Total F))

/-- Factoring the source changes the base of the comparison only by the right-unit cast. -/
theorem cartesianComparisonCell_base {γ δ : Γ} {f g : γ ⟶ δ} (α : f ⟶ g)
    (a : F.obj γ) :
    (cartesianComparisonCell F α a).base = eqToHom (Category.comp_id f) ≫ α := by
  change (eqToHom (cartesianLift_factorization F (x := ⟨γ,a⟩)
    (y := ⟨δ,(F.map g).obj a⟩) ⟨f,(F.map₂ α).app a⟩)).base ≫ α = _
  rw [total_eqToHom_base F]

/-- Source boundary for the cartesian comparison's naturality square. -/
theorem cartesianComparisonCell_source {γ δ : Γ} {f g : γ ⟶ δ} (α : f ⟶ g)
    {a b : F.obj γ} (u : a ⟶ b) :
    (fiberInclusion F γ).map u ≫
        (cartesianLift F f b ≫ (fiberInclusion F δ).map ((F.map₂ α).app b)) =
      (cartesianLift F f a ≫ (fiberInclusion F δ).map ((F.map₂ α).app a)) ≫
        (fiberInclusion F δ).map ((F.map g).map u) := by
  rw [← Category.assoc, cartesianLift_naturality F f u, Category.assoc,
    ← (fiberInclusion F δ).map_comp, (F.map₂ α).naturality u,
    (fiberInclusion F δ).map_comp, ← Category.assoc]

omit [Strict Γ] in
private theorem cell_comp_base {x y : Total F} {p q r : Hom F x y}
    (α : p ⟶ q) (β : q ⟶ r) : (α ≫ β).base = α.base ≫ β.base := rfl

/-- A total cell has an equality fiber when its fiber witness is a canonical cast. -/
def EqualityFiber {x y : Total F} {p q : x ⟶ y} (α : p ⟶ q) : Prop :=
  ∃ h : p.fiber = (F.map₂ α.base).app x.fiber ≫ q.fiber, α.fiber = eqToHom h

theorem equalityFiber_cast {x y : Total F} {p q : x ⟶ y} (h : p = q) :
    EqualityFiber F (eqToHom h) := ⟨_, total_eqToHom_fiber F h⟩

theorem equalityFiber_comp {x y : Total F} {p q r : x ⟶ y}
    {α : p ⟶ q} {β : q ⟶ r} (hα : EqualityFiber F α) (hβ : EqualityFiber F β) :
    EqualityFiber F (α ≫ β) := by
  obtain ⟨ha, ha'⟩ := hα
  obtain ⟨hb, hb'⟩ := hβ
  have he := fiber_comp α β
  rw [ha', hb', Bicategory.whiskerLeft_eqToHom, eqToHom_trans, eqToHom_trans] at he
  exact ⟨_, he⟩

theorem equalityFiber_whiskerLeft {x y z : Total F} (p : x ⟶ y)
    {q r : y ⟶ z} {α : q ⟶ r} (hα : EqualityFiber F α) :
    EqualityFiber F (p ◁ α) := by
  obtain ⟨h, hh⟩ := hα
  have he : (p ◁ α).fiber = (compBoundary F p.base q.base x.fiber ◁
    ((F.map q.base).map p.fiber ◁ α.fiber) ≫ eqToHom _) := rfl
  rw [hh, Bicategory.whiskerLeft_eqToHom, Bicategory.whiskerLeft_eqToHom,
    eqToHom_trans] at he
  exact ⟨_, he⟩

theorem equalityFiber_whiskerRight {x y z : Total F} {p q : x ⟶ y}
    {α : p ⟶ q} (hα : EqualityFiber F α) (r : y ⟶ z) :
    EqualityFiber F (α ▷ r) := by
  obtain ⟨h, hh⟩ := hα
  have he : (α ▷ r).fiber = (eqToHom _ ≫
    (compBoundary F p.base r.base x.fiber ◁ (F.map r.base).map₂ α.fiber) ▷ r.fiber ≫
      eqToHom _) := rfl
  rw [hh, (F.map r.base).map₂_eqToHom, Bicategory.whiskerLeft_eqToHom,
    Bicategory.eqToHom_whiskerRight, eqToHom_trans, eqToHom_trans] at he
  exact ⟨_, he⟩

theorem equalityFiber_ext {x y : Total F} {p q : x ⟶ y} {α β : p ⟶ q}
    (h : α.base = β.base) (hα : EqualityFiber F α) (hβ : EqualityFiber F β) : α = β := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ h ?_
  obtain ⟨ha, ha'⟩ := hα
  obtain ⟨hb, hb'⟩ := hβ
  rw [ha', hb', eqToHom_trans]

theorem cartesianComparisonCell_equalityFiber {γ δ : Γ} {f g : γ ⟶ δ}
    (α : f ⟶ g) (a : F.obj γ) : EqualityFiber F (cartesianComparisonCell F α a) :=
  equalityFiber_comp F (equalityFiber_cast F _) ⟨(Category.comp_id _).symm, rfl⟩

private theorem unit_comparison_square {C : Type*} [Bicategory C] [Strict C]
    {x y : C} {f g : x ⟶ y} (α : f ⟶ g)
    (hs : 𝟙 x ≫ (f ≫ 𝟙 y) = (f ≫ 𝟙 y) ≫ 𝟙 y)
    (ht : 𝟙 x ≫ g = g ≫ 𝟙 y) :
    (𝟙 x ◁ (eqToHom (Category.comp_id f) ≫ α)) ≫ eqToHom ht =
      eqToHom hs ≫ ((eqToHom (Category.comp_id f) ≫ α) ▷ 𝟙 y) := by
  simp [Bicategory.id_whiskerLeft, Bicategory.whiskerRight_id,
    Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso, Category.assoc]

theorem cartesianComparisonCell_naturality {γ δ : Γ} {f g : γ ⟶ δ} (α : f ⟶ g)
    {a b : F.obj γ} (u : a ⟶ b) :
    (fiberInclusion F γ).map u ◁ cartesianComparisonCell F α b ≫
        eqToHom (cartesianLift_naturality F g u) =
      eqToHom (cartesianComparisonCell_source F α u) ≫
        cartesianComparisonCell F α a ▷ (fiberInclusion F δ).map ((F.map g).map u) := by
  apply equalityFiber_ext F
  · simp only [cell_comp_base F,
      total_eqToHom_base F]
    change (𝟙 γ ◁ (cartesianComparisonCell F α b).base) ≫ eqToHom _ =
      eqToHom _ ≫ ((cartesianComparisonCell F α a).base ▷ 𝟙 δ)
    rw [cartesianComparisonCell_base, cartesianComparisonCell_base]
    exact unit_comparison_square α _ _
  · exact equalityFiber_comp F (equalityFiber_whiskerLeft F _
      (cartesianComparisonCell_equalityFiber F α b)) (equalityFiber_cast F _)
  · exact equalityFiber_comp F (equalityFiber_cast F _)
      (equalityFiber_whiskerRight F (cartesianComparisonCell_equalityFiber F α a) _)

/-- A genuine base 2-cell acts on each dependent pair through the later family. -/
def sigmaCellComponent {γ δ : Γ} {f g : γ ⟶ δ} (α : f ⟶ g)
    (x : sigmaFiber F γ B) : (sigmaMap F B f).obj x ⟶ (sigmaMap F B g).obj x :=
  ⟨(F.map₂ α).app x.base,
    eqToHom (congrArg (fun H => H.obj x.fiber)
      (B.map_comp (cartesianLift F f x.base)
        ((fiberInclusion F δ).map ((F.map₂ α).app x.base))).symm) ≫
      (B.map₂ (cartesianComparisonCell F α x.base)).app x.fiber⟩

/-- The first component is the original family's action on the supplied base cell. -/
theorem sigmaCellComponent_base {γ δ : Γ} {f g : γ ⟶ δ} (α : f ⟶ g)
    (x : sigmaFiber F γ B) :
    (sigmaCellComponent F B α x).base = (F.map₂ α).app x.base := rfl

/-- The second component uses the genuine cartesian comparison under `B.map₂`. -/
theorem sigmaCellComponent_fiber_heq {γ δ : Γ} {f g : γ ⟶ δ} (α : f ⟶ g)
    (x : sigmaFiber F γ B) :
    HEq (sigmaCellComponent F B α x).fiber
      ((B.map₂ (cartesianComparisonCell F α x.base)).app x.fiber) :=
  eqToHom_comp_heq _ _

private theorem mapped_cast_right_heq {a b : Total F} {p q r : a ⟶ b}
    (θ : p ⟶ q) (h : q = r) (x : B.obj a) :
    HEq ((B.map₂ (θ ≫ eqToHom h)).app x) ((B.map₂ θ).app x) := by
  rw [B.map₂_comp, B.map₂_eqToHom, StrictTwoTransformation.Trans.comp_app,
    StrictTwoTransformation.Trans.eqToHom_app]
  exact comp_eqToHom_heq _ _

private theorem mapped_cast_left_heq {a b : Total F} {p q r : a ⟶ b}
    (h : p = q) (θ : q ⟶ r) (x : B.obj a) :
    HEq ((B.map₂ (eqToHom h ≫ θ)).app x) ((B.map₂ θ).app x) := by
  rw [B.map₂_comp, B.map₂_eqToHom, StrictTwoTransformation.Trans.comp_app,
    StrictTwoTransformation.Trans.eqToHom_app]
  exact eqToHom_comp_heq _ _

private theorem mapped_left_heq {a b c : Total F} (p : a ⟶ b)
    {q r : b ⟶ c} (θ : q ⟶ r) (x : B.obj a) :
    HEq ((B.map₂ (p ◁ θ)).app x) ((B.map₂ θ).app ((B.map p).obj x)) := by
  rw [action_whiskerLeft]
  exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

private theorem mapped_right_heq {a b c : Total F} {p q : a ⟶ b}
    (θ : p ⟶ q) (r : b ⟶ c) (x : B.obj a) :
    HEq ((B.map₂ (θ ▷ r)).app x) ((B.map r).map ((B.map₂ θ).app x)) := by
  rw [action_whiskerRight]
  exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

/-- Applying a later family retains the cartesian comparison's naturality square. -/
theorem cartesianComparisonCell_mapped_naturality_heq {γ δ : Γ} {f g : γ ⟶ δ}
    (α : f ⟶ g) {a b : F.obj γ} (u : a ⟶ b) (x : B.obj ⟨γ,a⟩) :
    HEq ((B.map₂ (cartesianComparisonCell F α b)).app
      ((B.map ((fiberInclusion F γ).map u)).obj x))
      ((B.map ((fiberInclusion F δ).map ((F.map g).map u))).map
        ((B.map₂ (cartesianComparisonCell F α a)).app x)) := by
  have h := congrArg (fun θ => (B.map₂ θ).app x) (cartesianComparisonCell_naturality F α u)
  exact (mapped_left_heq F B _ _ x).symm.trans
    ((mapped_cast_right_heq F B _ _ x).symm.trans
      ((heq_of_eq h).trans ((mapped_cast_left_heq F B _ _ x).trans
        (mapped_right_heq F B _ _ x))))

end SquareKit.Internal.PathTransport.TwoFamily
