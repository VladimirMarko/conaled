import SquareKit.Internal.PathTransport.TwoFamilyFiber
import SquareKit.Internal.PathTransport.TwoFamilyMap
import SquareKit.Internal.PathTransport.TwoFamilyHigherReindex

namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)

/-- The cartesian arrow from a fiber object to its transport. -/
def cartesianLift {γ δ : Γ} (f : γ ⟶ δ) (a : F.obj γ) :
    (fiberInclusion F γ).obj a ⟶ (fiberInclusion F δ).obj ((F.map f).obj a) :=
  ⟨f, 𝟙 _⟩

/-- Every total arrow factors into a cartesian arrow followed by a fiber arrow. -/
theorem cartesianLift_factorization {x y : Total F} (p : x ⟶ y) :
    cartesianLift F p.base x.fiber ≫ (fiberInclusion F y.base).map p.fiber = p := by
  apply toUnderlyingHom_injective F
  refine Grothendieck.ext _ _ ?_ ?_
  · exact Category.comp_id p.base
  · change eqToHom _ ≫ (eqToHom _ ≫ (F.map (𝟙 y.base)).map (𝟙 _) ≫ eqToHom _ ≫ p.fiber) = p.fiber
    rw [(F.map (𝟙 y.base)).map_id]
    simp only [Category.id_comp, ← Category.assoc, eqToHom_trans, eqToHom_refl]

/-- A base 2-cell supplies a genuine total comparison; its fiber is the unit boundary. -/
def cartesianLiftCell {γ δ : Γ} {f g : γ ⟶ δ} (α : f ⟶ g) (a : F.obj γ) :
    (show (fiberInclusion F γ).obj a ⟶ (fiberInclusion F δ).obj ((F.map g).obj a) from
      ⟨f, (F.map₂ α).app a⟩) ⟶ cartesianLift F g a :=
  TwoGroupoidHom.cell (E := evaluation F a) (b := (F.map g).obj a)
    (f := (F.map₂ α).app a) (g := 𝟙 _) α (eqToHom (Category.comp_id _).symm)

/-- Cartesian comparison retains the supplied base 2-cell exactly. -/
theorem cartesianLiftCell_base {γ δ : Γ} {f g : γ ⟶ δ} (α : f ⟶ g) (a : F.obj γ) :
    (cartesianLiftCell F α a).base = α := rfl

/-- The same comparison with its source expressed by cartesian-vertical factorization. -/
def cartesianComparisonCell {γ δ : Γ} {f g : γ ⟶ δ} (α : f ⟶ g) (a : F.obj γ) :
    cartesianLift F f a ≫ (fiberInclusion F δ).map ((F.map₂ α).app a) ⟶
      cartesianLift F g a :=
  eqToHom (cartesianLift_factorization F (x := ⟨γ,a⟩) (y := ⟨δ,(F.map g).obj a⟩) ⟨f, (F.map₂ α).app a⟩) ≫
    cartesianLiftCell F α a

/-- Cartesian arrows commute with every arrow of the source fiber. -/
theorem cartesianLift_naturality {γ δ : Γ} (f : γ ⟶ δ)
    {a b : F.obj γ} (u : a ⟶ b) :
    (fiberInclusion F γ).map u ≫ cartesianLift F f b =
      cartesianLift F f a ≫ (fiberInclusion F δ).map ((F.map f).map u) := by
  exact toUnderlyingHom_injective F ((Grothendieck.ιNatTrans (F := underlying F) f).naturality u)

omit [Strict Γ] in
private theorem cell_comp_base {x y : Total F} {p q r : Hom F x y}
    (α : p ⟶ q) (β : q ⟶ r) : (α ≫ β).base = α.base ≫ β.base := rfl

omit [Strict Γ] in
private theorem fiber_cast_right {x y : Total F} {p q r : Hom F x y}
    (α : p ⟶ q) (h : q = r) : HEq (α ≫ eqToHom h).fiber α.fiber := by
  cases h
  rw [eqToHom_refl, Category.comp_id]

omit [Strict Γ] in
private theorem fiber_cast_left {x y : Total F} {p q r : Hom F x y}
    (h : p = q) (α : q ⟶ r) : HEq (eqToHom h ≫ α).fiber α.fiber := by
  cases h
  rw [eqToHom_refl, Category.id_comp]

private theorem map_boundary_heq {C D : Type*} [Bicategory C] [Strict C]
    [Bicategory D] [Strict D] (H : StrictPseudofunctor C D)
    {a a' b : C} (e : a' = a) {u v : a ⟶ b} (α : u ⟶ v)
    {t : a' ⟶ b} (h : eqToHom e ≫ v = t) :
    HEq (H.map₂ (eqToHom e ◁ α ≫ eqToHom h)) (H.map₂ α) := by
  cases e
  simp [Bicategory.id_whiskerLeft, Strict.leftUnitor_eqToIso,
    H.map₂_comp, H.map₂_eqToHom, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]

theorem cartesianLift_naturality₂ {γ δ : Γ} (f : γ ⟶ δ)
    {a b : F.obj γ} {u v : a ⟶ b} (α : u ⟶ v) :
    (fiberInclusion F γ).map₂ α ▷ cartesianLift F f b ≫
        eqToHom (cartesianLift_naturality F f v) =
      eqToHom (cartesianLift_naturality F f u) ≫
        cartesianLift F f a ◁ (fiberInclusion F δ).map₂ ((F.map f).map₂ α) := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
  · simp only [cell_comp_base F, total_eqToHom_base F]
    change (𝟙 (𝟙 γ) ▷ f) ≫ eqToHom _ = eqToHom _ ≫ (f ◁ 𝟙 (𝟙 δ))
    simp [whiskerLeft_id, id_whiskerRight]
  · apply eq_of_heq
    simp only [heq_comp_eqToHom_iff]
    apply HEq.trans (fiber_cast_right F _ _)
    apply HEq.trans _ (fiber_cast_left F _ _).symm
    change HEq (eqToHom _ ≫
      (compBoundary F (𝟙 γ) f a ◁ (F.map f).map₂ (fiberInclusionCell F γ α).fiber) ▷
        (𝟙 _) ≫ eqToHom _)
      (compBoundary F f (𝟙 δ) a ◁
        ((F.map (𝟙 δ)).map (𝟙 _) ◁ (fiberInclusionCell F δ ((F.map f).map₂ α)).fiber) ≫ eqToHom _)
    apply HEq.trans (eqToHom_comp_heq _ _)
    apply HEq.trans (comp_eqToHom_heq _ _)
    rw [Bicategory.whiskerRight_id]
    simp only [Strict.rightUnitor_eqToIso, eqToIso.inv, eqToIso.hom]
    apply HEq.trans (eqToHom_comp_heq _ _)
    apply HEq.trans (comp_eqToHom_heq _ _)
    apply HEq.trans (eqToHom_left_heq _ _)
    apply HEq.trans (map_boundary_heq (F.map f) _ α _)
    symm
    apply HEq.trans (comp_eqToHom_heq _ _)
    apply HEq.trans (eqToHom_left_heq _ _)
    rw [(F.map (𝟙 δ)).map_id, Bicategory.id_whiskerLeft]
    simp only [Strict.leftUnitor_eqToIso, eqToIso.inv, eqToIso.hom]
    apply HEq.trans (eqToHom_comp_heq _ _)
    apply HEq.trans (comp_eqToHom_heq _ _)
    exact fiberInclusionCell_fiber_heq F δ ((F.map f).map₂ α)

/-- The split cartesian comparison retains naturality at genuine fiber 2-cells. -/
def cartesianComparison {γ δ : Γ} (f : γ ⟶ δ) :
    StrictTwoTransformation.Trans (fiberInclusion F γ)
      ((F.map f).comp (fiberInclusion F δ)) where
  app := cartesianLift F f
  naturality := cartesianLift_naturality F f
  naturality₂ := cartesianLift_naturality₂ F f

universe uB vB wB
/-- Apply an arbitrary later family to the cartesian comparison. -/
def sigmaTransportComparison
    (B : Family.{max uΓ u,max vΓ v,max wΓ w,uB,vB,wB} (Total F))
    {γ δ : Γ} (f : γ ⟶ δ) :
    StrictTwoTransformation.Trans (fiberRestriction F γ B)
      ((F.map f).comp (fiberRestriction F δ B)) where
  app := (StrictTwoTransformation.Trans.whiskerRight (cartesianComparison F f) B).app
  naturality := (StrictTwoTransformation.Trans.whiskerRight (cartesianComparison F f) B).naturality
  naturality₂ := (StrictTwoTransformation.Trans.whiskerRight (cartesianComparison F f) B).naturality₂

/-- Transport a dependent pair along a base arrow, retaining both higher components. -/
def sigmaMap
    (B : Family.{max uΓ u,max vΓ v,max wΓ w,uB,vB,wB} (Total F))
    {γ δ : Γ} (f : γ ⟶ δ) :
    StrictPseudofunctor (sigmaFiber F γ B) (sigmaFiber F δ B) :=
  (StrongMap.toHigher (sigmaTransportComparison F B f).toStrong).comp
    (reindexHigher (fiberRestriction F δ B) (F.map f))

/-- The first cell component is transported by the original family. -/
theorem sigmaMap_cell_base
    (B : Family.{max uΓ u,max vΓ v,max wΓ w,uB,vB,wB} (Total F))
    {γ δ : Γ} (f : γ ⟶ δ) {x y : sigmaFiber F γ B}
    {p q : x ⟶ y} (α : p ⟶ q) :
    ((sigmaMap F B f).map₂ α).base = (F.map f).map₂ α.base := rfl

/-- The second cell component is the later family's actual action, up to boundary casts. -/
theorem sigmaMap_cell_fiber_heq
    (B : Family.{max uΓ u,max vΓ v,max wΓ w,uB,vB,wB} (Total F))
    {γ δ : Γ} (f : γ ⟶ δ) {x y : sigmaFiber F γ B}
    {p q : x ⟶ y} (α : p ⟶ q) :
    HEq ((sigmaMap F B f).map₂ α).fiber
      ((B.map (cartesianLift F f y.base)).map₂ α.fiber) := by
  change HEq (_ ◁ (B.map (cartesianLift F f y.base)).map₂ α.fiber ≫ eqToHom _) _
  apply HEq.trans (comp_eqToHom_heq _ _)
  change HEq ((eqToHom ((sigmaTransportComparison F B f).naturality p.base).symm).app x.fiber ◁ _) _
  rw [StrictTwoTransformation.Trans.eqToHom_app]
  exact eqToHom_left_heq _ _

end SquareKit.Internal.PathTransport.TwoFamily
