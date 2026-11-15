import SquareKit.Internal.PathTransport.TwoFamilyPathContractionLift
import SquareKit.Internal.PathTransport.TwoFamilyPathContractionEndpoints
import SquareKit.Internal.PathTransport.TwoFamilySigmaAction
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
omit [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] [Bicategory.Strict Γ] in
private theorem canonical_comp {x y z : Total F} (p : x.base ⟶ y.base) (q : y.base ⟶ z.base)
 (hp : (F.map p).obj x.fiber = y.fiber) (hq : (F.map q).obj y.fiber = z.fiber)
 (hr : (F.map (p ≫ q)).obj x.fiber = z.fiber) :
 compose F (⟨p, eqToHom hp⟩ : Hom F x y) (⟨q, eqToHom hq⟩ : Hom F y z) =
 (⟨p ≫ q, eqToHom hr⟩ : Hom F x z) := by
 apply Pseudofunctor.CoGrothendieck.ext
 · rfl
 · apply heq_of_eq
   change eqToHom _ ≫ (F.map q).map (eqToHom hp) ≫ eqToHom hq = eqToHom hr
   rw [StrongMap.map_eqToHom]
   simp only [eqToHom_trans]

omit [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] [Bicategory.Strict Γ] in
private theorem canonical_eq {x y : Total F} {p q : x.base ⟶ y.base}
 (e : p = q) (h : (F.map p).obj x.fiber = y.fiber)
 (k : (F.map q).obj x.fiber = y.fiber) :
 (⟨p, eqToHom h⟩ : Hom F x y) = ⟨q, eqToHom k⟩ := by cases e; rfl
private theorem discrete_mk_eqToHom {C : Type*} [Category* C] {a b : C} (h : a = b) :
 Discrete.mk (eqToHom h) = eqToHom (congrArg LocallyDiscrete.mk h) := by cases h; rfl

private theorem reflexivity_canonical {x y : Total F} (p : x ⟶ y) :
 pathReflexivityMap F p =
 (⟨(diagonalTotal F).map p, eqToHom (congrArg LocallyDiscrete.mk (diagonal_identity F p))⟩ :
 Hom (openIdHigher F) (pathReflexivityObj F x) (pathReflexivityObj F y)) := by
 unfold pathReflexivityMap
 congr 1
 exact discrete_mk_eqToHom _
omit [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] [Bicategory.Strict Γ] in
private theorem canonical_prefix {x y z : Total F} (p : x.base ⟶ y.base) (q : Hom F y z)
    (hp : (F.map p).obj x.fiber = y.fiber) (r : x.base ⟶ z.base)
    (e : p ≫ q.base = r) (h : (F.map r).obj x.fiber = (F.map q.base).obj y.fiber) :
    compose F (⟨p,eqToHom hp⟩ : Hom F x y) q =
      (⟨r,eqToHom h ≫ q.fiber⟩ : Hom F x z) := by
  cases e
  apply Pseudofunctor.CoGrothendieck.ext
  · rfl
  · apply heq_of_eq
    change eqToHom _ ≫ (F.map q.base).map (eqToHom hp) ≫ q.fiber = _
    rw [StrongMap.map_eqToHom]
    simp only [eqToHom_trans_assoc]

/-- The actual left path composite has the normalized canonical fiber arrow. -/
theorem contractionLeftArrow_composite {x y : PathContext F} (p : x ⟶ y) :
    (pathReflexivity F).map ((pathFirst F).map p) ≫ contractionComponent F y =
      contractionLeftArrow F p := by
  change pathReflexivityMap F ((pathFirst F).map p) ≫ _ = _
  rw [reflexivity_canonical]
  let e := contractionLeftEndpoint_composite F p
  let h := congrArg (fun r => (openIdMap F r).obj (𝟙 x.base.fiber.1)) e
  let k := congrArg LocallyDiscrete.mk (h.trans (contractionLeftBoundary F p))
  change compose (openIdHigher F) _ _ = _
  erw [canonical_comp (openIdHigher F)
    (x := pathReflexivityObj F ((pathFirst F).obj x))
    (y := pathReflexivityObj F ((pathFirst F).obj y)) (z := y)
    ((diagonalTotal F).map ((pathFirst F).map p)) (contractionEndpoint F y)
    (congrArg LocallyDiscrete.mk (diagonal_identity F ((pathFirst F).map p)))
    (congrArg LocallyDiscrete.mk (contractionBoundary F y)) k]
  change _ = (⟨_, Discrete.mk (eqToHom (contractionLeftBoundary F p))⟩ : Hom (openIdHigher F) _ _)
  rw [discrete_mk_eqToHom]
  exact canonical_eq (openIdHigher F) e _ _
/-- The actual right path composite retains the supplied path-family cell. -/
theorem contractionRightArrow_composite {x y : PathContext F} (p : x ⟶ y) :
    contractionComponent F x ≫ p = contractionRightArrow F p := by
  have h := canonical_prefix (openIdHigher F)
    (x := pathReflexivityObj F ((pathFirst F).obj x)) (y := x) (z := y)
    (contractionEndpoint F x) p
    (congrArg LocallyDiscrete.mk (contractionBoundary F x)) (contractionRightEndpoint F p)
    (contractionRightEndpoint_composite F p)
    (congrArg LocallyDiscrete.mk (contractionRightBoundary F p))
  change compose (openIdHigher F) (⟨contractionEndpoint F x,
    eqToHom (congrArg LocallyDiscrete.mk (contractionBoundary F x))⟩) p = _
  refine h.trans ?_
  apply Pseudofunctor.CoGrothendieck.ext
  · rfl
  · apply heq_of_eq
    change eqToHom (congrArg LocallyDiscrete.mk (contractionRightBoundary F p)) ≫ p.fiber =
      Discrete.mk (eqToHom (contractionRightBoundary F p) ≫ p.fiber.as)
    rw [← discrete_mk_eqToHom (contractionRightBoundary F p)]
    rfl
/-- The genuine comparison between the actual contraction composites. -/
noncomputable def contractionNaturalityCell {x y : PathContext F} (p : x ⟶ y) :
    (pathReflexivity F).map ((pathFirst F).map p) ≫ contractionComponent F y ⟶
      contractionComponent F x ≫ p :=
  eqToHom (contractionLeftArrow_composite F p) ≫ contractionLiftCell F p ≫
    eqToHom (contractionRightArrow_composite F p).symm
private theorem endpointFiber_cast_right {x y : PathContext F} {p q r : x ⟶ y}
    (α : p ⟶ q) (h : q = r) : HEq (α ≫ eqToHom h).base.fiber α.base.fiber := by
  cases h
  rw [eqToHom_refl, Category.comp_id]
private theorem endpointFiber_cast_left {x y : PathContext F} {p q r : x ⟶ y}
    (h : p = q) (α : q ⟶ r) : HEq (eqToHom h ≫ α).base.fiber α.base.fiber := by
  cases h
  rw [eqToHom_refl, Category.id_comp]
/-- Boundary casts retain the genuine endpoint comparison fiber cells. -/
theorem contractionNaturalityCell_endpoint_heq {x y : PathContext F} (p : x ⟶ y) :
    HEq (contractionNaturalityCell F p).base.fiber (contractionEndpointSquare F p).fiber := by
  apply HEq.trans (endpointFiber_cast_left F _ _)
  exact endpointFiber_cast_right F _ _
end SquareKit.Internal.PathTransport.TwoFamily
