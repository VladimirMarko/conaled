import SquareKit.Internal.PathTransport.TwoOpenIdentityHigher
import SquareKit.Internal.PathTransport.TwoFamilyHigher
import SquareKit.Internal.PathTransport.TwoFamilyMap

/-! Path contexts retain both endpoint data and the full identity hom-groupoid. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]

/-- The context of two dependent endpoints and a path between them. -/
abbrev PathContext := Total (openIdHigher F)

instance openIdFiberGroupoid (x : Total (endpointFamily F)) :
    IsGroupoid ((openIdHigher F).obj x) := by
  change IsGroupoid (LocallyDiscrete (x.fiber.1 ⟶ x.fiber.2))
  refine ⟨fun f => ?_⟩
  let : IsIso f.as := IsGroupoid.all_isIso (C := x.fiber.1 ⟶ x.fiber.2) _
  exact ⟨⟨⟨inv f.as⟩, Discrete.ext (IsIso.hom_inv_id f.as),
    Discrete.ext (IsIso.inv_hom_id f.as)⟩⟩

instance openIdFiberLocallyGroupoid (x : Total (endpointFamily F)) :
    IsLocallyGroupoid ((openIdHigher F).obj x) := by
  change IsLocallyGroupoid (LocallyDiscrete (x.fiber.1 ⟶ x.fiber.2))
  intro a b
  change IsGroupoid (Discrete (a.as ⟶ b.as))
  infer_instance

/-- Forget the path while retaining both endpoints and all endpoint cells. -/
noncomputable def pathEndpoints :
    StrictPseudofunctor (PathContext F) (Total (endpointFamily F)) :=
  projectionHigher (openIdHigher F)

/-- Duplicate a dependent endpoint in every dimension. -/
def diagonalTotal : StrictPseudofunctor (Total F) (Total (endpointFamily F)) :=
  StrongMap.toHigher (diagonalFamily F).toStrong

/-- The first dependent endpoint, retaining its genuine cells. -/
noncomputable def pathFirst : StrictPseudofunctor (PathContext F) (Total F) :=
  (pathEndpoints F).comp (StrongMap.toHigher (firstEndpoint F).toStrong)

/-- The second dependent endpoint, retaining its genuine cells. -/
noncomputable def pathSecond : StrictPseudofunctor (PathContext F) (Total F) :=
  (pathEndpoints F).comp (StrongMap.toHigher (secondEndpoint F).toStrong)

instance pathContextGroupoid [IsGroupoid Γ] : IsGroupoid (PathContext F) :=
  totalIsGroupoid (openIdHigher F)

instance pathContextLocallyGroupoid [IsLocallyGroupoid Γ] :
    IsLocallyGroupoid (PathContext F) := totalLocallyGroupoid (openIdHigher F)

/-- A path is genuine fiber data over a common base and two endpoints. -/
def pathObject (γ : Γ) (a b : F.obj γ) (p : a ⟶ b) : PathContext F :=
  ⟨⟨γ, (a,b)⟩, ⟨p⟩⟩

/-- Reflexivity at an arbitrary dependent object is its identity arrow. -/
def pathReflexivityObj (x : Total F) : PathContext F :=
  pathObject F x.base x.fiber x.fiber (𝟙 x.fiber)

theorem pathFirst_object (γ : Γ) (a b : F.obj γ) (p : a ⟶ b) :
    (pathFirst F).obj (pathObject F γ a b p) = ⟨γ,a⟩ := rfl

theorem pathSecond_object (γ : Γ) (a b : F.obj γ) (p : a ⟶ b) :
    (pathSecond F).obj (pathObject F γ a b p) = ⟨γ,b⟩ := rfl

omit [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] in
theorem diagonal_fiber_fst {x y : Total F} (p : x ⟶ y) :
    ((diagonalTotal F).map p).fiber.1 = p.fiber := by
  simp [diagonalTotal, StrongMap.toHigher, StrongMap.map,
    StrictTwoTransformation.Trans.toStrong, diagonalFamily, diagonalFunctor]
  change (𝟙 _ ≫ p.fiber) = p.fiber
  exact Category.id_comp _

omit [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] in
theorem diagonal_fiber_snd {x y : Total F} (p : x ⟶ y) :
    ((diagonalTotal F).map p).fiber.2 = p.fiber := by
  simp [diagonalTotal, StrongMap.toHigher, StrongMap.map,
    StrictTwoTransformation.Trans.toStrong, diagonalFamily, diagonalFunctor]
  change (𝟙 _ ≫ p.fiber) = p.fiber
  exact Category.id_comp _

private theorem homTransport_identity {A B : Type*} [Bicategory A] [Bicategory B]
    [Strict A] [Strict B] (H : StrictPseudofunctor A B) {a : A} {b : B}
    (u : H.obj a ⟶ b) [IsIso u] :
    (TwoIdentityTransport.homTransport H u u).obj (𝟙 a) = 𝟙 b := by
  simp [TwoIdentityTransport.homTransport, H.map_id]

omit [∀ γ, IsLocallyGroupoid (F.obj γ)] in
/-- Diagonal endpoint transport preserves the identity path as an object. -/
theorem diagonal_identity {x y : Total F} (p : x ⟶ y) :
    (openIdMap F ((diagonalTotal F).map p)).obj (𝟙 x.fiber) = 𝟙 y.fiber := by
  let : IsIso p.fiber := IsGroupoid.all_isIso (C := F.obj y.base) _
  change (TwoIdentityTransport.homTransport (F.map p.base)
    ((diagonalTotal F).map p).fiber.1 ((diagonalTotal F).map p).fiber.2).obj (𝟙 x.fiber) = _
  simpa only [diagonal_fiber_fst, diagonal_fiber_snd] using
    homTransport_identity (F.map p.base) p.fiber

/-- The reflexive path over each dependent arrow uses diagonal endpoint transport. -/
noncomputable def pathReflexivityMap {x y : Total F} (p : x ⟶ y) :
    pathReflexivityObj F x ⟶ pathReflexivityObj F y :=
  ⟨(diagonalTotal F).map p, Discrete.mk (eqToHom (diagonal_identity F p))⟩

end SquareKit.Internal.PathTransport.TwoFamily
