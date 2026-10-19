import SquareKit.SmoothOpenOperations

/-! Experimental algebraic comparison of an ordinary principal subdomain with
localization of its source presentation. Universal maps range over all smooth
algebras, including nonreduced stages. -/
noncomputable section
namespace SquareKit.SmoothAlgebra.Localization
variable {n : ℕ} (f g : Free n)
variable {B : Type*} [CommRing B] [Algebra ℝ B] [Structure B]

theorem nested_unit : IsUnit (nestedMap f g (principalBase f g)) := by
  have hu := base_isUnit (fun _ : Fin 1 => f*g) 0
  change IsUnit (principalBase (f*g) (f*g)) at hu
  rw [(principalBase (f*g)).map_mul,IsUnit.mul_iff] at hu
  have he := congrArg (fun h : Hom (Free n) (Principal (f*g)) => h g) (nestedMap_base f g)
  change nestedMap f g (principalBase f g) = principalBase (f*g) g at he
  rw [he]
  exact hu.2

def subLift (h : Hom (Principal f) B) (hu : IsUnit (h (principalBase f g))) :
    Hom (Principal (f*g)) B :=
  principalLift (f*g) (h.comp (principalBase f)) (by
    change IsUnit (h (principalBase f (f*g)))
    rw [(principalBase f).map_mul,h.map_mul]
    exact ((base_isUnit (fun _ : Fin 1 => f) 0).map h.toAlgHom).mul hu)

theorem subLift_base (h : Hom (Principal f) B) (hu : IsUnit (h (principalBase f g))) :
    (subLift f g h hu).comp (nestedMap f g) = h := by
  apply principal_unique f
  rw [← Hom.comp_assoc,nestedMap_base]
  unfold subLift
  apply lift_base

theorem sub_unique (h k : Hom (Principal (f*g)) B)
    (he : h.comp (nestedMap f g) = k.comp (nestedMap f g)) : h=k := by
  apply principal_unique (f*g)
  rw [← nestedMap_base f g,Hom.comp_assoc,Hom.comp_assoc,he]

end SquareKit.SmoothAlgebra.Localization
namespace SquareKit.EuclideanOpen
open CategoryTheory Opposite SmoothAlgebra SmoothPresentationSite Localization PresentedLocalization
variable (U : Domain) (g : Free U.dimension)

abbrev subdomain : Domain := ⟨U.dimension,U.defining*g⟩
abbrev subInclusion : subdomain U g ⟶ U := nested U.defining g
abbrev element : Carrier (code U) := principalBase U.defining g

abbrev localized : Code := localization (code U) (element U g)

def toSubdomain : localized U g ⟶ code (subdomain U g) :=
  (atHomEquiv (code U).equations (element U g)).symm
    ⟨nestedMap U.defining g,nested_unit U.defining g⟩

theorem toSubdomain_base : localizationBase (code U) (element U g) ≫ toSubdomain U g =
    Localization.pullback (subInclusion U g) := by
  rw [nested_pullback]
  exact congrArg Subtype.val ((atHomEquiv (code U).equations (element U g)).apply_symm_apply _)

def fromSubdomain : code (subdomain U g) ⟶ localized U g :=
  subLift U.defining g (localizationBase (code U) (element U g))
    (atBase_isUnit (code U).equations (element U g))

theorem fromSubdomain_base : Localization.pullback (subInclusion U g) ≫ fromSubdomain U g =
    localizationBase (code U) (element U g) := by
  rw [nested_pullback]
  exact subLift_base _ _ _ _

/-- A code isomorphism, not merely a correspondence of real points. -/
def subdomainIso : localized U g ≅ code (subdomain U g) where
  hom := toSubdomain U g
  inv := fromSubdomain U g
  hom_inv_id := by
    apply (atHomEquiv (code U).equations (element U g)).injective
    apply Subtype.ext
    change localizationBase (code U) (element U g) ≫ (toSubdomain U g ≫ fromSubdomain U g) = _
    rw [← Category.assoc,toSubdomain_base,fromSubdomain_base]
    rfl
  inv_hom_id := by
    apply sub_unique U.defining g
    rw [← nested_pullback U.defining g]
    change (show code U ⟶ code (subdomain U g) from Localization.pullback (subInclusion U g)) ≫ (fromSubdomain U g ≫ toSubdomain U g) = _
    rw [← Category.assoc,fromSubdomain_base,toSubdomain_base]
    rfl

end SquareKit.EuclideanOpen
