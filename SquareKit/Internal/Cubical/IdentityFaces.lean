import SquareKit.Internal.Cubical.IdentitySubstitution
import SquareKit.Internal.Cubical.Conversion

/-! On its marked face an identity is strict reflexivity, including its face data. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem identity_full_endpoints {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    (p : Term (identity A a b)) (h : ∀ x, (identityFace p).full x) : b = a := by
  apply Term.ext
  intro x
  exact ((p.val x).path.property (𝟙 _)).2.symm.trans
    ((p.val x).constant (𝟙 _) (h x) ((endpoint Γ true).val x))

theorem identity_full_refl {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    (p : Term (identity A a b)) (h : ∀ x, (identityFace p).full x) :
    p.convert (congrArg (identity A a) (identity_full_endpoints p h)) = identityRefl a := by
  apply Term.convert_eq
  apply Term.hext (congrArg (identity A a) (identity_full_endpoints p h))
  intro x
  apply IdentityElement.hext_right (identity_full_endpoints p h)
  · apply PiElement.ext
    intro y f r
    exact (p.val x).constant f (Face.full_substitute f.hom.unop _ (h x)) r
  · exact (Face.full_iff_top _).mp (h x)

theorem identity_restricted_full {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    (p : Term (identity A a b)) (x : (restrictContext (identityFace p)).Elements) :
    (identityFace (Term.map (identityReindex A a b (restrictInclusion (identityFace p)))
      (p.reindex (restrictInclusion (identityFace p))))).full x := x.val.property

end SquareKit.Cubical.Presheaf
