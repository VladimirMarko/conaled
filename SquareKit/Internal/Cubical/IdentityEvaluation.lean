import SquareKit.Internal.Cubical.NormalizedIdentity

/-! Evaluation of normalized identities preserves restriction and both endpoints. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

namespace LocalIdentity
variable {Γ : Context.{u}} {A : Family Γ} {a b : Term A}

noncomputable def eval {x : Γ.Elements} (p : LocalIdentity A a b x) (r : (interval Γ).obj x) : A.obj x :=
  p.fromLocal.path.val.val (𝟙 x) r

theorem fromLocal_map {x y : Γ.Elements} (f : x ⟶ y) (p : LocalIdentity A a b x) :
    ((normalizedIdentity A a b).map f p).fromLocal = (identity A a b).map f p.fromLocal :=
  LocalIdentity.fromLocal_toLocal _

theorem eval_map {x y : Γ.Elements} (f : x ⟶ y) (p : LocalIdentity A a b x) (r : (interval Γ).obj x) :
    A.map f (p.eval r) = ((normalizedIdentity A a b).map f p).eval ((interval Γ).map f r) := by
  have h := p.fromLocal.path.val.naturality (𝟙 x) f r
  have h' : A.map f (p.eval r) =
      ((identity A a b).map f p.fromLocal).path.val.val (𝟙 y) ((interval Γ).map f r) := by
    exact h.trans (congrArg (fun k : x ⟶ y => p.fromLocal.path.val.val k ((interval Γ).map f r))
      ((Category.id_comp f).trans (Category.comp_id f).symm))
  exact h'.trans (congrArg (fun q : IdentityElement A a b y => q.path.val.val (𝟙 y) ((interval Γ).map f r))
    (fromLocal_map f p)).symm

theorem eval_zero {x : Γ.Elements} (p : LocalIdentity A a b x) :
    p.eval ((endpoint Γ false).val x) = a.val x := (p.fromLocal.path.property (𝟙 x)).1

theorem eval_one {x : Γ.Elements} (p : LocalIdentity A a b x) :
    p.eval ((endpoint Γ true).val x) = b.val x := (p.fromLocal.path.property (𝟙 x)).2

theorem eval_refl (a : Term A) (x : Γ.Elements) (r : (interval Γ).obj x) :
    ((normalizedIdentityRefl a).val x).eval r = a.val x :=
  congrArg (fun p : IdentityElement A a a x => p.path.val.val (𝟙 x) r)
    (LocalIdentity.fromLocal_toLocal ((identityRefl a).val x))

end LocalIdentity
end SquareKit.Cubical.Presheaf
