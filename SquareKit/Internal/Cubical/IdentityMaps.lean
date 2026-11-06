import SquareKit.Internal.Cubical.IdentityEvaluation

/-! Pointwise identity maps retain the selected constancy face and reflexivity. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
universe u
variable {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) {a b : Term A}

def IdentityElement.map {x : Γ.Elements} (p : IdentityElement A a b x) :
    IdentityElement B (a.map f) (b.map f) x where
  path := ⟨{
    val := fun {y} g r => f.app y (p.path.val.val g r)
    naturality := by
      intro y z g k r
      exact (f.naturality_apply k _).symm.trans
        (congrArg (f.app z) (p.path.val.naturality g k r)) },
    fun g => ⟨congrArg (f.app _) (p.path.property g).1,
      congrArg (f.app _) (p.path.property g).2⟩⟩
  face := p.face
  constant g h r := congrArg (f.app _) (p.constant g h r)

def identityMap (a b : Term A) : identity A a b ⟶ identity B (a.map f) (b.map f) where
  app _ := TypeCat.ofHom (IdentityElement.map f)
  naturality _ _ _ := rfl

def normalizedIdentityMap (a b : Term A) :
    normalizedIdentity A a b ⟶ normalizedIdentity B (a.map f) (b.map f) :=
  (normalizedIdentityIso A a b).inv ≫ identityMap f a b ≫
    (normalizedIdentityIso B (a.map f) (b.map f)).hom

theorem normalizedIdentityMap_eval {x : Γ.Elements}
    (p : LocalIdentity A a b x) (r : (interval Γ).obj x) :
    ((normalizedIdentityMap f a b).app x p).eval r = f.app x (p.eval r) := by
  exact congrArg (fun q : IdentityElement B (a.map f) (b.map f) x => q.path.val.val (𝟙 _) r)
    (LocalIdentity.fromLocal_toLocal (IdentityElement.map f p.fromLocal))

theorem normalizedIdentityMap_refl (a : Term A) :
    (normalizedIdentityRefl a).map (normalizedIdentityMap f a a) =
      normalizedIdentityRefl (a.map f) := by
  apply Term.ext
  intro x
  change ((IdentityElement.map f ((identityRefl a).val x).toLocal.fromLocal)).toLocal = _
  rw [LocalIdentity.fromLocal_toLocal]
  rfl

end SquareKit.Cubical.Presheaf
