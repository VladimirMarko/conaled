import SquareKit.Internal.Cubical.IdentitySubstitution
import SquareKit.Internal.Cubical.NormalizedPaths

/-! The local presentation retains both the path and its selected constancy
face. Constancy remains a proposition about that data. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

abbrev IdentityData {Γ : Context.{u}} (A : Family Γ) (a b : Term A) (x : Γ.Elements) :=
  LocalPath (reindex A (projection (interval Γ))) a b x × Face.Carrier x.obj.unop.dimension

def IdentityElement.localData {Γ : Context.{u}} {A : Family Γ} {a b : Term A} {x : Γ.Elements}
    (p : IdentityElement A a b x) : IdentityData A a b x := ⟨p.path.toLocal,p.face⟩

abbrev LocalIdentity {Γ : Context.{u}} (A : Family Γ) (a b : Term A) (x : Γ.Elements) :=
  {s : IdentityData A a b x // ∃ p : IdentityElement A a b x, p.localData = s}

def IdentityElement.toLocal {Γ : Context.{u}} {A : Family Γ} {a b : Term A} {x : Γ.Elements}
    (p : IdentityElement A a b x) : LocalIdentity A a b x := ⟨p.localData,p,rfl⟩

def LocalIdentity.fromLocal {Γ : Context.{u}} {A : Family Γ} {a b : Term A} {x : Γ.Elements}
    (s : LocalIdentity A a b x) : IdentityElement A a b x where
  path := s.val.1.fromLocal
  face := s.val.2
  constant := by
    obtain ⟨p,hp⟩ := s.property
    have hpath : p.path = s.val.1.fromLocal :=
      (LocalPath.fromLocal_toLocal p.path).symm.trans (congrArg (fun t => t.1.fromLocal) hp)
    have hface : p.face = s.val.2 := congrArg Prod.snd hp
    intro y f hf r
    rw [← hpath]
    exact p.constant f (hface.symm ▸ hf) r

theorem LocalIdentity.fromLocal_toLocal {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    {x : Γ.Elements} (p : IdentityElement A a b x) : p.toLocal.fromLocal = p := by
  apply IdentityElement.ext
  · exact LocalPath.fromLocal_toLocal p.path
  · rfl

theorem LocalIdentity.toLocal_fromLocal {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    {x : Γ.Elements} (s : LocalIdentity A a b x) : s.fromLocal.toLocal = s := by
  apply Subtype.ext
  exact Prod.ext (LocalPath.toLocal_fromLocal s.val.1) rfl

def localIdentityEquiv {Γ : Context.{u}} (A : Family Γ) (a b : Term A) (x : Γ.Elements) :
    IdentityElement A a b x ≃ LocalIdentity A a b x where
  toFun := IdentityElement.toLocal
  invFun := LocalIdentity.fromLocal
  left_inv := LocalIdentity.fromLocal_toLocal
  right_inv := LocalIdentity.toLocal_fromLocal

end SquareKit.Cubical.Presheaf
