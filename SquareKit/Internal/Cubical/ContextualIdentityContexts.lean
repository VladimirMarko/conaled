import SquareKit.Internal.Cubical.ContextualStructuralModel
import SquareKit.Internal.Cubical.NormalizedIdentityElimination
import SquareKit.Internal.Cubical.NormalizedIdentitySubstitution
import SquareKit.Internal.PathTransport.ContextualModel

namespace SquareKit.Cubical.Contextual
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Presheaf SquareKit.Internal.PathTransport.Typed
universe u
variable (Base : LawfulFamily terminal.{u}) (Fiber : LawfulFamily (total Base.family))
local notation "M" => structuralModel Base Fiber

private theorem cast_section_heq {Γ : Presheaf.Context.{u}} {A B : LawfulFamily Γ}
    (e : A = B) (t : ULift.{u+1} (Term A.family)) :
    HEq ((cast (congrArg (fun C : LawfulFamily Γ => ULift.{u+1} (Term C.family)) e) t).down) t.down := by
  cases e
  rfl

theorem rootSub_eq {Γ : Presheaf.Context.{u}} (A : LawfulFamily Γ) (a : ULift.{u+1} (Term A.family)) :
    ((M).rootSub A a).down = NormalizedIdentitySingleton.reflexivity A.family a.down := by
  let C := reindex A.family (projection A.family)
  let x := a.down.reindex (projection A.family)
  let y := generic A.family
  let σ := pair (𝟙 Γ) a.down
  let p := normalizedIdentityRefl a.down
  have h := normalizedIdentity_fromReindexed C x y σ p
  have he : Term.map (normalizedIdentityIso (reindex C σ) (x.reindex σ) (y.reindex σ)).inv p = identityRefl a.down :=
    Term.map_iso_roundtrip (normalizedIdentityIso A.family a.down a.down) (identityRefl a.down)
  rw [he] at h
  have rhs : NormalizedIdentitySingleton.reflexivity A.family a.down =
      pair σ (p.convert (normalizedIdentity_reindex C x y σ).symm) :=
    congrArg (pair σ) h
  rw [rhs]
  apply congrArg (pair σ)
  apply eq_of_heq
  exact (cast_section_heq ((M).pathFamily_root A a).symm ⟨p⟩).trans
    (Term.convert_heq _ p).symm

end SquareKit.Cubical.Contextual
