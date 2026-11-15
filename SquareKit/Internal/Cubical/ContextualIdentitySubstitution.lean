import SquareKit.Internal.Cubical.ContextualIdentityContexts
import SquareKit.Internal.Cubical.NormalizedIdentityContextMaps

namespace SquareKit.Cubical.Contextual
open CategoryTheory Presheaf SquareKit.Internal.PathTransport.Typed
universe u
variable (Base : LawfulFamily terminal.{u}) (Fiber : LawfulFamily (total Base.family))
local notation "M" => structuralModel Base Fiber

private theorem cast_section_heq {Γ : Presheaf.Context.{u}} {A B : LawfulFamily Γ}
    (e : A = B) (t : ULift.{u+1} (Term A.family)) :
    HEq ((cast (congrArg (fun C : LawfulFamily Γ => ULift.{u+1} (Term C.family)) e) t).down) t.down := by
  cases e
  rfl

private theorem map_eqToHom_heq {Γ Δ : Context.{u}} {A B : Family Γ} (e : A = B)
    (σ : Δ ⟶ Γ) (p : Term (reindex A σ)) :
    HEq (Term.map (Functor.whiskerLeft σ.mapElements (eqToHom e)) p) p := by cases e; rfl

set_option backward.isDefEq.respectTransparency false in
theorem pathSub_eq {Γ Δ : (M).Context} (A : (M).Family Γ) (a : (M).Section Γ A)
    (σ : (M).Substitution Δ Γ) :
    ((M).pathSub A a σ).down = NormalizedIdentitySingleton.reindexMap A.family a.down σ.down := by
  rw [← NormalizedIdentitySingleton.directMap_eq]
  unfold NormalizedIdentitySingleton.directMap
  rw [familyReindexMap_pair]
  apply congrArg (pair (projection (NormalizedIdentitySingleton.fiber (reindex A.family σ.down)
    (a.down.reindex σ.down)) ≫ liftSub A.family σ.down))
  apply eq_of_heq
  exact (cast_section_heq ((M).pathSub_type A a σ).symm
    ⟨generic (NormalizedIdentitySingleton.fiber (reindex A.family σ.down) (a.down.reindex σ.down))⟩).trans
      (map_eqToHom_heq (NormalizedIdentitySingleton.familyEquality A.family a.down σ.down).symm
        (projection (NormalizedIdentitySingleton.fiber (reindex A.family σ.down) (a.down.reindex σ.down)))
        (generic (NormalizedIdentitySingleton.fiber (reindex A.family σ.down) (a.down.reindex σ.down)))).symm

end SquareKit.Cubical.Contextual
