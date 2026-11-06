import SquareKit.Internal.Cubical.ContextualIdentityElimination
import SquareKit.Internal.Cubical.TelescopeIdentityImage

namespace SquareKit.Cubical.Contextual
open CategoryTheory Presheaf SquareKit.Internal.PathTransport.Typed
universe u
variable (Base : LawfulFamily terminal.{u}) (Fiber : LawfulFamily (total Base.family))
local notation "M" => structuralModel Base Fiber
namespace IdentityElimination
set_option backward.isDefEq.respectTransparency false

/-- An internal property of the selected result, not a replacement of its data. -/
def Generated {Γ : (M).Context} (A : (M).Family Γ) (a : (M).Section Γ A) {n}
    (T : StructuralModel.Telescope M ((M).pathContext A a) n) (C : (M).Family T.total) (t : Term C.family) : Prop :=
  NormalizedTelescopeIdentityElimination.Generated A.family a.down (Telescope.realize Base Fiber T)
    (reindex C.family (Telescope.totalIso Base Fiber T).hom)
    (Telescope.fillers Base Fiber T) (Telescope.fillers_lawful Base Fiber T)
    (C.filling.reindex (Telescope.totalIso Base Fiber T).hom) (t.reindex (Telescope.totalIso Base Fiber T).hom)

theorem generated_eliminate {Γ : (M).Context} (A : (M).Family Γ) (a : (M).Section Γ A) {n}
    (T : StructuralModel.Telescope M ((M).pathContext A a) n) (C : (M).Family T.total)
    (d : Term (reindex C.family ((M).rootTail A a T).down)) :
    Generated Base Fiber A a T C (eliminate Base Fiber A a T C d) := by
  unfold Generated eliminate
  rw [Term.descendIso_reindex]
  exact NormalizedTelescopeIdentityElimination.generated_eliminate _ _ _ _ _ _ _ _

theorem branch_restricted {Γ : (M).Context} (A : (M).Family Γ) (a : (M).Section Γ A) {n}
    (T : StructuralModel.Telescope M ((M).pathContext A a) n) (C : (M).Family T.total) (t : Term C.family) :
    branch Base Fiber A a T C (t.reindex ((M).rootTail A a T).down) =
      (t.reindex (Telescope.totalIso Base Fiber T).hom).reindex
        ((Telescope.realize Base Fiber T).map (NormalizedIdentitySingleton.reflexivity A.family a.down)) :=
  Term.reindexSquare_of_reindex C.family ((M).rootTail A a T).down
    (Telescope.branchIso Base Fiber A a T).hom
    ((Telescope.realize Base Fiber T).map (NormalizedIdentitySingleton.reflexivity A.family a.down))
    (Telescope.totalIso Base Fiber T).hom (Telescope.branch_square Base Fiber A a T).symm t

theorem reconstruct {Γ : (M).Context} (A : (M).Family Γ) (a : (M).Section Γ A) {n}
    (T : StructuralModel.Telescope M ((M).pathContext A a) n) (C : (M).Family T.total) (t : Term C.family)
    (ht : Generated Base Fiber A a T C t) :
    eliminate Base Fiber A a T C (t.reindex ((M).rootTail A a T).down) = t := by
  obtain ⟨d,hd⟩ := ht
  let r := (Telescope.realize Base Fiber T).map (NormalizedIdentitySingleton.reflexivity A.family a.down)
  have hb := NormalizedTelescopeIdentityElimination.eliminate_beta A.family a.down
    (Telescope.realize Base Fiber T) (reindex C.family (Telescope.totalIso Base Fiber T).hom) d
    (Telescope.fillers Base Fiber T) (Telescope.fillers_lawful Base Fiber T)
    (C.filling.reindex (Telescope.totalIso Base Fiber T).hom) (C.lawful.reindex _)
  have hbranch := (branch_restricted Base Fiber A a T C t).trans
    ((congrArg (fun q => q.reindex r) hd).trans hb)
  apply Term.reindex_injective_iso (Telescope.totalIso Base Fiber T)
  have he := congrArg (fun q => NormalizedTelescopeIdentityElimination.eliminate A.family a.down
    (Telescope.realize Base Fiber T) (reindex C.family (Telescope.totalIso Base Fiber T).hom) q
    (Telescope.fillers Base Fiber T) (Telescope.fillers_lawful Base Fiber T)
    (C.filling.reindex (Telescope.totalIso Base Fiber T).hom)) hbranch
  exact (Term.descendIso_reindex (Telescope.totalIso Base Fiber T)
    (assembled Base Fiber A a T C (t.reindex ((M).rootTail A a T).down))).trans (he.trans hd.symm)

end IdentityElimination
end SquareKit.Cubical.Contextual
