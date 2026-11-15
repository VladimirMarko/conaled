import SquareKit.Internal.Cubical.ContextualIdentitySubstitution
import SquareKit.Internal.Cubical.ContextualTelescopeSubstitution
import SquareKit.Internal.Cubical.ContextualTelescopeIdentity
import SquareKit.Internal.Cubical.ContextEqualityReindex

namespace SquareKit.Cubical.Contextual
open CategoryTheory Presheaf SquareKit.Internal.PathTransport.Typed
universe u
variable (Base : LawfulFamily terminal.{u}) (Fiber : LawfulFamily (total Base.family))
local notation "M" => structuralModel Base Fiber
namespace Telescope

theorem pathTail_realize {Γ Δ : (M).Context} (A : (M).Family Γ) (a : (M).Section Γ A) {n}
    (T : StructuralModel.Telescope M ((M).pathContext A a) n) (σ : (M).Substitution Δ Γ) :
    realize Base Fiber ((M).pathTail A a T σ) =
      (realize Base Fiber T).reindex (NormalizedIdentitySingleton.reindexMap A.family a.down σ.down) :=
  (realize_pullback Base Fiber T ((M).pathSub A a σ)).trans
    (congrArg (realize Base Fiber T).reindex (pathSub_eq Base Fiber A a σ))

set_option backward.isDefEq.respectTransparency false in
theorem pathTail_square {Γ Δ : (M).Context} (A : (M).Family Γ) (a : (M).Section Γ A) {n}
    (T : StructuralModel.Telescope M ((M).pathContext A a) n) (σ : (M).Substitution Δ Γ) :
    (totalIso Base Fiber ((M).pathTail A a T σ)).hom ≫ ((M).pathTailMap A a T σ).down =
      eqToHom (congrArg Presheaf.Telescope.context (pathTail_realize Base Fiber A a T σ)) ≫
        (realize Base Fiber T).map (NormalizedIdentitySingleton.reindexMap A.family a.down σ.down) ≫
        (totalIso Base Fiber T).hom := by
  have h := congrArg (fun f => (totalIso Base Fiber ((M).pathTail A a T σ)).hom ≫ f)
    (map_eq Base Fiber T ((M).pathSub A a σ))
  have hm := (realize Base Fiber T).map_congr (pathSub_eq Base Fiber A a σ)
  have hc := congrArg (fun f => eqToHom (congrArg Presheaf.Telescope.context
      (realize_pullback Base Fiber T ((M).pathSub A a σ))) ≫ f ≫ (totalIso Base Fiber T).hom) hm
  exact h.symm.trans (by simpa only [totalIso,eqToIso.hom,← Category.assoc,eqToHom_trans,
    eqToHom_refl,Category.id_comp] using hc.symm)

theorem pathTail_fillers {Γ Δ : (M).Context} (A : (M).Family Γ) (a : (M).Section Γ A) {n}
    (T : StructuralModel.Telescope M ((M).pathContext A a) n) (σ : (M).Substitution Δ Γ) :
    HEq (fillers Base Fiber ((M).pathTail A a T σ))
      ((fillers Base Fiber T).reindex (NormalizedIdentitySingleton.reindexMap A.family a.down σ.down)) :=
  (fillers_pullback Base Fiber T ((M).pathSub A a σ)).trans
    (Presheaf.Telescope.Fillings.reindex_heq (fillers Base Fiber T) (pathSub_eq Base Fiber A a σ))

end Telescope
end SquareKit.Cubical.Contextual
