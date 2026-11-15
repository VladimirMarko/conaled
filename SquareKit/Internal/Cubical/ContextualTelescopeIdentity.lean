import SquareKit.Internal.Cubical.ContextualTelescopes
import SquareKit.Internal.Cubical.ContextualIdentityContexts
import SquareKit.Internal.Cubical.NormalizedTelescopeIdentityElimination
import SquareKit.Internal.Cubical.ContextIsoSectionSquares

namespace SquareKit.Cubical.Contextual
open CategoryTheory Presheaf SquareKit.Internal.PathTransport.Typed
universe u
variable (Base : LawfulFamily terminal.{u}) (Fiber : LawfulFamily (total Base.family))
local notation "M" => structuralModel Base Fiber
namespace Telescope
set_option backward.isDefEq.respectTransparency false
variable {Γ : Context.{u}} (A : LawfulFamily Γ) (a : ULift.{u+1} (Term A.family))
  {n : Nat}

noncomputable def totalIso {Γ n} (T : StructuralModel.Telescope M Γ n) : (realize Base Fiber T).context ≅ T.total := eqToIso (total_eq Base Fiber T)

theorem branch_context_eq (T : StructuralModel.Telescope M ((M).pathContext A a) n) :
    ((realize Base Fiber T).reindex (NormalizedIdentitySingleton.reflexivity A.family a.down)).context =
      (StructuralModel.Telescope.pullback M T ((M).rootSub A a)).total := by
  rw [← rootSub_eq Base Fiber A a, ← realize_pullback Base Fiber T]
  exact total_eq Base Fiber _

noncomputable def branchIso (T : StructuralModel.Telescope M ((M).pathContext A a) n) :
    ((realize Base Fiber T).reindex (NormalizedIdentitySingleton.reflexivity A.family a.down)).context ≅
      (StructuralModel.Telescope.pullback M T ((M).rootSub A a)).total :=
  eqToIso (branch_context_eq Base Fiber A a T)

private theorem map_congr {Ω Ξ : Context.{u}} (S : Presheaf.Telescope Ω)
    {σ τ : Ξ ⟶ Ω} (e : σ = τ) :
    eqToHom (congrArg (fun f => (S.reindex f).context) e) ≫ S.map τ = S.map σ := by
  cases e
  simp

theorem branch_square (T : StructuralModel.Telescope M ((M).pathContext A a) n) :
    (branchIso Base Fiber A a T).hom ≫ ((M).rootTail A a T).down =
      (realize Base Fiber T).map (NormalizedIdentitySingleton.reflexivity A.family a.down) ≫
        (totalIso Base Fiber T).hom := by
  have h := map_eq Base Fiber T ((M).rootSub A a)
  have hmap := congrArg (fun f => eqToHom (branch_context_eq Base Fiber A a T) ≫ f) h
  have hr := map_congr (realize Base Fiber T) (rootSub_eq Base Fiber A a).symm
  exact hmap.symm.trans (by
    simpa only [branchIso, totalIso, eqToIso.hom, ← Category.assoc, eqToHom_trans] using
      (congrArg (fun f => f ≫ (totalIso Base Fiber T).hom) hr))

end Telescope
end SquareKit.Cubical.Contextual
