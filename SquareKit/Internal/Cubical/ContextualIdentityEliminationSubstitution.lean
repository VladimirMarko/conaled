import SquareKit.Internal.Cubical.ContextualIdentityImageSubstitution

namespace SquareKit.Cubical.Contextual
open CategoryTheory Presheaf SquareKit.Internal.PathTransport.Typed
universe u
variable (Base : LawfulFamily terminal.{u}) (Fiber : LawfulFamily (total Base.family))
local notation "M" => structuralModel Base Fiber
namespace IdentityElimination

private theorem cast_section_heq {Γ : Presheaf.Context.{u}} {A B : LawfulFamily Γ}
    (e : A = B) (t : ULift.{u+1} (Term A.family)) :
    HEq ((cast (congrArg (fun C : LawfulFamily Γ => ULift.{u+1} (Term C.family)) e) t).down) t.down := by
  cases e
  rfl

theorem eliminate_reindex {Γ Δ : (M).Context} (A : (M).Family Γ) (a : (M).Section Γ A) {n}
    (T : StructuralModel.Telescope M ((M).pathContext A a) n) (C : (M).Family T.total)
    (d : (M).Section (StructuralModel.Telescope.pullback M T ((M).rootSub A a)).total
      ((M).subTy C ((M).rootTail A a T))) (σ : (M).Substitution Δ Γ) :
    eliminate Base Fiber ((M).subTy A σ) ((M).subTm a σ) ((M).pathTail A a T σ)
      ((M).subTy C ((M).pathTailMap A a T σ)) (((M).reindexBranch A a T σ C d).down) =
      (eliminate Base Fiber A a T C d.down).reindex ((M).pathTailMap A a T σ).down := by
  let t := eliminate Base Fiber A a T C d.down
  let s := t.reindex ((M).pathTailMap A a T σ).down
  have hi := reconstruct Base Fiber ((M).subTy A σ) ((M).subTm a σ) ((M).pathTail A a T σ)
    ((M).subTy C ((M).pathTailMap A a T σ)) s
    (generated_reindex Base Fiber A a T C t (generated_eliminate Base Fiber A a T C d.down) σ)
  have hs := congrArg ULift.down ((M).branchMap_square A a T σ)
  have hm := Term.reindex_heq_maps t hs
  have hb := congrArg (fun q => q.reindex ((M).branchMap A a T σ).down)
    (eliminate_beta Base Fiber A a T C d.down)
  have hc := cast_section_heq ((M).branchMap_type A a T σ C).symm ((M).subTm d ((M).branchMap A a T σ))
  have hbranch : ((M).reindexBranch A a T σ C d).down =
      s.reindex ((M).rootTail ((M).subTy A σ) ((M).subTm a σ) ((M).pathTail A a T σ)).down :=
    eq_of_heq (hc.trans ((heq_of_eq hb).symm.trans hm.symm))
  exact (congrArg (fun q => eliminate Base Fiber ((M).subTy A σ) ((M).subTm a σ)
    ((M).pathTail A a T σ) ((M).subTy C ((M).pathTailMap A a T σ)) q) hbranch).trans hi

end IdentityElimination
end SquareKit.Cubical.Contextual
