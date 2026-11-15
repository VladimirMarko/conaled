import SquareKit.Internal.Cubical.ContextualIdentityImage
import SquareKit.Internal.Cubical.ContextualPathTail

namespace SquareKit.Cubical.Contextual
open CategoryTheory Presheaf SquareKit.Internal.PathTransport.Typed
universe u
variable (Base : LawfulFamily terminal.{u}) (Fiber : LawfulFamily (total Base.family))
local notation "M" => structuralModel Base Fiber
namespace IdentityElimination

theorem generated_reindex {Γ Δ : (M).Context} (A : (M).Family Γ) (a : (M).Section Γ A) {n}
    (T : StructuralModel.Telescope M ((M).pathContext A a) n) (C : (M).Family T.total) (t : Term C.family)
    (ht : Generated Base Fiber A a T C t) (σ : (M).Substitution Δ Γ) :
    Generated Base Fiber ((M).subTy A σ) ((M).subTm a σ) ((M).pathTail A a T σ)
      ((M).subTy C ((M).pathTailMap A a T σ)) (t.reindex ((M).pathTailMap A a T σ).down) := by
  let τ := NormalizedIdentitySingleton.reindexMap A.family a.down σ.down
  let T' := (M).pathTail A a T σ
  let e := Telescope.totalIso Base Fiber T
  let e' := Telescope.totalIso Base Fiber T'
  let s := ((M).pathTailMap A a T σ).down
  let r := (Telescope.realize Base Fiber T).map τ ≫ e.hom
  have hT := Telescope.pathTail_realize Base Fiber A a T σ
  have hs := Telescope.pathTail_square Base Fiber A a T σ
  have hc := family_reindex_context_square C.family s e'.hom (congrArg Presheaf.Telescope.context hT) r hs
  have hf := Filling.reindex_context_square C.filling s e'.hom (congrArg Presheaf.Telescope.context hT) r hs
  have hterm := Term.reindex_context_square t s e'.hom (congrArg Presheaf.Telescope.context hT) r hs
  have hfs := Telescope.pathTail_fillers Base Fiber A a T σ
  have h := NormalizedTelescopeIdentityElimination.generated_reindex A.family a.down
    (Telescope.realize Base Fiber T) (reindex C.family e.hom)
    (Telescope.fillers Base Fiber T) (Telescope.fillers_lawful Base Fiber T)
    (C.filling.reindex e.hom) (C.lawful.reindex e.hom) (t.reindex e.hom) ht σ.down
  exact (NormalizedTelescopeIdentityElimination.generated_heq (reindex A.family σ.down) (a.down.reindex σ.down)
    hT hc hfs (Telescope.fillers_lawful Base Fiber T')
    ((Telescope.fillers_lawful Base Fiber T).reindex τ) hf hterm).mpr h

end IdentityElimination
end SquareKit.Cubical.Contextual
