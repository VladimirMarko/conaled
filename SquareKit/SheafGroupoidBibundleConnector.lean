import SquareKit.SheafGroupoidBibundleConverse
import SquareKit.SheafGroupoidBundlePoints

/-! Unique left connectors from the full source functor. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bibundle
open SquareKit.SheafGroupoid.Bibundle SquareKit.SheafGroupoid.Bundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H : Operations J} [G.Laws] [H.Laws]
variable (P : Bibundle G H) {X : Sheaf J (Type (max u v))}

theorem globalConnector (ff : (sourceFunctor P (X := X)).FullyFaithful)
    (m n : G.Object X) (k : H.Object X)
    (p : PointTerm (Bundle.reindex P.right m.map) k)
    (q : PointTerm (Bundle.reindex P.right n.map) k) :
    ∃! g : m ⟶ n, ∀ z : X.obj.Elements,
      P.left.act (arrowValue G g z) (value H k z) (p.val z) = q.val z := by
  let fp := pointMap (Bundle.reindex P.right m.map) k p
  let fq := pointMap (Bundle.reindex P.right n.map) k q
  let e := asIso fp
  let g := ff.preimage (e.inv ≫ fq)
  have hg : fp ≫ sourceMap P g = fq := by
    change e.hom ≫ (sourceFunctor P).map (ff.preimage (e.inv ≫ fq)) = fq
    rw [ff.map_preimage, ← Category.assoc, e.hom_inv_id, Category.id_comp]
  have evaluate (f : m ⟶ n) :
      fp ≫ sourceMap P f = fq ↔ ∀ z : X.obj.Elements,
        P.left.act (arrowValue G f z) (value H k z) (p.val z) = q.val z := by
    constructor
    · intro he z
      have hv := congrArg (fun a : regular H k ⟶ Bundle.reindex P.right n.map =>
        a.hom.app (point H X z (value H k z)) (regularIdentity H k z)) he
      change (sourceMap P f).hom.app _ (fp.hom.app _ (regularIdentity H k z)) =
        fq.hom.app _ (regularIdentity H k z) at hv
      rw [pointMap_identity, pointMap_identity] at hv
      exact hv
    · intro he
      apply regularMap_ext
      intro z
      change (sourceMap P f).hom.app _ (fp.hom.app _ (regularIdentity H k z)) =
        fq.hom.app _ (regularIdentity H k z)
      rw [pointMap_identity, pointMap_identity]
      exact he z
  refine ⟨g, (evaluate g).mp hg, ?_⟩
  intro f hf
  apply ff.map_injective
  apply (cancel_epi fp).mp
  exact ((evaluate f).mpr hf).trans hg.symm

end SquareKit.SheafGroupoid.Bibundle
