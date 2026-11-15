import SquareKit.SelectedFeedback
import SquareKit.CategoryProduct
import SquareKit.ObjectReindexBasic

namespace SquareKit.SelectedFeedback
universe u v w u' v' w' r

/-- Product feedback keeps each component's witness independently. -/
def product {O : Type u} {Q : Type u'} {C : CategoryOps.{u,v} O}
    {D : CategoryOps.{u',v'} Q} {p : O → O → O} {q : Q → Q → Q}
    (T : SelectedFeedback C p) (U : SelectedFeedback D q) :
    SelectedFeedback (CategoryProduct.ops C D)
      (fun a b => (p a.1 b.1, q a.2 b.2)) where
  WF f := T.WF f.1 × U.WF f.2
  trace f h := (T.trace f.1 h.1, U.trace f.2 h.2)

/-- Pull back raw arrows along an object function, without quotienting objects. -/
abbrev reindexed {O : Type u} {J : Type r} (C : CategoryOps.{u,v} O)
    (F : J → O) : CategoryOps J := ObjectReindex.ops C F

/-- The two comparison arrows need no inverse laws to define raw feedback. -/
def reindex {O : Type u} {J : Type r} {C : CategoryOps.{u,v} O}
    {p : O → O → O} (T : SelectedFeedback C p) (F : J → O)
    (q : J → J → J) (comparison : ∀ a b, Comparison C (F (q a b)) (p (F a) (F b))) :
    SelectedFeedback (reindexed C F) q where
  WF {a b s} f := T.WF (C.comp (comparison b s).hom
    (C.comp f (comparison a s).inv))
  trace {a b s} f h := T.trace
    (C.comp (comparison b s).hom (C.comp f (comparison a s).inv)) h

end SquareKit.SelectedFeedback
