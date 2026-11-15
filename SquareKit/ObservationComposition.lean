import SquareKit.IndexedCompositional
import SquareKit.ObservationExtension

/-! Compare constructor/observer extensions through local compatibility with a
common independent interpretation. Equality of old cells alone is insufficient. -/
namespace SquareKit.IndexedCompositional.Rule
universe i o b a x d
variable {I : Type i} {S : Signature.{i,o} I} {B : Behavior.{i,b,a} I}

/-- Two extension orders agree on finite observations if both discharge all
local constructor/observer interactions against the same native interpretation. -/
theorem compare_observations (left right : Rule S B)
    {D : I → Type d} {X : I → Type x}
    (alg : ∀ {j} (op : S.Op j), (∀ k, D (S.child op k)) → D j)
    (native : B.Coalgebra D)
    (hl : left.Compatible alg native) (hr : right.Compatible alg native)
    (c : B.Coalgebra X) (f : ∀ j, X j → D j) (hf : B.Morphism c native f)
    {j k} (path : B.Path j k) (t : Term S X j) :
    B.observe (left.lift c) path t = B.observe (right.lift c) path t := by
  have l := B.observe_morphism _ _ _ (left.fold_morphism alg native hl c f hf) path t
  have r := B.observe_morphism _ _ _ (right.fold_morphism alg native hr c f hf) path t
  exact l.symm.trans r

end SquareKit.IndexedCompositional.Rule
