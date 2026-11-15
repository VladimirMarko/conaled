import SquareKit.PredicateCategory
import SquareKit.RelationalCategory
import SquareKit.Assembly

namespace SquareKit.PredicateCategory
universe u w
/-- The unary predicate is erased to existence when placed in a Prop-valued relation. -/
def toRelation : RawMap ops.{u,w} RelationalCategory.ops.{u} where
  obj A := ⟨A.Carrier,PUnit,fun x _ => Nonempty (A.pred x)⟩
  map f := ⟨f.toFun,id,fun ⟨h⟩ => ⟨f.imp _ h⟩⟩
theorem toRelation_laws : MapLaws toRelation.{u,w} equiv (equality _) := by
  constructor
  · intro a b f g h; exact Relational.RelSquare.ext (congrFun h) (fun _ => rfl)
  · intro; rfl
  · intros; rfl

/-- A binary relation becomes a predicate on the full pair of carriers. -/
def ofRelation : RawMap RelationalCategory.ops.{u} ops.{u,0} where
  obj A := ⟨A.R × A.S,fun x => PLift (A.Rel x.1 x.2)⟩
  map f := ⟨fun x => (f.impl x.1,f.spec x.2),fun _ h => ⟨f.preserves h.down⟩⟩
theorem ofRelation_laws : MapLaws ofRelation.{u} (equality _) equiv := by
  constructor
  · intro a b f g h; cases h; rfl
  · intro; rfl
  · intros; rfl

/-- An assembly provides a predicate of existence of realizers. No tracker is retained. -/
def ofAssembly : RawMap (ofCategory Realizability.Assembly.{u}) ops.{u,0} where
  obj A := ⟨A.Carrier,fun x => PLift (∃ n, A.realizes n x)⟩
  map f := ⟨f.toFun,fun x h => ⟨by
    obtain ⟨n,hn⟩ := h.down
    obtain ⟨φ,_,ht⟩ := f.tracked
    obtain ⟨m,_,hm⟩ := ht x n hn
    exact ⟨m,hm⟩⟩⟩
theorem ofAssembly_laws : MapLaws ofAssembly.{u} (equality _) equiv := by
  constructor
  · intro a b f g h; cases h; rfl
  · intro; rfl
  · intros; rfl

/-- Recovering an assembly map on natural numbers still requires computability. -/
theorem assembly_lift_requires_computable (f : Nat → Nat)
    (h : ∃ g : Realizability.Assembly.Hom (Realizability.Assembly.encoded Nat)
      (Realizability.Assembly.encoded Nat),
      (ofAssembly.map g).toFun = f) : Computable f :=
  (Realizability.Assembly.nat_tracked_iff f).mp h
end SquareKit.PredicateCategory
