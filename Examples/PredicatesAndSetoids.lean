import SquareKit.PredicateComparisons
import SquareKit.SetoidCategory

namespace Examples.PredicatesAndSetoids
open SquareKit
universe u w

def emptyPredicate : PredicateCategory.Obj := ⟨Bool,fun _ => Empty⟩
def falseMap : PredicateCategory.Hom emptyPredicate emptyPredicate := ⟨fun _ => false,fun _ h => h.elim⟩
def trueMap : PredicateCategory.Hom emptyPredicate emptyPredicate := ⟨fun _ => true,fun _ h => h.elim⟩

theorem no_admissible_inputs (x : Bool) : ¬ Nonempty (emptyPredicate.pred x) := fun ⟨h⟩ => h.elim
/-- Total-function equality still observes inputs whose predicates are empty. -/
theorem empty_predicate_arrows_differ : ¬ PredicateCategory.equiv.Rel falseMap trueMap := by
  intro h
  have bad := congrFun h false
  cases bad

def witnessed : PredicateCategory.Obj := ⟨Unit,fun _ => Bool⟩
def keepWitness : PredicateCategory.Hom witnessed witnessed := ⟨id,fun _ => id⟩
def flipWitness : PredicateCategory.Hom witnessed witnessed := ⟨id,fun _ => Bool.not⟩
theorem witness_maps_distinct : keepWitness ≠ flipWitness := by
  intro h
  have bad := congrArg (fun f : PredicateCategory.Hom witnessed witnessed => f.imp () false) h
  cases bad
theorem witness_maps_equivalent : PredicateCategory.equiv.Rel keepWitness flipWitness := rfl

def liftedPredicate (A : Type u) : PredicateCategory.Obj.{u,w} := ⟨A,fun _ => PUnit.{w+1}⟩
theorem predicate_universes (A : Type u) (a : A) :
    (PredicateCategory.ops.ident (a := liftedPredicate.{u,w} A)).imp a PUnit.unit = PUnit.unit := rfl

theorem product_witness :
    (PredicateCategory.products.pair keepWitness flipWitness).imp () false = (false,true) := rfl

theorem relational_map_preserves :
    (PredicateCategory.toRelation.map flipWitness).impl () = () := rfl

def parity : SetoidCategory.Obj := ⟨Nat,{
  r := fun x y => x % 2 = y % 2
  iseqv := ⟨fun _ => rfl,Eq.symm,Eq.trans⟩ }⟩
def parityId : SetoidCategory.Hom parity parity := ⟨id,fun h => h⟩
def plusTwo : SetoidCategory.Hom parity parity := ⟨fun x : Nat => x+2,by
  intro x y h
  change Nat at x y
  change x%2 = y%2 at h
  change (x+2)%2 = (y+2)%2
  simpa using h⟩
theorem parity_related : SetoidCategory.equiv.Rel parityId plusTwo := by
  intro x
  change Nat at x
  change x%2 = (x+2)%2
  omega

theorem parity_functions_distinct : parityId.toFun ≠ plusTwo.toFun := by
  intro h
  have bad := congrFun h (0 : Nat)
  cases bad

theorem setoid_pair_recovers : SetoidCategory.equiv.Rel
    (SetoidCategory.ops.comp SetoidCategory.products.fst
      (SetoidCategory.products.pair parityId plusTwo)) parityId :=
  SetoidCategory.product_laws.fst_pair parityId plusTwo

theorem setoid_curry_recovers (f : SetoidCategory.Hom (SetoidCategory.prod parity parity) parity) :
    SetoidCategory.equiv.Rel (SetoidCategory.closed.uncurry (SetoidCategory.closed.curry f)) f :=
  SetoidCategory.closed_laws.beta f

theorem left_distribution_recovers :
    SetoidCategory.equiv.Rel
      (SetoidCategory.ops.comp (collect SetoidCategory.ops SetoidCategory.products SetoidCategory.coproducts
        (a := parity) (b := parity) (c := parity)) SetoidCategory.distribution.distribute)
      SetoidCategory.ops.ident := SetoidCategory.distribution_laws.collect_distribute _ _ _
theorem right_distribution_recovers :
    SetoidCategory.equiv.Rel
      (SetoidCategory.ops.comp (collectRight SetoidCategory.products SetoidCategory.coproducts
        (a := parity) (b := parity) (c := parity)) SetoidCategory.rightDistribution.distribute)
      SetoidCategory.ops.ident := SetoidCategory.rightDistribution_laws.collect_distribute _ _ _
theorem assembly_underlying {A B : Realizability.Assembly.{u}} (f : Realizability.Assembly.Hom A B)
    (x : A.Carrier) : (PredicateCategory.ofAssembly.map f).toFun x = f.toFun x := rfl

theorem setoid_sum_recovers : SetoidCategory.equiv.Rel
    (SetoidCategory.ops.comp (SetoidCategory.coproducts.copair parityId plusTwo)
      SetoidCategory.coproducts.inr) plusTwo := SetoidCategory.coproduct_laws.right _ _
end Examples.PredicatesAndSetoids
