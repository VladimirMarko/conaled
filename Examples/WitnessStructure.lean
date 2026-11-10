import Examples.WitnessEquivalence
import SquareKit.WitnessErasure
import SquareKit.WitnessDistributionMap
import SquareKit.WitnessSourceNormalization

namespace Examples.WitnessStructure
open SquareKit
open Examples.WitnessEquivalence

def products : ProductOps one := ⟨fun _ _ => (), (), (), fun _ _ => ()⟩
def productCongr : SquareKit.WitnessEquivalence.ProductCongr witnesses products := ⟨fun p q => p && q⟩
def productLaws (chosen : Bool) : SquareKit.WitnessEquivalence.ProductLaws witnesses products :=
  ⟨fun _ _ => chosen, fun _ _ => chosen, fun _ => chosen⟩

def comparison : ProductMap (RawMap.id one) products products := fun _ _ => ⟨(), ()⟩
def inverse : ∀ a b, SquareKit.WitnessEquivalence.ComparisonLaws witnesses (comparison a b) := fun _ _ => ⟨false, true⟩
def preservation : SquareKit.WitnessEquivalence.ProductMapLaws witnesses comparison :=
  ⟨false, true, fun _ _ => false⟩
def transported (chosen : Bool) : SquareKit.WitnessEquivalence.ProductLaws witnesses products :=
  SquareKit.WitnessEquivalence.ProductMap.transportLaws preserves (reflection chosen) congruence laws inverse preservation
    productCongr (productLaws false)

theorem transport_keeps_selected_reflection :
    (transported false).fst_pair (a := ()) (b := ()) (c := ()) () () ≠
    (transported true).fst_pair (a := ()) (b := ()) (c := ()) () () := by
  change false ≠ true
  decide

def forward (chosen : Bool) :=
  (productLaws chosen).forward congruence (a := ()) (b := ()) (c := ())
    (f := ()) (g := ()) (k := ()) true

theorem projection_witnesses_computed : forward false = (true, true) := rfl

theorem erasedProducts : SquareKit.ProductLaws witnesses.erase products := (productLaws true).erase

-- Raw arrows distinguish the selected comparison from identity.
def arrows : CategoryOps Unit := ⟨fun _ _ => Bool, false, Bool.xor⟩
def arrowWitnesses : SquareKit.WitnessEquivalence arrows :=
  ⟨fun _ _ => Bool, fun _ => false, Bool.not, fun p q => p || q⟩
def arrowProducts : ProductOps arrows := ⟨fun _ _ => (), false, false, Bool.xor⟩
def nonidentity : ProductMap (RawMap.id arrows) arrowProducts arrowProducts :=
  fun _ _ => ⟨true, true⟩
def nonidentityInverse : ∀ a b, SquareKit.WitnessEquivalence.ComparisonLaws arrowWitnesses
    (nonidentity a b) := fun _ _ => ⟨false, true⟩
def nonidentityPreservation : SquareKit.WitnessEquivalence.ProductMapLaws arrowWitnesses
    nonidentity := ⟨false, true, fun _ _ => true⟩
theorem comparison_is_not_identity : (nonidentity () ()).hom ≠ arrows.ident (a := ()) := by
  change true ≠ false
  decide
theorem selected_inverse_witnesses_differ :
    (nonidentityInverse () ()).hom_inv ≠ (nonidentityInverse () ()).inv_hom := by
  change false ≠ true
  decide
theorem nonidentity_erasure_recovers : SquareKit.ProductMapLaws arrowWitnesses.erase
    nonidentity := nonidentityPreservation.erase
def arrowCongr : arrowWitnesses.Congr := ⟨fun p q => p && q⟩
def arrowLaws : arrowWitnesses.Laws := ⟨fun _ => false, fun _ => false, fun _ _ _ => false⟩
def native : SquareKit.WitnessEquivalence.CartesianH (H := arrowWitnesses) nonidentity :=
  nonidentityPreservation.felix arrowCongr arrowLaws nonidentityInverse
def nativeComposition := SquareKit.WitnessEquivalence.CartesianH.compose
  (SquareKit.WitnessEquivalence.Preservation.id arrowWitnesses) arrowCongr arrowLaws native native

theorem composed_comparison_computes :
    (SquareKit.ProductMap.comp nonidentity nonidentity () ()).hom = false := rfl
theorem composed_witness_computes :
    nativeComposition.pair (a := ()) (b := ()) (c := ()) true false = true := rfl

def closed : ClosedOps one products := ⟨fun _ _ => (), (), fun _ => ()⟩
def closedUniversal : SquareKit.WitnessEquivalence.ClosedUniversal (E := witnesses) closed :=
  ⟨fun p => p, fun p => !p⟩
def closedLaws := closedUniversal.laws congruence laws productCongr (productLaws false)
  (⟨fun p => p⟩ : SquareKit.WitnessEquivalence.ClosedCongr witnesses products closed)
theorem closed_selected_beta : closedLaws.beta (x := ()) (a := ()) (b := ()) () = true := rfl
theorem closed_selected_eta : closedLaws.eta (x := ()) (a := ()) (b := ()) () = false := rfl

def sums : CoproductOps one := ⟨fun _ _ => (), (), (), fun _ _ => ()⟩
def distribution : DistributionOps one products sums := ⟨()⟩
def distributionWitnesses : SquareKit.WitnessEquivalence.DistributionLaws witnesses products sums distribution :=
  ⟨fun _ _ _ => true, fun _ _ _ => false⟩
theorem distribution_witnesses_distinct : distributionWitnesses.collect_distribute () () () ≠
    distributionWitnesses.distribute_collect () () () := by
  change true ≠ false
  decide
theorem distribution_erasure : SquareKit.DistributionLaws one witnesses.erase products sums distribution :=
  distributionWitnesses.erase

def sourceClosed := closedUniversal.source congruence laws productCongr
def normalizedAgain := sourceClosed.normalized congruence laws productCongr
theorem normalization_is_not_a_witness_inverse :
    normalizedAgain.forward (x := ()) (a := ()) (b := ()) (f := ()) (g := ()) false ≠
      closedUniversal.forward (x := ()) (a := ()) (b := ()) (f := ()) (g := ()) false := by
  change true ≠ false
  decide

end Examples.WitnessStructure
