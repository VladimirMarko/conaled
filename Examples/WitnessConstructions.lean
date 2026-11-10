import Examples.WitnessStructure
import SquareKit.WitnessArrow
import SquareKit.WitnessSquared
import SquareKit.WitnessObjectReindex
import SquareKit.WitnessMorphismRestriction
import SquareKit.WitnessMonoid

namespace Examples.WitnessConstructions
open SquareKit
open Examples.WitnessEquivalence
open Examples.WitnessStructure (products productCongr productLaws)

-- Independent expectations: projection preserves the chosen component, and
-- square equality must retain its commutativity witness even when side relations ignore it.
def productRelation := WitnessProduct.equiv one one witnesses witnesses
example : (WitnessProduct.fst_laws witnesses witnesses).congr
    (a := ((),())) (b := ((),())) (f := ((),())) (g := ((),())) (true,false) = true := rfl
example : (WitnessProduct.snd_laws witnesses witnesses).congr
    (a := ((),())) (b := ((),())) (f := ((),())) (g := ((),())) (true,false) = false := rfl

def commaRelation := WitnessComma.equiv congruence laws preserves preserves
example : commaRelation.Rel (square false) (square true) := (true,false)
example : square false ≠ square true := squares_distinct
example : (WitnessComma.toProduct_laws congruence laws preserves preserves).congr
    (f := square false) (g := square true) (true,false) = (true,false) := rfl

def composedProjection := SquareKit.WitnessEquivalence.Preservation.compose
  (WitnessComma.toProduct_laws congruence laws preserves preserves)
  (WitnessProduct.fst_laws witnesses witnesses)
example : composedProjection.congr (f := square false) (g := square true) (true,false) = true := rfl
example : (commaRelation.erase.Rel (square false) (square true)) ↔
    (Comma.equiv congruence.erase laws.erase preserves.erase preserves.erase).Rel
      (square false).erase (square true).erase := WitnessComma.erase_relation _ _ _ _ _ _

-- A non-involutive symmetry is permitted. Transposition cannot silently assume otherwise.
def constantSymmetry : SquareKit.WitnessEquivalence one :=
  ⟨fun _ _ => Bool,fun _ => false,fun _ => false,fun h _ => h⟩
def marked : WitnessArrow.Hom constantSymmetry object object := ⟨(),(),true⟩
example : WitnessArrow.transpose (WitnessArrow.transpose marked) ≠ marked := by
  intro h
  have q := congrArg WitnessComma.Hom.commutes h
  exact Bool.false_ne_true q
example : (WitnessArrow.transpose (WitnessArrow.transpose marked)).erase = marked.erase :=
  WitnessComma.Hom.erase_eq _ _ rfl rfl

example : (WitnessArrow.vertical congruence laws (square false) (square true) false).left = () := rfl
example : (WitnessComma.vertical congruence laws (square false) (square true) false).erase =
    Comma.vertical congruence.erase laws.erase (square false).erase (square true).erase ⟨false⟩ :=
  WitnessComma.erase_vertical _ _ _ _ _

def arrowSquareProducts := WitnessArrow.products congruence laws products productCongr (productLaws true)
def arrowProductLaws := WitnessArrow.products_laws congruence laws products productCongr (productLaws true)
example : arrowProductLaws.fst_pair (square false) (square true) = (true,true) := rfl
example : SquareKit.ProductLaws (WitnessArrow.equiv congruence laws).erase arrowSquareProducts :=
  arrowProductLaws.erase

-- Squared has one target witness, whereas Product has two independently chosen witnesses.
def squaredRelation := WitnessSquared.induced products witnesses
example : squaredRelation.Rel (a := ((),())) (b := ((),())) ((),()) ((),()) := true
example : (WitnessSquared.map_laws congruence laws productCongr (productLaws false)).congr
    (a := ((),())) (b := ((),())) (f := ((),())) (g := ((),())) (true,false) = false := rfl
example : (squaredRelation.erase) = (Squared.unsquare products).induced witnesses.erase :=
  WitnessSquared.erase_induced products witnesses
example : squaredRelation.Laws := WitnessSquared.induced_laws congruence laws productCongr (productLaws false)

-- Object reindexing permits a noninjective object map and nonidentity product comparisons.
open Examples.WitnessStructure (arrows arrowWitnesses arrowProducts arrowCongr arrowLaws)
def collapse : Bool → Unit := fun _ => ()
def compare (_ _ : Bool) : Comparison arrows () () := ⟨true,true⟩
def reindexedProducts := ObjectReindex.products collapse arrowProducts (fun x _ => x) compare
def compareLaws (a b : Bool) : SquareKit.WitnessEquivalence.ComparisonLaws arrowWitnesses (compare a b) :=
  ⟨false,true⟩
def reindexedProductLaws : SquareKit.WitnessEquivalence.ProductLaws
    (WitnessObjectReindex.equiv collapse arrowWitnesses) reindexedProducts :=
  WitnessObjectReindex.product_laws collapse arrowCongr arrowLaws arrowProducts (fun x _ => x)
    compare compareLaws ⟨fun p q => p && q⟩ ⟨fun _ _ => false,fun _ _ => true,fun _ => false⟩
example : (ObjectReindex.products collapse arrowProducts (fun x _ => x) compare).fst
    (a := false) (b := true) = true := rfl
example : SquareKit.ProductLaws (WitnessObjectReindex.equiv collapse arrowWitnesses).erase reindexedProducts :=
  reindexedProductLaws.erase

-- Morphism admissibility and semantic witnesses are separate pieces of data.
def admissible : {a b : Unit} → one.Hom a b → Type := fun _ => Bool
def closure : MorphismRestriction.CategoryClosure one admissible := ⟨false,fun h k => h && k⟩
def restricted (b : Bool) : MorphismRestriction.Hom one admissible () () := ⟨(),b⟩
example : restricted false ≠ restricted true := by
  intro h
  exact Bool.false_ne_true (congrArg MorphismRestriction.Hom.sat h)
example : (WitnessMorphismRestriction.equiv closure witnesses).Rel (restricted false) (restricted true) := true
example : (WitnessMorphismRestriction.forget_laws closure witnesses).congr
    (f := restricted false) (g := restricted true) true = true := rfl
example : (WitnessMorphismRestriction.equiv closure witnesses).Laws :=
  WitnessMorphismRestriction.laws closure laws

-- A raw monoid needs selected witnesses, without equations on witness composition.
def rawMonoid : SetoidMonoid.Ops Bool := ⟨false,Bool.xor⟩
def monoidRelation : WitnessMonoid.Relation Bool :=
  ⟨fun _ _ => Bool,fun _ => false,Bool.not,fun h k => !(h && k)⟩
def monoidLaws : WitnessMonoid.Laws rawMonoid monoidRelation :=
  ⟨fun h k => h && k,fun _ => true,fun _ => false,fun _ _ _ => true⟩
example : (WitnessMonoid.laws monoidLaws).id_comp (a := ()) (b := ()) true = true := rfl
example : SetoidMonoid.Laws rawMonoid monoidRelation.erase := monoidLaws.erase

end Examples.WitnessConstructions
