import SquareKit.Relations
import SquareKit.CommaOptionalExact

/-! Relation preservation stays primitive. The witness map retains both values;
its target is the shared comma category of exact representations. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.RelationalCategory
open Relational
universe u

def ops : CategoryOps RelRep.{u} where
  Hom := RelSquare
  ident := identity _
  comp := compose

def products : ProductOps ops.{u} where
  prod := product
  fst := first _ _
  snd := second _ _
  pair := pair

def terminal : TerminalOps ops.{u} := ⟨Relational.terminal, terminate _⟩

def closed : ClosedOps ops.{u} products where
  exp := exponential
  evaluation := evaluation _ _
  curry := curry

/-- An exact square is a relation-preserving pair of horizontal maps. -/
def graphMap : RawMap Comma.Exact.categoryOps ops.{u} where
  obj a := graph (Comma.Exact.toRep a)
  map f := ofSquare (Comma.Exact.toSquare f)

theorem graphMap_laws : MapLaws graphMap.{u} (equality _) (equality _) where
  congr := by intros; subst_vars; rfl
  ident := rfl
  comp _ _ := rfl

def witnessMap : RawMap ops.{u} Comma.Exact.categoryOps where
  obj a := Comma.Exact.ofRep (witness a)
  map f := Comma.Exact.ofSquare (witnessSquare f)

theorem witnessMap_laws : MapLaws witnessMap.{u} (equality _) (equality _) where
  congr := by intros; subst_vars; rfl
  ident := rfl
  comp _ _ := rfl

def graphProducts : ProductMap graphMap.{u} Comma.Exact.products products := fun _a _b => {
  hom := ⟨id, id, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩
  inv := ⟨id, id, fun h => Prod.ext h.1 h.2⟩ }

theorem graphProducts_inverse (a b : Comma.Exact.Object.{u}) :
    ComparisonLaws (equality _) (graphProducts a b) := ⟨rfl, rfl⟩

theorem graphProducts_laws : ProductMapLaws (equality _) graphProducts.{u} where
  fst := rfl
  snd := rfl
  pair _ _ := rfl

def implementation : RawMap ops.{u} FunctionCategory.ops := ⟨RelRep.R, RelSquare.impl⟩
def semantics : RawMap ops.{u} FunctionCategory.ops := ⟨RelRep.S, RelSquare.spec⟩

theorem implementation_laws : MapLaws implementation.{u} (equality _) (equality _) :=
  ⟨by intros; subst_vars; rfl, rfl, fun _ _ => rfl⟩
theorem semantics_laws : MapLaws semantics.{u} (equality _) (equality _) :=
  ⟨by intros; subst_vars; rfl, rfl, fun _ _ => rfl⟩

/-- Semantic projection preserves products strictly, independently of the relation. -/
def semanticsProducts : ProductMap semantics.{u} products FunctionCategory.products :=
  fun _ _ => Comparison.id _ _

theorem semanticsProducts_laws : ProductMapLaws (equality _) semanticsProducts.{u} :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

theorem categoryLaws : CategoryLaws ops.{u} (equality _) where
  id_comp f := RelSquare.ext (congrFun (FunctionCategory.laws.id_comp f.impl))
    (congrFun (FunctionCategory.laws.id_comp f.spec))
  comp_id f := RelSquare.ext (congrFun (FunctionCategory.laws.comp_id f.impl))
    (congrFun (FunctionCategory.laws.comp_id f.spec))
  assoc h g f := RelSquare.ext (congrFun (FunctionCategory.laws.assoc h.impl g.impl f.impl))
    (congrFun (FunctionCategory.laws.assoc h.spec g.spec f.spec))

/-- The reverse graph conversion also preserves the implementation map. -/
theorem ofSquare_toSquare {a b : Squares.Rep.{u}} (f : RelSquare (graph a) (graph b)) :
    ofSquare (toSquare f) = f := rfl

theorem graph_roundtrip {a b : Comma.Exact.Object.{u}} (f : Comma.Exact.Arrow a b) :
    Comma.Exact.ofSquare (toSquare (graphMap.map f)) = f := rfl

theorem exact_roundtrip {a b : Squares.Rep.{u}} (f : Squares.Square a b) :
    toSquare (graphMap.map (Comma.Exact.ofSquare f)) = f :=
  congrArg Comma.Exact.toSquare (graph_roundtrip (Comma.Exact.ofSquare f))

theorem witness_compose {a b c : RelRep.{u}} (g : RelSquare b c) (f : RelSquare a b) :
    witnessSquare (compose g f) = Squares.compose (witnessSquare g) (witnessSquare f) :=
  congrArg Comma.Exact.toSquare (witnessMap_laws.comp g f)

/-- A product witness splits into two complete witnesses. -/
def witnessProducts : ProductMap witnessMap.{u} products Comma.Exact.products := fun a b => {
  hom := Comma.Exact.ofSquare (a := witness (product a b)) (b := Squares.product (witness a) (witness b)) {
    impl p := (⟨(p.val.1.1, p.val.2.1), p.property.1⟩,
      ⟨(p.val.1.2, p.val.2.2), p.property.2⟩)
    spec := id
    commutes _ := rfl }
  inv := Comma.Exact.ofSquare (a := Squares.product (witness a) (witness b)) (b := witness (product a b)) {
    impl p := ⟨((p.1.val.1, p.2.val.1), (p.1.val.2, p.2.val.2)),
      ⟨p.1.property, p.2.property⟩⟩
    spec := id
    commutes _ := rfl } }

theorem witnessProducts_inverse (a b : RelRep.{u}) :
    ComparisonLaws (equality _) (witnessProducts a b) where
  hom_inv := rfl
  inv_hom := rfl

theorem witnessProducts_laws : ProductMapLaws (equality _) witnessProducts.{u} where
  fst := rfl
  snd := rfl
  pair _ _ := rfl

def witnessTerminal : TerminalMap witnessMap.{u} terminal Comma.Exact.terminal where
  hom := Comma.Exact.ofSquare (Squares.terminate (witness Relational.terminal))
  inv := Comma.Exact.ofSquare (a := Squares.terminal) (b := witness Relational.terminal) {
    impl _ := ⟨(PUnit.unit, PUnit.unit), True.intro⟩
    spec := id
    commutes _ := rfl }

theorem witnessTerminal_inverse : ComparisonLaws (equality _) witnessTerminal.{u} :=
  ⟨rfl, rfl⟩
theorem witnessTerminal_laws : TerminalMapLaws (equality _) witnessTerminal.{u} := ⟨rfl⟩

/-- Shared composition of interpretation maps needs no new preservation proof. -/
theorem graphWitness_laws : MapLaws (graphMap.{u}.comp witnessMap) (equality _) (equality _) :=
  RawMap.comp_laws graphMap_laws witnessMap_laws

/-- Function witnesses give compatible functions on witness spaces. This is
only a forward map: arbitrary witness functions may inspect semantic data. -/
def witnessFunction (a b : RelRep.{u}) : Squares.Square
    (witness (exponential a b)) (Squares.exponential (witness a) (witness b)) where
  impl p := ⟨(fun x => ⟨(p.val.1 x.val.1, p.val.2 x.val.2), p.property x.property⟩, p.val.2), fun _ => rfl⟩
  spec := id
  commutes _ := rfl

/-- Evaluation consumes exactly the original function relation. -/
theorem witness_evaluation (a b : RelRep.{u}) :
    Squares.compose (Squares.evaluation (witness a) (witness b))
      (Squares.compose (Squares.pair
        (Squares.compose (witnessFunction a b) (Squares.first _ _)) (Squares.second _ _))
        (Comma.Exact.toSquare (witnessProducts (exponential a b) a).hom)) =
      witnessSquare (evaluation a b) := rfl

theorem witness_curry {x a b : RelRep.{u}} (f : RelSquare (product x a) b) :
    Squares.compose (witnessFunction a b) (witnessSquare (curry f)) =
      Squares.curry (Squares.compose (witnessSquare f)
        (Comma.Exact.toSquare (witnessProducts x a).inv)) := rfl

theorem productLaws : ProductLaws (equality ops.{u}) products where
  fst_pair f g := RelSquare.ext (congrFun (FunctionCategory.productLaws.fst_pair f.impl g.impl))
    (congrFun (FunctionCategory.productLaws.fst_pair f.spec g.spec))
  snd_pair f g := RelSquare.ext (congrFun (FunctionCategory.productLaws.snd_pair f.impl g.impl))
    (congrFun (FunctionCategory.productLaws.snd_pair f.spec g.spec))
  pair_eta f := RelSquare.ext (congrFun (FunctionCategory.productLaws.pair_eta f.impl))
    (congrFun (FunctionCategory.productLaws.pair_eta f.spec))

theorem closedLaws : ClosedLaws (equality ops.{u}) products closed where
  beta := uncurry_curry
  eta := curry_uncurry
  natural _ _ := RelSquare.ext (fun _ => rfl) (fun _ => rfl)

/-- Public product and closed interfaces recover the original statements. -/
theorem recover_first_pair {x a b : RelRep.{u}} (f : RelSquare x a) (g : RelSquare x b) :
    compose (first a b) (pair f g) = f := productLaws.fst_pair f g

theorem recover_second_pair {x a b : RelRep.{u}} (f : RelSquare x a) (g : RelSquare x b) :
    compose (second a b) (pair f g) = g := productLaws.snd_pair f g

theorem recover_pair_eta {x a b : RelRep.{u}} (f : RelSquare x (product a b)) :
    pair (compose (first a b) f) (compose (second a b) f) = f := productLaws.pair_eta f

theorem recover_uncurry_curry {x a b : RelRep.{u}} (f : RelSquare (product x a) b) :
    uncurry (curry f) = f := closedLaws.beta f

theorem recover_curry_uncurry {x a b : RelRep.{u}} (f : RelSquare x (exponential a b)) :
    curry (uncurry f) = f := closedLaws.eta f

end SquareKit.RelationalCategory
