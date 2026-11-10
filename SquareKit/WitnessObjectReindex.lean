import SquareKit.ObjectReindex
import SquareKit.WitnessFelixPreservation
namespace SquareKit.WitnessObjectReindex
open ObjectReindex (ops forget terminal products initial coproducts)
universe u v r
variable {O : Type u} {J : Type r} {C : CategoryOps.{u,v} O} (F : J → O)
def equiv (E : WitnessEquivalence C) : WitnessEquivalence (ops C F) :=
  WitnessEquivalence.induced (forget C F) E
def forget_laws (E : WitnessEquivalence C) : WitnessEquivalence.Preservation (forget C F) (equiv F E) E :=
  ⟨fun h => h, E.refl _,fun _ _ => E.refl _⟩
def congr {E : WitnessEquivalence C} (K : E.Congr) : (equiv F E).Congr := ⟨K.comp⟩
def laws {E : WitnessEquivalence C} (L : E.Laws) : (equiv F E).Laws :=
  ⟨L.id_comp,L.comp_id,L.assoc⟩
variable {E : WitnessEquivalence C}
def terminal_preserves (T : TerminalOps C) (unit : J) (i : Comparison C (F unit) T.unit) :
    WitnessEquivalence.TerminalMapLaws (F := forget C F) (T := terminal F T unit i) E i := ⟨E.refl _⟩
def products_preserve (P : ProductOps C) (p : J → J → J)
    (i : ∀ a b, Comparison C (F (p a b)) (P.prod (F a) (F b))) :
    WitnessEquivalence.ProductMapLaws (F := forget C F) (S := products F P p i) E i :=
  ⟨E.refl _,E.refl _,fun _ _ => E.refl _⟩
def initial_preserves (T : InitialOps C) (zero : J) (i : Comparison C (F zero) T.zero) :
    WitnessEquivalence.InitialMapLaws (F := forget C F) (T := initial F T zero i) E i := ⟨E.refl _⟩
def coproducts_preserve (S : CoproductOps C) (s : J → J → J)
    (i : ∀ a b, Comparison C (F (s a b)) (S.sum (F a) (F b))) :
    WitnessEquivalence.CoproductMapLaws (F := forget C F) (S := coproducts F S s i) E i :=
  ⟨E.refl _,E.refl _,fun _ _ => E.refl _⟩

variable (CC : E.Congr) (CL : E.Laws)
include CC CL in
def terminal_laws (T : TerminalOps C) (unit : J) (i : Comparison C (F unit) T.unit)
    (I : WitnessEquivalence.ComparisonLaws E i) (TL : WitnessEquivalence.TerminalLaws E T) :
    WitnessEquivalence.TerminalLaws (equiv F E) (terminal F T unit i) :=
  WitnessEquivalence.TerminalMap.transportLaws (fun h => h) CC CL I
    (terminal_preserves F T unit i) TL

include CC in
def product_congr (P : ProductOps C) (p : J → J → J)
    (i : ∀ a b, Comparison C (F (p a b)) (P.prod (F a) (F b))) (PC : WitnessEquivalence.ProductCongr E P) :
    WitnessEquivalence.ProductCongr (equiv F E) (products F P p i) :=
  WitnessEquivalence.ProductMap.transportCongr (forget_laws F E) (fun h => h) CC
    (products_preserve F P p i) PC

include CC CL in
def product_laws (P : ProductOps C) (p : J → J → J)
    (i : ∀ a b, Comparison C (F (p a b)) (P.prod (F a) (F b)))
    (I : ∀ a b, WitnessEquivalence.ComparisonLaws E (i a b)) (PC : WitnessEquivalence.ProductCongr E P) (PL : WitnessEquivalence.ProductLaws E P) :
    WitnessEquivalence.ProductLaws (equiv F E) (products F P p i) :=
  WitnessEquivalence.ProductMap.transportLaws (forget_laws F E) (fun h => h) CC CL I
    (products_preserve F P p i) PC PL

include CC CL in
def initial_laws (T : InitialOps C) (zero : J) (i : Comparison C (F zero) T.zero)
    (I : WitnessEquivalence.ComparisonLaws E i) (TL : WitnessEquivalence.InitialLaws E T) :
    WitnessEquivalence.InitialLaws (equiv F E) (initial F T zero i) :=
  WitnessEquivalence.InitialMap.transportLaws (fun h => h) CC CL I.inv_hom
    (initial_preserves F T zero i) TL

include CC in
def coproduct_congr (S : CoproductOps C) (s : J → J → J)
    (i : ∀ a b, Comparison C (F (s a b)) (S.sum (F a) (F b))) (SC : WitnessEquivalence.CoproductCongr E S) :
    WitnessEquivalence.CoproductCongr (equiv F E) (coproducts F S s i) :=
  WitnessEquivalence.CoproductMap.transportCongr (forget_laws F E) (fun h => h) CC
    (coproducts_preserve F S s i) SC

include CC CL in
def coproduct_laws (S : CoproductOps C) (s : J → J → J)
    (i : ∀ a b, Comparison C (F (s a b)) (S.sum (F a) (F b)))
    (I : ∀ a b, WitnessEquivalence.ComparisonLaws E (i a b)) (SC : WitnessEquivalence.CoproductCongr E S) (SL : WitnessEquivalence.CoproductLaws E S) :
    WitnessEquivalence.CoproductLaws (equiv F E) (coproducts F S s i) :=
  WitnessEquivalence.CoproductMap.transportLaws (forget_laws F E) (fun h => h) CC CL I
    (coproducts_preserve F S s i) SC SL

theorem erase_equiv (E : WitnessEquivalence C) :
    (equiv F E).erase = ObjectReindex.equiv F E.erase := rfl
end SquareKit.WitnessObjectReindex
