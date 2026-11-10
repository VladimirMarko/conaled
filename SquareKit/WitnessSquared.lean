import SquareKit.Squared
import SquareKit.WitnessProduct
import SquareKit.WitnessFelixPreservation

namespace SquareKit.WitnessSquared
open Squared (unsquare productMap terminalMap)
open SquareKit.Cartesian
open WitnessEquivalence.Cartesian
universe u v
variable {O : Type u} {C : CategoryOps.{u,v} O} {P : ProductOps C}
variable {E : WitnessEquivalence C} (CC : E.Congr) (CL : E.Laws)
variable (PC : WitnessEquivalence.ProductCongr E P) (PL : WitnessEquivalence.ProductLaws E P)
include CC CL PC PL in
def map_laws : WitnessEquivalence.Preservation (unsquare P) (WitnessProduct.equiv C C E E) E :=
  ⟨fun h => WitnessEquivalence.Cartesian.tensor_congr CC PC h.1 h.2,
    WitnessEquivalence.Cartesian.tensor_ident CL PC PL _ _,
    fun g f => E.symm (WitnessEquivalence.Cartesian.tensor_comp CC CL PC PL g.1 g.2 f.1 f.2)⟩

include CC CL PC PL in
def transpose_pair {x a b c d : O} (f : C.Hom x a) (g : C.Hom x b)
    (h : C.Hom x c) (k : C.Hom x d) :
    E.Rel (C.comp (transpose P) (P.pair (P.pair f g) (P.pair h k)))
      (P.pair (P.pair f h) (P.pair g k)) := by
  apply E.trans (PL.pair_comp CC CL PC _ _ _)
  apply PC.pair
  · apply E.trans (PL.pair_comp CC CL PC _ _ _)
    apply PC.pair
    · exact E.trans (CL.assoc _ _ _) (E.trans (CC.comp (E.refl _) (PL.fst_pair _ _)) (PL.fst_pair _ _))
    · exact E.trans (CL.assoc _ _ _) (E.trans (CC.comp (E.refl _) (PL.snd_pair _ _)) (PL.fst_pair _ _))
  · apply E.trans (PL.pair_comp CC CL PC _ _ _)
    apply PC.pair
    · exact E.trans (CL.assoc _ _ _) (E.trans (CC.comp (E.refl _) (PL.fst_pair _ _)) (PL.snd_pair _ _))
    · exact E.trans (CL.assoc _ _ _) (E.trans (CC.comp (E.refl _) (PL.snd_pair _ _)) (PL.snd_pair _ _))

include CC CL PC PL in
def transpose_transpose (a b c d : O) :
    E.Rel (C.comp (transpose P) (transpose P (a := a) (b := b) (c := c) (d := d))) C.ident :=
  E.trans (transpose_pair CC CL PC PL _ _ _ _)
    (E.trans (PC.pair (PL.pair_eta _) (PL.pair_eta _)) (PL.projections CL PC))
include CC CL PC PL in
def productMap_inverse (a b : O × O) : WitnessEquivalence.ComparisonLaws E (productMap (P := P) a b) :=
  ⟨transpose_transpose CC CL PC PL _ _ _ _,transpose_transpose CC CL PC PL _ _ _ _⟩
include CC CL PC PL in
def productMap_laws : WitnessEquivalence.ProductMapLaws E (productMap (P := P)) := by
  constructor
  · intro a b
    exact E.symm (PL.fst_pair _ _)
  · intro a b
    exact E.symm (PL.snd_pair _ _)
  · intro a b c f g
    change E.Rel (tensor P (P.pair f.1 g.1) (P.pair f.2 g.2))
      (C.comp (transpose P) (P.pair (tensor P f.1 f.2) (tensor P g.1 g.2)))
    apply E.symm
    exact E.trans (transpose_pair CC CL PC PL _ _ _ _)
      (PC.pair (E.symm (PL.pair_comp CC CL PC _ _ _))
        (E.symm (PL.pair_comp CC CL PC _ _ _)))

variable (T : TerminalOps C)
include CC CL PC PL in
def terminalMap_inverse (TL : WitnessEquivalence.TerminalLaws E T) :
    WitnessEquivalence.ComparisonLaws E (terminalMap (P := P) T) :=
  ⟨WitnessEquivalence.Cartesian.unitRight_insertRight PL T _,
    WitnessEquivalence.Cartesian.insertRight_unitRight CC CL PC PL T TL _⟩
include CC CL PC PL in
def terminalMap_laws (TL : WitnessEquivalence.TerminalLaws E T) :
    WitnessEquivalence.TerminalMapLaws E (terminalMap (P := P) T) := by
  constructor
  intro a
  change E.Rel (P.pair _ _) (C.comp (P.pair C.ident T.terminal) T.terminal)
  exact E.trans (PC.pair (TL.unique _) (TL.unique _))
    (E.symm (E.trans (PL.pair_comp CC CL PC _ _ _)
      (PC.pair (CL.id_comp _) (TL.unique _))))

def induced (P : ProductOps C) (E : WitnessEquivalence C) :=
  WitnessEquivalence.induced (unsquare P) E
include CC CL PC PL in
def induced_laws : (induced P E).Laws :=
  WitnessEquivalence.transportLaws (map_laws CC CL PC PL).induced (fun h => h) CC CL
include CC CL PC PL in
def induced_congr : (induced P E).Congr :=
  WitnessEquivalence.transportCongr (map_laws CC CL PC PL).induced (fun h => h) CC

theorem erase_induced (P : ProductOps C) (E : WitnessEquivalence C) :
    (induced P E).erase = (unsquare P).induced E.erase := rfl
end SquareKit.WitnessSquared
