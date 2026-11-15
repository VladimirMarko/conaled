import SquareKit.CategoryProduct
import SquareKit.CartesianLaws

/-! Unsquaring has a middle-four product comparison; its induced relation need not be componentwise. -/
namespace SquareKit.Squared
universe u v
open Cartesian
variable {O : Type u} {C : CategoryOps.{u,v} O} (P : ProductOps C)
def unsquare : RawMap (CategoryProduct.ops C C) C :=
  ⟨fun a => P.prod a.1 a.2, fun f => tensor P f.1 f.2⟩

variable {P} {E : HomEquiv C} (CC : CategoryCongr C E) (CL : CategoryLaws C E)
variable (PC : ProductCongr E P) (PL : ProductLaws E P)
include CC CL PC PL in
theorem map_laws : MapLaws (unsquare P) (CategoryProduct.equiv C C E E) E :=
  ⟨fun h => tensor_congr CC PC h.1 h.2, tensor_ident CL PC PL _ _,
    fun g f => E.symm (tensor_comp CC CL PC PL g.1 g.2 f.1 f.2)⟩

def productMap : ProductMap (unsquare P) (CategoryProduct.products P P) P :=
  fun _ _ => ⟨transpose P,transpose P⟩
include CC CL PC PL in
theorem productMap_inverse (a b : O × O) : ComparisonLaws E (productMap (P := P) a b) :=
  ⟨transpose_transpose CC CL PC PL _ _ _ _, transpose_transpose CC CL PC PL _ _ _ _⟩

local instance {a b : O} : IsPreorder (C.Hom a b) E.Rel where
  refl := E.refl
  trans _ _ _ := E.trans
attribute [local gcongr] CategoryCongr.comp ProductCongr.pair
attribute [local refl] HomEquiv.refl

include CC CL PC PL in
theorem productMap_laws : ProductMapLaws E (productMap (P := P)) := by
  constructor
  · intro a b
    change E.Rel (tensor P P.fst P.fst) (C.comp P.fst (transpose P))
    simp only [tensor, transpose]
    exact E.symm (PL.fst_pair _ _)
  · intro a b
    change E.Rel (tensor P P.snd P.snd) (C.comp P.snd (transpose P))
    simp only [tensor, transpose]
    exact E.symm (PL.snd_pair _ _)
  · intro a b c f g
    change E.Rel (tensor P (P.pair f.1 g.1) (P.pair f.2 g.2))
      (C.comp (transpose P) (P.pair (tensor P f.1 f.2) (tensor P g.1 g.2)))
    apply E.symm
    simp only [tensor, transpose]
    repeat first
      | grw [PL.pair_comp CC CL PC]
      | grw [CL.assoc]
      | grw [PL.fst_pair]
      | grw [PL.snd_pair]
    exact PC.pair (E.symm (PL.pair_comp CC CL PC _ _ _))
      (E.symm (PL.pair_comp CC CL PC _ _ _))

variable (T : TerminalOps C)
def terminalMap : TerminalMap (unsquare P) (CategoryProduct.terminal T T) T :=
  ⟨unitRight P T, insertRight P T⟩
include CC CL PC PL in
theorem terminalMap_inverse (TL : TerminalLaws E T) : ComparisonLaws E (terminalMap (P := P) T) :=
  ⟨unitRight_insertRight PL T _,insertRight_unitRight CC CL PC PL T TL _⟩
include CC CL PC PL in
theorem terminalMap_laws (TL : TerminalLaws E T) : TerminalMapLaws E (terminalMap (P := P) T) :=
  ⟨terminal_tensor CC CL PC PL T TL _ _⟩

include CC CL PC PL in
/-- Law transport uses the induced relation, with reflection supplied by its definition. -/
theorem induced_laws : CategoryLaws (CategoryProduct.ops C C) ((unsquare P).induced E) :=
  RawMap.transportLaws
    ((unsquare P).inducedLaws E (tensor_ident CL PC PL _ _)
      (fun g f => E.symm (tensor_comp CC CL PC PL g.1 g.2 f.1 f.2)))
    ((unsquare P).induced_reflects E) CC CL
end SquareKit.Squared
