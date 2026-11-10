import SquareKit.Internal.PathTransport.CechMatchingConstant
import Mathlib.CategoryTheory.Products.Basic

/-! Independent matching commutes with products of parameter diagrams. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v

def product (D E : Diagram.{u,v}) : Diagram.{u,v} where
  localCategory := Grpd.of (D.localCategory × E.localCategory)
  doubleCategory := Grpd.of (D.doubleCategory × E.doubleCategory)
  tripleCategory := Grpd.of (D.tripleCategory × E.tripleCategory)
  first := D.first.prod E.first
  second := D.second.prod E.second
  diagonal := D.diagonal.prod E.diagonal
  firstSecond := D.firstSecond.prod E.firstSecond
  firstThird := D.firstThird.prod E.firstThird
  secondThird := D.secondThird.prod E.secondThird
  diagonalFirst := NatIso.prod D.diagonalFirst E.diagonalFirst
  diagonalSecond := NatIso.prod D.diagonalSecond E.diagonalSecond
  tripleFirst := NatIso.prod D.tripleFirst E.tripleFirst
  tripleMiddle := NatIso.prod D.tripleMiddle E.tripleMiddle
  tripleLast := NatIso.prod D.tripleLast E.tripleLast

def productDatum {D E : Diagram.{u,v}} (d : Datum D) (e : Datum E) : Datum (product D E) where
  localObject := (d.localObject, e.localObject)
  overlap := d.overlap.prod e.overlap
  diagonal := CategoryTheory.Prod.hom_ext d.diagonal e.diagonal
  cocycle := CategoryTheory.Prod.hom_ext d.cocycle e.cocycle

def productFunctor (D E : Diagram.{u,v}) : Datum D × Datum E ⥤ Datum (product D E) where
  obj d := productDatum d.1 d.2
  map f := ⟨(f.1.localArrow, f.2.localArrow),
    CategoryTheory.Prod.hom_ext f.1.commutes f.2.commutes⟩
  map_id _ := Datum.Hom.ext _ _ rfl
  map_comp _ _ := Datum.Hom.ext _ _ rfl

def firstDatum {D E : Diagram.{u,v}} (d : Datum (product D E)) : Datum D where
  localObject := d.localObject.1
  overlap := {
    hom := d.overlap.hom.1
    inv := d.overlap.inv.1
    hom_inv_id := congrArg Prod.fst d.overlap.hom_inv_id
    inv_hom_id := congrArg Prod.fst d.overlap.inv_hom_id }
  diagonal := congrArg Prod.fst d.diagonal
  cocycle := congrArg Prod.fst d.cocycle

def secondDatum {D E : Diagram.{u,v}} (d : Datum (product D E)) : Datum E where
  localObject := d.localObject.2
  overlap := {
    hom := d.overlap.hom.2
    inv := d.overlap.inv.2
    hom_inv_id := congrArg Prod.snd d.overlap.hom_inv_id
    inv_hom_id := congrArg Prod.snd d.overlap.inv_hom_id }
  diagonal := congrArg Prod.snd d.diagonal
  cocycle := congrArg Prod.snd d.cocycle

instance (D E : Diagram.{u,v}) : (productFunctor D E).Faithful where
  map_injective h := by
    apply CategoryTheory.Prod.hom_ext
    · apply Datum.Hom.ext
      exact congrArg (fun f => f.localArrow.1) h
    · apply Datum.Hom.ext
      exact congrArg (fun f => f.localArrow.2) h

instance (D E : Diagram.{u,v}) : (productFunctor D E).Full where
  map_surjective f := ⟨(⟨f.localArrow.1, congrArg Prod.fst f.commutes⟩,
    ⟨f.localArrow.2, congrArg Prod.snd f.commutes⟩), Datum.Hom.ext _ _ rfl⟩

instance (D E : Diagram.{u,v}) : (productFunctor D E).EssSurj where
  mem_essImage d := by
    refine ⟨(firstDatum d, secondDatum d), ⟨eqToIso ?_⟩⟩
    apply Datum.ext rfl
    apply heq_of_eq
    apply Iso.ext
    rfl

instance (D E : Diagram.{u,v}) : (productFunctor D E).IsEquivalence where

def productEquivalence (D E : Diagram.{u,v}) : Datum D × Datum E ≌ Datum (product D E) :=
  (productFunctor D E).asEquivalence

/-- Constant non-discrete fibers retain their arrows over arbitrary matching data. -/
def constantProductEquivalence (D : Diagram.{u,v}) (C : Grpd.{u,v}) :
    Datum D × C ≌ Datum (product D (constant C)) :=
  ((CategoryTheory.Equivalence.refl : Datum D ≌ Datum D).prod (constantEquivalence C)).trans (productEquivalence D (constant C))

end SquareKit.Internal.PathTransport.CechMatching
