import SquareKit.Internal.Cubical.CocycleGlobalizationInverse
import SquareKit.Internal.Cubical.PartialSections

/-! Terms in the cocycle family are maps into its actual presheaf. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory
open Presheaf

def cocycleFamily (Γ : Context.{0}) : Family Γ := Functor.Elements.π Γ ⋙ cocycles

def cocycleTerm {Γ : Context.{0}} (v : Γ ⟶ cocycles) : Term (cocycleFamily Γ) where
  val x := v.app x.obj x.val
  property f := map_restriction v f

def termMap {Γ : Context.{0}} (t : Term (cocycleFamily Γ)) : Γ ⟶ cocycles where
  app I := TypeCat.ofHom (fun x => t.val (Γ.elementsMk I x))
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (t.property (Functor.Elements.homMk f rfl : Γ.elementsMk I x ⟶
      Γ.elementsMk J (Γ.map f x))).symm

theorem cocycleTerm_termMap {Γ : Context.{0}} (t : Term (cocycleFamily Γ)) :
    cocycleTerm (termMap t) = t := rfl

def termCocycle {Γ : Context.{0}} (t : Term (cocycleFamily Γ)) : Cocycle2 Γ.Elementsᵒᵖ :=
  mapToGlobal (termMap t)

def cocycleSection {Γ : Context.{0}} (z : Cocycle2 Γ.Elementsᵒᵖ) : Term (cocycleFamily Γ) :=
  cocycleTerm (globalToMap z)

theorem cocycleSection_termCocycle {Γ : Context.{0}} (t : Term (cocycleFamily Γ)) :
    cocycleSection (termCocycle t) = t := by
  unfold cocycleSection termCocycle
  rw [globalToMap_mapToGlobal]
  rfl

theorem termCocycle_reindex {Γ Δ : Context.{0}} (t : Term (cocycleFamily Γ)) (σ : Δ ⟶ Γ) :
    termCocycle (t.reindex σ) = (termCocycle t).pullback σ.mapElements.op := rfl

end SquareKit.Cubical.CategoryCocycles
