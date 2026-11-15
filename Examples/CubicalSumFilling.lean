import SquareKit.Internal.Cubical.SumFilling
import Examples.CubicalDiscreteFilling

/-! Sum filling retains a selected natural and its dependent finite component. -/
namespace Examples.CubicalSumFilling
set_option backward.isDefEq.respectTransparency false
open CategoryTheory SquareKit.Cubical.Presheaf CubicalPresheaf CubicalDiscreteFilling

abbrev argument : Family naturals := discreteFamily index (fun _ => ℕ)

def secondIndex : Term (constantFamily (total argument) ℕ) where
  val x := x.val.2
  property f := congrArg Sigma.snd f.map_val

abbrev result : Family (total argument) := discreteFamily secondIndex (fun n => Fin (n+1))

def chosen : Term argument where
  val x := show ℕ from Nat.succ x.val
  property {x y} f := by
    change Nat.succ x.val = Nat.succ y.val
    exact congrArg Nat.succ f.map_val

def chosenResult : Term (reindex result (pair (𝟙 naturals) chosen)) where
  val x := show Fin (Nat.succ (Nat.succ x.val)) from Fin.last (Nat.succ x.val)
  property f := cast_last _ _ (congrArg Nat.succ f.map_val)

abbrev chosenPair : Term (sigma argument result) := sigmaIntro chosen chosenResult
abbrev path := projection (interval naturals)

def pairBox : OpenBox (reindex (sigma argument result) path) (Cofibration.top naturals) where
  tube := PartialSection.ofTerm _ (chosenPair.reindex path)
  base := chosenPair
  boundary _ _ := rfl

abbrev firstFilling := discreteFilling index (fun _ => ℕ)
abbrev secondFilling := discreteFilling secondIndex (fun n => Fin (n+1))
abbrev pairFilling := sigmaFilling firstFilling (discreteFilling_lawful index (fun _ => ℕ)) secondFilling

theorem lawful : pairFilling.Lawful := sigmaFilling_lawful firstFilling
  (discreteFilling_lawful index (fun _ => ℕ)) secondFilling
  (discreteFilling_lawful secondIndex (fun n => Fin (n+1)))

theorem selected_pair (x : naturals.Elements) :
    (pairFilling.comp path (Cofibration.top naturals) pairBox).val x = chosenPair.val x :=
  Filling.comp_boundary lawful path (Cofibration.top naturals) pairBox x rfl

theorem preserves_two_components :
    (((pairFilling.comp path (Cofibration.top naturals) pairBox).reindex (twice ≫ successor)).val
      (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : ℕ))) = ⟨(6 : ℕ),(6 : Fin 7)⟩ := by
  exact selected_pair ((twice ≫ successor).mapElements.obj
    (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : ℕ)))

theorem second_component_not_erased :
    ((((pairFilling.comp path (Cofibration.top naturals) pairBox).reindex (twice ≫ successor)).val
      (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : ℕ))).2.val) ≠ 0 := by
  rw [preserves_two_components]
  decide

end Examples.CubicalSumFilling
