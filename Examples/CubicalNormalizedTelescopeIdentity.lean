import SquareKit.Internal.Cubical.NormalizedTelescopeIdentityElimination
import Examples.CubicalSumFilling

/-! A two-variable dependent tail: a natural followed by Fin(n+1). The J branch
returns the selected second variable in that same dependent fiber. -/
namespace Examples.CubicalNormalizedTelescopeIdentity
set_option backward.isDefEq.respectTransparency false
open CategoryTheory SquareKit.Cubical.Presheaf CubicalPresheaf CubicalDiscreteFilling CubicalSumFilling

abbrev singleton := NormalizedIdentitySingleton.context argument chosen
abbrev singletonIndex : Term (constantFamily singleton ℕ) := (generic argument).reindex (projection (NormalizedIdentitySingleton.fiber argument chosen))
abbrev first : Family singleton := discreteFamily singletonIndex (fun _ => ℕ)

def firstIndex : Term (constantFamily (total first) ℕ) where
  val x := x.val.2
  property f := congrArg Sigma.snd f.map_val

abbrev second : Family (total first) := discreteFamily firstIndex (fun n => Fin (n+1))
abbrev tail : Telescope singleton := .cons first (.cons second (.nil (total second)))
abbrev motive : Family tail.context := reindex second (projection second)
abbrev firstFiller := discreteFilling singletonIndex (fun _ => ℕ)
abbrev secondFiller := discreteFilling firstIndex (fun n => Fin (n+1))
def fillers : tail.Fillings := .cons firstFiller (.cons secondFiller (.nil _))
theorem fillers_lawful : fillers.Lawful :=
  ⟨discreteFilling_lawful singletonIndex (fun _ => ℕ),
    discreteFilling_lawful firstIndex (fun n => Fin (n+1)), True.intro⟩
abbrev motiveFiller := secondFiller.reindex (projection second)
abbrev motiveLawful := (discreteFilling_lawful firstIndex (fun n => Fin (n+1))).reindex (projection second)
abbrev root := NormalizedIdentitySingleton.reflexivity argument chosen
abbrev branch : Term (reindex motive (tail.map root)) := (generic second).reindex (tail.map root)
noncomputable abbrev eliminated : Term motive :=
  NormalizedTelescopeIdentityElimination.eliminate argument chosen tail motive branch fillers fillers_lawful motiveFiller

theorem strict_branch : eliminated.reindex (tail.map root) = branch :=
  NormalizedTelescopeIdentityElimination.eliminate_beta argument chosen tail motive branch fillers fillers_lawful
    motiveFiller motiveLawful

theorem retains_second_variable :
    (eliminated.reindex (tail.map root)).val
      ((tail.reindex root).context.elementsMk (Opposite.op ⟨0⟩) ⟨⟨(2 : ℕ),(6 : ℕ)⟩,(5 : Fin 7)⟩) =
      (5 : Fin 7) := by
  rw [strict_branch]
  rfl

theorem erasure_rejected :
    ((eliminated.reindex (tail.map root)).val
      ((tail.reindex root).context.elementsMk (Opposite.op ⟨0⟩) ⟨⟨(2 : ℕ),(6 : ℕ)⟩,(5 : Fin 7)⟩)).val ≠ 0 := by
  rw [retains_second_variable]
  decide

end Examples.CubicalNormalizedTelescopeIdentity
