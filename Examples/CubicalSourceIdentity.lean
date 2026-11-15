import SquareKit.Internal.Cubical.ContextualModel
import Examples.CubicalNormalizedTelescopeIdentity

/-! The existing source telescope feeds the constructed strict eliminator.
Its dependent Fin witness survives the reflexive branch without erasure. -/
namespace Examples.CubicalSourceIdentity
open CategoryTheory SquareKit.Cubical.Presheaf SquareKit.Cubical.Contextual
  SquareKit.Internal.PathTransport.Typed CubicalPresheaf CubicalDiscreteFilling
  CubicalSumFilling CubicalNormalizedTelescopeIdentity
variable (Base : LawfulFamily terminal.{0}) (Fiber : LawfulFamily (total Base.family))
local notation "M" => structuralModel Base Fiber

noncomputable def sourceArgument : (M).Family naturals :=
  ⟨⟨argument,discreteFilling index (fun _ => ℕ)⟩,discreteFilling_lawful index (fun _ => ℕ)⟩
noncomputable def sourceFirst : LawfulFamily singleton :=
  ⟨⟨first,firstFiller⟩,discreteFilling_lawful singletonIndex (fun _ => ℕ)⟩
noncomputable def sourceSecond : LawfulFamily (total first) :=
  ⟨⟨second,secondFiller⟩,discreteFilling_lawful firstIndex (fun n => Fin (n+1))⟩
noncomputable def sourceTail : StructuralModel.Telescope M
    ((M).pathContext (sourceArgument Base Fiber) ⟨chosen⟩) 2 :=
  .cons sourceFirst (.cons sourceSecond .nil)
noncomputable def sourceMotive : (M).Family (sourceTail Base Fiber).total :=
  ⟨⟨motive,motiveFiller⟩,motiveLawful⟩
noncomputable abbrev sourceRoot := ((M).rootTail (sourceArgument Base Fiber) ⟨chosen⟩ (sourceTail Base Fiber)).down
noncomputable abbrev sourceBranch := (generic second).reindex (sourceRoot Base Fiber)
noncomputable def eliminated : Term motive :=
  ((SquareKit.Cubical.Contextual.model Base Fiber).j (sourceArgument Base Fiber) ⟨chosen⟩
    (sourceTail Base Fiber) (sourceMotive Base Fiber) ⟨sourceBranch Base Fiber⟩).down

theorem strict_branch : (eliminated Base Fiber).reindex (sourceRoot Base Fiber) = sourceBranch Base Fiber :=
  SquareKit.Cubical.Contextual.model_j_beta Base Fiber
    (sourceArgument Base Fiber) ⟨chosen⟩ (sourceTail Base Fiber)
    (sourceMotive Base Fiber) ⟨sourceBranch Base Fiber⟩

theorem selected_witness :
    ((eliminated Base Fiber).reindex (sourceRoot Base Fiber)).val
      ((StructuralModel.Telescope.pullback M (sourceTail Base Fiber)
        ((M).rootSub (sourceArgument Base Fiber) ⟨chosen⟩)).total.elementsMk
          (Opposite.op ⟨0⟩) ⟨⟨(2 : ℕ),(6 : ℕ)⟩,(5 : Fin 7)⟩) = (5 : Fin 7) := by
  rw [strict_branch]
  rfl

theorem erasure_rejected :
    (((eliminated Base Fiber).reindex (sourceRoot Base Fiber)).val
      ((StructuralModel.Telescope.pullback M (sourceTail Base Fiber)
        ((M).rootSub (sourceArgument Base Fiber) ⟨chosen⟩)).total.elementsMk
          (Opposite.op ⟨0⟩) ⟨⟨(2 : ℕ),(6 : ℕ)⟩,(5 : Fin 7)⟩)).val ≠ 0 := by
  rw [selected_witness]
  exact (by decide : (5 : Fin 7).val ≠ 0)

end Examples.CubicalSourceIdentity
