import SquareKit.Internal.Cubical.TelescopeIdentitySubstitution
import Examples.CubicalTelescopeIdentity

/-! The selected two-variable J construction survives two base substitutions,
including its dependent result and the chosen finite witness. -/
namespace Examples.CubicalTelescopeSubstitution
open CategoryTheory SquareKit.Cubical.Presheaf CubicalPresheaf CubicalSumFilling CubicalTelescopeIdentity

abbrev substitution := twice ≫ successor
abbrev singletonMap := IdentitySingleton.reindexMap argument chosen substitution
abbrev newTail := tail.reindex singletonMap
abbrev newMotive := reindex motive (tail.map singletonMap)
abbrev newRoot := IdentitySingleton.reflexivity (reindex argument substitution) (chosen.reindex substitution)
noncomputable abbrev newEliminated : Term newMotive :=
  TelescopeIdentityElimination.eliminate (reindex argument substitution) (chosen.reindex substitution)
    newTail newMotive
    (TelescopeIdentityElimination.substitutedBranch argument chosen tail motive branch substitution)
    (fillers.reindex singletonMap) (fillers_lawful.reindex singletonMap)
    (motiveFiller.reindex (tail.map singletonMap))

theorem two_substitutions : newEliminated = eliminated.reindex (tail.map singletonMap) :=
  TelescopeIdentityElimination.eliminate_reindex argument chosen tail motive branch substitution
    fillers fillers_lawful motiveFiller motiveLawful

theorem evaluation_reindex (t : Term motive) :
    ((t.reindex (tail.map singletonMap)).reindex (newTail.map newRoot)).val
      ((newTail.reindex newRoot).context.elementsMk (Opposite.op ⟨0⟩) ⟨⟨(2 : ℕ),(6 : ℕ)⟩,(5 : Fin 7)⟩) =
      (t.reindex (tail.map root)).val
        ((tail.reindex root).context.elementsMk (Opposite.op ⟨0⟩) ⟨⟨(5 : ℕ),(6 : ℕ)⟩,(5 : Fin 7)⟩) := by
  let x := (newTail.reindex newRoot).context.elementsMk (Opposite.op ⟨0⟩)
    ⟨⟨(2 : ℕ),(6 : ℕ)⟩,(5 : Fin 7)⟩
  let y := (tail.reindex root).context.elementsMk (Opposite.op ⟨0⟩)
    ⟨⟨(5 : ℕ),(6 : ℕ)⟩,(5 : Fin 7)⟩
  have hb := congrArg (fun f => f.app (Opposite.op ⟨0⟩) (2 : ℕ))
    (IdentitySingleton.reindexMap_reflexivity argument chosen substitution)
  have hp : (tail.map singletonMap).mapElements.obj ((newTail.map newRoot).mapElements.obj x) =
      (tail.map root).mapElements.obj y := by
    exact congrArg (tail.context.elementsMk (Opposite.op ⟨0⟩))
      (congrArg (fun z : singleton.obj (Opposite.op ⟨0⟩) =>
        (⟨⟨z,(6 : ℕ)⟩,(5 : Fin 7)⟩ : tail.context.obj (Opposite.op ⟨0⟩))) hb)
  exact eq_of_heq (Term.val_heq_of_heq rfl (heq_of_eq (rfl : t = t)) hp)

theorem selected_of_equations (t : Term motive) (q : Term newMotive)
    (ht : q = t.reindex (tail.map singletonMap)) (hb0 : t.reindex (tail.map root) = branch) :
    (q.reindex (newTail.map newRoot)).val
      ((newTail.reindex newRoot).context.elementsMk (Opposite.op ⟨0⟩) ⟨⟨(2 : ℕ),(6 : ℕ)⟩,(5 : Fin 7)⟩) =
      (5 : Fin 7) := by
  let x := (newTail.reindex newRoot).context.elementsMk (Opposite.op ⟨0⟩)
    ⟨⟨(2 : ℕ),(6 : ℕ)⟩,(5 : Fin 7)⟩
  let y := (tail.reindex root).context.elementsMk (Opposite.op ⟨0⟩)
    ⟨⟨(5 : ℕ),(6 : ℕ)⟩,(5 : Fin 7)⟩
  have hv := congrArg (fun q : Term newMotive => (q.reindex (newTail.map newRoot)).val x) ht
  have hb := congrArg (fun t => t.val y) hb0
  exact hv.trans ((evaluation_reindex t).trans hb)

theorem selected_witness :
    (newEliminated.reindex (newTail.map newRoot)).val
      ((newTail.reindex newRoot).context.elementsMk (Opposite.op ⟨0⟩) ⟨⟨(2 : ℕ),(6 : ℕ)⟩,(5 : Fin 7)⟩) =
      (5 : Fin 7) :=
  selected_of_equations eliminated newEliminated two_substitutions strict_branch

theorem erasure_rejected :
    ((newEliminated.reindex (newTail.map newRoot)).val
      ((newTail.reindex newRoot).context.elementsMk (Opposite.op ⟨0⟩) ⟨⟨(2 : ℕ),(6 : ℕ)⟩,(5 : Fin 7)⟩)).val ≠ 0 := by
  rw [selected_witness]
  decide

end Examples.CubicalTelescopeSubstitution
