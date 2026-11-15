import SquareKit.Internal.Cubical.Judgments.NaturalsTheory
import Examples.CubicalTypeFormers

/-! The typed source successor equation is interpreted at a varying finite
motive, retaining the induction hypothesis as an actual dependent section. -/
namespace Examples.CubicalSourceNaturals
set_option backward.isDefEq.respectTransparency false
open CategoryTheory SquareKit SquareKit.Cubical Source
open GuardedTheory Naturals Presheaf CubicalTypeFormers

noncomputable def successorSource :
    Derivation theory (List.ofFn successorBetaRule.premise) successorBetaRule.conclusion := by
  have d := Derivation.rule (T := theory) (.inr .successorBeta) GuardedTheory.Term.var
    (fun i => .hypothesis (List.mem_ofFn.mpr ⟨i,rfl⟩))
  simpa only [theory,Theory.extend,Naturals.rule,Atom.subst_id] using d

noncomputable def environment : Fin 4 → Value :=
  ![.context base,.family (total numbers) finiteMotive,
    .term base (reindex finiteMotive (Presheaf.pair (𝟙 base) (natZero base))) zeroCase,
    .term (total finiteMotive) (reindex finiteMotive (projection finiteMotive ≫ natSuccessorSub base)) stepCase.toTerm]

theorem premises : ∀ p ∈ List.ofFn successorBetaRule.premise, p.eval Naturals.algebra environment := by
  intro p hp
  rcases List.mem_ofFn.mp hp with ⟨i,rfl⟩
  have hz := zeroSub_eval (.var (0 : Fin 4)) environment base rfl
  have hs := successorSub_eval (.var (0 : Fin 4)) environment base rfl
  fin_cases i
  · exact ⟨base,rfl⟩
  · refine ⟨total numbers,finiteMotive,?_,rfl⟩
    change Source.operation .extend ![.context base,extraOperation .nat ![.context base]] = _
    rw [extra_nat]
    simp [Source.operation]
  · refine ⟨base,reindex finiteMotive (Presheaf.pair (𝟙 base) (natZero base)),zeroCase,rfl,?_,rfl⟩
    change Source.operation .subTy ![.family (total numbers) finiteMotive,
      (zeroSub (.var (0 : Fin 4))).eval Naturals.algebra environment] = _
    rw [hz]
    simp [Source.operation]
  · refine ⟨total finiteMotive,reindex finiteMotive (projection finiteMotive ≫ natSuccessorSub base),stepCase.toTerm,?_,?_,rfl⟩
    · change Source.operation .extend ![Source.operation .extend ![.context base,extraOperation .nat ![.context base]],
        .family (total numbers) finiteMotive] = _
      rw [extra_nat]
      simp [Source.operation]
    · change Source.operation .subTy ![.family (total numbers) finiteMotive,
        Source.operation .comp ![(successorSub (.var (0 : Fin 4))).eval Naturals.algebra environment,
          Source.operation .weaken ![Source.operation .extend ![.context base,extraOperation .nat ![.context base]],
            .family (total numbers) finiteMotive]]] = _
      rw [hs,extra_nat]
      simp [Source.operation]

theorem interpreted_successor :
    countedLast.reindex (natSuccessorSub base) =
      stepCase.toTerm.reindex (Presheaf.pair (𝟙 (total numbers)) countedLast) := by
  have h := interpret successorSource environment premises
  have hs := successorSub_eval (.var (0 : Fin 4)) environment base rfl
  let e := extraOperation .elim ![.context base,.family (total numbers) finiteMotive,
    .term base (reindex finiteMotive (Presheaf.pair (𝟙 base) (natZero base))) zeroCase,
    .term (total finiteMotive) (reindex finiteMotive (projection finiteMotive ≫ natSuccessorSub base)) stepCase.toTerm]
  change Source.operation .subTm ![e,(successorSub (.var (0 : Fin 4))).eval Naturals.algebra environment] =
    Source.operation .subTm ![.term (total finiteMotive) (reindex finiteMotive (projection finiteMotive ≫ natSuccessorSub base)) stepCase.toTerm,
      Source.operation .pair ![.family (total numbers) finiteMotive,
        Source.operation .id ![Source.operation .extend ![.context base,extraOperation .nat ![.context base]]],e]] at h
  rw [hs] at h
  dsimp only [e] at h
  rw [extra_elim,extra_nat] at h
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,Value.familyAt_family,Value.substitutionAt_substitution,
    Value.termIn_term] at h
  have ht : Value.termAt (total numbers)
      (Semantics.subTy finiteMotive (Semantics.idSub (total numbers)))
      (.term (total numbers) finiteMotive (natElim zeroCase (NatStep.ofTerm stepCase.toTerm))) =
      some countedLast := Value.termAt_term _ _ _
  rw [ht] at h
  simp only [Value.termIn_term] at h
  exact eq_of_heq (Value.term.inj h).2.2

theorem interpreted_successor_at_two :
    countedLast.val ((total numbers).elementsMk (Opposite.op ⟨0⟩) ⟨PUnit.unit,⟨3⟩⟩) =
      (countedLast.val ((total numbers).elementsMk (Opposite.op ⟨0⟩) ⟨PUnit.unit,⟨2⟩⟩)).succ :=
  congrArg (fun t => t.val ((total numbers).elementsMk (Opposite.op ⟨0⟩) ⟨PUnit.unit,⟨2⟩⟩)) interpreted_successor

end Examples.CubicalSourceNaturals
