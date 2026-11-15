import SquareKit.Internal.Cubical.Judgments.NaturalsTheory
import SquareKit.Internal.Cubical.SourceBinding

/-! Fixed-X interpretation of the selected recursive contraction through
the guarded Nat source rule and the constructed successor binding interface. -/
namespace Examples.CubicalSourceContraction
set_option backward.isDefEq.respectTransparency false
open CategoryTheory SquareKit SquareKit.Cubical Source
open GuardedTheory Naturals Presheaf
universe u
variable (X : Context.{u})

noncomputable def successorSource :
    Derivation theory (List.ofFn successorBetaRule.premise) successorBetaRule.conclusion := by
  have d := Derivation.rule (T := theory) (.inr .successorBeta) GuardedTheory.Term.var
    (fun i => .hypothesis (List.mem_ofFn.mpr ⟨i,rfl⟩))
  simpa only [theory,Theory.extend,Naturals.rule,Atom.subst_id] using d

noncomputable def environment : Fin 4 → Value :=
  ![.context terminal.{u},.family (total (natFamily terminal.{u})) (methodFamily X),
    .term terminal.{u} (reindex (methodFamily X) (Presheaf.pair (𝟙 terminal.{u}) (natZero terminal.{u}))) (sourceZero X),
    .term (total (methodFamily X)) (reindex (methodFamily X) (projection (methodFamily X) ≫ natSuccessorSub terminal.{u})) (sourceSuccessor X).toTerm]

theorem premises : ∀ p ∈ List.ofFn successorBetaRule.premise, p.eval Naturals.algebra (environment X) := by
  intro p hp
  rcases List.mem_ofFn.mp hp with ⟨i,rfl⟩
  have hz := zeroSub_eval (.var (0 : Fin 4)) (environment X) terminal.{u} rfl
  have hs := successorSub_eval (.var (0 : Fin 4)) (environment X) terminal.{u} rfl
  fin_cases i
  · exact ⟨terminal.{u},rfl⟩
  · refine ⟨total (natFamily terminal.{u}),(methodFamily X),?_,rfl⟩
    change Source.operation .extend ![.context terminal.{u},extraOperation .nat ![.context terminal.{u}]] = _
    rw [extra_nat]
    simp [Source.operation]
  · refine ⟨terminal.{u},reindex (methodFamily X) (Presheaf.pair (𝟙 terminal.{u}) (natZero terminal.{u})),(sourceZero X),rfl,?_,rfl⟩
    change Source.operation .subTy ![.family (total (natFamily terminal.{u})) (methodFamily X),
      (zeroSub (.var (0 : Fin 4))).eval Naturals.algebra (environment X)] = _
    rw [hz]
    simp [Source.operation]
  · refine ⟨total (methodFamily X),reindex (methodFamily X) (projection (methodFamily X) ≫ natSuccessorSub terminal.{u}),(sourceSuccessor X).toTerm,?_,?_,rfl⟩
    · change Source.operation .extend ![Source.operation .extend ![.context terminal.{u},extraOperation .nat ![.context terminal.{u}]],
        .family (total (natFamily terminal.{u})) (methodFamily X)] = _
      rw [extra_nat]
      simp [Source.operation]
    · change Source.operation .subTy ![.family (total (natFamily terminal.{u})) (methodFamily X),
        Source.operation .comp ![(successorSub (.var (0 : Fin 4))).eval Naturals.algebra (environment X),
          Source.operation .weaken ![Source.operation .extend ![.context terminal.{u},extraOperation .nat ![.context terminal.{u}]],
            .family (total (natFamily terminal.{u})) (methodFamily X)]]] = _
      rw [hs,extra_nat]
      simp [Source.operation]

theorem interpreted_successor :
    (sourceRecursion X).reindex (natSuccessorSub terminal.{u}) =
      (sourceSuccessor X).toTerm.reindex (Presheaf.pair (𝟙 (total (natFamily terminal.{u}))) (sourceRecursion X)) := by
  have h := interpret successorSource (environment X) (premises X)
  have hs := successorSub_eval (.var (0 : Fin 4)) (environment X) terminal.{u} rfl
  let e := extraOperation .elim ![.context terminal.{u},.family (total (natFamily terminal.{u})) (methodFamily X),
    .term terminal.{u} (reindex (methodFamily X) (Presheaf.pair (𝟙 terminal.{u}) (natZero terminal.{u}))) (sourceZero X),
    .term (total (methodFamily X)) (reindex (methodFamily X) (projection (methodFamily X) ≫ natSuccessorSub terminal.{u})) (sourceSuccessor X).toTerm]
  change Source.operation .subTm ![e,(successorSub (.var (0 : Fin 4))).eval Naturals.algebra (environment X)] =
    Source.operation .subTm ![.term (total (methodFamily X)) (reindex (methodFamily X) (projection (methodFamily X) ≫ natSuccessorSub terminal.{u})) (sourceSuccessor X).toTerm,
      Source.operation .pair ![.family (total (natFamily terminal.{u})) (methodFamily X),
        Source.operation .id ![Source.operation .extend ![.context terminal.{u},extraOperation .nat ![.context terminal.{u}]]],e]] at h
  rw [hs] at h
  dsimp only [e] at h
  rw [extra_elim,extra_nat] at h
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,Value.familyAt_family,Value.substitutionAt_substitution,
    Value.termIn_term] at h
  have ht : Value.termAt (total (natFamily terminal.{u}))
      (Semantics.subTy (methodFamily X) (Semantics.idSub (total (natFamily terminal.{u}))))
      (.term (total (natFamily terminal.{u})) (methodFamily X) (natElim (sourceZero X) (NatStep.ofTerm (sourceSuccessor X).toTerm))) =
      some (sourceRecursion X) := Value.termAt_term _ _ _
  rw [ht] at h
  simp only [Value.termIn_term] at h
  exact eq_of_heq (Value.term.inj h).2.2

noncomputable def zeroSource :
    Derivation theory (List.ofFn zeroBetaRule.premise) zeroBetaRule.conclusion := by
  have d := Derivation.rule (T := theory) (.inr .zeroBeta) GuardedTheory.Term.var
    (fun i => .hypothesis (List.mem_ofFn.mpr ⟨i,rfl⟩))
  simpa only [theory,Theory.extend,Naturals.rule,Atom.subst_id] using d

theorem interpreted_zero :
    (sourceRecursion X).reindex (Presheaf.pair (𝟙 terminal.{u}) (natZero terminal)) = sourceZero X := by
  have h := interpret zeroSource (environment X) (premises X)
  have hz := zeroSub_eval (.var (0 : Fin 4)) (environment X) terminal.{u} rfl
  change Source.operation .subTm ![
    extraOperation .elim ![.context terminal,.family (total (natFamily terminal)) (methodFamily X),
      .term terminal (reindex (methodFamily X) (Presheaf.pair (𝟙 terminal) (natZero terminal))) (sourceZero X),
      .term (total (methodFamily X)) (reindex (methodFamily X)
        (projection (methodFamily X) ≫ natSuccessorSub terminal)) (sourceSuccessor X).toTerm],
    (zeroSub (.var (0 : Fin 4))).eval Naturals.algebra (environment X)] = _ at h
  rw [hz,extra_elim] at h
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.termIn_term] at h
  exact eq_of_heq (Value.term.inj h).2.2

/-- Source computation fixes the recursive operation at every index. -/
theorem recursion_characterized : ∀ n, interpretedContraction X n = contractCube X n := by
  apply source_characterization_unique
  · exact congrArg (fun t => t.val (terminal.elementsMk (Opposite.op ⟨0⟩) PUnit.unit)) (interpreted_zero X)
  · intro n
    exact congrArg (fun t => t.val ((total (natFamily terminal.{u})).elementsMk
      (Opposite.op ⟨0⟩) ⟨PUnit.unit,⟨n⟩⟩)) (interpreted_successor X)

/-- The interpreted successor uses the checked c,j,i binding, at every n. -/
theorem recursion_successor_body (n : ℕ) :
    normalizedCubeFunction (interpretedContraction X (n+1) ≫ cubeCurry X n) =
      normalizedLam (interpretedStepBody X n (interpretedContraction X n)) := by
  have hs : interpretedContraction X (n+1) = sourceStep X n (interpretedContraction X n) :=
    congrArg (fun t => t.val ((total (natFamily terminal.{u})).elementsMk
      (Opposite.op ⟨0⟩) ⟨PUnit.unit,⟨n⟩⟩)) (interpreted_successor X)
  rw [hs]
  exact sourceStep_normalized X n _

/-- At dimension one the interpreted body evaluates at i meet j. -/
theorem recursion_one_body (x : (bodyContext X 0).Elements) :
    (normalizedApp (normalizedCubeFunction
      (interpretedContraction X 1 ≫ cubeCurry X 0))).val x =
      x.val.1.1.apply (Cube.meet x.val.2.down x.val.1.2.down) := by
  rw [recursion_successor_body,normalizedApp_lam,interpretedStepBody_eq]
  have hz : interpretedContraction X 0 = projection (interval (cubes X 0)) :=
    congrArg (fun t => t.val (terminal.elementsMk (Opposite.op ⟨0⟩) PUnit.unit)) (interpreted_zero X)
  rw [hz]
  rfl

end Examples.CubicalSourceContraction
