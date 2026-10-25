import Applications.Elaboration.Strategies

/-! Checked applications of the elaboration contract, including data projections
and failures. Expected arithmetic: five sevens sum to 35; the dependent consumer
adds the retained length, giving 40. -/
namespace Elaboration.Examples

/-- A source declaration computes its length; neither component is proof-erased. -/
def producer : Source [] [] .packet := .vector 0 (.add (.lit 2) (.lit 3)) (.lit 7)

def solved : Assignment := ⟨fun _ => some 5, fun _ => some 0⟩
def missing : Assignment := ⟨fun _ => none, fun _ => none⟩
def wrongUniverse : Assignment := ⟨fun _ => some 5, fun _ => some 1⟩

abbrev producerFinal : Final [] [] := ⟨emit producer, solved⟩

theorem producer_elaborates :
    Elaborates (.term producer) (some .packet) producerFinal.output :=
  elaborate_sound (show elaborate (.term producer) (some .packet) = .ok (emit producer) by rfl)

theorem producer_accepted : Accepted (.term producer) (some .packet) producerFinal :=
  finalize_sound producer_elaborates
    (show finalize solved (emit producer) = .ok producerFinal by rfl)

/-- These projections compute from the delivered artifact, not a Prop witness. -/
theorem computed_length :
    (producerFinal.output.code.eval solved.value emptyValuation emptyValuation).1 = 5 := by
  dsimp only [producerFinal, emit]
  rw [lower_sound]
  rfl

theorem computed_entries :
    (producerFinal.output.code.eval solved.value emptyValuation emptyValuation).2.toList =
      [7, 7, 7, 7, 7] := by
  dsimp only [producerFinal, emit]
  rw [lower_sound]
  rfl

/-- A second declaration refers to the first at its packet type and eliminates
its Sigma into a consumer whose vector argument is indexed by its length. -/
def consumer : Source [] [.packet] .nat := .total (.named .here)

abbrev consumerFinal : Final [] [.packet] := ⟨emit consumer, solved⟩

theorem consumer_accepted : Accepted (.term consumer) (some .nat) consumerFinal :=
  finalize_sound (emit_admissible (.term consumer (Or.inr rfl))) (by rfl)

theorem dependent_consumer_result :
    consumerFinal.output.code.eval solved.value emptyValuation
      (install producerFinal emptyValuation) = 40 := by
  dsimp only [consumerFinal, emit]
  rw [lower_sound]
  rfl

/-- Same length but different entries is observably different. -/
def otherProducer : Source [] [] .packet := .vector 0 (.add (.lit 2) (.lit 3)) (.lit 8)

theorem witnesses_distinguished :
    consume ((lower producer).eval solved.value emptyValuation emptyValuation) ≠
      consume ((lower otherProducer).eval solved.value emptyValuation emptyValuation) := by
  rw [lower_sound, lower_sound]
  decide

def openProducer : Source [.nat] [] .packet := .vector 0 (.bound .here) (.lit 7)
def lengthSubstitution : Substitution [.nat] [] []
  | _, .here => .add (.lit 2) (.lit 3)
  | _, .there x => nomatch x

theorem substitute_computed_length :
    (lower openProducer).subst (fun x => lower (lengthSubstitution x)) = lower producer := by
  rw [← lower_subst]
  rfl

theorem substituted_obligations :
    ((lower openProducer).subst (fun x => lower (lengthSubstitution x))).Typed solved := by
  apply lowered_substitution_typed
  · intro c hc
    simp [openProducer, Source.requirements] at hc
    subst c
    rfl
  · intro u x
    cases x with
    | here => simp [lengthSubstitution, Source.requirements, Solves]
    | there x => cases x

theorem weakened_length (v : Nat) :
    (producer.weaken (u := .nat)).eval solved.value (Valuation.extend (t := .nat) emptyValuation v) emptyValuation =
      producer.eval solved.value emptyValuation emptyValuation :=
  weaken_sound (u := .nat) producer _ _ _ v

theorem old_declaration_survives :
    (consumer.renameGlobals (fun x => .there x)).eval solved.value emptyValuation
      (Valuation.extend (t := .nat) (install producerFinal emptyValuation) 99) = 40 := by
  rw [environment_extension]
  rfl

/-- A genuinely open computational length. It can be elaborated but not finalized
until both its universe variable and its natural metavariable are assigned. -/
def implicitProducer : Source [] [] .packet := .vector 0 (.hole 3) (.lit 7)

theorem implicit_pending : Elaborates (.term implicitProducer) none (emit implicitProducer) :=
  emit_admissible (.term implicitProducer (Or.inl rfl))

theorem implicit_rejected : finalize missing (emit implicitProducer) =
    .error (.unresolved (.universeZero 0)) := rfl

def levelOnly : Assignment := ⟨fun _ => none, fun _ => some 0⟩

theorem implicit_length_rejected : finalize levelOnly (emit implicitProducer) =
    .error (.unresolved (.assigned 3)) := rfl

theorem wrong_universe_rejected : finalize wrongUniverse (emit producer) =
    .error (.unresolved (.universeZero 0)) := rfl

theorem implicit_accepted :
    Accepted (.term implicitProducer) none ⟨emit implicitProducer, solved⟩ :=
  finalize_sound (θ := solved) implicit_pending (by rfl)

/-- Refinement adds a specified length to the prior open-hole obligations. -/
def lengthProblem := implicitProducer.requirements ++ [.metaEq 3 5]

theorem refined_pending : Pending (.term implicitProducer) none (emit implicitProducer)
    lengthProblem := ⟨implicit_pending, add_constraints _ _⟩

theorem refined_solution : Solves solved lengthProblem :=
  (checkConstraints_correct solved lengthProblem).mp (by rfl)

theorem refined_accepted : Accepted (.term implicitProducer) none ⟨emit implicitProducer, solved⟩ :=
  refined_pending.accept refined_solution

theorem solution_chain : missing.Refines solved := by
  constructor <;> intros <;> contradiction

theorem retained_after_refinement (η : Assignment) (h : solved.Refines η) :
    implicitProducer.eval solved.value emptyValuation emptyValuation =
      implicitProducer.eval η.value emptyValuation emptyValuation :=
  implicitProducer.eval_refine h implicit_accepted.2 _ _

theorem ambiguity_diagnostic : elaborate (.overloaded 3 : Phrase [] []) none =
    .error .ambiguous := rfl

theorem ambiguous_not_admissible (o : Output [] []) :
    ¬ Elaborates (.overloaded 3) none o := by
  rintro ⟨s, hs, _⟩
  exact unresolved_overload 3 ⟨_, s, hs⟩

theorem expected_type_selects :
    elaborate (.overloaded 3 : Phrase [] []) (some .nat) = .ok (emit (.lit 3)) ∧
    elaborate (.overloaded 3 : Phrase [] []) (some .packet) =
      .ok (emit (.vector 0 (.lit 3) (.lit 0))) := ⟨rfl, rfl⟩

theorem mismatch_diagnostic : elaborate (.term producer) (some .nat) =
    .error .expectedMismatch := rfl

/-- Another well-typed packet is still the wrong translation for this source. -/
theorem typed_wrong_output_rejected :
    ¬ Faithful producer (lower otherProducer) := by
  intro h
  have he := congrArg consume (h solved.value emptyValuation emptyValuation)
  have hn := witnesses_distinguished
  apply hn
  exact ((congrArg consume (lower_sound producer _ _ _)).trans he.symm)

theorem second_strategy_admissible :
    Elaborates (.term producer) (some .packet) (emit producer).reorder :=
  elaborateReordered_sound
    (show elaborateReordered (.term producer) (some .packet) = .ok (emit producer).reorder by rfl)

theorem strategies_retain_data :
    ((emit producer).reorder.code.eval solved.value emptyValuation emptyValuation).2.toList =
      [7, 7, 7, 7, 7] := by
  change ((reorderedLowering.impl producer).eval _ _ _).2.toList = _
  rw [translation_composition]
  rfl

theorem producer_installation : DeclarationElaborates emptyValuation (.term producer)
    (some .packet) producerFinal (install producerFinal emptyValuation) :=
  install_admissible producer_accepted

theorem producer_fragment_complete :
    elaborate (.term producer) none = .ok (emit producer) :=
  elaborate_complete (.term producer (Or.inl rfl))

theorem failed_hole_is_required :
    Obligation.assigned 3 ∈ implicitProducer.requirements ∧
      ¬ (Obligation.assigned 3).Holds levelOnly :=
  checkConstraints_diagnostic (by rfl)

theorem strategies_have_different_code :
    (emit producer).code ≠ (emit producer).reorder.code := by
  intro h
  simp only [emit, producer, lower, Output.reorder, Core.reverseAdds] at h
  injection h with huni hlen hentry
  injection hlen with hleft
  injection hleft
  contradiction

end Elaboration.Examples
