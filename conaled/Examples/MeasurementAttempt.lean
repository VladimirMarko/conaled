import Applications.Interaction.Measurement
import Applications.Interaction.Snapshot

/-!
# Checked uses of the single-attempt controller

Expected outcomes come from the four independent evidence requirements: a
zero exit with complete output is insufficient when cleanup or publication is
unknown. The concrete successful world also witnesses satisfiability of the
primitive trust obligations. These are mathematical cases, not OS tests.
-/
namespace Examples.MeasurementAttempt
open Interaction Interaction.Measurement

def finished : Observation := ⟨.exited 0, true, .confirmed, .confirmed⟩
def launched : Controller := ⟨true, none⟩

theorem launch_authorized : begin initial = some launched := rfl

theorem finished_good : Good finished := ⟨rfl, rfl, rfl, rfl⟩

theorem success_reachable : successful (record launched finished) = true := by
  have h := (decide_iff finished).mpr finished_good
  simpa [successful, record, launched] using h

/-- A nonzero exit is complete evidence of an unsuccessful command. -/
theorem nonzero_rejected : decide { finished with completion := .exited 7 } ≠ true := by
  intro h
  have bad := ((decide_iff _).mp h).1
  cases bad

/-- Even complete output and confirmed cleanup/publication do not settle exit. -/
theorem unknown_rejected : decide { finished with completion := .unknown } ≠ true := by
  intro h
  have bad := ((decide_iff _).mp h).1
  cases bad

theorem partial_timeout_rejected : decide
    { finished with completion := .timedOut, outputComplete := false } ≠ true := by
  intro h
  have bad := ((decide_iff _).mp h).1
  cases bad

theorem missing_output_rejected : decide { finished with outputComplete := false } ≠ true := by
  intro h
  have bad := ((decide_iff _).mp h).2.1
  cases bad

theorem cleanup_unknown_rejected : decide { finished with cleanup := .unknown } ≠ true := by
  intro h
  have bad := ((decide_iff _).mp h).2.2.1
  cases bad

theorem publication_failed_rejected : decide { finished with publication := .failed } ≠ true := by
  intro h
  have bad := ((decide_iff _).mp h).2.2.2
  cases bad

theorem publication_unknown_rejected : decide { finished with publication := .unknown } ≠ true := by
  intro h
  have bad := ((decide_iff _).mp h).2.2.2
  cases bad

/-- Recording uncertain completion and then failed publication never grants a retry. -/
theorem uncertain_no_retry : begin
    (record (record launched { finished with completion := .unknown })
      { finished with publication := .failed }) = none := by
  apply no_reexecution (s := launched) rfl
  exact (Relation.ReflTransGen.single ⟨_, rfl⟩).tail ⟨_, rfl⟩

def goodWorld : World := ⟨some 0, true, true, true⟩

theorem goodWorld_corresponds : Corresponds goodWorld finished := by
  refine ⟨?_, (fun _ => rfl), (fun _ => rfl), (fun _ => rfl)⟩
  intro n h
  have hn : 0 = n := Completion.exited.inj h
  exact congrArg some hn

theorem completed_world : Completed goodWorld :=
  successful_world (record launched finished) finished goodWorld rfl
    goodWorld_corresponds success_reachable

/-- Primitive truth matters: the same claimed observation can accompany a world
whose publication never occurred. The controller cannot detect that lie. -/
def unpublishedWorld : World := ⟨some 0, true, true, false⟩

theorem false_publication_not_trusted : ¬ Corresponds unpublishedWorld finished := by
  intro h
  have bad := h.2.2.2 rfl
  cases bad

/-- Reuse the existing interference theorem: sealed input 17 remains the consumed
value after the live source changes to 23. This assumes the consumer relation;
the runtime fixture separately checks the adapter supplies those captured bytes. -/
theorem captured_under_mutation :
    (⟨23, 17, some 17⟩ : Snapshot.State Nat).compiled = some 17 := by
  apply Snapshot.compile_sealed 17 (s := ⟨17, 0, none⟩) trivial
  exact ⟨⟨17, 17, none⟩, ⟨rfl, rfl, rfl⟩,
    ⟨23, 17, none⟩, Relation.ReflTransGen.single ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

end Examples.MeasurementAttempt
