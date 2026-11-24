import Applications.Resources.FirstHitScan

/-! The store [0,2,0,3] has consecutive prefix sums 0,0,2,2,5.
Threshold 5 is reached only after the last entry; threshold 6 is never reached.
All result proofs use the public measured execution theorem. -/
namespace Examples.FirstHitScan
open Resources Resources.FirstHitScan Resources.MeasuredLoop

def data : Array Nat := #[0,2,0,3]
def read := arrayRead data

private theorem four_steps (t : Nat) (h : 2 < t) :
    Steps (done 4) (step read) 4 (0,(0,t)) (4,(5,t)) := by
  apply Steps.step (by simp [done]; omega)
  apply Steps.step (by simp [done, step, read, arrayRead, data]; omega)
  apply Steps.step (by simp [done, step, read, arrayRead, data]; omega)
  apply Steps.step (by simp [done, step, read, arrayRead, data]; omega)
  apply Steps.stop
  simp [done, step, read, arrayRead, data]

theorem last_entry : compiled 4 read (0,(0,5)) = ((4,5),47) :=
  compiled_of_steps (four_steps 5 (by decide))

theorem unreached : compiled 4 read (0,(0,6)) = ((4,5),47) :=
  compiled_of_steps (four_steps 6 (by decide))

theorem first_hit_with_zero : compiled 4 read (0,(0,2)) = ((2,2),27) := by
  apply compiled_of_steps (k := 2) (y := (2,(2,2)))
  exact .step (by decide) (.step (by decide) (.stop (by decide)))

theorem supplied_start_and_sum : compiled 4 read (1,(7,9)) = ((2,9),17) := by
  apply compiled_of_steps (k := 1) (y := (2,(9,9)))
  exact .step (by decide) (.stop (by decide))

theorem immediate : compiled 4 read (1,(7,7)) = ((1,7),7) :=
  compiled_of_steps (.stop (by decide))

theorem exhausted : compiled 4 read (4,(1,8)) = ((4,1),7) :=
  compiled_of_steps (.stop (by decide))

theorem empty : compiled 0 (arrayRead #[]) (0,(1,8)) = ((0,1),7) :=
  compiled_of_steps (.stop (by decide))

/-- Minimality is connected to the independent sumPrefix sum, not just an output. -/
theorem last_entry_spec : FirstHit read 4 (0,(0,5)) 4 (4,5) :=
  (source_correct (four_steps 5 (by decide)) (by decide)).1

theorem native_last_entry : native 4 read (0,(0,5)) = ((4,5),47) := by
  rw [← routes_equal]
  exact last_entry

/-- The second indexed representation reuses local read preservation and the
same source execution. Its precise observation includes the stopping index. -/
theorem finite_function_last_entry :
    compiled 4 (finiteRead (fun j : Fin data.size => data[j])) (0,(0,5)) = ((4,5),47) := by
  change compiled data.size (finiteRead (fun j : Fin data.size => data[j])) (0,(0,5)) = _
  rw [← array_reuse data]
  exact last_entry

/-- A post-read convention would incorrectly read once even on immediate stop. -/
theorem no_read_on_immediate :
    FirstHit read 4 (1,(7,7)) 0 (1,7) ∧ step read (1,(7,7)) ≠ (1,(7,7)) := by
  constructor
  · exact (source_correct (Steps.stop (by decide)) (by decide)).1
  · decide

/-- Changing one legal read changes the precise terminal observation. -/
theorem changed_read_rejected :
    compiled 4 (fun _ => 0) (0,(0,5)) ≠ compiled 4 read (0,(0,5)) := by
  have hz : compiled 4 (fun _ => 0) (0,(0,5)) = ((4,0),47) := by
    apply compiled_of_steps (k := 4) (y := (4,(0,5)))
    exact .step (by decide) (.step (by decide) (.step (by decide) (.step (by decide) (.stop (by decide)))))
  rw [hz, last_entry]
  decide

end Examples.FirstHitScan
