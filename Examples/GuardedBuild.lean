import Applications.Resources.GuardedBuild
import Applications.Resources.ListExecution
import Examples.RunCompression

/-! Independent stopping boundaries connected to the guarded executor's public
value relation and exact work identity. Dropping counts predicate tests; insertion
also counts its one new cons cell. Independent run certificates reach the measured
builder, and its complete finite execution composes with the actual head observer.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.GuardedBuild

open Resources.GuardedBuild

universe u
variable {α : Type u}

private def belowThree (n : Nat) : Bool := decide (n < 3)

/-- The final passing 1 lies after the first failure and remains untouched. -/
theorem first_failure_spec : DropSpec belowThree [1, 2, 9, 1] [9, 1] := by
  refine ⟨[1, 2], rfl, ?_, Or.inr ⟨9, [1], rfl, by decide⟩⟩
  simp [belowThree]

/-- Two passing tests and one failed test cost three, preserving the whole suffix. -/
theorem first_failure : dropRun belowThree [1, 2, 9, 1] = ([9, 1], 3) := by
  have hv := dropRun_unique belowThree [1, 2, 9, 1] [9, 1] first_failure_spec
  apply Prod.ext hv
  have hb := dropRun_balance belowThree [1, 2, 9, 1]
  rw [hv] at hb
  simp only [List.length_cons, List.length_nil, survivorCharge] at hb
  omega

/-- Exhaustion performs one test per element and has no final failed test. -/
theorem drop_all (xs : List α) : dropRun (fun _ => true) xs = ([], xs.length) := by
  have hv := dropRun_unique (fun _ : α => true) xs []
    ⟨xs, by simp, by simp, Or.inl rfl⟩
  apply Prod.ext hv
  have hb := dropRun_balance (fun _ : α => true) xs
  simpa [hv, survivorCharge] using hb

theorem drop_empty (q : α → Bool) : dropRun q [] = ([], 0) := rfl

/-- A failed first test charges one even when there is only one element. -/
theorem drop_singleton_failure (x : α) :
    dropRun (fun _ => false) [x] = ([x], 1) := by
  have hv := dropRun_unique (fun _ : α => false) [x] [x]
    ⟨[], rfl, by simp, Or.inr ⟨x, [], rfl, rfl⟩⟩
  apply Prod.ext hv
  have hb := dropRun_balance (fun _ : α => false) [x]
  simpa [hv, survivorCharge] using hb

/-- A failed test preserves the old element; the inserted cons adds a second unit. -/
theorem insert_false : insertRun (fun (_ _ : Nat) => false) 1 [2] = ([1, 2], 2) := by
  rw [insertRun, drop_singleton_failure]
  rfl

/-- One passing test exhausts the old singleton, then the new cons costs one. -/
theorem insert_true : insertRun (fun (_ _ : Nat) => true) 1 [2] = ([1], 2) := by
  rw [insertRun, drop_all]
  rfl

/-- Exhausting an arbitrary old suffix makes the actual insertion work linear. -/
theorem insert_all (x : α) (xs : List α) :
    insertRun (fun _ _ => true) x xs = ([x], xs.length + 1) := by
  rw [insertRun, drop_all]
  rfl

theorem insert_empty (p : α → α → Bool) (x : α) :
    insertRun p x [] = ([x], 1) := rfl

/-- An arbitrary guard may ignore the inserted value; the later passing 1 survives. -/
theorem insert_prefix :
    insertRun (fun (_ : Nat) y => belowThree y) 7 [1, 2, 9, 1] = ([7, 9, 1], 4) := by
  rw [insertRun, first_failure]
  rfl

theorem insert_prefix_value :
    insert (fun (_ : Nat) y => belowThree y) 7 [1, 2, 9, 1] = [7, 9, 1] := by
  rw [← insertRun_value]
  exact congrArg Prod.fst insert_prefix

/-- The checked pair and the general potential law witness the same correction. -/
theorem failed_test_correction :
    insertRun (fun (_ _ : Nat) => false) 1 [2] = ([1, 2], 2) ∧
      (insertRun (fun (_ _ : Nat) => false) 1 [2]).2 +
        (insertRun (fun (_ _ : Nat) => false) 1 [2]).1.length > [2].length + 2 :=
  ⟨insert_false, failed_test_charge_two_counterexample⟩

theorem build_empty (p : α → α → Bool) : buildRun p [] = ([], 0) := rfl

theorem build_singleton (p : α → α → Bool) (x : α) : buildRun p [x] = ([x], 1) := by
  simp only [buildRun, Resources.pure_bind, insert_empty]

/-- The suffix is built first: one initial cons, then two failed tests and two cons. -/
theorem source_false_build :
    buildRun (fun (_ _ : Nat) => false) [1, 2, 3] = ([1, 2, 3], 5) := by
  rw [buildRun_eq_run_reverse]
  rfl

/-- The first insertion starts empty; exactly the next two insertions stop at failure. -/
theorem source_false_build_survivors :
    survivors (fun (_ _ : Nat) => false) [1, 2, 3] = 2 := by
  have h := buildRun_potential_exact (fun (_ _ : Nat) => false) [1, 2, 3]
  rw [source_false_build] at h
  simp only [List.length_cons, List.length_nil] at h
  omega

universe uGuardedClient

/-- Run the complete finite equality builder, then observe its head. This is
not a short-circuiting compression operation. -/
def buildHead {α : Type uGuardedClient} [BEq α] (xs : List α) :
    Resources.Measured (Option α) Nat :=
  Resources.bind (buildRun (· == ·) xs) Resources.ListExecution.head

theorem buildHead_value {α : Type uGuardedClient} [BEq α] [LawfulBEq α]
    (xs : List α) : (buildHead xs).1 = xs.head? := by
  unfold buildHead
  rw [Resources.bind_value, Resources.ListExecution.head_value,
    buildRun_equality_value]
  cases xs with
  | nil => rfl
  | cons x xs =>
    exact Applications.Sequences.RunCompression.build_equality_head x xs

/-- The observer contributes one unit after the actual builder's work,
independently of any equality law. -/
theorem buildHead_work {α : Type uGuardedClient} [BEq α] (xs : List α) :
    (buildHead xs).2 = (buildRun (· == ·) xs).2 + 1 := by
  simp only [buildHead, Resources.bind, Resources.ListExecution.head_work]

theorem buildHead_work_le {α : Type uGuardedClient} [BEq α] (xs : List α) :
    (buildHead xs).2 ≤ 3 * xs.length + 1 := by
  rw [buildHead_work]
  exact Nat.add_le_add_right (buildRun_work_le (· == ·) xs) 1

/-- The source's eight-entry fixture, certified from adjacent original inputs.
The two occurrences of 2 separated by the run of 1 remain separate. -/
theorem source_runs_certificate :
    Applications.Sequences.RunCompression.Spec
      ([4, 4, 2, 1, 1, 1, 2, 5] : List Nat) [4, 2, 1, 2, 5] := by
  have tail : Applications.Sequences.RunCompression.Spec
      ([1, 1, 1, 2, 5] : List Nat) [1, 2, 5] :=
    .repeated (.repeated (.boundary (by decide) (.boundary (by decide) (.single 5))))
  exact .repeated (.boundary (by decide) (.boundary (by decide) tail))

theorem source_runs_value :
    (buildRun (fun x y : Nat => x == y) [4, 4, 2, 1, 1, 1, 2, 5]).1 =
      [4, 2, 1, 2, 5] :=
  buildRun_equality_of_spec source_runs_certificate

/-- One public-contract client covers Build.example@229 and
BuildEquality.example@158 without replacing their two provenance rows. -/
theorem source_runs_build :
    Resources.GuardedBuild.build (fun x y : Nat => x == y)
      [4, 4, 2, 1, 1, 1, 2, 5] = [4, 2, 1, 2, 5] :=
  (buildRun_value (fun x y : Nat => x == y)
    [4, 4, 2, 1, 1, 1, 2, 5]).symm.trans source_runs_value

/-- Actual insertion costs in suffix-first order are 1,2,2,3,3,2,2,3.
The value uses the independent certificate; work uses the actual run bridge. -/
theorem source_runs_pair :
    buildRun (fun x y : Nat => x == y) [4, 4, 2, 1, 1, 1, 2, 5] =
      ([4, 2, 1, 2, 5], 18) := by
  apply Prod.ext
  · exact source_runs_value
  · calc
      (buildRun (fun x y : Nat => x == y) [4, 4, 2, 1, 1, 1, 2, 5]).2 =
          (Resources.run (insertRun (fun x y : Nat => x == y))
            [5, 2, 1, 1, 1, 2, 4, 4] []).2 :=
        congrArg Prod.snd (buildRun_eq_run_reverse (fun x y : Nat => x == y)
          [4, 4, 2, 1, 1, 1, 2, 5])
      _ = 18 := rfl

theorem separated_runs_certificate :
    Applications.Sequences.RunCompression.Spec
      ([1, 2, 1, 1, 2, 2, 1] : List Nat) [1, 2, 1, 2, 1] := by
  have tail : Applications.Sequences.RunCompression.Spec
      ([2, 2, 1] : List Nat) [2, 1] :=
    .repeated (.boundary (by decide) (.single 1))
  exact .boundary (by decide)
    (.boundary (by decide) (.repeated (.boundary (by decide) tail)))

theorem separated_runs_value :
    (buildRun (fun x y : Nat => x == y) [1, 2, 1, 1, 2, 2, 1]).1 =
      [1, 2, 1, 2, 1] :=
  buildRun_equality_of_spec separated_runs_certificate

/-- BuildEquality.example@159 reaches the existing standard realization
through the same adjacent-input certificate. -/
theorem separated_runs_compress :
    Applications.Sequences.RunCompression.compress
      ([1, 2, 1, 1, 2, 2, 1] : List Nat) = [1, 2, 1, 2, 1] :=
  Applications.Sequences.RunCompression.compress_unique separated_runs_certificate

/-- The measured nil pair retains the existing checked empty value client.
Examples.RunCompression.empty also retains BuildEquality.example@160 for the
standard compression realization. -/
theorem source_empty :
    buildRun (fun x y : Nat => x == y) [] = ([], 0) := by
  apply Prod.ext
  · exact (buildRun_equality_value ([] : List Nat)).trans Examples.RunCompression.empty.1
  · rfl

theorem buildHead_empty : buildHead ([] : List Nat) = (none, 1) := by
  apply Prod.ext
  · exact buildHead_value ([] : List Nat)
  · calc
      (buildHead ([] : List Nat)).2 = (buildRun (· == ·) ([] : List Nat)).2 + 1 :=
        buildHead_work []
      _ = 1 := rfl

/-- Observing only the head still charges the full finite build: eighteen
builder units and one observer unit. -/
theorem buildHead_source_runs :
    buildHead ([4, 4, 2, 1, 1, 1, 2, 5] : List Nat) = (some 4, 19) := by
  apply Prod.ext
  · exact buildHead_value [4, 4, 2, 1, 1, 1, 2, 5]
  · calc
      (buildHead ([4, 4, 2, 1, 1, 1, 2, 5] : List Nat)).2 =
          (buildRun (· == ·) [4, 4, 2, 1, 1, 1, 2, 5]).2 + 1 :=
        buildHead_work _
      _ = 19 := by rw [source_runs_pair]

end Examples.GuardedBuild
