import Applications.Resources.ListReversal
import Applications.Resources.Workload

/-!
Two ordinary-list alternatives discussed before the difference-list scanner
in FDSA, Chapter 2, p. 22. Repeated append incurs the terminal-inclusive append
count from `ListReversal`; prepending and then reversing uses the existing
accumulator-reversal execution twice. Both compute the input in its original
order. The append-only subobservation, full recursive loop, and one-unit outer
wrapper remain explicit. No compiled-library or machine-time claim is made.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.ListBuildCosts
universe u
variable {α : Type u}

/-- Append one incoming element to the already constructed ordinary prefix. -/
def appendStep (a : α) (prefix : List α) : Measured (List α) Nat :=
  ListReversal.appendRun prefix [a]

/-- Observe only the append invocations; the supplied seed is already constructed. -/
def appendSubRun (items prefix : List α) : Measured (List α) Nat :=
  run appendStep items prefix

@[simp] theorem appendSubRun_nil (prefix : List α) :
    appendSubRun [] prefix = (prefix, 0) := rfl

theorem appendSubRun_cons (a : α) (items prefix : List α) :
    appendSubRun (a :: items) prefix =
      ((appendSubRun items (prefix ++ [a])).1,
        prefix.length + 1 + (appendSubRun items (prefix ++ [a])).2) := by
  simp only [appendSubRun, run_cons, appendStep, ListReversal.appendRun_exact]

theorem appendSubRun_value (items prefix : List α) :
    (appendSubRun items prefix).1 = prefix ++ items := by
  induction items generalizing prefix with
  | nil => simp
  | cons a items ih =>
      simp only [appendSubRun_cons, ih, List.append_assoc, List.singleton_append]

/-- Each next append traverses the prefix returned by the preceding append. -/
theorem appendSubRun_double_cost (items prefix : List α) :
    2 * (appendSubRun items prefix).2 =
      2 * items.length * prefix.length + items.length * (items.length + 1) := by
  induction items generalizing prefix with
  | nil => simp
  | cons a items ih =>
      have h := ih (prefix ++ [a])
      simp only [List.length_append, List.length_singleton] at h
      simp only [appendSubRun_cons, List.length_cons]
      nlinarith

/-- Natural division is derived from the execution's division-free exact equality. -/
theorem appendSubRun_cost (items prefix : List α) :
    (appendSubRun items prefix).2 =
      items.length * prefix.length + items.length * (items.length + 1) / 2 := by
  have h := appendSubRun_double_cost items prefix
  simp only [Nat.mul_assoc] at h
  omega

theorem appendSubRun_empty_cost (items : List α) :
    (appendSubRun items []).2 = items.length * (items.length + 1) / 2 := by
  simpa using appendSubRun_cost items []

/-- The full loop adds one entry at each recursive call, including the terminal call. -/
def appendLoopRun : List α → List α → Measured (List α) Nat
  | [], prefix => CallCount.tick (pure prefix)
  | a :: items, prefix =>
      CallCount.tick (bind (ListReversal.appendRun prefix [a]) (appendLoopRun items))

@[simp] theorem appendLoopRun_nil (prefix : List α) :
    appendLoopRun [] prefix = (prefix, 1) := rfl

theorem appendLoopRun_cons (a : α) (items prefix : List α) :
    appendLoopRun (a :: items) prefix =
      ((appendLoopRun items (prefix ++ [a])).1,
        prefix.length + 1 + (appendLoopRun items (prefix ++ [a])).2 + 1) := by
  simp only [appendLoopRun, ListReversal.appendRun_exact, bind, CallCount.tick]

theorem appendLoopRun_value (items prefix : List α) :
    (appendLoopRun items prefix).1 = prefix ++ items := by
  induction items generalizing prefix with
  | nil => simp
  | cons a items ih =>
      simp only [appendLoopRun_cons, ih, List.append_assoc, List.singleton_append]

theorem appendLoopRun_cost (items prefix : List α) :
    (appendLoopRun items prefix).2 =
      (appendSubRun items prefix).2 + items.length + 1 := by
  induction items generalizing prefix with
  | nil => rfl
  | cons a items ih =>
      have h := ih (prefix ++ [a])
      simp only [appendLoopRun_cons, appendSubRun_cons, List.length_cons]
      omega

/-- One wrapper entry supplies the empty seed and executes the full append loop. -/
def appendBuildRun (items : List α) : Measured (List α) Nat :=
  CallCount.tick (appendLoopRun items [])

theorem appendBuildRun_value (items : List α) : (appendBuildRun items).1 = items := by
  simp only [appendBuildRun, CallCount.tick_value, appendLoopRun_value, List.nil_append]

theorem appendBuildRun_cost (items : List α) :
    (appendBuildRun items).2 = items.length * (items.length + 1) / 2 + items.length + 2 := by
  rw [appendBuildRun, CallCount.tick_cost, appendLoopRun_cost, appendSubRun_empty_cost]
  omega

theorem appendBuildRun_double_cost (items : List α) :
    2 * (appendBuildRun items).2 = items.length * items.length + 3 * items.length + 4 := by
  have h := appendSubRun_double_cost items []
  simp only [List.length_nil, Nat.mul_zero, Nat.zero_add] at h
  rw [appendBuildRun, CallCount.tick_cost, appendLoopRun_cost]
  nlinarith

theorem appendBuildRun_exact (items : List α) :
    appendBuildRun items =
      (items, items.length * (items.length + 1) / 2 + items.length + 2) := by
  apply Prod.ext
  · exact appendBuildRun_value items
  · exact appendBuildRun_cost items

/-- Prepend each input element, then feed that actual reversed value to reversal. -/
def consReverseBuildRun (items : List α) : Measured (List α) Nat :=
  CallCount.tick (bind (SymmetricCosts.reverseRun items [])
    (fun reversed => SymmetricCosts.reverseRun reversed []))

theorem consReverseBuildRun_value (items : List α) :
    (consReverseBuildRun items).1 = items := by
  simp [consReverseBuildRun, bind, SymmetricCosts.reverseRun_value]

theorem consReverseBuildRun_cost (items : List α) :
    (consReverseBuildRun items).2 = 2 * items.length + 3 := by
  simp only [consReverseBuildRun, CallCount.tick_cost, bind,
    SymmetricCosts.reverseRun_work, SymmetricCosts.reverseRun_value,
    List.append_nil, List.length_reverse]
  omega

theorem consReverseBuildRun_exact (items : List α) :
    consReverseBuildRun items = (items, 2 * items.length + 3) := by
  apply Prod.ext
  · exact consReverseBuildRun_value items
  · exact consReverseBuildRun_cost items

/-- Ordered values agree; their observations have been established independently. -/
theorem realizations_agree (items : List α) :
    (appendBuildRun items).1 = (consReverseBuildRun items).1 := by
  rw [appendBuildRun_value, consReverseBuildRun_value]

/-- A quadratic lower bound, in a subtraction-free form valid even on empty input. -/
theorem appendBuildRun_quadratic_lower (items : List α) :
    items.length * items.length ≤ 2 * (appendBuildRun items).2 := by
  rw [appendBuildRun_double_cost]
  omega

theorem appendBuildRun_quadratic_upper (items : List α) (hn : 1 ≤ items.length) :
    (appendBuildRun items).2 ≤ 4 * items.length * items.length := by
  have hs : items.length ≤ items.length * items.length := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left items.length hn
  have hc := appendBuildRun_double_cost items
  nlinarith

theorem consReverseBuildRun_linear_upper (items : List α) (hn : 1 ≤ items.length) :
    (consReverseBuildRun items).2 ≤ 5 * items.length := by
  rw [consReverseBuildRun_cost]
  omega

end Resources.ListBuildCosts
