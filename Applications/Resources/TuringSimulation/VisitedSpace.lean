import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Interval
import Mathlib.Order.Monotone.Basic
import Lean.Elab.Tactic.Omega

/-!
# Actual native prefixes, visited cells and physical tape containment

Observe the actual native command and head movement at every prefix. Bounds include input cells, all visited positions, the enclosing interval and every nonblank physical cell; terminal none adds no cells.
-/

set_option autoImplicit false
set_option warningAsError true


namespace Resources.TuringSimulation.VisitedSpace

open Function Turing

/-- Signed displacement of an actual native movement. -/
def directionOffset : Dir → ℤ
  | .left => -1
  | .right => 1

/-- Writes and absent transitions do not move the physical head. -/
def commandOffset {Γ Q : Type*} : Option (Q × TM0.Stmt Γ) → ℤ
  | some (_, .move d) => directionOffset d
  | some (_, .write _) => 0
  | none => 0

theorem commandOffset_bounds {Γ Q : Type*} (a : Option (Q × TM0.Stmt Γ)) :
    -1 ≤ commandOffset a ∧ commandOffset a ≤ 1 := by
  cases a with
  | none =>
    change (-1 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ 1
    decide
  | some a =>
    rcases a with ⟨q, s⟩
    cases s with
    | write _ =>
      change (-1 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ 1
      decide
    | move d =>
      cases d with
      | left =>
        change (-1 : ℤ) ≤ -1 ∧ (-1 : ℤ) ≤ 1
        decide
      | right =>
        change (-1 : ℤ) ≤ 1 ∧ (1 : ℤ) ≤ 1
        decide

section NativeRun

variable {Γ Q : Type*} [Inhabited Γ] [Inhabited Q]

/-- The literal native optional iterate, with the supplied initial cfg retained. -/
def cfgAt (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q) (n : ℕ) :
    Option (TM0.Cfg Γ Q) :=
  (flip Bind.bind (TM0.step M))^[n] (some start)

theorem cfgAt_zero (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q) :
    cfgAt M start 0 = some start := rfl

theorem cfgAt_succ (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q) (n : ℕ) :
    cfgAt M start (n + 1) = (cfgAt M start n).bind (TM0.step M) :=
  Function.iterate_succ_apply' (flip Bind.bind (TM0.step M)) n (some start)

/-- The command actually selected by the native state and tape-head symbol. -/
def commandAt (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q) (n : ℕ) :
    Option (Q × TM0.Stmt Γ) :=
  (cfgAt M start n).bind (fun c => M c.q c.Tape.head)

theorem commandAt_of_live (M : TM0.Machine Γ Q) (start c : TM0.Cfg Γ Q)
    (n : ℕ) (h : cfgAt M start n = some c) :
    commandAt M start n = M c.q c.Tape.head := by
  unfold commandAt
  rw [h]; rfl

theorem commandAt_of_none (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q)
    (n : ℕ) (h : cfgAt M start n = none) : commandAt M start n = none := by
  unfold commandAt
  rw [h]; rfl

/-- Absolute head coordinate at a native prefix. After outer none, the last
coordinate is retained as bookkeeping; `visitedCells` excludes absent prefixes. -/
def headPosition (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q) (origin : ℤ) : ℕ → ℤ
  | 0 => origin
  | n + 1 => headPosition M start origin n + commandOffset (commandAt M start n)

theorem headPosition_zero (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q) (origin : ℤ) :
    headPosition M start origin 0 = origin := rfl

theorem headPosition_succ (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q)
    (origin : ℤ) (n : ℕ) :
    headPosition M start origin (n + 1) =
      headPosition M start origin n + commandOffset (commandAt M start n) := rfl

theorem headPosition_step_bounds (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q)
    (origin : ℤ) (n : ℕ) :
    headPosition M start origin n - 1 ≤ headPosition M start origin (n + 1) ∧
      headPosition M start origin (n + 1) ≤ headPosition M start origin n + 1 := by
  have h := commandOffset_bounds (commandAt M start n)
  rw [headPosition_succ]
  omega

theorem headPosition_bounds (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q)
    (origin : ℤ) (n : ℕ) :
    origin - n ≤ headPosition M start origin n ∧
      headPosition M start origin n ≤ origin + n := by
  induction n with
  | zero => simp only [headPosition_zero, Nat.cast_zero, sub_zero, add_zero, le_refl, and_self]
  | succ n ih =>
    have h := headPosition_step_bounds M start origin n
    omega

/-- Exactly the positions of actual live native prefixes, including prefix 0. -/
def visitedCells (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q) (origin : ℤ)
    (T : ℕ) : Finset ℤ :=
  ((Finset.range (T + 1)).filter (fun i => (cfgAt M start i).isSome = true)).image
    (headPosition M start origin)

theorem mem_visitedCells (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q)
    (origin : ℤ) (T : ℕ) (x : ℤ) :
    x ∈ visitedCells M start origin T ↔
      ∃ i, i ≤ T ∧ (cfgAt M start i).isSome = true ∧
        headPosition M start origin i = x := by
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, hpos⟩
    rcases Finset.mem_filter.mp hi with ⟨hrange, hlive⟩
    exact ⟨i, Nat.le_of_lt_succ (Finset.mem_range.mp hrange), hlive, hpos⟩
  · rintro ⟨i, hi, hlive, hpos⟩
    exact Finset.mem_image.mpr ⟨i,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hi), hlive⟩, hpos⟩

theorem live_head_mem_visitedCells (M : TM0.Machine Γ Q) (start c : TM0.Cfg Γ Q)
    (origin : ℤ) (i T : ℕ) (hi : i ≤ T) (hc : cfgAt M start i = some c) :
    headPosition M start origin i ∈ visitedCells M start origin T := by
  apply (mem_visitedCells M start origin T _).mpr
  exact ⟨i, hi, by rw [hc]; rfl, rfl⟩

theorem origin_mem_visitedCells (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q)
    (origin : ℤ) (T : ℕ) : origin ∈ visitedCells M start origin T := by
  exact (mem_visitedCells M start origin T origin).mpr
    ⟨0, Nat.zero_le T, rfl, rfl⟩

theorem visitedCells_mono (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q)
    (origin : ℤ) {i j : ℕ} (hij : i ≤ j) :
    visitedCells M start origin i ⊆ visitedCells M start origin j := by
  intro x hx
  rcases (mem_visitedCells M start origin i x).mp hx with ⟨k, hk, hlive, hpos⟩
  exact (mem_visitedCells M start origin j x).mpr
    ⟨k, le_trans hk hij, hlive, hpos⟩

theorem visitedCells_card_le (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q)
    (origin : ℤ) (T : ℕ) : (visitedCells M start origin T).card ≤ T + 1 := by
  calc
    _ ≤ ((Finset.range (T + 1)).filter
        (fun i => (cfgAt M start i).isSome = true)).card := Finset.card_image_le
    _ ≤ (Finset.range (T + 1)).card := Finset.card_filter_le _ _
    _ = T + 1 := Finset.card_range _

/-- An outer-none prefix contributes no live head position. -/
theorem visitedCells_succ_of_none (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q)
    (origin : ℤ) (n : ℕ) (h : cfgAt M start (n + 1) = none) :
    visitedCells M start origin (n + 1) = visitedCells M start origin n := by
  apply Finset.Subset.antisymm
  · intro x hx
    rcases (mem_visitedCells M start origin (n + 1) x).mp hx with
      ⟨i, hi, hlive, hpos⟩
    have hne : i ≠ n + 1 := by
      intro heq
      subst i
      rw [h] at hlive
      cases hlive
    exact (mem_visitedCells M start origin n x).mpr ⟨i, by omega, hlive, hpos⟩
  · exact visitedCells_mono M start origin (Nat.le_succ n)

theorem cfgAt_add_of_none (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q)
    (n : ℕ) (h : cfgAt M start n = none) (k : ℕ) :
    cfgAt M start (n + k) = none := by
  induction k with
  | zero => simpa only [Nat.add_zero] using h
  | succ k ih =>
    rw [Nat.add_succ, cfgAt_succ, ih]; rfl

/-- Restarting at an actual live prefix preserves every subsequent complete
optional configuration, including any later outer-none prefix. -/
theorem cfgAt_add_of_live (M : TM0.Machine Γ Q) (start finish : TM0.Cfg Γ Q)
    (n : ℕ) (h : cfgAt M start n = some finish) (k : ℕ) :
    cfgAt M start (n + k) = cfgAt M finish k := by
  induction k with
  | zero => simpa only [Nat.add_zero, cfgAt_zero] using h
  | succ k ih =>
    rw [Nat.add_succ, cfgAt_succ, ih, cfgAt_succ]

/-- The entire actual command is preserved by a live split: next control,
movement or written symbol, and absence of a command. -/
theorem commandAt_add_of_live (M : TM0.Machine Γ Q) (start finish : TM0.Cfg Γ Q)
    (n : ℕ) (h : cfgAt M start n = some finish) (k : ℕ) :
    commandAt M start (n + k) = commandAt M finish k := by
  unfold commandAt
  rw [cfgAt_add_of_live M start finish n h k]

/-- The suffix uses the actual coordinate reached at the live split. This
follows the native command offsets, not an equality of endpoint tapes. -/
theorem headPosition_add_of_live (M : TM0.Machine Γ Q)
    (start finish : TM0.Cfg Γ Q) (origin : ℤ)
    (n : ℕ) (h : cfgAt M start n = some finish) (k : ℕ) :
    headPosition M start origin (n + k) =
      headPosition M finish (headPosition M start origin n) k := by
  induction k with
  | zero => simp only [Nat.add_zero, headPosition_zero]
  | succ k ih =>
    rw [Nat.add_succ, headPosition_succ, ih,
      commandAt_add_of_live M start finish n h k, headPosition_succ]


theorem visitedCells_add_of_none (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q)
    (origin : ℤ) (n : ℕ) (h : cfgAt M start n = none) (k : ℕ) :
    visitedCells M start origin (n + k) = visitedCells M start origin n := by
  induction k with
  | zero => rw [Nat.add_zero]
  | succ k ih =>
    rw [Nat.add_succ, visitedCells_succ_of_none M start origin (n + k)
      (cfgAt_add_of_none M start n h (k + 1)), ih]

end NativeRun

/-- Declared input coordinates. Blank-valued input symbols still occupy an
input position; these cells need not all have been visited yet. -/
def inputCells (origin : ℤ) (N : ℕ) : Finset ℤ :=
  (Finset.range N).image (fun i : ℕ => origin + (i : ℤ))

theorem mem_inputCells (origin : ℤ) (N : ℕ) (x : ℤ) :
    x ∈ inputCells origin N ↔ ∃ i : ℕ, i < N ∧ origin + i = x := by
  simp only [inputCells, Finset.mem_image, Finset.mem_range]

section Interval

variable {Γ Q : Type*} [Inhabited Γ] [Inhabited Q]

/-- Initial input positions together with all actual head visits. -/
def inputVisitedCells (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q) (origin : ℤ)
    (N T : ℕ) : Finset ℤ := inputCells origin N ∪ visitedCells M start origin T

/-- Left endpoint of the interval reached by the actual primitive head trace. -/
def leftEdge (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q) (origin : ℤ) : ℕ → ℤ
  | 0 => origin
  | n + 1 => min (leftEdge M start origin n) (headPosition M start origin (n + 1))

/-- Right endpoint; initially includes the declared input and the head cell. -/
def rightEdge (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q) (origin : ℤ)
    (N : ℕ) : ℕ → ℤ
  | 0 => origin + ((N - 1 : ℕ) : ℤ)
  | n + 1 => max (rightEdge M start origin N n) (headPosition M start origin (n + 1))

theorem leftEdge_succ (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q)
    (origin : ℤ) (n : ℕ) :
    leftEdge M start origin (n + 1) =
      min (leftEdge M start origin n) (headPosition M start origin (n + 1)) := rfl

theorem rightEdge_succ (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q)
    (origin : ℤ) (N n : ℕ) :
    rightEdge M start origin N (n + 1) =
      max (rightEdge M start origin N n) (headPosition M start origin (n + 1)) := rfl

/-- A genuine finite interval enclosing the input and all primitive visits,
not merely the final nonblank support or the TM1 boundary configurations. -/
def visitedInterval (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q) (origin : ℤ)
    (N T : ℕ) : Finset ℤ :=
  Finset.Icc (leftEdge M start origin T) (rightEdge M start origin N T)

theorem headPosition_between_edges (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q)
    (origin : ℤ) (N n : ℕ) :
    leftEdge M start origin n ≤ headPosition M start origin n ∧
      headPosition M start origin n ≤ rightEdge M start origin N n := by
  cases n with
  | zero =>
    change origin ≤ origin ∧ origin ≤ origin + ((N - 1 : ℕ) : ℤ)
    omega
  | succ n => exact ⟨min_le_right _ _, le_max_right _ _⟩

theorem leftEdge_antitone (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q)
    (origin : ℤ) : Antitone (leftEdge M start origin) :=
  antitone_nat_of_succ_le (fun _ => min_le_left _ _)

theorem rightEdge_monotone (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q)
    (origin : ℤ) (N : ℕ) : Monotone (rightEdge M start origin N) :=
  monotone_nat_of_le_succ (fun _ => le_max_left _ _)

theorem visitedCells_subset_interval (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q)
    (origin : ℤ) (N T : ℕ) :
    visitedCells M start origin T ⊆ visitedInterval M start origin N T := by
  intro x hx
  rcases (mem_visitedCells M start origin T x).mp hx with ⟨i, hi, _, hpos⟩
  rw [← hpos]
  have h := headPosition_between_edges M start origin N i
  exact Finset.mem_Icc.mpr
    ⟨le_trans (leftEdge_antitone M start origin hi) h.1,
      le_trans h.2 (rightEdge_monotone M start origin N hi)⟩

theorem inputCells_subset_interval (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q)
    (origin : ℤ) (N T : ℕ) : inputCells origin N ⊆ visitedInterval M start origin N T := by
  intro x hx
  rcases (mem_inputCells origin N x).mp hx with ⟨i, hi, hpos⟩
  have hl := leftEdge_antitone M start origin (Nat.zero_le T)
  have hr := rightEdge_monotone M start origin N (Nat.zero_le T)
  change leftEdge M start origin T ≤ origin at hl
  change origin + ((N - 1 : ℕ) : ℤ) ≤ rightEdge M start origin N T at hr
  apply Finset.mem_Icc.mpr
  omega

theorem inputVisitedCells_subset_interval (M : TM0.Machine Γ Q)
    (start : TM0.Cfg Γ Q) (origin : ℤ) (N T : ℕ) :
    inputVisitedCells M start origin N T ⊆ visitedInterval M start origin N T := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact inputCells_subset_interval M start origin N T hx
  · exact visitedCells_subset_interval M start origin N T hx

/-- Every real move enlarges the enclosing interval by at most one. The two
endpoints cannot both extend in one step because the old head lies between them. -/
theorem interval_width_le (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q)
    (origin : ℤ) (N T : ℕ) :
    rightEdge M start origin N T + 1 - leftEdge M start origin T ≤
      ((max N 1 + T : ℕ) : ℤ) := by
  induction T with
  | zero =>
    change origin + ((N - 1 : ℕ) : ℤ) + 1 - origin ≤ ((max N 1 + 0 : ℕ) : ℤ)
    omega
  | succ T ih =>
    have hold := headPosition_between_edges M start origin N T
    have hmove := headPosition_step_bounds M start origin T
    rw [rightEdge_succ, leftEdge_succ]
    omega

theorem visitedInterval_card_le (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q)
    (origin : ℤ) (N T : ℕ) :
    (visitedInterval M start origin N T).card ≤ max N 1 + T := by
  rw [visitedInterval, Int.card_Icc]
  exact Int.toNat_le.mpr (interval_width_le M start origin N T)

theorem inputVisitedCells_card_le (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q)
    (origin : ℤ) (N T : ℕ) :
    (inputVisitedCells M start origin N T).card ≤ max N 1 + T :=
  le_trans (Finset.card_le_card (inputVisitedCells_subset_interval M start origin N T))
    (visitedInterval_card_le M start origin N T)

theorem visitedInterval_succ_of_no_command (M : TM0.Machine Γ Q)
    (start : TM0.Cfg Γ Q) (origin : ℤ) (N n : ℕ)
    (h : commandAt M start n = none) :
    visitedInterval M start origin N (n + 1) = visitedInterval M start origin N n := by
  have hp : headPosition M start origin (n + 1) = headPosition M start origin n := by
    rw [headPosition_succ, h]; simp only [commandOffset, add_zero]
  have hb := headPosition_between_edges M start origin N n
  unfold visitedInterval
  rw [leftEdge_succ, rightEdge_succ, hp, min_eq_left hb.1, max_eq_left hb.2]

theorem visitedInterval_add_of_none (M : TM0.Machine Γ Q)
    (start : TM0.Cfg Γ Q) (origin : ℤ) (N n : ℕ)
    (h : cfgAt M start n = none) (k : ℕ) :
    visitedInterval M start origin N (n + k) = visitedInterval M start origin N n := by
  induction k with
  | zero => rw [Nat.add_zero]
  | succ k ih =>
    rw [Nat.add_succ, visitedInterval_succ_of_no_command M start origin N (n + k)
      (commandAt_of_none M start (n + k) (cfgAt_add_of_none M start n h k)), ih]

/-- An existing witness keeps its exact run count and optional endpoint. The
space conclusion covers every actual prefix up to that count. -/
theorem space_le_of_run (M : TM0.Machine Γ Q) (start : TM0.Cfg Γ Q)
    (endpoint : Option (TM0.Cfg Γ Q)) (B : ℕ)
    (run : StateTransition.EvalsToInTime (TM0.step M) start endpoint B)
    (origin : ℤ) (N : ℕ) :
    cfgAt M start run.steps = endpoint ∧
      ∀ i ≤ run.steps,
        (visitedCells M start origin i).card ≤ B + 1 ∧
        (inputVisitedCells M start origin N i).card ≤ max N 1 + B ∧
        (visitedInterval M start origin N i).card ≤ max N 1 + B := by
  refine ⟨run.evals_in_steps, ?_⟩
  intro i hi
  have hib : i ≤ B := le_trans hi run.steps_le_m
  exact ⟨le_trans (visitedCells_card_le M start origin i) (Nat.add_le_add_right hib 1),
    le_trans (inputVisitedCells_card_le M start origin N i) (Nat.add_le_add_left hib _),
    le_trans (visitedInterval_card_le M start origin N i) (Nat.add_le_add_left hib _)⟩

end Interval

end Resources.TuringSimulation.VisitedSpace

namespace Resources.TuringSimulation.VisitedSpace

open Function Turing

section CoordinateFrame

variable {Γ : Type*} [Inhabited Γ]

/-- A native move and its observed head displacement leave every global tape
cell at the same global coordinate. -/
theorem move_nth_at_global_coordinate (T : Tape Γ) (d : Dir) (x p : ℤ) :
    (T.move d).nth (x - (p + directionOffset d)) = T.nth (x - p) := by
  cases d with
  | left =>
    rw [directionOffset, Tape.move_left_nth]
    congr 1
    omega
  | right =>
    rw [directionOffset, Tape.move_right_nth]
    congr 1
    omega

/-- A write changes only the actual current global head position. -/
theorem write_nth_at_other_global_coordinate (T : Tape Γ) (a : Γ) (x p : ℤ)
    (h : x ≠ p) : (T.write a).nth (x - p) = T.nth (x - p) := by
  rw [Tape.write_nth, ite_eq_right (sub_ne_zero.mpr h)]

/-- Native list initialization is blank outside the declared input positions.
This does not identify an empty input with an input containing a blank symbol. -/
theorem mk₁_nth_eq_default_of_not_mem_inputCells (input : List Γ)
    (origin x : ℤ) (hx : x ∉ inputCells origin input.length) :
    (Tape.mk₁ input).nth (x - origin) = default := by
  cases hcoord : x - origin with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast] at hcoord
    have hn : input.length ≤ n := by
      by_contra h
      apply hx
      exact (mem_inputCells origin input.length x).mpr ⟨n, by omega, by omega⟩
    change (Tape.mk' (ListBlank.mk []) (ListBlank.mk input)).nth (n : ℤ) = default
    rw [Tape.mk'_nth_nat, ListBlank.nth_mk]
    exact List.getI_eq_default _ hn
  | negSucc n =>
    change (ListBlank.mk ([] : List Γ)).nth n = default
    rw [ListBlank.nth_mk]
    exact List.getI_eq_default _ (Nat.zero_le n)

end CoordinateFrame

section ActualPrefixes

variable {Γ Q : Type*} [Inhabited Γ] [Inhabited Q]

/-- An absent successor means the selected native command was absent, so the
terminal transition cannot hide a final movement. -/
theorem commandAt_eq_none_of_next_none (M : TM0.Machine Γ Q)
    (start : TM0.Cfg Γ Q) (n : ℕ) (hnext : cfgAt M start (n + 1) = none) :
    commandAt M start n = none := by
  cases hprev : cfgAt M start n with
  | none => exact commandAt_of_none M start n hprev
  | some c =>
    rw [commandAt_of_live M start c n hprev]
    rcases c with ⟨q, T⟩
    cases hcmd : M q T.head with
    | none => rfl
    | some a =>
      rw [cfgAt_succ, hprev] at hnext
      change TM0.step M ⟨q, T⟩ = none at hnext
      simp only [TM0.step, hcmd, Option.map_some, Option.some_ne_none] at hnext

/-- Both the exact visited set and its interval remain unchanged when the
actual next native prefix is outer none. -/
theorem terminal_prefix_adds_no_cells (M : TM0.Machine Γ Q)
    (start : TM0.Cfg Γ Q) (origin : ℤ) (N n : ℕ)
    (hnext : cfgAt M start (n + 1) = none) :
    visitedCells M start origin (n + 1) = visitedCells M start origin n ∧
      visitedInterval M start origin N (n + 1) = visitedInterval M start origin N n := by
  exact ⟨visitedCells_succ_of_none M start origin n hnext,
    visitedInterval_succ_of_no_command M start origin N n
      (commandAt_eq_none_of_next_none M start n hnext)⟩

/-- A supplied actual live-halt witness has a distinct next outer-none
prefix, and that terminal observation adds neither a visit nor an interval cell. -/
theorem halted_run_adds_no_cells (M : TM0.Machine Γ Q)
    (start finish : TM0.Cfg Γ Q) (B : ℕ)
    (run : StateTransition.EvalsToInTime (TM0.step M) start (some finish) B)
    (stopped : TM0.step M finish = none) (origin : ℤ) (N : ℕ) :
    cfgAt M start (run.steps + 1) = none ∧
      visitedCells M start origin (run.steps + 1) = visitedCells M start origin run.steps ∧
      visitedInterval M start origin N (run.steps + 1) =
        visitedInterval M start origin N run.steps := by
  have hnext : cfgAt M start (run.steps + 1) = none := by
    rw [cfgAt_succ]
    have hrun : cfgAt M start run.steps = some finish := run.evals_in_steps
    rw [hrun]
    exact stopped
  exact ⟨hnext, terminal_prefix_adds_no_cells M start origin N run.steps hnext⟩

/-- The actual native successor preserves every global cell other than the
pre-step head position. The command and full successor cfg are those of M. -/
theorem step_nth_at_other_global_coordinate (M : TM0.Machine Γ Q)
    (c finish : TM0.Cfg Γ Q) (x p : ℤ) (hstep : TM0.step M c = some finish)
    (hne : x ≠ p) :
    finish.Tape.nth (x - (p + commandOffset (M c.q c.Tape.head))) =
      c.Tape.nth (x - p) := by
  rcases c with ⟨q, T⟩
  cases hcmd : M q T.head with
  | none =>
    have hs : TM0.step M ⟨q, T⟩ = none := by
      change (M q T.head).map _ = none
      rw [hcmd]; rfl
    rw [hs] at hstep
    cases hstep
  | some a =>
    rcases a with ⟨q', s⟩
    cases s with
    | move d =>
      have hs : TM0.step M ⟨q, T⟩ = some ⟨q', T.move d⟩ := by
        change (M q T.head).map _ = _
        rw [hcmd]; rfl
      have heq : (⟨q', T.move d⟩ : TM0.Cfg Γ Q) = finish :=
        Option.some.inj (hs.symm.trans hstep)
      subst finish
      change (T.move d).nth (x - (p + directionOffset d)) = T.nth (x - p)
      exact move_nth_at_global_coordinate T d x p
    | write a =>
      have hs : TM0.step M ⟨q, T⟩ = some ⟨q', T.write a⟩ := by
        change (M q T.head).map _ = _
        rw [hcmd]; rfl
      have heq : (⟨q', T.write a⟩ : TM0.Cfg Γ Q) = finish :=
        Option.some.inj (hs.symm.trans hstep)
      subst finish
      change (T.write a).nth (x - (p + 0)) = T.nth (x - p)
      rw [add_zero]
      exact write_nth_at_other_global_coordinate T a x p hne

/-- Every never-visited cell retains its initial value at every actual live
primitive prefix. The initial cfg and complete native tape are preserved. -/
theorem nth_eq_initial_of_not_visited (M : TM0.Machine Γ Q)
    (start finish : TM0.Cfg Γ Q) (origin x : ℤ) (n : ℕ)
    (hcfg : cfgAt M start n = some finish)
    (hx : x ∉ visitedCells M start origin n) :
    finish.Tape.nth (x - headPosition M start origin n) = start.Tape.nth (x - origin) := by
  revert hcfg hx
  induction n generalizing finish with
  | zero =>
    intro hcfg _hx
    have heq : start = finish := Option.some.inj hcfg
    subst finish
    rfl
  | succ n ih =>
    intro hcfg hx
    cases hprev : cfgAt M start n with
    | none =>
      rw [cfgAt_succ, hprev] at hcfg
      cases hcfg
    | some c =>
      have hstep : TM0.step M c = some finish := by
        rw [cfgAt_succ, hprev] at hcfg
        exact hcfg
      have hxprev : x ∉ visitedCells M start origin n := by
        intro hmem
        exact hx (visitedCells_mono M start origin (Nat.le_succ n) hmem)
      have hxhead : x ≠ headPosition M start origin n := by
        intro heq
        apply hx
        rw [heq]
        exact live_head_mem_visitedCells M start c origin n (n + 1) (Nat.le_succ n) hprev
      rw [headPosition_succ, commandAt_of_live M start c n hprev]
      exact (step_nth_at_other_global_coordinate M c finish x
        (headPosition M start origin n) hstep hxhead).trans (ih c hprev hxprev)

/-- A general supplied start may contain other cells. This theorem therefore
requires their actual initial support to fit the supplied input coordinates. -/
theorem nth_eq_default_of_not_inputVisitedCells (M : TM0.Machine Γ Q)
    (start finish : TM0.Cfg Γ Q) (origin x : ℤ) (N n : ℕ)
    (initialSupport : ∀ y, y ∉ inputCells origin N → start.Tape.nth (y - origin) = default)
    (hcfg : cfgAt M start n = some finish)
    (hx : x ∉ inputVisitedCells M start origin N n) :
    finish.Tape.nth (x - headPosition M start origin n) = default := by
  have hinput : x ∉ inputCells origin N := fun h => hx (Finset.mem_union_left _ h)
  have hvisit : x ∉ visitedCells M start origin n := fun h => hx (Finset.mem_union_right _ h)
  exact (nth_eq_initial_of_not_visited M start finish origin x n hcfg hvisit).trans
    (initialSupport x hinput)

/-- Under actual native list initialization, every actual live prefix is blank
outside its input-plus-visited footprint. Empty input still visits the origin. -/
theorem init_nth_eq_default_of_not_inputVisitedCells (M : TM0.Machine Γ Q)
    (input : List Γ) (finish : TM0.Cfg Γ Q) (origin x : ℤ) (n : ℕ)
    (hcfg : cfgAt M (TM0.init input) n = some finish)
    (hx : x ∉ inputVisitedCells M (TM0.init input) origin input.length n) :
    finish.Tape.nth (x - headPosition M (TM0.init input) origin n) = default := by
  exact nth_eq_default_of_not_inputVisitedCells M (TM0.init input) finish origin x
    input.length n
    (fun y hy => mk₁_nth_eq_default_of_not_mem_inputCells input origin y hy) hcfg hx

/-- At every actual live prefix of an existing native initialized run, any
nonblank global tape cell belongs to the same bounded interval as the visits. -/
theorem init_nonblank_mem_interval_of_run (M : TM0.Machine Γ Q)
    (input : List Γ) (endpoint : Option (TM0.Cfg Γ Q)) (B : ℕ)
    (run : StateTransition.EvalsToInTime (TM0.step M) (TM0.init input) endpoint B)
    (origin : ℤ) :
    ∀ i ≤ run.steps, ∀ finish, cfgAt M (TM0.init input) i = some finish →
      ∀ x, finish.Tape.nth (x - headPosition M (TM0.init input) origin i) ≠ default →
        x ∈ visitedInterval M (TM0.init input) origin input.length i := by
  intro i _hi finish hcfg x hnonblank
  apply inputVisitedCells_subset_interval M (TM0.init input) origin input.length i
  by_contra hx
  exact hnonblank (init_nth_eq_default_of_not_inputVisitedCells M input finish origin x i hcfg hx)

end ActualPrefixes

end Resources.TuringSimulation.VisitedSpace
