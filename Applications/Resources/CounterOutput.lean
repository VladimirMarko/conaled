import Applications.Resources.CounterGeometry
import Applications.Linear.StructuredCosts

/-! Executed finite counter prefixes and explicit output tokens. Costs count writes
and emitted tokens separately, not host time or allocation. Source mapping and
statement review: `docs/research/counter-output.md`. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.CounterOutput
open BinaryCounter

/-- Observe n states, executing only the transitions needed to obtain them. -/
def prefixRun : Nat → Bits → Measured (List Bits) Nat
  | 0, _ => ([], 0)
  | 1, bs => ([bs], 0)
  | n + 2, bs =>
    let next := incWithCost bs
    let rest := prefixRun (n + 1) next.1
    (bs :: rest.1, next.2 + rest.2)

theorem prefixRun_eq (n : Nat) (bs : Bits) :
    prefixRun n bs = (iteratePrefix inc n bs, totalCost (n-1) bs) := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => simp [prefixRun, incWithCost_eq, ih, totalCost_succ, iteratePrefix]

/-- Ordered bills come from the existing actual transition recorder. -/
theorem prefixRun_bills (n : Nat) (bs : Bits) :
    (prefixRun n bs).2 = (CounterGeometry.bills (n-1) bs).sum := by
  rw [prefixRun_eq, CounterGeometry.bills_sum]

def digitMass (states : List Bits) : Nat := (states.map List.length).sum

theorem inc_length_le (bs : Bits) : (inc bs).length ≤ bs.length + 1 := by
  induction bs with
  | nil => simp [inc]
  | cons b bs ih => cases b <;> simp only [inc, List.length_cons] <;> omega

theorem prefix_digitMass_bound (n : Nat) (bs : Bits) :
    digitMass (iteratePrefix inc n bs) ≤ n * bs.length + ∑ i ∈ Finset.range n, i := by
  induction n generalizing bs with
  | zero => simp [iteratePrefix, digitMass]
  | succ n ih =>
    have hr := ih (inc bs)
    have hl := Nat.mul_le_mul_left n (inc_length_le bs)
    simp only [Nat.mul_add, Nat.mul_one] at hl
    simp only [iteratePrefix, List.iterate, digitMass, List.map_cons, List.sum_cons,
      Finset.sum_range_succ, Nat.add_mul, Nat.one_mul]
    dsimp [digitMass, iteratePrefix] at hr
    omega

inductive Symbol where
  | digit (b : Bool) | left | right | lineEnd
  deriving DecidableEq, Repr

/-- Independent literal line specification. -/
def lineSpec (bs : Bits) : List Symbol :=
  [.left] ++ bs.map Symbol.digit ++ [.right, .lineEnd]

/-- Every recursive digit emission contributes one token charge. -/
def renderDigits : Bits → Measured (List Symbol) Nat
  | [] => ([], 0)
  | b :: bs =>
    let r := renderDigits bs
    (.digit b :: r.1, 1 + r.2)

theorem renderDigits_eq (bs : Bits) :
    renderDigits bs = (bs.map Symbol.digit, bs.length) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [renderDigits, ih, Nat.add_comm]

def renderState (bs : Bits) : Measured (List Symbol) Nat :=
  let r := renderDigits bs
  (.left :: (r.1 ++ [.right, .lineEnd]), 1 + r.2 + 1 + 1)

theorem renderState_eq (bs : Bits) :
    renderState bs = (lineSpec bs, bs.length + 3) := by
  simp only [renderState, renderDigits_eq, lineSpec, List.singleton_append]
  congr 1
  omega

/-- Digit projection, a left inverse on rendered lines, not an input validator. -/
def decodeDigits (line : List Symbol) : Bits :=
  line.filterMap (fun t => match t with | .digit b => some b | _ => none)

theorem lineSpec_decode (bs : Bits) : decodeDigits (lineSpec bs) = bs := by
  simp [decodeDigits, lineSpec, List.filterMap_append, List.filterMap_map]

theorem lineSpec_length (bs : Bits) : (lineSpec bs).length = bs.length + 3 := by
  simp only [lineSpec, List.length_append, List.length_cons, List.length_nil, List.length_map]
  omega

/-- Local adapter into the existing native varying-callback traversal. -/
def outputCallback (bs : Bits) : Measured (List Symbol) StructuredLinear.Costs.Work :=
  let r := renderState bs
  (r.1, StructuredLinear.Costs.tick .outputWrite r.2)

def outputCharge : StructuredLinear.Costs.Work →+ Nat where
  toFun w := w .outputWrite
  map_zero' := rfl
  map_add' _ _ := rfl

def renderStates (states : List Bits) : Measured (List (List Symbol)) Nat :=
  let r := StructuredLinear.Costs.traverse outputCallback states
  (r.1, r.2 .outputWrite)

/-- The executable renderer is exactly a repricing of the retained native traversal. -/
theorem renderStates_native (states : List Bits) :
    renderStates states =
      reweight outputCharge (StructuredLinear.Costs.traverse outputCallback states) := rfl

theorem renderStates_eq (states : List Bits) :
    renderStates states = (states.map lineSpec, digitMass states + 3 * states.length) := by
  induction states with
  | nil => rfl
  | cons bs rest ih =>
    simp [renderStates, StructuredLinear.Costs.traverse, outputCallback,
      renderState_eq, StructuredLinear.Costs.tick] at ih ⊢
    simp [digitMass, Nat.mul_add, Nat.add_assoc, Nat.add_comm] at ih ⊢
    omega

theorem renderStates_decode (states : List Bits) :
    (renderStates states).1.map decodeDigits = states := by
  simp [renderStates_eq, List.map_map, Function.comp_def, lineSpec_decode]

theorem renderStates_actual_symbols (states : List Bits) :
    (renderStates states).2 = ((renderStates states).1.map List.length).sum := by
  rw [renderStates_eq]
  induction states with
  | nil => rfl
  | cons bs rest ih =>
    simp [digitMass, lineSpec_length, Nat.mul_add] at ih ⊢
    omega

/-- Repricing existing traversal observations preserves its complete value. -/
theorem traversal_reweight {X Y C : Type} [AddCommMonoid C]
    (h : StructuredLinear.Costs.Work →+ C)
    (f : X → Measured Y StructuredLinear.Costs.Work) (xs : List X) :
    reweight h (StructuredLinear.Costs.traverse f xs) =
      (xs.map (fun x => (f x).1), (xs.map (fun x => h (f x).2)).sum) := by
  simp [reweight, StructuredLinear.Costs.traverse_value,
    StructuredLinear.Costs.traverse_cost, map_list_sum, List.map_map, Function.comp_def]

structure Printed where
  lines : List (List Symbol)
  transitionWork : Nat
  symbols : Nat
  deriving Repr

def printCounter (n : Nat) (seed : Bits) : Printed :=
  let states := prefixRun n seed
  let output := renderStates states.1
  ⟨output.1, states.2, output.2⟩

theorem printCounter_states (n : Nat) (seed : Bits) :
    (printCounter n seed).lines.map decodeDigits = iteratePrefix inc n seed := by
  simp [printCounter, renderStates_decode, prefixRun_eq]

theorem printCounter_values (n : Nat) :
    ((printCounter n []).lines.map decodeDigits).map value = List.range n := by
  rw [printCounter_states]
  exact bits_values n

theorem printCounter_transitions (n : Nat) (seed : Bits) :
    (printCounter n seed).transitionWork = totalCost (n-1) seed := by
  simp [printCounter, prefixRun_eq]

theorem printCounter_symbols (n : Nat) (seed : Bits) :
    (printCounter n seed).symbols = digitMass (iteratePrefix inc n seed) + 3*n := by
  simp [printCounter, renderStates_eq, prefixRun_eq]

theorem printCounter_actual_symbols (n : Nat) (seed : Bits) :
    (printCounter n seed).symbols = ((printCounter n seed).lines.map List.length).sum :=
  renderStates_actual_symbols (prefixRun n seed).1

theorem printCounter_transition_bound (n : Nat) :
    (printCounter n []).transitionWork ≤ 2*(n-1) := by
  rw [printCounter_transitions]
  exact CounterGeometry.geometric_bound _

theorem printCounter_symbols_upper (n : Nat) :
    (printCounter n []).symbols ≤ n*n + 3*n := by
  rw [printCounter_symbols]
  have hd := prefix_digitMass_bound n []
  have hs : (∑ i ∈ Finset.range n, i) ≤ n*n := by
    calc
      _ ≤ ∑ _i ∈ Finset.range n, n := Finset.sum_le_sum (fun i hi => Nat.le_of_lt (Finset.mem_range.mp hi))
      _ = n*n := by simp
  simp only [List.length_nil, Nat.mul_zero, Nat.zero_add] at hd
  omega

theorem compute_and_output_upper (n : Nat) :
    (printCounter n []).transitionWork + (printCounter n []).symbols ≤ 6*(n*n) := by
  have hc := printCounter_transition_bound n
  have hp := printCounter_symbols_upper n
  have hn := Nat.le_mul_self n
  omega
end Resources.CounterOutput
