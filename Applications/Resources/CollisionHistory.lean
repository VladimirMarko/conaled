import Applications.Resources.CollisionWork
import Applications.Resources.PositiveArithmetic
import Applications.Resources.PositiveCounter
import Applications.Search.Collisions.Representations
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Collision work for explicit functional update histories

Head-first history lookup realizes the source functional updates. Unary equality
and signed binary comparison are actual measured recurrences. Their value
bridges identify source Boolean observations; their declared work does not claim
to be the native cost of Lean's equality instances or integer primitives.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.CollisionHistory

open Numerals.PositiveArithmetic (bitLength bitLength_pos bitLength_eq_size)

/-- Signed magnitude length, with zero assigned one bit and sign work separate. -/
def bZ (z : ZNum) : Nat := max 1 (Nat.size (Int.natAbs (z : Int)))

@[simp] theorem bZ_zero : bZ 0 = 1 := by simp [bZ]

@[simp] theorem bZ_pos (p : PosNum) : bZ (.pos p) = bitLength p := by
  unfold bZ
  rw [ZNum.cast_pos, ← p.to_nat_to_int, Int.natAbs_natCast]
  change max 1 (Nat.size (Numerals.PositiveKeys.numeric p)) = bitLength p
  rw [← bitLength_eq_size]
  exact max_eq_right (bitLength_pos p)

@[simp] theorem bZ_neg (p : PosNum) : bZ (.neg p) = bitLength p := by
  unfold bZ
  rw [ZNum.cast_neg, Int.natAbs_neg, ← p.to_nat_to_int, Int.natAbs_natCast]
  change max 1 (Nat.size (Numerals.PositiveKeys.numeric p)) = bitLength p
  rw [← bitLength_eq_size]
  exact max_eq_right (bitLength_pos p)

theorem bZ_positive (z : ZNum) : 1 ≤ bZ z := le_max_left _ _

/-- The inspected `ZNum.cmp` sign branches, with one wrapper visit. Negative
same-sign arguments reverse the actual measured positive comparison. -/
def signedCmpRun : ZNum → ZNum → Measured Ordering Nat
  | .zero, .zero => (.eq, 1)
  | .pos p, .pos q =>
      let result := PositiveArithmetic.cmpRun p q
      (result.1, 1 + result.2)
  | .neg p, .neg q =>
      let result := PositiveArithmetic.cmpRun q p
      (result.1, 1 + result.2)
  | .pos _, _ => (.gt, 1)
  | .neg _, _ => (.lt, 1)
  | _, .pos _ => (.lt, 1)
  | _, .neg _ => (.gt, 1)

theorem signedCmpRun_value (x y : ZNum) : (signedCmpRun x y).1 = ZNum.cmp x y := by
  cases x <;> cases y <;> simp [signedCmpRun, ZNum.cmp, PositiveArithmetic.cmpRun_value]

theorem signedCmpRun_cost_le_left (x y : ZNum) : (signedCmpRun x y).2 ≤ bZ x + 1 := by
  cases x <;> cases y <;>
    simp only [signedCmpRun, bZ_pos, bZ_neg, PositiveArithmetic.cmpRun_cost] <;> omega

theorem signedCmpRun_cost_le_right (x y : ZNum) : (signedCmpRun x y).2 ≤ bZ y + 1 := by
  cases x <;> cases y <;>
    simp only [signedCmpRun, bZ_pos, bZ_neg, PositiveArithmetic.cmpRun_cost] <;> omega

theorem signedCmp_eq_iff (x y : ZNum) : ZNum.cmp x y = .eq ↔ x = y := by
  constructor
  · intro h
    simpa only [h] using ZNum.cmp_to_int x y
  · rintro rfl
    cases x with
    | zero => rfl
    | pos p => exact (PosNum.cmp_eq p p).2 rfl
    | neg p => exact (PosNum.cmp_eq p p).2 rfl

/-- Equality selection adds one declared constant dispatch after comparison. -/
def signedEqRun (x y : ZNum) : Measured Bool Nat :=
  let result := signedCmpRun x y
  (decide (result.1 = .eq), result.2 + 1)

/-- Strict selection is the same inspected comparator, usable by the BST client. -/
def signedLtRun (x y : ZNum) : Measured Bool Nat :=
  let result := signedCmpRun x y
  (decide (result.1 = .lt), result.2 + 1)

/-- Extensional source equality realization, not a cost assertion about DecidableEq. -/
theorem signedEqRun_value (x y : ZNum) :
    (signedEqRun x y).1 = Search.Collisions.RatherSlow.eqb x y := by
  simp [signedEqRun, signedCmpRun_value, signedCmp_eq_iff, Search.Collisions.RatherSlow.eqb]

theorem signedEqRun_int (x y : ZNum) :
    (signedEqRun x y).1 = decide ((x : Int) = (y : Int)) :=
  (signedEqRun_value x y).trans (Search.Collisions.RatherSlow.eqb_int x y)

theorem signedLtRun_value (x y : ZNum) :
    (signedLtRun x y).1 = decide ((x : Int) < (y : Int)) := by
  simp only [signedLtRun, signedCmpRun_value, ZNum.lt_to_int]
  rfl

theorem signedEqRun_cost_le_left (x y : ZNum) : (signedEqRun x y).2 ≤ bZ x + 2 := by
  have bound := signedCmpRun_cost_le_left x y
  change (signedCmpRun x y).2 + 1 ≤ _
  omega

theorem signedEqRun_cost_le_right (x y : ZNum) : (signedEqRun x y).2 ≤ bZ y + 2 := by
  have bound := signedCmpRun_cost_le_right x y
  change (signedCmpRun x y).2 + 1 ≤ _
  omega

theorem signedLtRun_cost_le_left (x y : ZNum) : (signedLtRun x y).2 ≤ bZ x + 2 :=
  signedEqRun_cost_le_left x y

theorem signedLtRun_cost_le_right (x y : ZNum) : (signedLtRun x y).2 ≤ bZ y + 2 :=
  signedEqRun_cost_le_right x y

theorem signedEqRun_bound (x y : ZNum) (B : Nat) (key_bound : bZ x ≤ B) :
    (signedEqRun x y).2 ≤ 2 * (B + 1) := by
  have bound := signedEqRun_cost_le_left x y
  omega

theorem signedLtRun_bound_left (x y : ZNum) (B : Nat) (key_bound : bZ x ≤ B) :
    (signedLtRun x y).2 ≤ 2 * (B + 1) := by
  have bound := signedLtRun_cost_le_left x y
  omega

theorem signedLtRun_bound_right (x y : ZNum) (B : Nat) (key_bound : bZ y ≤ B) :
    (signedLtRun x y).2 ≤ 2 * (B + 1) := by
  have bound := signedLtRun_cost_le_right x y
  omega

/-- The source unary Boolean equality, including the terminal constructor visit. -/
def unaryEqRun : Nat → Nat → Measured Bool Nat
  | 0, 0 => (true, 1)
  | 0, _ + 1 => (false, 1)
  | _ + 1, 0 => (false, 1)
  | x + 1, y + 1 =>
      let result := unaryEqRun x y
      (result.1, 1 + result.2)

theorem unaryEqRun_value (x y : Nat) : (unaryEqRun x y).1 = decide (x = y) := by
  induction x generalizing y with
  | zero => cases y <;> rfl
  | succ x ih => cases y <;> simp [unaryEqRun, ih]

theorem unaryEqRun_cost (x y : Nat) : (unaryEqRun x y).2 = min x y + 1 := by
  induction x generalizing y with
  | zero => cases y <;> simp [unaryEqRun]
  | succ x ih => cases y <;> simp [unaryEqRun, ih, Nat.succ_min_succ, Nat.add_comm]

universe u v
variable {κ : Type u} {R : Type v}

/-- Separate operation observations; counter wrapper dispatch is not a bit write. -/
inductive Metric where
  | keyTests | keyWork | lookupTerminal | historyCells
  | counterWork | counterCalls | loopSteps | loopTerminal
  deriving DecidableEq

abbrev Cost := Metric → Nat

def tick (metric : Metric) (n : Nat) : Cost := fun observed => if observed = metric then n else 0

def coordinate (metric : Metric) : Cost →+ Nat where
  toFun cost := cost metric
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Unit prices for the eight explicitly separated observations. -/
def total (cost : Cost) : Nat :=
  cost .keyTests + cost .keyWork + cost .lookupTerminal + cost .historyCells +
    cost .counterWork + cost .counterCalls + cost .loopSteps + cost .loopTerminal

/-- Newest update first; no new state or table hierarchy is introduced. -/
abbrev History (κ : Type u) := List (κ × Bool)

def decode [DecidableEq κ] : History κ → κ → Bool
  | [] => fun _ => false
  | (key, value) :: rest => Function.update (decode rest) key value

def ops [DecidableEq κ] : Search.TotalTable.Ops κ Bool (History κ) where
  empty := []
  get key history := decode history key
  set key value history := (key, value) :: history

theorem laws [DecidableEq κ] : Search.TotalTable.Laws (ops (κ := κ)) false (fun _ => True) where
  empty_valid := trivial
  set_valid _ _ _ _ := trivial
  get_empty _ := rfl
  get_set_same key value history _ := by simp [ops, decode]
  get_set_other key query value history different _ := by simp [ops, decode, Ne.symm different]

def comparisonRun (eq : κ → κ → Measured Bool Nat) (written query : κ) : Measured Bool Cost :=
  reweight (fun work => tick .keyTests 1 + tick .keyWork work) (eq written query)

/-- Each nonempty history cell tests its written key before consulting the tail.
The empty observation is charged even when no equality test occurs. -/
def lookupRun (eq : κ → κ → Measured Bool Nat) (query : κ) : History κ → Measured Bool Cost
  | [] => (false, tick .lookupTerminal 1)
  | (written, value) :: rest =>
      bind (comparisonRun eq written query) fun same =>
        if same then pure value else lookupRun eq query rest

/-- Creating one update cell never searches the earlier history. -/
def writeRun (key : κ) (value : Bool) (history : History κ) : Measured (History κ) Cost :=
  ((key, value) :: history, tick .historyCells 1)

/-- Account separately for the measured increment and its one wrapper dispatch. -/
def incrementRun (increment : R → Measured R Nat) (counter : R) : Measured R Cost :=
  reweight (fun work => tick .counterWork work + tick .counterCalls 1) (increment counter)

/-- A parameter specialization of the single collision step. -/
def step (eq : κ → κ → Measured Bool Nat) (increment : R → Measured R Nat) :=
  CollisionWork.step (lookupRun eq) writeRun (incrementRun increment) (tick .loopSteps 1)

def run (eq : κ → κ → Measured Bool Nat) (increment : R → Measured R Nat)
    (xs : List κ) (state : R × History κ) : Measured (R × History κ) Cost :=
  CollisionWork.run (lookupRun eq) writeRun (incrementRun increment)
    (tick .loopSteps 1) (tick .loopTerminal 1) xs state

@[simp] theorem run_nil (eq : κ → κ → Measured Bool Nat) (increment : R → Measured R Nat)
    (state : R × History κ) : run eq increment [] state = (state, tick .loopTerminal 1) :=
  CollisionWork.run_nil _ _ _ _ _ _

theorem run_cons (eq : κ → κ → Measured Bool Nat) (increment : R → Measured R Nat)
    (key : κ) (xs : List κ) (state : R × History κ) :
    run eq increment (key :: xs) state = bind (step eq increment key state) (run eq increment xs) :=
  CollisionWork.run_cons _ _ _ _ _ _ _ _

theorem lookupRun_value [DecidableEq κ] (eq : κ → κ → Measured Bool Nat)
    (eq_value : ∀ written query, (eq written query).1 = decide (written = query))
    (query : κ) (history : History κ) : (lookupRun eq query history).1 = decode history query := by
  induction history with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨written, value⟩
      by_cases same : written = query
      · subst query
        simp [lookupRun, comparisonRun, reweight, bind, pure, eq_value, decode]
      · simp [lookupRun, comparisonRun, reweight, bind, eq_value, decode, same, Ne.symm same, ih]

theorem lookupRun_tests_le (eq : κ → κ → Measured Bool Nat) (query : κ) (history : History κ) :
    (lookupRun eq query history).2 .keyTests ≤ history.length := by
  induction history with
  | nil => simp [lookupRun, tick]
  | cons binding rest ih =>
      cases same : (eq binding.1 query).1 with
      | false =>
          simp [lookupRun, comparisonRun, reweight, bind, tick, same]
          omega
      | true => simp [lookupRun, comparisonRun, reweight, bind, pure, tick, same]

theorem lookupRun_work_le (eq : κ → κ → Measured Bool Nat) (query : κ) (history : History κ)
    (bound : Nat) (bounded : ∀ binding ∈ history, (eq binding.1 query).2 ≤ bound) :
    (lookupRun eq query history).2 .keyWork ≤ history.length * bound := by
  induction history with
  | nil => simp [lookupRun, tick]
  | cons binding rest ih =>
      have first := bounded binding List.mem_cons_self
      have tail := ih (fun entry inside => bounded entry (List.mem_cons_of_mem binding inside))
      cases same : (eq binding.1 query).1 <;>
        simp [lookupRun, comparisonRun, reweight, bind, pure, tick, same, Nat.add_mul] <;> omega

theorem lookupRun_terminal_le (eq : κ → κ → Measured Bool Nat) (query : κ) (history : History κ) :
    (lookupRun eq query history).2 .lookupTerminal ≤ 1 := by
  induction history with
  | nil => simp [lookupRun, tick]
  | cons binding rest ih =>
      cases same : (eq binding.1 query).1 <;>
        simp [lookupRun, comparisonRun, reweight, bind, pure, tick, same, ih]

@[simp] theorem lookupRun_other (eq : κ → κ → Measured Bool Nat) (query : κ) (history : History κ)
    (metric : Metric) (not_test : metric ≠ .keyTests) (not_work : metric ≠ .keyWork)
    (not_terminal : metric ≠ .lookupTerminal) : (lookupRun eq query history).2 metric = 0 := by
  induction history with
  | nil => simp [lookupRun, tick, not_terminal]
  | cons binding rest ih =>
      cases same : (eq binding.1 query).1 <;>
        simp [lookupRun, comparisonRun, reweight, bind, pure, tick, same, not_test, not_work, ih]

/-- Both representation coordinates are decoded together. The counter may be
Num while the accepted common semantic counter is Nat. -/
theorem run_value [DecidableEq κ] (eq : κ → κ → Measured Bool Nat)
    (eq_value : ∀ written query, (eq written query).1 = decide (written = query))
    (increment : R → Measured R Nat) (counterValue : R → Nat)
    (increment_value : ∀ counter, counterValue (increment counter).1 = counterValue counter + 1)
    (xs : List κ) (state : R × History κ) :
    (counterValue (run eq increment xs state).1.1, (run eq increment xs state).1.2) =
      Search.Collisions.run ops xs (counterValue state.1, state.2) := by
  apply CollisionWork.run_value_fusion (lookupRun eq) writeRun (incrementRun increment)
    (tick .loopSteps 1) (tick .loopTerminal 1) ops
    (fun state => (counterValue state.1, state.2)) (fun _ => True) (by intros; trivial)
    ?_ xs state trivial
  intro key initial _
  cases seen : decode initial.2 key <;>
    simp [CollisionWork.step, bind, lookupRun_value eq eq_value, incrementRun, reweight,
      writeRun, Search.Collisions.step, ops, seen, increment_value]

/-- Precisely the histories reached from empty by fresh true writes. -/
def Good (history : History κ) : Prop :=
  (history.map Prod.fst).Nodup ∧ ∀ binding ∈ history, binding.2 = true

@[simp] theorem good_nil : Good ([] : History κ) := by simp [Good]

theorem decode_true_iff [DecidableEq κ] (history : History κ)
    (marked : ∀ binding ∈ history, binding.2 = true) (query : κ) :
    decode history query = true ↔ query ∈ history.map Prod.fst := by
  induction history with
  | nil => simp [decode]
  | cons binding rest ih =>
      rcases binding with ⟨written, value⟩
      have value_true : value = true := marked (written, value) List.mem_cons_self
      have tail := ih (fun binding inside => marked binding (List.mem_cons_of_mem _ inside))
      by_cases same : query = written
      · subst query
        simp [decode, value_true]
      · simp [decode, same, tail]

theorem good_fresh_cons [DecidableEq κ] (history : History κ) (good : Good history)
    (key : κ) (fresh : decode history key = false) : Good ((key, true) :: history) := by
  have missing : key ∉ history.map Prod.fst := by
    intro inside
    have marked := (decode_true_iff history good.2 key).2 inside
    rw [fresh] at marked
    contradiction
  refine ⟨by simpa using List.nodup_cons.mpr ⟨missing, good.1⟩, ?_⟩
  intro binding member
  rcases List.mem_cons.mp member with first | tail
  · subst binding
    rfl
  · exact good.2 binding tail

theorem run_good [DecidableEq κ] (eq : κ → κ → Measured Bool Nat)
    (eq_value : ∀ written query, (eq written query).1 = decide (written = query))
    (increment : R → Measured R Nat) (xs : List κ) (state : R × History κ)
    (good : Good state.2) : Good (run eq increment xs state).1.2 := by
  apply CollisionWork.run_invariant (lookupRun eq) writeRun (incrementRun increment)
    (tick .loopSteps 1) (tick .loopTerminal 1) (fun state => Good state.2) ?_ xs state good
  intro key initial valid
  cases seen : decode initial.2 key
  · simpa [CollisionWork.step, bind, lookupRun_value eq eq_value, seen, writeRun] using
      good_fresh_cons initial.2 valid key seen
  · simpa [CollisionWork.step, bind, lookupRun_value eq eq_value, seen, incrementRun, reweight] using valid

def Supported (keys : Finset κ) (history : History κ) : Prop :=
  Good history ∧ ∀ binding ∈ history, binding.1 ∈ keys

@[simp] theorem supported_nil (keys : Finset κ) : Supported keys [] := by simp [Supported, Good]

theorem supported_length_le [DecidableEq κ] (keys : Finset κ) (history : History κ)
    (supported : Supported keys history) : history.length ≤ keys.card := by
  calc
    history.length = (history.map Prod.fst).length := by simp
    _ = (history.map Prod.fst).toFinset.card := (List.toFinset_card_of_nodup supported.1.1).symm
    _ ≤ keys.card := Finset.card_le_card (by
      intro key inside
      obtain ⟨binding, member, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp inside)
      exact supported.2 binding member)

theorem step_supported [DecidableEq κ] (eq : κ → κ → Measured Bool Nat)
    (eq_value : ∀ written query, (eq written query).1 = decide (written = query))
    (increment : R → Measured R Nat) (keys : Finset κ) (key : κ) (state : R × History κ)
    (admitted : key ∈ keys) (supported : Supported keys state.2) :
    Supported keys (step eq increment key state).1.2 := by
  cases seen : decode state.2 key
  · have fresh_good := good_fresh_cons state.2 supported.1 key seen
    have members : ∀ binding ∈ (key, true) :: state.2, binding.1 ∈ keys := by
      intro binding member
      rcases List.mem_cons.mp member with first | tail
      · subst binding
        exact admitted
      · exact supported.2 binding tail
    simpa [Supported, step, CollisionWork.step, bind, lookupRun_value eq eq_value, seen, writeRun] using
      And.intro fresh_good members
  · simpa [step, CollisionWork.step, bind, lookupRun_value eq eq_value, seen, incrementRun, reweight] using supported

theorem run_supported [DecidableEq κ] (eq : κ → κ → Measured Bool Nat)
    (eq_value : ∀ written query, (eq written query).1 = decide (written = query))
    (increment : R → Measured R Nat) (keys : Finset κ) (xs : List κ)
    (inputs : ∀ key ∈ xs, key ∈ keys) (state : R × History κ)
    (supported : Supported keys state.2) : Supported keys (run eq increment xs state).1.2 := by
  exact CollisionWork.run_invariant_on (lookupRun eq) writeRun (incrementRun increment)
    (tick .loopSteps 1) (tick .loopTerminal 1) (fun key => key ∈ keys)
    (fun state => Supported keys state.2) (step_supported eq eq_value increment keys)
    xs inputs state supported

/-- Every processed prefix has one history cell per distinct key, not one per query. -/
theorem run_history_length [DecidableEq κ] (eq : κ → κ → Measured Bool Nat)
    (eq_value : ∀ written query, (eq written query).1 = decide (written = query))
    (increment : R → Measured R Nat) (counterValue : R → Nat)
    (increment_value : ∀ counter, counterValue (increment counter).1 = counterValue counter + 1)
    (xs : List κ) (counter : R) :
    (run eq increment xs (counter, [])).1.2.length = xs.toFinset.card := by
  have good := run_good eq eq_value increment xs (counter, []) good_nil
  have erased := congrArg Prod.snd (run_value eq eq_value increment counterValue increment_value xs (counter, []))
  have keys_eq : ((run eq increment xs (counter, [])).1.2.map Prod.fst).toFinset = xs.toFinset := by
    ext key
    simp only [List.mem_toFinset]
    have seen := Search.Collisions.prefix_seen (laws (κ := κ)) xs (counterValue counter) key
    change decode (Search.Collisions.run ops xs (counterValue counter, [])).2 key = true ↔ key ∈ xs at seen
    rw [← erased] at seen
    exact (decode_true_iff _ good.2 key).symm.trans seen
  rw [← keys_eq, List.toFinset_card_of_nodup good.1, List.length_map]

theorem step_cost (eq : κ → κ → Measured Bool Nat) (increment : R → Measured R Nat)
    (key : κ) (state : R × History κ) (metric : Metric) :
    (step eq increment key state).2 metric =
      tick .loopSteps 1 metric + ((lookupRun eq key state.2).2 metric +
        if (lookupRun eq key state.2).1 then
          tick .counterWork (increment state.1).2 metric + tick .counterCalls 1 metric
        else tick .historyCells 1 metric) := by
  cases seen : (lookupRun eq key state.2).1 <;>
    simp [step, CollisionWork.step, bind, incrementRun, writeRun, reweight, seen]

/-- Table costs are independent of the selected counter implementation. -/
theorem run_keyTests_le [DecidableEq κ] (eq : κ → κ → Measured Bool Nat)
    (eq_value : ∀ written query, (eq written query).1 = decide (written = query))
    (increment : R → Measured R Nat) (keys : Finset κ) (xs : List κ)
    (inputs : ∀ key ∈ xs, key ∈ keys) (state : R × History κ)
    (supported : Supported keys state.2) :
    (run eq increment xs state).2 .keyTests ≤ xs.length * keys.card := by
  have result := CollisionWork.run_cost_le_sum_on (lookupRun eq) writeRun (incrementRun increment)
    (tick .loopSteps 1) (tick .loopTerminal 1) (coordinate .keyTests) (fun _ => keys.card)
    (fun key => key ∈ keys) (fun state => Supported keys state.2)
    (step_supported eq eq_value increment keys) (fun key initial _ valid => by
      change (step eq increment key initial).2 .keyTests ≤ _
      simp only [step_cost]
      simp only [tick, reduceCtorEq, ↓reduceIte, Nat.zero_add, Nat.add_zero, ite_self]
      exact (lookupRun_tests_le eq key initial.2).trans (supported_length_le keys initial.2 valid))
    xs inputs state supported
  simpa [run, coordinate, tick, Nat.mul_comm] using result

theorem run_keyWork_le [DecidableEq κ] (eq : κ → κ → Measured Bool Nat)
    (eq_value : ∀ written query, (eq written query).1 = decide (written = query))
    (increment : R → Measured R Nat) (keys : Finset κ) (bound : Nat)
    (bounded : ∀ written query, query ∈ keys → (eq written query).2 ≤ bound)
    (xs : List κ) (inputs : ∀ key ∈ xs, key ∈ keys) (state : R × History κ)
    (supported : Supported keys state.2) :
    (run eq increment xs state).2 .keyWork ≤ xs.length * keys.card * bound := by
  have result := CollisionWork.run_cost_le_sum_on (lookupRun eq) writeRun (incrementRun increment)
    (tick .loopSteps 1) (tick .loopTerminal 1) (coordinate .keyWork) (fun _ => keys.card * bound)
    (fun key => key ∈ keys) (fun state => Supported keys state.2)
    (step_supported eq eq_value increment keys) (fun key initial admitted valid => by
      change (step eq increment key initial).2 .keyWork ≤ _
      simp only [step_cost]
      simp only [tick, reduceCtorEq, ↓reduceIte, Nat.zero_add, Nat.add_zero, ite_self]
      exact (lookupRun_work_le eq key initial.2 bound (fun binding _ => bounded binding.1 key admitted)).trans
        (Nat.mul_le_mul_right bound (supported_length_le keys initial.2 valid)))
    xs inputs state supported
  simpa [run, coordinate, tick, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using result

theorem run_lookupTerminal_le (eq : κ → κ → Measured Bool Nat) (increment : R → Measured R Nat)
    (xs : List κ) (state : R × History κ) :
    (run eq increment xs state).2 .lookupTerminal ≤ xs.length := by
  have result := CollisionWork.run_cost_le_sum (lookupRun eq) writeRun (incrementRun increment)
    (tick .loopSteps 1) (tick .loopTerminal 1) (coordinate .lookupTerminal) (fun _ => 1)
    (fun _ => True) (by intros; trivial) (fun key initial _ => by
      change (step eq increment key initial).2 .lookupTerminal ≤ _
      simpa [step_cost, tick] using lookupRun_terminal_le eq key initial.2) xs state trivial
  simpa [run, coordinate, tick] using result

theorem run_historyCells_le (eq : κ → κ → Measured Bool Nat) (increment : R → Measured R Nat)
    (xs : List κ) (state : R × History κ) :
    (run eq increment xs state).2 .historyCells ≤ xs.length := by
  have result := CollisionWork.run_cost_le_sum (lookupRun eq) writeRun (incrementRun increment)
    (tick .loopSteps 1) (tick .loopTerminal 1) (coordinate .historyCells) (fun _ => 1)
    (fun _ => True) (by intros; trivial) (fun key initial _ => by
      change (step eq increment key initial).2 .historyCells ≤ _
      simp only [step_cost]
      cases (lookupRun eq key initial.2).1 <;> simp [tick]) xs state trivial
  simpa [run, coordinate, tick] using result

theorem run_counterCalls_le (eq : κ → κ → Measured Bool Nat) (increment : R → Measured R Nat)
    (xs : List κ) (state : R × History κ) :
    (run eq increment xs state).2 .counterCalls ≤ xs.length := by
  have result := CollisionWork.run_cost_le_sum (lookupRun eq) writeRun (incrementRun increment)
    (tick .loopSteps 1) (tick .loopTerminal 1) (coordinate .counterCalls) (fun _ => 1)
    (fun _ => True) (by intros; trivial) (fun key initial _ => by
      change (step eq increment key initial).2 .counterCalls ≤ _
      simp only [step_cost]
      cases (lookupRun eq key initial.2).1 <;> simp [tick]) xs state trivial
  simpa [run, coordinate, tick] using result

theorem run_loopSteps (eq : κ → κ → Measured Bool Nat) (increment : R → Measured R Nat)
    (xs : List κ) (state : R × History κ) : (run eq increment xs state).2 .loopSteps = xs.length := by
  have result := CollisionWork.run_constant_observation (lookupRun eq) writeRun (incrementRun increment)
    (tick .loopSteps 1) (tick .loopTerminal 1) (coordinate .loopSteps) 1 (fun key initial => by
      change (step eq increment key initial).2 .loopSteps = _
      simp [step_cost, tick]) xs state
  simpa [run, coordinate, tick] using result

theorem run_loopTerminal (eq : κ → κ → Measured Bool Nat) (increment : R → Measured R Nat)
    (xs : List κ) (state : R × History κ) : (run eq increment xs state).2 .loopTerminal = 1 := by
  have result := CollisionWork.run_constant_observation (lookupRun eq) writeRun (incrementRun increment)
    (tick .loopSteps 1) (tick .loopTerminal 1) (coordinate .loopTerminal) 0 (fun key initial => by
      change (step eq increment key initial).2 .loopTerminal = _
      simp [step_cost, tick]) xs state
  simpa [run, coordinate, tick] using result

theorem step_historyCells (eq : κ → κ → Measured Bool Nat) (increment : R → Measured R Nat)
    (key : κ) (state : R × History κ) :
    (step eq increment key state).2 .historyCells + state.2.length =
      (step eq increment key state).1.2.length := by
  cases seen : (lookupRun eq key state.2).1 <;>
    simp [step, CollisionWork.step, bind, incrementRun, writeRun, reweight, tick, seen, Nat.add_comm]

theorem run_historyCells_add_length (eq : κ → κ → Measured Bool Nat) (increment : R → Measured R Nat)
    (xs : List κ) (state : R × History κ) :
    (run eq increment xs state).2 .historyCells + state.2.length = (run eq increment xs state).1.2.length := by
  induction xs generalizing state with
  | nil => simp [tick]
  | cons key xs ih =>
      have first := step_historyCells eq increment key state
      have tail := ih (step eq increment key state).1
      rw [run_cons]
      simp only [bind, Pi.add_apply]
      omega

theorem run_historyCells_exact [DecidableEq κ] (eq : κ → κ → Measured Bool Nat)
    (eq_value : ∀ written query, (eq written query).1 = decide (written = query))
    (increment : R → Measured R Nat) (counterValue : R → Nat)
    (increment_value : ∀ counter, counterValue (increment counter).1 = counterValue counter + 1)
    (xs : List κ) (counter : R) :
    (run eq increment xs (counter, [])).2 .historyCells = xs.toFinset.card := by
  have cells := run_historyCells_add_length eq increment xs (counter, [])
  simpa [run_history_length eq eq_value increment counterValue increment_value xs counter] using cells

theorem step_counterCalls (eq : κ → κ → Measured Bool Nat) (increment : R → Measured R Nat)
    (counterValue : R → Nat)
    (increment_value : ∀ counter, counterValue (increment counter).1 = counterValue counter + 1)
    (key : κ) (state : R × History κ) :
    (step eq increment key state).2 .counterCalls + counterValue state.1 =
      counterValue (step eq increment key state).1.1 := by
  cases seen : (lookupRun eq key state.2).1 <;>
    simp [step, CollisionWork.step, bind, incrementRun, writeRun, reweight, tick, seen,
      increment_value, Nat.add_comm]

theorem run_counterCalls_add_value (eq : κ → κ → Measured Bool Nat) (increment : R → Measured R Nat)
    (counterValue : R → Nat)
    (increment_value : ∀ counter, counterValue (increment counter).1 = counterValue counter + 1)
    (xs : List κ) (state : R × History κ) :
    (run eq increment xs state).2 .counterCalls + counterValue state.1 =
      counterValue (run eq increment xs state).1.1 := by
  induction xs generalizing state with
  | nil => simp [tick]
  | cons key xs ih =>
      have first := step_counterCalls eq increment counterValue increment_value key state
      have tail := ih (step eq increment key state).1
      rw [run_cons]
      simp only [bind, Pi.add_apply]
      omega

theorem run_counter_bounds (eq : κ → κ → Measured Bool Nat) (increment : R → Measured R Nat)
    (counterValue : R → Nat)
    (increment_value : ∀ counter, counterValue (increment counter).1 = counterValue counter + 1)
    (xs : List κ) (state : R × History κ) :
    counterValue state.1 ≤ counterValue (run eq increment xs state).1.1 ∧
      counterValue (run eq increment xs state).1.1 ≤ counterValue state.1 + xs.length := by
  have calls := run_counterCalls_add_value eq increment counterValue increment_value xs state
  have bound := run_counterCalls_le eq increment xs state
  omega

theorem run_binary_counter_potential (eq : κ → κ → Measured Bool Nat)
    (xs : List κ) (state : Num × History κ) :
    (run eq PositiveCounter.numAddOneRun xs state).2 .counterWork +
        BinaryCounter.ones (PositiveCounter.numDigits (run eq PositiveCounter.numAddOneRun xs state).1.1) =
      BinaryCounter.ones (PositiveCounter.numDigits state.1) +
        Resources.budget (step eq PositiveCounter.numAddOneRun)
          (fun key state => if (lookupRun eq key state.2).1 then 2 else 0) xs state := by
  exact CollisionWork.run_counter_potential (lookupRun eq) writeRun
    (incrementRun PositiveCounter.numAddOneRun) (tick .loopSteps 1) (tick .loopTerminal 1)
    (coordinate .counterWork) (fun counter => BinaryCounter.ones (PositiveCounter.numDigits counter)) 2
    (by intro key history; simp [coordinate])
    (by intros; simp [coordinate, writeRun, tick]) (by simp [coordinate, tick])
    (by simp [coordinate, tick])
    (by intro counter; simpa [coordinate, incrementRun, reweight, tick] using
      PositiveCounter.numAddOneRun_potential counter) xs state

theorem run_binary_counter_work_le (eq : κ → κ → Measured Bool Nat)
    (xs : List κ) (state : Num × History κ) :
    (run eq PositiveCounter.numAddOneRun xs state).2 .counterWork ≤
      BinaryCounter.ones (PositiveCounter.numDigits state.1) + 2 * xs.length := by
  exact CollisionWork.run_counter_cost_le (lookupRun eq) writeRun
    (incrementRun PositiveCounter.numAddOneRun) (tick .loopSteps 1) (tick .loopTerminal 1)
    (coordinate .counterWork) (fun counter => BinaryCounter.ones (PositiveCounter.numDigits counter)) 2
    (by intro key history; simp [coordinate])
    (by intros; simp [coordinate, writeRun, tick]) (by simp [coordinate, tick])
    (by simp [coordinate, tick])
    (by intro counter; simpa [coordinate, incrementRun, reweight, tick] using
      PositiveCounter.numAddOneRun_potential counter) xs state

/-- Exact first-operand unary addition accounting on each duplicate branch. -/
theorem step_unary_counter (eq : κ → κ → Measured Bool Nat) (key : κ) (state : Nat × History κ) :
    2 * (step eq (fun c => CollisionWork.unaryAddRun c 1) key state).2 .counterWork +
        state.1 * (state.1 + 1) =
      (step eq (fun c => CollisionWork.unaryAddRun c 1) key state).1.1 *
        ((step eq (fun c => CollisionWork.unaryAddRun c 1) key state).1.1 + 1) := by
  cases seen : (lookupRun eq key state.2).1 <;>
    simp [step, CollisionWork.step, bind, incrementRun, writeRun, reweight, tick, seen,
      CollisionWork.unaryAddRun_value, CollisionWork.unaryAddRun_cost]
  ring

theorem run_unary_counter (eq : κ → κ → Measured Bool Nat) (xs : List κ) (state : Nat × History κ) :
    2 * (run eq (fun c => CollisionWork.unaryAddRun c 1) xs state).2 .counterWork +
        state.1 * (state.1 + 1) =
      (run eq (fun c => CollisionWork.unaryAddRun c 1) xs state).1.1 *
        ((run eq (fun c => CollisionWork.unaryAddRun c 1) xs state).1.1 + 1) := by
  induction xs generalizing state with
  | nil => simp [tick]
  | cons key xs ih =>
      have first := step_unary_counter eq key state
      have tail := ih (step eq (fun c => CollisionWork.unaryAddRun c 1) key state).1
      rw [run_cons]
      simp only [bind, Pi.add_apply]
      nlinarith

theorem run_unary_counter_work_le (eq : κ → κ → Measured Bool Nat) (xs : List κ) (history : History κ) :
    (run eq (fun c => CollisionWork.unaryAddRun c 1) xs (0, history)).2 .counterWork ≤
      xs.length * (xs.length + 1) := by
  have conservation := run_unary_counter eq xs (0, history)
  have bounded := (run_counter_bounds eq (fun c => CollisionWork.unaryAddRun c 1) id
    (fun c => CollisionWork.unaryAddRun_value c 1) xs (0, history)).2
  simp only [id_eq, Nat.zero_add, Nat.zero_mul] at conservation bounded
  have product := Nat.mul_le_mul bounded (Nat.add_le_add_right bounded 1)
  nlinarith

/-- Decoder transport reaches the accepted total-function client, not just a
second history implementation. -/
theorem run_function_value [DecidableEq κ] (eq : κ → κ → Measured Bool Nat)
    (eq_value : ∀ written query, (eq written query).1 = decide (written = query))
    (increment : R → Measured R Nat) (counterValue : R → Nat)
    (increment_value : ∀ counter, counterValue (increment counter).1 = counterValue counter + 1)
    (xs : List κ) (state : R × History κ) :
    counterValue (run eq increment xs state).1.1 =
      Search.Collisions.loop (Search.TotalTable.functions false) xs (counterValue state.1) (decode state.2) := by
  have erased := congrArg Prod.fst (run_value eq eq_value increment counterValue increment_value xs state)
  exact erased.trans (Search.Collisions.loop_agrees laws (Search.TotalTable.functions_laws false)
    xs (counterValue state.1) trivial trivial rfl)

theorem run_count_from_empty [DecidableEq κ] (eq : κ → κ → Measured Bool Nat)
    (eq_value : ∀ written query, (eq written query).1 = decide (written = query))
    (increment : R → Measured R Nat) (counterValue : R → Nat)
    (increment_value : ∀ counter, counterValue (increment counter).1 = counterValue counter + 1)
    (xs : List κ) (counter : R) :
    counterValue (run eq increment xs (counter, [])).1.1 = counterValue counter + Search.Collisions.count xs := by
  have erased := congrArg Prod.fst (run_value eq eq_value increment counterValue increment_value xs (counter, []))
  exact erased.trans (Search.Collisions.run_from_empty laws xs (counterValue counter)).2.2

theorem run_counterCalls_exact [DecidableEq κ] (eq : κ → κ → Measured Bool Nat)
    (eq_value : ∀ written query, (eq written query).1 = decide (written = query))
    (increment : R → Measured R Nat) (counterValue : R → Nat)
    (increment_value : ∀ counter, counterValue (increment counter).1 = counterValue counter + 1)
    (xs : List κ) (counter : R) :
    (run eq increment xs (counter, [])).2 .counterCalls = Search.Collisions.count xs := by
  have calls := run_counterCalls_add_value eq increment counterValue increment_value xs (counter, [])
  have meaning := run_count_from_empty eq eq_value increment counterValue increment_value xs counter
  dsimp only at calls
  omega

theorem run_duplicate_budget (eq : κ → κ → Measured Bool Nat) (increment : R → Measured R Nat)
    (charge : Nat) (xs : List κ) (state : R × History κ) :
    Resources.budget (step eq increment)
        (fun key state => if (lookupRun eq key state.2).1 then charge else 0) xs state =
      charge * (run eq increment xs state).2 .counterCalls := by
  induction xs generalizing state with
  | nil => simp [Resources.budget, tick]
  | cons key xs ih =>
      rw [Resources.budget, run_cons]
      simp only [bind, Pi.add_apply, ih, Nat.mul_add, step_cost]
      cases (lookupRun eq key state.2).1 <;> simp [tick]

theorem run_binary_counter_exact (eq : κ → κ → Measured Bool Nat)
    (xs : List κ) (state : Num × History κ) :
    (run eq PositiveCounter.numAddOneRun xs state).2 .counterWork +
        BinaryCounter.ones (PositiveCounter.numDigits (run eq PositiveCounter.numAddOneRun xs state).1.1) =
      BinaryCounter.ones (PositiveCounter.numDigits state.1) +
        2 * (run eq PositiveCounter.numAddOneRun xs state).2 .counterCalls := by
  rw [run_binary_counter_potential, run_duplicate_budget]

/-- Source Nat loop erasure for an arbitrary initial counter and explicit history. -/
theorem unary_loop_source (xs : List Nat) (counter : Nat) (history : History Nat) :
    (run unaryEqRun (fun c => CollisionWork.unaryAddRun c 1) xs (counter, history)).1.1 =
      Search.Collisions.VerySlow.loop xs counter (decode history) := by
  exact (run_function_value unaryEqRun unaryEqRun_value (fun c => CollisionWork.unaryAddRun c 1)
    id (fun c => CollisionWork.unaryAddRun_value c 1) xs (counter, history)).trans
      (Search.Collisions.VerySlow.loop_common xs counter (decode history)).symm

/-- Existing Num represents exactly the reachable nonnegative signed counters.
No negative-branch resource claim is inferred from this source equation. -/
theorem signed_loop_source (xs : List ZNum) (counter : Num) (history : History ZNum) :
    (run signedEqRun PositiveCounter.numAddOneRun xs (counter, history)).1.1.toZNum =
      Search.Collisions.RatherSlow.loop xs counter.toZNum (decode history) := by
  apply ZNum.to_int_inj.mp
  rw [Search.Collisions.RatherSlow.loop_common]
  simp only [Num.cast_toZNum, ← Num.to_nat_to_int]
  rw [run_function_value signedEqRun (by intro x y; exact signedEqRun_value x y)
    PositiveCounter.numAddOneRun (fun c : Num => (c : Nat)) PositiveCounter.numAddOneRun_toNat]
  have offset := Search.Collisions.loop_add (Search.TotalTable.functions false) xs
    (counter : Nat) 0 (decode history)
  simp only [Nat.add_zero] at offset
  rw [offset, Nat.cast_add]

def unaryRun (xs : List Nat) : Measured (Nat × History Nat) Cost :=
  run unaryEqRun (fun c => CollisionWork.unaryAddRun c 1) xs (0, [])

def signedRun (xs : List ZNum) : Measured (Num × History ZNum) Cost :=
  run signedEqRun PositiveCounter.numAddOneRun xs (.zero, [])

theorem unaryRun_source (xs : List Nat) :
    (unaryRun xs).1.1 = Search.Collisions.VerySlow.collisions xs := unary_loop_source xs 0 []

theorem signedRun_source (xs : List ZNum) :
    (signedRun xs).1.1.toZNum = Search.Collisions.RatherSlow.collisions xs := signed_loop_source xs .zero []

theorem unaryRun_count (xs : List Nat) : (unaryRun xs).1.1 = Search.Collisions.count xs := by
  rw [unaryRun_source, Search.Collisions.VerySlow.collisions_correct]

theorem signedRun_count (xs : List ZNum) : ((signedRun xs).1.1 : Nat) = Search.Collisions.count xs := by
  simpa [signedRun] using run_count_from_empty signedEqRun (fun x y => signedEqRun_value x y)
    PositiveCounter.numAddOneRun (fun c : Num => (c : Nat)) PositiveCounter.numAddOneRun_toNat xs .zero

theorem unaryRun_cells (xs : List Nat) : (unaryRun xs).2 .historyCells = xs.toFinset.card :=
  run_historyCells_exact unaryEqRun unaryEqRun_value (fun c => CollisionWork.unaryAddRun c 1)
    id (fun c => CollisionWork.unaryAddRun_value c 1) xs 0

theorem signedRun_cells (xs : List ZNum) : (signedRun xs).2 .historyCells = xs.toFinset.card :=
  run_historyCells_exact signedEqRun (fun x y => signedEqRun_value x y)
    PositiveCounter.numAddOneRun (fun c : Num => (c : Nat)) PositiveCounter.numAddOneRun_toNat xs .zero

theorem unaryRun_counter_exact (xs : List Nat) :
    2 * (unaryRun xs).2 .counterWork = Search.Collisions.count xs * (Search.Collisions.count xs + 1) := by
  have conservation := run_unary_counter unaryEqRun xs (0, [])
  change 2 * (unaryRun xs).2 .counterWork + 0 * (0 + 1) =
    (unaryRun xs).1.1 * ((unaryRun xs).1.1 + 1) at conservation
  simpa [unaryRun_count] using conservation

theorem signedRun_counter_exact (xs : List ZNum) :
    (signedRun xs).2 .counterWork + BinaryCounter.ones (PositiveCounter.numDigits (signedRun xs).1.1) =
      2 * Search.Collisions.count xs := by
  have accounting := run_binary_counter_exact signedEqRun xs (.zero, [])
  have calls := run_counterCalls_exact signedEqRun (fun x y => signedEqRun_value x y)
    PositiveCounter.numAddOneRun (fun c : Num => (c : Nat)) PositiveCounter.numAddOneRun_toNat xs .zero
  simpa [signedRun, calls, PositiveCounter.numDigits_zero, BinaryCounter.ones] using accounting

/-- All equality, history, counter, wrapper, loop and terminal work is included. -/
theorem unaryRun_total_le (xs : List Nat) (M : Nat) (bounded : ∀ key ∈ xs, key ≤ M) :
    total (unaryRun xs).2 ≤
      xs.length * xs.toFinset.card * (M + 1) + xs.length * xs.toFinset.card +
        xs.length * (xs.length + 1) + 4 * xs.length + 1 := by
  have tests := run_keyTests_le unaryEqRun unaryEqRun_value (fun c => CollisionWork.unaryAddRun c 1)
    xs.toFinset xs (by simp) (0, []) (supported_nil _)
  have work := run_keyWork_le unaryEqRun unaryEqRun_value (fun c => CollisionWork.unaryAddRun c 1)
    xs.toFinset (M + 1) (by
      intro written query admitted
      rw [unaryEqRun_cost]
      have key_bound := bounded query (List.mem_toFinset.mp admitted)
      have smaller := min_le_right written query
      omega) xs (by simp) (0, []) (supported_nil _)
  have terminal := run_lookupTerminal_le unaryEqRun (fun c => CollisionWork.unaryAddRun c 1) xs (0, [])
  have cells := run_historyCells_le unaryEqRun (fun c => CollisionWork.unaryAddRun c 1) xs (0, [])
  have counter := run_unary_counter_work_le unaryEqRun xs []
  have calls := run_counterCalls_le unaryEqRun (fun c => CollisionWork.unaryAddRun c 1) xs (0, [])
  have loops := run_loopSteps unaryEqRun (fun c => CollisionWork.unaryAddRun c 1) xs (0, [])
  have final := run_loopTerminal unaryEqRun (fun c => CollisionWork.unaryAddRun c 1) xs (0, [])
  unfold total unaryRun
  omega

/-- Binary work has its own independent key-bit bound; counter writes and
wrapper dispatch remain in the complete total. -/
theorem signedRun_total_le (xs : List ZNum) (B : Nat) (bounded : ∀ key ∈ xs, bZ key ≤ B) :
    total (signedRun xs).2 ≤
      2 * xs.length * xs.toFinset.card * (B + 1) + xs.length * xs.toFinset.card +
        6 * xs.length + 1 := by
  have tests := run_keyTests_le signedEqRun (fun x y => signedEqRun_value x y)
    PositiveCounter.numAddOneRun xs.toFinset xs (by simp) (.zero, []) (supported_nil _)
  have work := run_keyWork_le signedEqRun (fun x y => signedEqRun_value x y)
    PositiveCounter.numAddOneRun xs.toFinset (2 * (B + 1)) (by
      intro written query admitted
      have key_bound := bounded query (List.mem_toFinset.mp admitted)
      have comparison := signedEqRun_cost_le_right written query
      omega) xs (by simp) (.zero, []) (supported_nil _)
  have terminal := run_lookupTerminal_le signedEqRun PositiveCounter.numAddOneRun xs (.zero, [])
  have cells := run_historyCells_le signedEqRun PositiveCounter.numAddOneRun xs (.zero, [])
  have counter := run_binary_counter_work_le signedEqRun xs (.zero, [])
  simp only [PositiveCounter.numDigits_zero, BinaryCounter.ones, Nat.zero_add] at counter
  have calls := run_counterCalls_le signedEqRun PositiveCounter.numAddOneRun xs (.zero, [])
  have loops := run_loopSteps signedEqRun PositiveCounter.numAddOneRun xs (.zero, [])
  have final := run_loopTerminal signedEqRun PositiveCounter.numAddOneRun xs (.zero, [])
  unfold total signedRun
  nlinarith

/-- An absent key traverses every update cell, in the actual head-first lookup. -/
theorem lookupRun_missing (eq : κ → κ → Measured Bool Nat) (query : κ) (history : History κ)
    (missing : ∀ binding ∈ history, (eq binding.1 query).1 = false) :
    (lookupRun eq query history).1 = false := by
  induction history with
  | nil => rfl
  | cons binding rest ih =>
      have first := missing binding List.mem_cons_self
      have tail := ih (fun entry inside => missing entry (List.mem_cons_of_mem binding inside))
      simpa [lookupRun, comparisonRun, reweight, bind, first] using tail

theorem lookupRun_missing_work_lower (eq : κ → κ → Measured Bool Nat) (query : κ)
    (history : History κ) (L : Nat)
    (missing : ∀ binding ∈ history, (eq binding.1 query).1 = false)
    (bounded : ∀ binding ∈ history, L ≤ (eq binding.1 query).2) :
    L * history.length ≤ (lookupRun eq query history).2 .keyWork := by
  induction history with
  | nil => simp [lookupRun, tick]
  | cons binding rest ih =>
      have first := missing binding List.mem_cons_self
      have cost := bounded binding List.mem_cons_self
      have tail := ih (fun entry inside => missing entry (List.mem_cons_of_mem binding inside))
        (fun entry inside => bounded entry (List.mem_cons_of_mem binding inside))
      simp [lookupRun, comparisonRun, reweight, bind, first, tick, Nat.mul_add]
      omega

/-- A distinct tail scans all older cells. This induction uses the common
measured client, allows any initial counter, and requires only the displayed
freshness and size conditions on the history. -/
theorem unary_distinct_lower (xs : List Nat) (counter : Nat) (history : History Nat) (L : Nat)
    (distinct : xs.Nodup) (fresh : ∀ key ∈ xs, key ∉ history.map Prod.fst)
    (large : ∀ key ∈ xs, L ≤ key + 1)
    (older : ∀ binding ∈ history, L ≤ binding.1 + 1) :
    L * (xs.length * history.length + (List.range xs.length).sum) ≤
      (run unaryEqRun (fun c => CollisionWork.unaryAddRun c 1) xs (counter, history)).2 .keyWork := by
  induction xs generalizing counter history with
  | nil => simp [tick]
  | cons key xs ih =>
      have head_fresh := fresh key List.mem_cons_self
      have head_large := large key List.mem_cons_self
      have missing : ∀ binding ∈ history, (unaryEqRun binding.1 key).1 = false := by
        intro binding member
        have different : binding.1 ≠ key := by
          intro same
          exact head_fresh (List.mem_map.mpr ⟨binding, member, same⟩)
        simp [unaryEqRun_value, different]
      have missed := lookupRun_missing unaryEqRun key history missing
      have first := lookupRun_missing_work_lower unaryEqRun key history L missing (by
        intro binding member
        rw [unaryEqRun_cost]
        have old_large := older binding member
        omega)
      have tail_fresh : ∀ query ∈ xs, query ∉ (((key, true) :: history).map Prod.fst) := by
        intro query member
        change query ∉ key :: history.map Prod.fst
        simp only [List.mem_cons, not_or]
        refine ⟨?_, fresh query (List.mem_cons_of_mem key member)⟩
        intro same
        subst query
        exact (List.nodup_cons.mp distinct).1 member
      have tail_large : ∀ query ∈ xs, L ≤ query + 1 :=
        fun query member => large query (List.mem_cons_of_mem key member)
      have next_older : ∀ binding ∈ (key, true) :: history, L ≤ binding.1 + 1 := by
        intro binding member
        rcases List.mem_cons.mp member with equal | inside
        · subst binding
          exact head_large
        · exact older binding inside
      have tail := ih counter ((key, true) :: history) (List.nodup_cons.mp distinct).2
        tail_fresh tail_large next_older
      have next : (step unaryEqRun (fun c => CollisionWork.unaryAddRun c 1) key
          (counter, history)).1 = (counter, (key, true) :: history) := by
        simp [step, CollisionWork.step, bind, missed, writeRun]
      rw [run_cons]
      change L * ((key :: xs).length * history.length + (List.range (key :: xs).length).sum) ≤
        (step unaryEqRun (fun c => CollisionWork.unaryAddRun c 1) key (counter, history)).2 .keyWork +
          (run unaryEqRun (fun c => CollisionWork.unaryAddRun c 1) xs
            (step unaryEqRun (fun c => CollisionWork.unaryAddRun c 1) key (counter, history)).1).2 .keyWork
      rw [next, step_cost]
      simp only [tick, reduceCtorEq, ↓reduceIte, Nat.zero_add, Nat.add_zero, ite_self,
        List.length_cons, List.range_succ, List.sum_append, List.sum_cons, List.sum_nil]
      simp only [List.length_cons] at tail
      nlinarith

/-- The source adversarial family is exactly the n distinct keys n through 2n-1. -/
theorem unaryInterval_lower_sum (n : Nat) :
    (n + 1) * (List.range n).sum ≤ (unaryRun (List.range' n n)).2 .keyWork := by
  have lower := unary_distinct_lower (List.range' n n) 0 [] (n + 1) List.nodup_range'
    (by simp) (by
      intro key member
      have bound := (List.mem_range'_1.mp member).1
      omega) (by simp)
  simpa [unaryRun] using lower

theorem unaryInterval_keyWork_lower (n : Nat) :
    (n + 1) * n * (n - 1) / 2 ≤ (unaryRun (List.range' n n)).2 .keyWork := by
  have range_finset : (List.range n).toFinset = Finset.range n := by ext key; simp
  have sum_bridge := List.sum_toFinset (fun key : Nat => key)
    (show (List.range n).Nodup from List.nodup_range)
  simp only [range_finset, List.map_id'] at sum_bridge
  have doubled : ((n + 1) * (List.range n).sum) * 2 = (n + 1) * n * (n - 1) := by
    rw [← sum_bridge, Nat.mul_assoc, Finset.sum_range_id_mul_two]
    ring
  rw [← doubled, Nat.mul_div_cancel _ Nat.zero_lt_two]
  exact unaryInterval_lower_sum n

/-- A lower bound on complete work for this family, valid also at n=0 and n=1.
It makes no lower-bound claim about arbitrary input lists. -/
theorem unaryInterval_lower (n : Nat) :
    (n + 1) * n * (n - 1) / 2 ≤ total (unaryRun (List.range' n n)).2 := by
  have lower := unaryInterval_keyWork_lower n
  unfold total
  omega

/-- The same actual family has an explicit cubic upper polynomial. -/
theorem unaryInterval_total_le (n : Nat) :
    total (unaryRun (List.range' n n)).2 ≤ 2 * n ^ 3 + 3 * n ^ 2 + 5 * n + 1 := by
  have bound := unaryRun_total_le (List.range' n n) (2 * n) (by
    intro key member
    have inside := (List.mem_range'_1.mp member).2
    omega)
  rw [List.toFinset_card_of_nodup List.nodup_range'] at bound
  simp only [List.length_range'] at bound
  nlinarith

end Resources.CollisionHistory
