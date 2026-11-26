import Applications.Resources.BinomialQueue.Bounds
import Applications.Resources.Growth

/-!
# Actual insertion trajectories and historical capacity

The only multi-step executor is `Resources.run`. Insertion credit is the number
of occupied slots in the actual initial forest, including padded forests. It
pays for one sequential trajectory; separately branching from a retained value
requires the corresponding initial credit on each trajectory. Capacity histories
also constrain every stored queue supplied to native merge. Mathematical
persistence does not assert physical pointer sharing or native running time.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.BinomialQueue

universe u
variable {K : Type u}

open Search.BinomialQueue

def potential (q : Queue K) : Nat := BinaryCounter.ones (occupancy q)

def weightedHom (prices : Cost) : Cost →+ Nat where
  toFun := weighted prices
  map_zero' := by simp [weighted]
  map_add' := weighted_add prices

def insertionsRun (cmp : K → K → Measured Bool Nat) (keys : List K) (q : Queue K) :
    Measured (Queue K) Cost := Resources.run (insertRun cmp) keys q

theorem insertionsRun_value (cmp : K → K → Measured Bool Nat) (keys : List K) (q : Queue K) :
    (insertionsRun cmp keys q).1 =
      keys.foldl (fun state key => insert (fun x y => (cmp x y).1) key state) q := by
  simp only [insertionsRun, Resources.run_state, insertRun_value]

theorem insertRun_proper (cmp : K → K → Measured Bool Nat) (key : K) (q : Queue K)
    (proper : ∀ t ∈ q, Proper t) : ∀ t ∈ (insertRun cmp key q).1, Proper t := by
  rw [insertRun_value]
  exact carry_proper _ q (.node key .nil .nil) proper rfl

theorem insertRun_occupancy (cmp : K → K → Measured Bool Nat) (key : K) (q : Queue K)
    (proper : ∀ t ∈ q, Proper t) :
    occupancy (insertRun cmp key q).1 = BinaryCounter.inc (occupancy q) := by
  rw [insertRun_value]
  exact occupancy_carry _ q (.node key .nil .nil) proper rfl (by simp)

/-- Links charge one comparison each; the binary counter additionally charges
the terminal write. Their potentials therefore differ by exactly that unit. -/
theorem insertRun_potential (cmp : K → K → Measured Bool Nat) (key : K) (q : Queue K)
    (proper : ∀ t ∈ q, Proper t) :
    (insertRun cmp key q).2 .comparisons + potential (insertRun cmp key q).1 =
      potential q + 1 := by
  have hc := (insertRun_leading_counts cmp key q proper).1
  have hb := BinaryCounter.flipCost_potential (occupancy q)
  rw [BinaryCounter.flipCost_eq_leadingOnes_add_one] at hb
  simp only [potential, insertRun_occupancy cmp key q proper]
  omega

/-- Changing observations does not change the actual charge trajectory. -/
theorem insertions_budget_constant (cmp : K → K → Measured Bool Nat)
    (charge : Nat) (keys : List K) (q : Queue K) :
    Resources.budget (insertRun cmp) (fun _ _ => charge) keys q = charge * keys.length := by
  let projected := fun key state => ((insertRun cmp key state).1, (0 : Nat))
  calc
    Resources.budget (insertRun cmp) (fun _ _ => charge) keys q =
        Resources.budget projected (fun _ _ => charge) keys q :=
      Resources.budget_congr_state (insertRun cmp) projected (fun _ _ => charge)
        (fun _ _ => rfl) keys q
    _ = charge * keys.length := Resources.budget_constant projected charge keys q

theorem insertionsRun_proper (cmp : K → K → Measured Bool Nat) (keys : List K) (q : Queue K)
    (proper : ∀ t ∈ q, Proper t) : ∀ t ∈ (insertionsRun cmp keys q).1, Proper t :=
  Resources.run_invariant (insertRun cmp) (fun state => ∀ t ∈ state, Proper t)
    (insertRun_proper cmp) keys q proper

/-- Both boundary potentials belong to the actual successive queue states. -/
theorem insertionsRun_potential (cmp : K → K → Measured Bool Nat) (keys : List K) (q : Queue K)
    (proper : ∀ t ∈ q, Proper t) :
    (insertionsRun cmp keys q).2 .comparisons + potential (insertionsRun cmp keys q).1 =
      potential q + keys.length := by
  have h := Resources.run_potential_map_exact_of_invariant (insertRun cmp)
    (fun _ _ => 1) potential (coordinate .comparisons)
    (fun state => ∀ t ∈ state, Proper t) (insertRun_proper cmp)
    (fun key state hstate => insertRun_potential cmp key state hstate) keys q proper
  simpa [insertionsRun, coordinate, insertions_budget_constant] using h

theorem insertionsRun_comparisons_le (cmp : K → K → Measured Bool Nat)
    (keys : List K) (q : Queue K) (proper : ∀ t ∈ q, Proper t) :
    (insertionsRun cmp keys q).2 .comparisons ≤ potential q + keys.length := by
  have h := insertionsRun_potential cmp keys q proper
  omega

theorem insertionsRun_occupancy (cmp : K → K → Measured Bool Nat)
    (keys : List K) (q : Queue K) (proper : ∀ t ∈ q, Proper t) :
    occupancy (insertionsRun cmp keys q).1 = BinaryCounter.advance keys.length (occupancy q) := by
  induction keys generalizing q with
  | nil => rfl
  | cons key keys ih =>
      change occupancy (insertionsRun cmp keys (insertRun cmp key q).1).1 = _
      rw [ih _ (insertRun_proper cmp key q proper), insertRun_occupancy cmp key q proper]
      rfl

theorem insertionsRun_binary_value (cmp : K → K → Measured Bool Nat)
    (keys : List K) (q : Queue K) (proper : ∀ t ∈ q, Proper t) :
    BinaryCounter.value (occupancy (insertionsRun cmp keys q).1) =
      BinaryCounter.value (occupancy q) + keys.length := by
  rw [insertionsRun_occupancy cmp keys q proper, BinaryCounter.value_advance]

theorem insertionsRun_canonical (cmp : K → K → Measured Bool Nat)
    (keys : List K) (q : Queue K) (proper : ∀ t ∈ q, Proper t) (canonical : Canonical q) :
    Canonical (insertionsRun cmp keys q).1 := by
  change BinaryCounter.Canonical (occupancy (insertionsRun cmp keys q).1)
  rw [insertionsRun_occupancy cmp keys q proper]
  exact BinaryCounter.canonical_advance keys.length (occupancy q) canonical

private theorem ones_positive_of_value_positive (bits : List Bool)
    (positive : 0 < BinaryCounter.value bits) : 0 < BinaryCounter.ones bits := by
  induction bits with
  | nil => simp [BinaryCounter.value] at positive
  | cons bit bits ih =>
      cases bit with
      | false =>
          apply ih
          simp only [BinaryCounter.value] at positive
          omega
      | true => simp [BinaryCounter.ones]

/-- The strict inequality has the source's necessary positive-N restriction. -/
theorem insertionsRun_empty_comparisons_lt (cmp : K → K → Measured Bool Nat)
    (keys : List K) (nonempty : keys ≠ []) :
    (insertionsRun cmp keys []).2 .comparisons < keys.length := by
  have hp := insertionsRun_potential cmp keys [] (by simp)
  have hv := insertionsRun_binary_value cmp keys [] (by simp)
  have hn : 0 < keys.length := List.length_pos_iff.mpr nonempty
  simp only [potential, occupancy_nil, BinaryCounter.ones] at hp
  have hb : BinaryCounter.value (occupancy (insertionsRun cmp keys []).1) = keys.length := by
    simpa [occupancy, BinaryCounter.value] using hv
  have hpos := ones_positive_of_value_positive _ (hb.symm ▸ hn)
  omega

theorem insertionsRun_nil (cmp : K → K → Measured Bool Nat) (q : Queue K) :
    insertionsRun cmp [] q = (q, 0) := rfl

def insertionBasePrice (prices : Cost) : Nat :=
  prices .insertCalls + prices .nodes + prices .carryCalls + prices .cons

/-- Unlike the stored-length bound, this bill counts exactly the occupied prefix. -/
theorem carryRun_weighted_le_leading (cmp : K → K → Measured Bool Nat)
    (prices : Cost) (C : Nat) (bound : ∀ x y, (cmp x y).2 ≤ C)
    (q : Queue K) (t : BinaryTree K) (proper : ∀ v ∈ q, Proper v)
    (ht : Proper t) (nonempty : t ≠ .nil) :
    weighted prices (carryRun cmp q t).2 ≤ prices .carryCalls + prices .cons +
      BinaryCounter.leadingOnes (occupancy q) * carryPrice prices C := by
  induction q generalizing t with
  | nil =>
      cases t with
      | nil => exact (nonempty rfl).elim
      | node => simp [carryRun, weighted_bill, occupancy, BinaryCounter.leadingOnes]
  | cons head tail ih =>
      have hp := proper head (by simp)
      have htail : ∀ v ∈ tail, Proper v := fun v hv => proper v (by simp [hv])
      cases t with
      | nil => exact (nonempty rfl).elim
      | node y c d =>
          cases head with
          | nil =>
              simp [carryRun, weighted_bill, occupancy, occupied, BinaryCounter.leadingOnes]
          | node x a b =>
              have hproper : Proper (smashRun cmp (.node y c d) (.node x a b)).1 := by
                rw [smashRun_value]
                exact smash_proper _ _ _
              have hnonempty : (smashRun cmp (.node y c d) (.node x a b)).1 ≠ .nil := by
                rw [smashRun_value]
                exact smash_ne_nil _ _ _ ht hp (by simp) (by simp)
              have hr := ih (smashRun cmp (.node y c d) (.node x a b)).1 htail hproper hnonempty
              have hs := smashRun_weighted_le cmp prices C bound (.node y c d) (.node x a b)
              simp only [carryRun, weighted_add, weighted_bill, Nat.mul_zero,
                Nat.mul_one, Nat.add_zero, occupancy_cons, occupied_node, BinaryCounter.leadingOnes]
              simp only [carryPrice, Nat.add_mul, Nat.one_mul] at *
              omega

theorem insertRun_weighted_le_leading (cmp : K → K → Measured Bool Nat)
    (prices : Cost) (C : Nat) (bound : ∀ x y, (cmp x y).2 ≤ C)
    (key : K) (q : Queue K) (proper : ∀ t ∈ q, Proper t) :
    weighted prices (insertRun cmp key q).2 ≤ insertionBasePrice prices +
      BinaryCounter.leadingOnes (occupancy q) * carryPrice prices C := by
  have h := carryRun_weighted_le_leading cmp prices C bound q (.node key .nil .nil)
    proper rfl (by simp)
  simp only [insertRun, weighted_add, weighted_bill, Nat.mul_zero, Nat.mul_one, Nat.add_zero]
  unfold insertionBasePrice
  omega

theorem insertRun_weighted_potential (cmp : K → K → Measured Bool Nat)
    (prices : Cost) (C : Nat) (bound : ∀ x y, (cmp x y).2 ≤ C)
    (key : K) (q : Queue K) (proper : ∀ t ∈ q, Proper t) :
    weighted prices (insertRun cmp key q).2 + carryPrice prices C * potential (insertRun cmp key q).1 ≤
      carryPrice prices C * potential q + (insertionBasePrice prices + carryPrice prices C) := by
  have hw := insertRun_weighted_le_leading cmp prices C bound key q proper
  have hc := (insertRun_leading_counts cmp key q proper).1
  have hp := congrArg (fun n => carryPrice prices C * n) (insertRun_potential cmp key q proper)
  rw [hc] at hp
  simp only [Nat.mul_add, Nat.mul_one] at hp
  rw [Nat.mul_comm (BinaryCounter.leadingOnes (occupancy q)) (carryPrice prices C)] at hw
  omega

theorem insertionsRun_weighted_potential (cmp : K → K → Measured Bool Nat)
    (prices : Cost) (C : Nat) (bound : ∀ x y, (cmp x y).2 ≤ C)
    (keys : List K) (q : Queue K) (proper : ∀ t ∈ q, Proper t) :
    weighted prices (insertionsRun cmp keys q).2 +
        carryPrice prices C * potential (insertionsRun cmp keys q).1 ≤
      carryPrice prices C * potential q +
        (insertionBasePrice prices + carryPrice prices C) * keys.length := by
  have h := Resources.run_potential_map_of_invariant (insertRun cmp)
    (fun _ _ => insertionBasePrice prices + carryPrice prices C)
    (fun state => carryPrice prices C * potential state) (weightedHom prices)
    (fun state => ∀ t ∈ state, Proper t) (insertRun_proper cmp)
    (fun key state hstate => insertRun_weighted_potential cmp prices C bound key state hstate)
    keys q proper
  simpa [insertionsRun, weightedHom, insertions_budget_constant] using h

theorem insertionsRun_weighted_le (cmp : K → K → Measured Bool Nat)
    (prices : Cost) (C : Nat) (bound : ∀ x y, (cmp x y).2 ≤ C)
    (keys : List K) (q : Queue K) (proper : ∀ t ∈ q, Proper t) :
    weighted prices (insertionsRun cmp keys q).2 ≤
      carryPrice prices C * potential q +
        (insertionBasePrice prices + carryPrice prices C) * keys.length := by
  have h := insertionsRun_weighted_potential cmp prices C bound keys q proper
  omega

/-- A fixed-tariff family of actual builds from empty has linear total work. -/
theorem insertionsRun_isBigO (cmp : K → K → Measured Bool Nat)
    (prices : Cost) (C : Nat) (bound : ∀ x y, (cmp x y).2 ≤ C)
    (inputs : Nat → List K) (lengths : ∀ n, (inputs n).length = n) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => (weighted prices (insertionsRun cmp (inputs n) []).2 : ℝ))
      (fun n => (n : ℝ)) := by
  apply Resources.isBigO_of_nat_bound _ id (insertionBasePrice prices + carryPrice prices C) 0
  intro n _
  simpa [potential, occupancy, BinaryCounter.ones, lengths] using
    insertionsRun_weighted_le cmp prices C bound (inputs n) [] (by simp)

/-- A chapter-local schedule of the three source updates. Merge retains its
actual stored operand; instruction dispatch and Option projection are uncharged. -/
inductive Instruction (K : Type u) where
  | insert (key : K)
  | merge (stored : Queue K)
  | deleteMax

def commandRun (cmp : K → K → Measured Bool Nat) : Instruction K → Queue K → Measured (Queue K) Cost
  | .insert key, q => insertRun cmp key q
  | .merge stored, q => mergeRun cmp q stored
  | .deleteMax, q =>
      let result := deleteMaxRun cmp q
      (match result.1 with | none => q | some (_, rest) => rest, result.2)

def runCommands (cmp : K → K → Measured Bool Nat) (commands : List (Instruction K))
    (q : Queue K) : Measured (Queue K) Cost := Resources.run (commandRun cmp) commands q

/-- Mass may grow only within H. Every retained merge operand must independently
satisfy rank validity and the same stored-capacity bound. -/
def Admissible [LE K] (B H : Nat) : Instruction K → Queue K → Prop
  | .insert _, q => mass q + 1 ≤ H
  | .merge stored, q => Valid stored ∧ Capacity B H stored ∧ mass q + mass stored ≤ H
  | .deleteMax, _ => True

/-- Conditions are checked at the actual state reached by each finite prefix. -/
def AdmissibleHistory [LE K] (cmp : K → K → Measured Bool Nat) (B H : Nat)
    (commands : List (Instruction K)) (q : Queue K) : Prop :=
  ∀ before instruction after, commands = before ++ instruction :: after →
    Admissible B H instruction (runCommands cmp before q).1

theorem admissibleHistory_nil [LE K] (cmp : K → K → Measured Bool Nat) (B H : Nat) (q : Queue K) :
    AdmissibleHistory cmp B H [] q := by
  intro before instruction after impossible
  have h := congrArg List.length impossible
  simp only [List.length_nil, List.length_append, List.length_cons] at h
  omega

theorem admissibleHistory_cons [LE K] (cmp : K → K → Measured Bool Nat) (B H : Nat)
    (instruction : Instruction K) (commands : List (Instruction K)) (q : Queue K) :
    AdmissibleHistory cmp B H (instruction :: commands) q ↔
      Admissible B H instruction q ∧
        AdmissibleHistory cmp B H commands (commandRun cmp instruction q).1 := by
  constructor
  · intro history
    constructor
    · exact history [] instruction commands rfl
    · intro before next after split
      have h := history (instruction :: before) next after (by simp [split])
      simpa only [runCommands, Resources.run_cons] using h
  · rintro ⟨head, tail⟩ before next after split
    cases before with
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at split
        rcases split with ⟨rfl, rfl⟩
        exact head
    | cons first before =>
        simp only [List.cons_append, List.cons.injEq] at split
        rcases split with ⟨rfl, split⟩
        have h := tail before next after split
        simpa only [runCommands, Resources.run_cons] using h

section CapacityHistory
variable [Preorder K] [Std.Total (fun x y : K => x ≤ y)]
variable (cmp : K → K → Measured Bool Nat)
variable (correct : ∀ x y, (cmp x y).1 = true ↔ ¬ x ≤ y)
include correct

theorem insertRun_capacity (B H : Nat) (key : K) (q : Queue K)
    (valid : Valid q) (capacity : Capacity B H q) (massBound : mass q + 1 ≤ H) :
    Capacity B H (insertRun cmp key q).1 := by
  change (insertRun cmp key q).1.length ≤ max B H.size
  rw [insertRun_value, insert_length _ correct key q valid]
  exact max_le capacity ((Nat.size_le_size massBound).trans (Nat.le_max_right _ _))

theorem mergeRun_capacity (B H : Nat) (p q : Queue K)
    (vp : Valid p) (vq : Valid q) (cp : Capacity B H p) (cq : Capacity B H q)
    (massBound : mass p + mass q ≤ H) : Capacity B H (mergeRun cmp p q).1 := by
  change (mergeRun cmp p q).1.length ≤ max B H.size
  rw [mergeRun_value, merge_length _ correct p q vp vq]
  exact max_le (max_le cp cq) ((Nat.size_le_size massBound).trans (Nat.le_max_right _ _))

theorem commandRun_invariant (B H : Nat) (instruction : Instruction K) (q : Queue K)
    (valid : Valid q) (massBound : mass q ≤ H) (capacity : Capacity B H q)
    (admissible : Admissible B H instruction q) :
    Valid (commandRun cmp instruction q).1 ∧
      mass (commandRun cmp instruction q).1 ≤ H ∧
      Capacity B H (commandRun cmp instruction q).1 := by
  cases instruction with
  | insert key =>
      have hv := insert_valid (fun x y => (cmp x y).1) correct key q valid
      have hm := insert_mass (fun x y => (cmp x y).1) key q valid
      have hc := insertRun_capacity cmp correct B H key q valid capacity admissible
      simp only [commandRun, insertRun_value] at hc ⊢
      exact ⟨hv, hm ▸ admissible, hc⟩
  | merge stored =>
      rcases admissible with ⟨storedValid, storedCapacity, joinedMass⟩
      have hv := merge_valid (fun x y => (cmp x y).1) correct q stored valid storedValid
      have hm := merge_mass (fun x y => (cmp x y).1) q stored valid storedValid
      have hc := mergeRun_capacity cmp correct B H q stored valid storedValid capacity storedCapacity joinedMass
      simp only [commandRun, mergeRun_value] at hc ⊢
      exact ⟨hv, hm ▸ joinedMass, hc⟩
  | deleteMax =>
      cases found : (deleteMaxRun cmp q).1 with
      | none => simpa only [commandRun, found] using And.intro valid (And.intro massBound capacity)
      | some result =>
          rcases result with ⟨m, rest⟩
          have hd : deleteMax (fun x y => (cmp x y).1) q = some (m, rest) := by
            simpa only [deleteMaxRun_value] using found
          have hv := deleteMax_some_valid correct q rest m valid hd
          have hm := deleteMax_some_mass correct q rest m valid hd
          have hl := deleteMax_length correct q rest m valid hd
          simp only [commandRun, found]
          refine ⟨hv, by omega, ?_⟩
          change rest.length ≤ max B H.size
          rw [hl]
          exact capacity

/-- Historical capacity is preserved by the actual successive states, including
native merges with independently bounded retained operands. -/
theorem runCommands_invariant (B H : Nat) (commands : List (Instruction K)) (q : Queue K)
    (valid : Valid q) (massBound : mass q ≤ H) (capacity : Capacity B H q)
    (history : AdmissibleHistory cmp B H commands q) :
    Valid (runCommands cmp commands q).1 ∧ mass (runCommands cmp commands q).1 ≤ H ∧
      Capacity B H (runCommands cmp commands q).1 := by
  induction commands generalizing q with
  | nil => exact ⟨valid, massBound, capacity⟩
  | cons instruction commands ih =>
      rcases (admissibleHistory_cons cmp B H instruction commands q).mp history with ⟨head, tail⟩
      have hs := commandRun_invariant cmp correct B H instruction q valid massBound capacity head
      exact ih _ hs.1 hs.2.1 hs.2.2 tail

theorem runCommands_prefix_invariant (B H : Nat) (commands before after : List (Instruction K))
    (q : Queue K) (valid : Valid q) (massBound : mass q ≤ H) (capacity : Capacity B H q)
    (history : AdmissibleHistory cmp B H commands q) (split : commands = before ++ after) :
    Valid (runCommands cmp before q).1 ∧ mass (runCommands cmp before q).1 ≤ H ∧
      Capacity B H (runCommands cmp before q).1 := by
  apply runCommands_invariant cmp correct B H before q valid massBound capacity
  intro start instruction suffix decomposed
  exact history start instruction (suffix ++ after) (by simp [split, decomposed, List.append_assoc])

def commandPrice (prices : Cost) (C : Nat) : Nat :=
  insertPrice prices C + (prices .mergeCalls + joinPrice prices C) + deletePrice prices C

theorem commandRun_weighted_le (prices : Cost) (C : Nat) (bound : ∀ x y, (cmp x y).2 ≤ C)
    (B H : Nat) (instruction : Instruction K) (q : Queue K)
    (valid : Valid q) (capacity : Capacity B H q) (admissible : Admissible B H instruction q) :
    weighted prices (commandRun cmp instruction q).2 ≤
      (max B H.size + 2) * commandPrice prices C := by
  cases instruction with
  | insert key =>
      have h := insertRun_capacity_bound cmp prices C bound B H key q capacity
      change weighted prices (insertRun cmp key q).2 ≤ _
      simp only [commandPrice, Nat.mul_add, Nat.add_mul, Nat.one_mul] at *
      omega
  | merge stored =>
      have h := mergeRun_capacity_bound cmp prices C bound B H q stored capacity admissible.2.1
      change weighted prices (mergeRun cmp q stored).2 ≤ _
      simp only [commandPrice, Nat.mul_add] at *
      omega
  | deleteMax =>
      have h := deleteMaxRun_capacity_bound cmp correct prices C bound B H q valid capacity
      change weighted prices (deleteMaxRun cmp q).2 ≤ _
      simp only [commandPrice, Nat.mul_add, Nat.add_mul, Nat.one_mul] at *
      omega

theorem runCommands_weighted_le (prices : Cost) (C : Nat) (bound : ∀ x y, (cmp x y).2 ≤ C)
    (B H : Nat) (commands : List (Instruction K)) (q : Queue K)
    (valid : Valid q) (massBound : mass q ≤ H) (capacity : Capacity B H q)
    (history : AdmissibleHistory cmp B H commands q) :
    weighted prices (runCommands cmp commands q).2 ≤
      commands.length * ((max B H.size + 2) * commandPrice prices C) := by
  induction commands generalizing q with
  | nil => simp [runCommands, Resources.run, Resources.pure, weighted]
  | cons instruction commands ih =>
      rcases (admissibleHistory_cons cmp B H instruction commands q).mp history with ⟨head, tail⟩
      have hs := commandRun_invariant cmp correct B H instruction q valid massBound capacity head
      have hh := commandRun_weighted_le cmp correct prices C bound B H instruction q valid capacity head
      have ht := ih _ hs.1 hs.2.1 hs.2.2 tail
      change weighted prices ((commandRun cmp instruction q).2 +
        (runCommands cmp commands (commandRun cmp instruction q).1).2) ≤ _
      rw [weighted_add]
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at ht hh ⊢
      omega

/-- A concrete family must supply its initial state, all stored operands and
actual prefix admissibility before this historical n·bitlength bound applies. -/
theorem runCommands_isBigO (prices : Cost) (C : Nat) (bound : ∀ x y, (cmp x y).2 ≤ C)
    (B : Nat) (commands : Nat → List (Instruction K)) (initial : Nat → Queue K)
    (lengths : ∀ n, (commands n).length = n)
    (valid : ∀ n, Valid (initial n)) (massBound : ∀ n, mass (initial n) ≤ n)
    (capacity : ∀ n, Capacity B n (initial n))
    (history : ∀ n, AdmissibleHistory cmp B n (commands n) (initial n)) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => (weighted prices (runCommands cmp (commands n) (initial n)).2 : ℝ))
      (fun n => ((n * (max B n.size + 2) : Nat) : ℝ)) := by
  apply Resources.isBigO_of_nat_bound _ _ (commandPrice prices C) 0
  intro n _
  have h := runCommands_weighted_le cmp correct prices C bound B n (commands n) (initial n)
    (valid n) (massBound n) (capacity n) (history n)
  simpa only [lengths, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem insertionsRun_valid (keys : List K) (q : Queue K) (valid : Valid q) :
    Valid (insertionsRun cmp keys q).1 := by
  apply Resources.run_invariant (insertRun cmp) Valid _ keys q valid
  intro key state hstate
  rw [insertRun_value]
  exact insert_valid _ correct key state hstate

theorem insertionsRun_mass (keys : List K) (q : Queue K) (valid : Valid q) :
    mass (insertionsRun cmp keys q).1 = mass q + keys.length := by
  have hbits := insertionsRun_binary_value cmp keys q (validFrom_proper valid)
  have hinitial := mass_eq_value valid
  have hfinal := mass_eq_value (insertionsRun_valid cmp correct keys q valid)
  simp only [Nat.pow_zero, Nat.one_mul] at hinitial hfinal
  omega

theorem insertionsRun_empty_length (keys : List K) :
    (insertionsRun cmp keys []).1.length = keys.length.size := by
  have hv := insertionsRun_valid cmp correct keys [] trivial
  have hc := insertionsRun_canonical cmp keys [] (by simp) canonical_nil
  rw [canonical_length hv hc, insertionsRun_mass cmp correct keys [] trivial]
  simp

/-- None retains the state; Some removes one occurrence without trimming slots. -/
theorem commandRun_deleteMax_state (q : Queue K) (valid : Valid q) :
    Valid (commandRun cmp .deleteMax q).1 ∧
      mass (commandRun cmp .deleteMax q).1 = mass q - 1 ∧
      (commandRun cmp .deleteMax q).1.length = q.length := by
  cases found : (deleteMaxRun cmp q).1 with
  | none =>
      have hd : deleteMax (fun x y => (cmp x y).1) q = none := by
        simpa only [deleteMaxRun_value] using found
      have hempty := (contents_eq_nil q).mpr ((deleteMax_eq_none_iff _ q).mp hd)
      have hm : mass q = 0 := by rw [← contents_length, hempty]; rfl
      simp only [commandRun, found]
      exact ⟨valid, by omega, by trivial⟩
  | some result =>
      rcases result with ⟨m, rest⟩
      have hd : deleteMax (fun x y => (cmp x y).1) q = some (m, rest) := by
        simpa only [deleteMaxRun_value] using found
      have hv := deleteMax_some_valid correct q rest m valid hd
      have hm := deleteMax_some_mass correct q rest m valid hd
      have hl := deleteMax_length correct q rest m valid hd
      simp only [commandRun, found]
      exact ⟨hv, by omega, hl⟩

def drainRun (cmp : K → K → Measured Bool Nat) (n : Nat) (q : Queue K) : Measured (Queue K) Cost :=
  runCommands cmp (List.replicate n .deleteMax) q

theorem drainRun_state (n : Nat) (q : Queue K) (valid : Valid q) :
    Valid (drainRun cmp n q).1 ∧ mass (drainRun cmp n q).1 = mass q - n ∧
      (drainRun cmp n q).1.length = q.length := by
  induction n generalizing q with
  | zero => exact ⟨valid, (Nat.sub_zero _).symm, rfl⟩
  | succ n ih =>
      have hs := commandRun_deleteMax_state cmp correct q valid
      have hr := ih (commandRun cmp .deleteMax q).1 hs.1
      change Valid (drainRun cmp n (commandRun cmp .deleteMax q).1).1 ∧
        mass (drainRun cmp n (commandRun cmp .deleteMax q).1).1 = mass q - (n + 1) ∧
        (drainRun cmp n (commandRun cmp .deleteMax q).1).1.length = q.length
      exact ⟨hr.1, by omega, hr.2.2.trans hs.2.2⟩

/-- Padding is reachable from empty by the actual build-and-drain schedule. -/
theorem build_drain_padding (keys : List K) :
    (drainRun cmp keys.length (insertionsRun cmp keys []).1).1 =
      List.replicate keys.length.size .nil := by
  have hv := insertionsRun_valid cmp correct keys [] trivial
  have hm : mass (insertionsRun cmp keys []).1 = keys.length := by
    simpa using insertionsRun_mass cmp correct keys [] trivial
  have hl := insertionsRun_empty_length cmp correct keys
  have hd := drainRun_state cmp correct keys.length (insertionsRun cmp keys []).1 hv
  have hempty : contents (drainRun cmp keys.length (insertionsRun cmp keys []).1).1 = [] := by
    apply List.length_eq_zero_iff.mp
    rw [contents_length, hd.2.1, hm, Nat.sub_self]
  have he := List.eq_replicate_length.mpr ((contents_eq_nil _).mp hempty)
  rw [hd.2.2, hl] at he
  exact he

theorem build_drain_power_padding (key : K) (r : Nat) :
    (drainRun cmp (2 ^ r) (insertionsRun cmp (List.replicate (2 ^ r) key) []).1).1 =
      List.replicate (r + 1) .nil := by
  simpa only [List.length_replicate, Nat.size_pow] using
    build_drain_padding cmp correct (List.replicate (2 ^ r) key)

theorem delete_after_power_drain (key : K) (r : Nat) :
    deleteMaxRun cmp
      (drainRun cmp (2 ^ r) (insertionsRun cmp (List.replicate (2 ^ r) key) []).1).1 =
      (none, charge .deleteMaxCalls 1 + charge .findMaxCalls (r + 2)) := by
  rw [build_drain_power_padding cmp correct key r]
  exact deleteMaxRun_padding cmp (r + 1)

end CapacityHistory

/-- The bitlength endpoint includes one extra bit at exact powers of two. -/
theorem size_le_clog_add_one (n : Nat) (positive : 0 < n) :
    n.size ≤ Nat.clog 2 n + 1 := by
  have h := Nat.le_pow_clog (by decide : 1 < 2) n
  apply Nat.size_le.mpr
  rw [Nat.pow_succ]
  omega

/-- With fixed initial padding, the historical capacity scale has ordinary
real logarithmic growth once the size parameter is at least two. -/
theorem capacity_scale_cast_le (B n : Nat) (hn : 2 ≤ n) :
    ((max B n.size + 2 : Nat) : ℝ) ≤ ((B : ℝ) + 5) * Real.logb 2 n := by
  have hs := size_le_clog_add_one n (by omega)
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 ≤ Real.logb 2 n := by
    calc
      1 = Real.logb 2 (2 : ℝ) := (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ Real.logb 2 n := Real.logb_le_logb_of_le (by norm_num) (by norm_num) hn'
  have hsize : max B n.size + 2 ≤ B + Nat.clog 2 n + 3 := by omega
  have hcast : ((max B n.size + 2 : Nat) : ℝ) ≤ (B : ℝ) + (Nat.clog 2 n : ℝ) + 3 := by
    exact_mod_cast hsize
  have hclog := Resources.clog_two_cast_le_two_logb n hn
  have hB := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg B)
  nlinarith

theorem capacity_scale_isBigO_log (B : Nat) :
    Asymptotics.IsBigO Filter.atTop (fun n : Nat => ((max B n.size + 2 : Nat) : ℝ))
      (fun n => Real.logb 2 n) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨(B : ℝ) + 5, Filter.eventually_atTop.mpr ⟨2, ?_⟩⟩
  intro n hn
  have hlog : 0 ≤ Real.logb 2 n :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n by omega))
  simpa only [Real.norm_natCast, Real.norm_of_nonneg hlog] using capacity_scale_cast_le B n hn

theorem n_capacity_scale_isBigO_log (B : Nat) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : Nat => ((n * (max B n.size + 2) : Nat) : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨(B : ℝ) + 5, Filter.eventually_atTop.mpr ⟨2, ?_⟩⟩
  intro n hn
  have hlog : 0 ≤ Real.logb 2 n :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n by omega))
  have h := mul_le_mul_of_nonneg_left (capacity_scale_cast_le B n hn) (Nat.cast_nonneg n)
  rw [Real.norm_natCast, Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg n) hlog)]
  simpa only [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using h

/-- Logarithmic insertion for a capacity-bounded family, with fixed tariffs. -/
theorem insertRun_isBigO_log (cmp : K → K → Measured Bool Nat)
    (prices : Cost) (C : Nat) (bound : ∀ x y, (cmp x y).2 ≤ C)
    (B : Nat) (keys : Nat → K) (queues : Nat → Queue K)
    (capacity : ∀ n, Capacity B n (queues n)) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => (weighted prices (insertRun cmp (keys n) (queues n)).2 : ℝ))
      (fun n => Real.logb 2 n) := by
  have h := Resources.isBigO_of_nat_bound
    (fun n => weighted prices (insertRun cmp (keys n) (queues n)).2)
    (fun n => max B n.size + 2) (insertPrice prices C) 0 (fun n _ => by
      calc
        _ ≤ (max B n.size + 1) * insertPrice prices C :=
          insertRun_capacity_bound cmp prices C bound B n (keys n) (queues n) (capacity n)
        _ ≤ (max B n.size + 2) * insertPrice prices C :=
          Nat.mul_le_mul_right _ (by omega)
        _ = insertPrice prices C * (max B n.size + 2) := Nat.mul_comm _ _)
  exact h.trans (capacity_scale_isBigO_log B)

theorem mergeRun_isBigO_log (cmp : K → K → Measured Bool Nat)
    (prices : Cost) (C : Nat) (bound : ∀ x y, (cmp x y).2 ≤ C)
    (B : Nat) (left right : Nat → Queue K)
    (cl : ∀ n, Capacity B n (left n)) (cr : ∀ n, Capacity B n (right n)) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => (weighted prices (mergeRun cmp (left n) (right n)).2 : ℝ))
      (fun n => Real.logb 2 n) := by
  have h := Resources.isBigO_of_nat_bound
    (fun n => weighted prices (mergeRun cmp (left n) (right n)).2)
    (fun n => max B n.size + 2) (prices .mergeCalls + joinPrice prices C) 0 (fun n _ => by
      simpa only [Nat.mul_comm] using
        mergeRun_capacity_bound cmp prices C bound B n (left n) (right n) (cl n) (cr n))
  exact h.trans (capacity_scale_isBigO_log B)

theorem deleteMaxRun_isBigO_log [Preorder K] [Std.Total (fun x y : K => x ≤ y)]
    (cmp : K → K → Measured Bool Nat) (correct : ∀ x y, (cmp x y).1 = true ↔ ¬ x ≤ y)
    (prices : Cost) (C : Nat) (bound : ∀ x y, (cmp x y).2 ≤ C)
    (B : Nat) (queues : Nat → Queue K) (valid : ∀ n, Valid (queues n))
    (capacity : ∀ n, Capacity B n (queues n)) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => (weighted prices (deleteMaxRun cmp (queues n)).2 : ℝ))
      (fun n => Real.logb 2 n) := by
  have h := Resources.isBigO_of_nat_bound
    (fun n => weighted prices (deleteMaxRun cmp (queues n)).2)
    (fun n => max B n.size + 2) (deletePrice prices C) 0 (fun n _ => by
      calc
        _ ≤ (max B n.size + 1) * deletePrice prices C :=
          deleteMaxRun_capacity_bound cmp correct prices C bound B n (queues n) (valid n) (capacity n)
        _ ≤ (max B n.size + 2) * deletePrice prices C := Nat.mul_le_mul_right _ (by omega)
        _ = deletePrice prices C * (max B n.size + 2) := Nat.mul_comm _ _)
  exact h.trans (capacity_scale_isBigO_log B)

theorem runCommands_isBigO_n_log [Preorder K] [Std.Total (fun x y : K => x ≤ y)]
    (cmp : K → K → Measured Bool Nat) (correct : ∀ x y, (cmp x y).1 = true ↔ ¬ x ≤ y)
    (prices : Cost) (C : Nat) (bound : ∀ x y, (cmp x y).2 ≤ C)
    (B : Nat) (commands : Nat → List (Instruction K)) (initial : Nat → Queue K)
    (lengths : ∀ n, (commands n).length = n)
    (valid : ∀ n, Valid (initial n)) (massBound : ∀ n, mass (initial n) ≤ n)
    (capacity : ∀ n, Capacity B n (initial n))
    (history : ∀ n, AdmissibleHistory cmp B n (commands n) (initial n)) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => (weighted prices (runCommands cmp (commands n) (initial n)).2 : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n) :=
  (runCommands_isBigO cmp correct prices C bound B commands initial lengths valid massBound capacity history).trans
    (n_capacity_scale_isBigO_log B)

end Resources.BinomialQueue
