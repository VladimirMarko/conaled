import Applications.Progress.Processors

/-!
# Checked cases for termination and productivity contracts

Expected calculations: countdown 2 returns after 3 transitions; countdown 3
then takes 4 more. A Boolean toggle emits false,true,false and returns to true.
Inclusive scan over 1,2,3 emits 1,3,6. Dropping two inputs before incrementing
0,1,2,... yields 3,4,5 and demands five inputs for three outputs.
-/
namespace Progress.Examples

def countdown : Machine Nat Nat
  | 0 => .inl 0
  | n + 1 => .inr n

theorem countdown_evaluates (n : Nat) : Evaluates countdown n 0 (n + 1) := by
  induction n with
  | zero => exact .done rfl
  | succ n ih => exact .next rfl ih

example : Evaluates countdown 2 0 3 := countdown_evaluates 2
example : search countdown 2 2 = none := rfl
example : search countdown 3 2 = some (0, 3) := search_complete (countdown_evaluates 2) le_rfl
example : check countdown 2 (3, 0, 3) = true := by decide
example : check countdown 2 (3, 1, 3) = false := by decide
example : check countdown 2 (3, 0, 2) = false := by decide

/-- Certificate acceptance supplies the public semantic judgment. -/
example : Evaluates countdown 2 0 3 :=
  check_sound (step := countdown) (s := 2) (c := (3, 0, 3)) (by decide)

example : Evaluates (sequential countdown countdown (fun _ => 3)) (.inl 2) 0 7 :=
  sequential_evaluates (start := fun _ => 3) (countdown_evaluates 2) (countdown_evaluates 3)

/-- The downstream domain is established by the first stage's postcondition. -/
example : ∀ n : Nat, True → ∃ a b k,
    Evaluates (sequential countdown countdown (fun a => a + 3)) (.inl n) b k ∧
      a = 0 ∧ b = 0 := by
  apply sequential_total (pre := fun _ => True) (mid := fun _ a => a = 0)
    (dom := fun n => n = 3) (post := fun _ b => b = 0)
  · intro n _; exact ⟨0, n + 1, countdown_evaluates n, rfl⟩
  · intro n _; exact ⟨0, n + 1, countdown_evaluates n, rfl⟩
  · intro _ a _ ha; simp [ha]

/-- Successful and unsuccessful searches are both admissible; only success
carries a finite evaluation. The input index is retained by the shared adapter. -/
example : (searchSquare countdown 3).impl (2 : Nat) = (2, some (0, 3)) := rfl
example : some (0, 3) ∈ admissible countdown 2 := by
  exact (searchSquare countdown 3).preserves (r := (2 : Nat)) rfl |>.2

example : ¬ Terminates (fun n : Nat => .inr (n + 1) : Machine Nat Nat) 0 := by
  rintro ⟨a, k, h⟩
  exact silent_no_evaluation _ h
example : search (fun n : Nat => .inr (n + 1) : Machine Nat Nat) 10 0 = none := rfl

/-- Finite control state, despite an unbounded sequence of observations. -/
def toggle : Coalgebra Bool Bool := fun b => (b, !b)

example : Delivers (guarded toggle) false [false, true, false] true 3 :=
  guarded_delivery toggle false 3
example : Productive (guarded toggle) false := guarded_productive toggle false
example : Delivers (paused toggle) (false, false) [false, true, false] (false, true) 6 :=
  paused_delivery toggle false 3
example : ∀ n, Delivers (guarded toggle) false (unfold toggle false n)
    (advance toggle false n) n ∧
    Delivers (paused toggle) (false, false) (unfold toggle false n)
      (false, advance toggle false n) (2 * n) := guarded_paused_progress toggle false

/-- Coherence compares actual deliveries, rather than assuming stream equality. -/
example : ([false, true] : List Bool).take [false, true, false].length =
    [false, true, false].take [false, true].length :=
  (guarded_delivery toggle false 2).coherent (guarded_delivery toggle false 3)

example : unfold (mapCoalgebra (!·) toggle) false 3 = [true, false, true] := by
  rw [unfold_map]; rfl
example : unfold (zipCoalgebra toggle toggle) (false, true) 3 =
    [(false, true), (true, false), (false, true)] := by
  rw [unfold_zip]; rfl

example : Delivers (guarded (zipCoalgebra toggle toggle)) (false, true)
    [(false, true), (true, false), (false, true)] (true, false) 3 :=
  guarded_delivery _ _ 3

/-- State-map transport retains the phase change, not just a list of values. -/
example : unfold toggle true 4 = (unfold toggle false 4).map (!·) := by
  exact unfold_transport toggle toggle (!·) (!·) (by intro b; cases b <;> rfl) false 4

def naturals : Coalgebra Nat Nat := fun n => (n, n + 1)
example : unfold (scanCoalgebra (· + ·) naturals) (0, 1) 3 = [1, 3, 6] := by
  rw [unfold_scan]; rfl
example : Delivers (guarded (scanCoalgebra (· + ·) naturals)) (0, 1)
    [1, 3, 6] (6, 4) 3 := guarded_delivery _ _ 3

/-- The same map-then-scan observations are produced incrementally and from
a finite input list. The two operational costs are three and four transitions. -/
example : Delivers
      (guarded (mealyCoalgebra (fun (s n : Nat) => (s + n, s + n))
        (mapCoalgebra (fun n => n + 1) naturals))) (0, 0) [1, 3, 6] (6, 3) 3 ∧
    Evaluates (mealyStep (fun (s n : Nat) => (s + n, s + n)))
      (0, [1, 2, 3], []) [1, 3, 6] 4 :=
  mealy_realizations _ (mapCoalgebra (fun n => n + 1) naturals) 0 0 3

/-- A scan can retain finite control too: parity over alternating bits. -/
example : unfold (scanCoalgebra Bool.xor toggle) (false, false) 4 =
    [false, true, true, false] := by
  rw [unfold_scan]; rfl
example : Delivers (guarded (scanCoalgebra Bool.xor toggle)) (false, false)
    [false, true, true, false] (false, false) 4 := guarded_delivery _ _ 4

/-- Rejecting every input is safe but cannot produce even one filtered output. -/
def zeros : Coalgebra Unit Nat := fun _ => (0, ())
example : ¬ Productive (filterProducer (fun n => decide (0 < n)) zeros) () :=
  filter_no_match _ _ (fun _ => rfl) ()

/-- Emitting an absent value is still an observation. It differs from skipping
an input while searching indefinitely for a present value. -/
example : Delivers (guarded (mapCoalgebra
    (fun n : Nat => if 0 < n then some n else none) zeros)) ()
    [none, none, none] () 3 := guarded_delivery _ _ 3

/-- Filtering the toggle does have a two-step next-output certificate from false.
The invariant permits every state, so local finite progress can be iterated. -/
example : Productive (filterProducer id toggle) false := by
  apply productive_of_next (fun _ => True) ?_ false True.intro
  intro b _
  cases b with
  | false => exact ⟨true, false, 2,
      check_sound (c := (2, (true, false), 2)) (by decide), True.intro⟩
  | true => exact ⟨true, false, 1,
      check_sound (c := (1, (true, false), 1)) (by decide), True.intro⟩

/-- Zero fuel is unknown even for a terminating machine. -/
example : search countdown 0 0 = none ∧ Terminates countdown 0 :=
  ⟨rfl, ⟨0, 1, countdown_evaluates 0⟩⟩

example : DeliversWithin (mapProcessor (fun n : Nat => n + 1)) (fun n => n + 1) :=
  map_delivery _
example : Causal (scanProcessor (· + ·) (0 : Nat)) := delivery_causal (scan_delivery _ _)
example : prefixOf ((scanProcessor (· + ·) (0 : Nat)).meaning (fun n => n + 1)) 3 =
    [1, 3, 6] := by
  change prefixOf (runStream _ _ _) 3 = _
  rw [runStream_prefix]; rfl

/-- Nonidentity demand composes: 3 desired outputs need 5 original inputs.
The first stage takes 3 transitions, then the map takes 4. -/
def droppedMap : Processor Nat Nat :=
  composeProcessor (mapProcessor (fun n => n + 1)) (dropProcessor 2)

example : droppedMap.demand 3 = 5 := rfl
example : DeliversWithin droppedMap (fun n => 3 + (n + 1)) :=
  compose_delivery (drop_delivery 2) (map_delivery _)
example : Evaluates (droppedMap.step 3) (droppedMap.start 3 [0, 1, 2, 3, 4]) [3, 4, 5] 7 := by
  exact sequential_evaluates
    (g := (mapProcessor (fun n : Nat => n + 1)).step 3)
    (start := (mapProcessor (fun n : Nat => n + 1)).start 3) (drop_evaluates 2 3 id)
    (mealy_evaluates (fun (_ : PUnit) (n : Nat) => (n + 1, PUnit.unit))
      PUnit.unit [2, 3, 4] [])
example : (composeProcessor (dropProcessor (A := Nat) 3) (dropProcessor 2)).demand 4 = 9 := rfl

/-- Different request lengths produce compatible actual machine results. -/
example {ys zs : List Nat} {k l : Nat}
    (hy : Evaluates (droppedMap.step 2) (droppedMap.start 2 [0, 1, 2, 3]) ys k)
    (hz : Evaluates (droppedMap.step 3) (droppedMap.start 3 [0, 1, 2, 3, 4]) zs l) :
    zs.take 2 = ys :=
  delivery_coherent (compose_delivery (drop_delivery 2) (map_delivery _))
    id (by decide : 2 ≤ 3) hy hz

/-- The shared square composition observes a map followed by a scan. -/
example : (composedMealySquare
      (fun (_ : PUnit) (n : Nat) => (n + 1, PUnit.unit))
      (fun (s n : Nat) => (s + n, s + n)) PUnit.unit 0 3).spec [0, 1, 2] = [1, 3, 6] := rfl
example : prefixOf
    ((composedMealySquare
      (fun (_ : PUnit) (n : Nat) => (n + 1, PUnit.unit))
      (fun (s n : Nat) => (s + n, s + n)) PUnit.unit 0 3).impl id) 3 = [1, 3, 6] := by
  exact (composedMealySquare
      (fun (_ : PUnit) (n : Nat) => (n + 1, PUnit.unit))
      (fun (s n : Nat) => (s + n, s + n)) PUnit.unit 0 3).preserves (r := id) rfl

end Progress.Examples
