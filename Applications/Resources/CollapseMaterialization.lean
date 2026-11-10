import Applications.Resources.CollapseDemand
import Applications.Resources.ListAppend

/-!
# Collapse: demanded production and full append materialization

The finite source demand model from checkpoint-335 Chapter01/CollapseAppendCosts
is adapted to conaled's existing measured append and cached/DList semantics.
See `docs/research/adwh-collapse-resources.md` for units and declaration provenance.

A standard list stores consumed blocks in reverse update order. The left observer
materializes the successive left appends; the function observer applies the same
updates to an arbitrary tail. The loop tests the total before asking for another
label, whose sum is delayed until that block is selected. Arithmetic has unit
cost. These are source-model operation counts, not evaluator, allocation, peak
memory, or machine-time claims.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.CollapseMaterialization

/-- Reuse actual generic append; charge a constructor observation and copy per
left cons, plus the final nil observation, on each append call separately. -/
def appendRun (xs tail : List Int) : Measured (List Int) Nat :=
  ListAppend.weighted 1 1 xs tail

theorem appendRun_exact (xs tail : List Int) :
    appendRun xs tail = (xs ++ tail, 2 * xs.length + 1) := by
  exact ListAppend.weighted_exact 1 1 xs tail

theorem appendRun_value (xs tail : List Int) : (appendRun xs tail).1 = xs ++ tail := by
  rw [appendRun_exact]

theorem appendRun_work (xs tail : List Int) :
    (appendRun xs tail).2 = 2 * xs.length + 1 := by rw [appendRun_exact]

/-- The history is newest-block-first, so updates are ordinary list cons. -/
def historyValue (history : List (List Int)) : List Int := history.reverse.flatten

/-- Fully observe the successive left-associated append results. -/
def leftMaterialize : List (List Int) → Measured (List Int) Nat
  | [] => ([], 0)
  | block :: previous =>
      let old := leftMaterialize previous
      let r := appendRun old.1 block
      (r.1, old.2 + r.2)

/-- Apply the function representation, preserving the supplied tail. -/
def applyFunction : List (List Int) → List Int → Measured (List Int) Nat
  | [], tail => (tail, 0)
  | block :: previous, tail =>
      let r := appendRun block tail
      let old := applyFunction previous r.1
      (old.1, r.2 + old.2)

theorem leftMaterialize_value (history : List (List Int)) :
    (leftMaterialize history).1 = historyValue history := by
  induction history <;>
    simp_all [leftMaterialize, appendRun_value, historyValue, List.reverse_cons]

theorem applyFunction_value (history : List (List Int)) (tail : List Int) :
    (applyFunction history tail).1 = historyValue history ++ tail := by
  induction history generalizing tail <;>
    simp_all [applyFunction, appendRun_value, historyValue, List.reverse_cons,
      List.append_assoc]

theorem applyFunction_cons_value (block : List Int) (previous : List (List Int))
    (tail : List Int) :
    (applyFunction (block :: previous) tail).1 =
      (applyFunction previous (block ++ tail)).1 := by
  simp only [applyFunction, appendRun_value]

theorem applyFunction_work (history : List (List Int)) (tail : List Int) :
    (applyFunction history tail).2 = 2 * (historyValue history).length + history.length := by
  induction history generalizing tail with
  | nil => rfl
  | cons block previous ih =>
      simp only [applyFunction, appendRun_work, ih, historyValue,
        List.reverse_cons, List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.length_append, List.length_cons]
      omega

theorem leftMaterialize_work_le (history : List (List Int)) :
    (leftMaterialize history).2 ≤ history.length * (2 * (historyValue history).length + 1) := by
  induction history with
  | nil => simp [leftMaterialize]
  | cons block previous ih =>
      have hm : previous.length * (2 * (historyValue previous).length + 1) ≤
          previous.length * (2 * ((historyValue previous).length + block.length) + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      simp only [leftMaterialize, appendRun_work, leftMaterialize_value,
        historyValue, List.reverse_cons, List.flatten_append, List.flatten_cons,
        List.flatten_nil, List.append_nil, List.length_append, List.length_cons,
        Nat.add_mul, Nat.one_mul] at ih hm ⊢
      omega

abbrev SumThunk := Unit → Measured Int Nat

/-- One map input case; on cons, build the sum thunk and the mapped cons. -/
def sumMapStep : List (List Int) → Option (SumThunk × List (List Int)) × Nat
  | [] => (none, 1)
  | block :: rest => (some ((fun _ => Steepness.sumRun block), rest), 3)

/-- One demanded step of `zip (map sum blocks) blocks`.
The zip counts its two constructor cases and its pair/cons construction. -/
def labelStep (blocks : List (List Int)) :
    Option (CollapseDemand.Label × List (List Int)) × Nat :=
  let mapped := sumMapStep blocks
  match mapped.1 with
  | none => (none, mapped.2 + 1)
  | some (sumThunk, _) =>
      match blocks with
      | [] => (none, mapped.2 + 2)
      | block :: rest => (some ((sumThunk, block), rest), mapped.2 + 4)

theorem labelStep_nil : labelStep [] = (none, 2) := rfl

theorem labelStep_cons (block : List Int) (rest : List (List Int)) :
    labelStep (block :: rest) =
      (some (((fun _ => Steepness.sumRun block), block), rest), 7) := rfl

theorem labelStep_tail_lt (blocks : List (List Int)) (p : CollapseDemand.Label)
    (rest : List (List Int)) (h : (labelStep blocks).1 = some (p, rest)) :
    rest.length < blocks.length := by
  cases blocks with
  | nil => simp [labelStep_nil] at h
  | cons block tail =>
      simp only [labelStep_cons, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩
      simp

structure BuildRun where
  history : List (List Int)
  used : List (List Int)
  sumWork : Nat
  labelWork : Nat
  selectors : Nat
  tests : Nat
  updates : Nat
  deriving Repr, DecidableEq

/-- Source loop with demanded map/zip production. `selectors` counts null,
head and tail individually; one accumulator update and scalar addition occur
per consumed block. The output history remains unmaterialized here. -/
def buildAux (s : Int) (history : List (List Int)) (blocks : List (List Int)) : BuildRun :=
  if 0 < s then ⟨history, [], 0, 0, 0, 1, 0⟩
  else
    let step := labelStep blocks
    match h : step.1 with
    | none => ⟨history, [], 0, step.2, 1, 1, 0⟩
    | some (p, rest) =>
        let t := p.1 ()
        let r := buildAux (s + t.1) (p.2 :: history) rest
        ⟨r.history, p.2 :: r.used, t.2 + r.sumWork, step.2 + r.labelWork,
          3 + r.selectors, 1 + r.tests, 1 + r.updates⟩
termination_by blocks.length
decreasing_by exact labelStep_tail_lt blocks p rest h

def build (blocks : List (List Int)) : BuildRun := buildAux 0 [] blocks

theorem buildAux_positive (s : Int) (history : List (List Int)) (blocks : List (List Int))
    (h : 0 < s) : buildAux s history blocks = ⟨history, [], 0, 0, 0, 1, 0⟩ := by
  rw [buildAux]
  simp [h]

theorem buildAux_value (s : Int) (history : List (List Int)) (blocks : List (List Int)) :
    historyValue (buildAux s history blocks).history =
      (CollapseDemand.cachedAux s (historyValue history) (CollapseDemand.lazyLabels blocks)).value := by
  induction blocks generalizing s history with
  | nil =>
      rw [buildAux]
      simp only [labelStep_nil, CollapseDemand.lazyLabels, List.map_nil,
        List.zip_nil_right, CollapseDemand.cachedAux]
      split <;> rfl
  | cons block rest ih =>
      rw [buildAux]
      simp only [labelStep_cons, CollapseDemand.lazyLabels_eq_map,
        List.map_cons, CollapseDemand.cachedAux]
      split
      · rfl
      · simpa [historyValue, CollapseDemand.lazyLabels_eq_map] using
          ih (s + (Steepness.sumRun block).1) (block :: history)

theorem buildAux_used (s : Int) (history : List (List Int)) (blocks : List (List Int)) :
    (buildAux s history blocks).used =
      (CollapseDemand.cachedAux s (historyValue history) (CollapseDemand.lazyLabels blocks)).used := by
  induction blocks generalizing s history with
  | nil =>
      rw [buildAux]
      simp only [labelStep_nil, CollapseDemand.lazyLabels, List.map_nil,
        List.zip_nil_right, CollapseDemand.cachedAux]
      split <;> rfl
  | cons block rest ih =>
      rw [buildAux]
      simp only [labelStep_cons, CollapseDemand.lazyLabels_eq_map,
        List.map_cons, CollapseDemand.cachedAux]
      split
      · rfl
      · simpa [historyValue, CollapseDemand.lazyLabels_eq_map] using
          congrArg (List.cons block) (ih (s + (Steepness.sumRun block).1) (block :: history))

theorem buildAux_sumWork (s : Int) (history : List (List Int)) (blocks : List (List Int)) :
    (buildAux s history blocks).sumWork =
      (CollapseDemand.cachedAux s (historyValue history) (CollapseDemand.lazyLabels blocks)).sumWork := by
  induction blocks generalizing s history with
  | nil =>
      rw [buildAux]
      simp only [labelStep_nil, CollapseDemand.lazyLabels, List.map_nil,
        List.zip_nil_right, CollapseDemand.cachedAux]
      split <;> rfl
  | cons block rest ih =>
      rw [buildAux]
      simp only [labelStep_cons, CollapseDemand.lazyLabels_eq_map,
        List.map_cons, CollapseDemand.cachedAux]
      split
      · rfl
      · simpa [historyValue, CollapseDemand.lazyLabels_eq_map] using
          congrArg ((Steepness.sumRun block).2 + ·)
            (ih (s + (Steepness.sumRun block).1) (block :: history))

theorem buildAux_history_blocks (s : Int) (history : List (List Int)) (blocks : List (List Int)) :
    (buildAux s history blocks).history.reverse =
      history.reverse ++ (buildAux s history blocks).used := by
  induction blocks generalizing s history with
  | nil =>
      rw [buildAux]
      simp only [labelStep_nil]
      split <;> simp
  | cons block rest ih =>
      rw [buildAux]
      simp only [labelStep_cons]
      split
      · simp
      · simpa [List.reverse_cons, List.append_assoc] using
          ih (s + (Steepness.sumRun block).1) (block :: history)

theorem buildAux_tests (s : Int) (history : List (List Int)) (blocks : List (List Int)) :
    (buildAux s history blocks).tests = (buildAux s history blocks).used.length + 1 := by
  induction blocks generalizing s history with
  | nil => rw [buildAux]; simp only [labelStep_nil]; split <;> rfl
  | cons block rest ih =>
      rw [buildAux]
      simp only [labelStep_cons]
      split
      · rfl
      · simp only [List.length_cons]
        have h := ih (s + (Steepness.sumRun block).1) (block :: history)
        omega

theorem buildAux_updates (s : Int) (history : List (List Int)) (blocks : List (List Int)) :
    (buildAux s history blocks).updates = (buildAux s history blocks).used.length := by
  induction blocks generalizing s history with
  | nil => rw [buildAux]; simp only [labelStep_nil]; split <;> rfl
  | cons block rest ih =>
      rw [buildAux]
      simp only [labelStep_cons]
      split
      · rfl
      · simp only [List.length_cons]
        have h := ih (s + (Steepness.sumRun block).1) (block :: history)
        omega

theorem buildAux_labelWork_le (s : Int) (history : List (List Int)) (blocks : List (List Int)) :
    (buildAux s history blocks).labelWork ≤ 7 * (buildAux s history blocks).used.length + 2 := by
  induction blocks generalizing s history with
  | nil => rw [buildAux]; simp only [labelStep_nil]; split <;> simp
  | cons block rest ih =>
      rw [buildAux]
      simp only [labelStep_cons]
      split
      · simp
      · simp only [List.length_cons]
        have h := ih (s + (Steepness.sumRun block).1) (block :: history)
        omega

theorem buildAux_selectors_le (s : Int) (history : List (List Int)) (blocks : List (List Int)) :
    (buildAux s history blocks).selectors ≤ 3 * (buildAux s history blocks).used.length + 1 := by
  induction blocks generalizing s history with
  | nil => rw [buildAux]; simp only [labelStep_nil]; split <;> simp
  | cons block rest ih =>
      rw [buildAux]
      simp only [labelStep_cons]
      split
      · simp
      · simp only [List.length_cons]
        have h := ih (s + (Steepness.sumRun block).1) (block :: history)
        omega

/-- Every tail is preserved, including when a nonempty accumulator is supplied. -/
theorem buildAux_apply (s : Int) (history : List (List Int))
    (blocks : List (List Int)) (tail : List Int) :
    (applyFunction (buildAux s history blocks).history tail).1 =
      (Sequences.Accumulation.cachedRun List.append
        (historyValue history, Multiplicative.ofAdd s)
        (Sequences.Accumulation.labelSums blocks)).1 ++ tail := by
  rw [applyFunction_value, buildAux_value, CollapseDemand.cachedAux_value,
    CollapseDemand.eagerLabels_lazyLabels]

theorem build_used (blocks : List (List Int)) :
    (build blocks).used = (CollapseDemand.cached blocks).used :=
  buildAux_used 0 [] blocks

theorem build_history_blocks (blocks : List (List Int)) :
    (build blocks).history.reverse = (build blocks).used := by
  simpa [build] using buildAux_history_blocks 0 [] blocks

theorem build_history_length (blocks : List (List Int)) :
    (build blocks).history.length = (build blocks).used.length := by
  simpa using congrArg List.length (build_history_blocks blocks)

theorem build_selected (blocks : List (List Int)) :
    ∃ remaining, blocks = (build blocks).used ++ remaining ∧
      Sequences.Accumulation.NonpositiveBefore 0 (build blocks).used ∧
      (remaining = [] ∨ 0 < (historyValue (build blocks).history).sum) := by
  have hv : historyValue (build blocks).history = (CollapseDemand.cached blocks).value :=
    buildAux_value 0 [] blocks
  simpa only [build_used, hv] using CollapseDemand.cached_selected blocks

theorem build_sumWork (blocks : List (List Int)) :
    (build blocks).sumWork =
      2 * (build blocks).used.flatten.length + (build blocks).used.length := by
  rw [build, buildAux_sumWork, CollapseDemand.cachedAux_sumWork, buildAux_used]

/-- Scalar addition and construction of the next accumulator are two units per
update. Sum, producer, selector and comparison counters retain their own units. -/
def overhead (r : BuildRun) : Nat :=
  r.sumWork + r.labelWork + r.selectors + r.tests + 2 * r.updates

theorem build_overhead_le (blocks : List (List Int)) :
    overhead (build blocks) ≤
      2 * (build blocks).used.flatten.length + 14 * (build blocks).used.length + 4 := by
  have hs := build_sumWork blocks
  have hl := buildAux_labelWork_le 0 [] blocks
  have hn := buildAux_selectors_le 0 [] blocks
  have ht := buildAux_tests 0 [] blocks
  have hu := buildAux_updates 0 [] blocks
  change (build blocks).labelWork ≤ 7 * (build blocks).used.length + 2 at hl
  change (build blocks).selectors ≤ 3 * (build blocks).used.length + 1 at hn
  change (build blocks).tests = (build blocks).used.length + 1 at ht
  change (build blocks).updates = (build blocks).used.length at hu
  unfold overhead
  omega

def leftCollapse (blocks : List (List Int)) : Measured (List Int) Nat :=
  let r := build blocks
  let out := leftMaterialize r.history
  (out.1, overhead r + out.2)

def differenceCollapse (blocks : List (List Int)) : Measured (List Int) Nat :=
  let r := build blocks
  let out := applyFunction r.history []
  (out.1, overhead r + out.2)

theorem leftCollapse_value (blocks : List (List Int)) :
    (leftCollapse blocks).1 = Sequences.Accumulation.collapseCached blocks := by
  simp only [leftCollapse, leftMaterialize_value, build, buildAux_value]
  exact CollapseDemand.cached_value blocks

/-- The measured function observer agrees with conaled's actual DList at every tail. -/
theorem build_apply_difference (blocks : List (List Int)) (tail : List Int) :
    (applyFunction (build blocks).history tail).1 =
      (Sequences.Accumulation.differenceResult blocks).1.apply tail := by
  rw [Sequences.Accumulation.differenceResult_apply]
  have h := buildAux_apply 0 [] blocks tail
  change (applyFunction (build blocks).history tail).1 =
    Sequences.Accumulation.collapseCached blocks ++ tail at h
  rw [(Sequences.Accumulation.cachedResult_refines blocks).2] at h
  exact h

theorem differenceCollapse_value (blocks : List (List Int)) :
    (differenceCollapse blocks).1 = Sequences.Accumulation.collapseDifference blocks := by
  have h := build_apply_difference blocks []
  rw [Sequences.Accumulation.differenceResult_apply] at h
  simpa only [differenceCollapse, List.append_nil,
    (Sequences.Accumulation.differenceResult_refines blocks).2] using h

theorem differenceCollapse_correct (blocks : List (List Int)) :
    Sequences.Accumulation.CollapseSpec [] blocks (differenceCollapse blocks).1 := by
  rw [differenceCollapse_value]
  exact Sequences.Accumulation.collapseDifference_correct blocks

theorem difference_materialization_work (blocks : List (List Int)) :
    (applyFunction (build blocks).history []).2 =
      2 * (build blocks).used.flatten.length + (build blocks).used.length := by
  rw [applyFunction_work, historyValue, build_history_blocks, build_history_length]

theorem differenceCollapse_work_le_used (blocks : List (List Int)) :
    (differenceCollapse blocks).2 ≤
      4 * (build blocks).used.flatten.length + 15 * (build blocks).used.length + 4 := by
  have h := build_overhead_le blocks
  simp only [differenceCollapse, difference_materialization_work]
  omega

theorem differenceCollapse_work_ge_used (blocks : List (List Int)) :
    2 * (build blocks).used.flatten.length + (build blocks).used.length + 1 ≤
      (differenceCollapse blocks).2 := by
  have ht := buildAux_tests 0 [] blocks
  change (build blocks).tests = (build blocks).used.length + 1 at ht
  simp only [differenceCollapse, difference_materialization_work, overhead]
  omega

theorem used_size_le (blocks : List (List Int)) :
    (build blocks).used.length ≤ blocks.length ∧
      (build blocks).used.flatten.length ≤ blocks.flatten.length := by
  obtain ⟨suffix, hp⟩ := CollapseDemand.cachedAux_used_prefix 0 [] blocks
  have hl := congrArg List.length hp
  simp only [List.length_append] at hl
  have hn := congrArg (fun xss : List (List Int) => xss.flatten.length) hp
  simp only [List.flatten_append, List.length_append] at hn
  rw [build_used]
  change (CollapseDemand.cachedAux 0 [] (CollapseDemand.lazyLabels blocks)).used.length ≤ _ ∧
    (CollapseDemand.cachedAux 0 [] (CollapseDemand.lazyLabels blocks)).used.flatten.length ≤ _
  omega

theorem differenceCollapse_work_le (blocks : List (List Int)) :
    (differenceCollapse blocks).2 ≤ 4 * blocks.flatten.length + 15 * blocks.length + 4 := by
  have h := differenceCollapse_work_le_used blocks
  have hsz := used_size_le blocks
  omega

theorem leftCollapse_work_le_used (blocks : List (List Int)) :
    (leftCollapse blocks).2 ≤
      2 * (build blocks).used.flatten.length + 14 * (build blocks).used.length + 4 +
        (build blocks).used.length * (2 * (build blocks).used.flatten.length + 1) := by
  have h := build_overhead_le blocks
  have ha := leftMaterialize_work_le (build blocks).history
  rw [historyValue, build_history_blocks, build_history_length] at ha
  simp only [leftCollapse]
  omega

theorem leftCollapse_work_le (blocks : List (List Int)) :
    (leftCollapse blocks).2 ≤
      2 * blocks.flatten.length + 14 * blocks.length + 4 +
        blocks.length * (2 * blocks.flatten.length + 1) := by
  have h := leftCollapse_work_le_used blocks
  have hsz := used_size_le blocks
  have hm := Nat.mul_le_mul hsz.1
    (show 2 * (build blocks).used.flatten.length + 1 ≤ 2 * blocks.flatten.length + 1 by omega)
  omega

theorem build_first_positive (block : List Int) (suffix : List (List Int))
    (h : 0 < block.sum) :
    build (block :: suffix) =
      ⟨[block], [block], 2 * block.length + 1, 7, 3, 2, 1⟩ := by
  rw [build, buildAux]
  simp only [Int.lt_irrefl, ↓reduceIte, labelStep_cons, Steepness.sumRun_value,
    Steepness.sumRun_work, Int.zero_add]
  rw [buildAux_positive _ _ _ h]
  rfl

theorem difference_first_positive (block : List Int) (suffix : List (List Int))
    (h : 0 < block.sum) :
    differenceCollapse (block :: suffix) = (block, 4 * block.length + 16) := by
  simp [differenceCollapse, build_first_positive block suffix h,
    applyFunction_value, applyFunction_work, historyValue, overhead]
  omega

theorem left_first_positive (block : List Int) (suffix : List (List Int))
    (h : 0 < block.sum) :
    leftCollapse (block :: suffix) = (block, 2 * block.length + 16) := by
  simp only [leftCollapse, build_first_positive block suffix h, leftMaterialize,
    appendRun_exact, List.nil_append, List.length_nil, overhead]

theorem history_singleton_value_length (history : List (List Int))
    (h : ∀ block ∈ history, block = [0]) :
    (historyValue history).length = history.length := by
  induction history with
  | nil => rfl
  | cons block previous ih =>
      have hb := h block (by simp)
      have hp : ∀ b ∈ previous, b = [0] := fun b hm => h b (by simp [hm])
      have hi := ih hp
      change previous.reverse.flatten.length = previous.length at hi
      simp [historyValue, List.reverse_cons, hb, hi]

theorem leftMaterialize_singleton_work (history : List (List Int))
    (h : ∀ block ∈ history, block = [0]) :
    (leftMaterialize history).2 = history.length * history.length := by
  induction history with
  | nil => rfl
  | cons block previous ih =>
      have hp : ∀ b ∈ previous, b = [0] := fun b hm => h b (by simp [hm])
      simp only [leftMaterialize, appendRun_work, leftMaterialize_value,
        ih hp, history_singleton_value_length previous hp, List.length_cons]
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
      omega

theorem build_zeroBlocks_used (n : Nat) :
    (build (List.replicate n [0])).used = List.replicate n [0] := by
  rw [build_used]
  exact CollapseDemand.cachedAux_zeroBlocks_used n [] (by simp)

theorem left_zeroBlocks_materialization (n : Nat) :
    (leftMaterialize (build (List.replicate n [0])).history).2 = n * n := by
  have hb : (build (List.replicate n [0])).history.reverse = List.replicate n [0] := by
    rw [build_history_blocks, build_zeroBlocks_used]
  have hl : (build (List.replicate n [0])).history.length = n := by
    simpa using congrArg List.length hb
  have h := leftMaterialize_singleton_work (build (List.replicate n [0])).history
    (by
      intro b hm
      have hr : b ∈ (build (List.replicate n [0])).history.reverse := by simpa using hm
      rw [hb] at hr
      exact (List.mem_replicate.mp hr).2)
  simpa [hl] using h

theorem left_quadratic_work_witness (n : Nat) :
    ∃ blocks : List (List Int), blocks.length = n ∧ blocks.flatten.length = n ∧
      n * n ≤ (leftCollapse blocks).2 ∧ (differenceCollapse blocks).2 ≤ 19 * n + 4 := by
  have hn : (List.replicate n [(0 : Int)]).flatten.length = n := by
    induction n <;> simp_all [List.replicate_succ]
  refine ⟨List.replicate n [0], by simp, hn, ?_, ?_⟩
  · simp only [leftCollapse, left_zeroBlocks_materialization]
    omega
  · have h := differenceCollapse_work_le (List.replicate n [0])
    simp only [hn, List.length_replicate] at h
    omega

theorem produced_length_le (blocks : List (List Int)) :
    (Sequences.Accumulation.collapse blocks).length ≤ blocks.flatten.length := by
  have hv := buildAux_value 0 [] blocks
  change historyValue (build blocks).history = (CollapseDemand.cached blocks).value at hv
  rw [CollapseDemand.cached_value, (Sequences.Accumulation.cachedResult_refines blocks).2] at hv
  rw [← hv, historyValue, build_history_blocks]
  exact (used_size_le blocks).2

def leftSquare : Squares.Square ⟨List (List Int), List (List Int), id⟩
    ⟨Measured (List Int) Nat, List Int, Prod.fst⟩ :=
  erasureSquare leftCollapse Sequences.Accumulation.collapse
    (fun blocks => (leftCollapse_value blocks).trans
      (Sequences.Accumulation.cachedResult_refines blocks).2)

def differenceSquare : Squares.Square ⟨List (List Int), List (List Int), id⟩
    ⟨Measured (List Int) Nat, List Int, Prod.fst⟩ :=
  erasureSquare differenceCollapse Sequences.Accumulation.collapse
    (fun blocks => (differenceCollapse_value blocks).trans
      (Sequences.Accumulation.differenceResult_refines blocks).2)

end Resources.CollapseMaterialization
