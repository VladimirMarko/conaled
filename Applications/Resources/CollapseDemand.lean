import Applications.Resources.Steepness
import Applications.Sequences.Accumulation

/-!
# Collapse: demanded sums and short-circuit guards

Adapted from checkpoint-335 Chapter01/CollapseDemand.lean; see
`docs/research/adwh-collapse-resources.md` for exact provenance and statement
review. The source on printed pp14-15 tests the accumulated total before observing the
remaining block spine. This model keeps that order, including the final test
when no blocks remain. `lazyLabels` is the literal zip of mapped sum thunks and
the blocks: the thunk is forced only when that block is consumed. The measured
sum work comes from the value-producing `Steepness.sumRun` executor.

The report records selected sum work, scalar additions, comparisons, and outer
spine cases separately. Constructing labels, lazy append materialization, integer
bit complexity, and machine runtime are not charged by this module. In
particular, no work is attributed to the sum of a discarded suffix block.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.CollapseDemand

abbrev Label := (Unit → Measured Int Nat) × List Int

/-- The exact `zip (map sum blocks) blocks` shape with delayed sum components. -/
def lazyLabels (blocks : List (List Int)) : List Label :=
  (blocks.map (fun block => fun (_ : Unit) => Steepness.sumRun block)).zip blocks

theorem lazyLabels_eq_map (blocks : List (List Int)) :
    lazyLabels blocks =
      blocks.map (fun block => ((fun (_ : Unit) => Steepness.sumRun block), block)) := by
  induction blocks <;> simp_all [lazyLabels]

def eagerLabels (labels : List Label) : List (List Int × Multiplicative Int) :=
  labels.map (fun p => (p.2, Multiplicative.ofAdd (p.1 ()).1))

theorem eagerLabels_lazyLabels (blocks : List (List Int)) :
    eagerLabels (lazyLabels blocks) = Sequences.Accumulation.labelSums blocks := by
  induction blocks <;>
    simp_all [eagerLabels, lazyLabels, Sequences.Accumulation.labelSums,
      Steepness.sumRun_value]

/-- Finite demand trace; list-valued fields describe observations, not extra
charged runtime allocations. The counters use the explicit model above. -/
structure Run where
  value : List Int
  used : List (List Int)
  sumInputs : List (List Int)
  sumWork : Nat
  scalarAdds : Nat
  tests : Nat
  spineCases : Nat
  deriving Repr, DecidableEq

/-- The total is demanded before the remaining input is inspected. -/
def plainAux (acc : List Int) (blocks : List (List Int)) : Run :=
  let s := Steepness.sumRun acc
  if 0 < s.1 then
    ⟨acc, [], [acc], s.2, 0, 1, 0⟩
  else
    match blocks with
    | [] => ⟨acc, [], [acc], s.2, 0, 1, 1⟩
    | block :: rest =>
        let r := plainAux (acc ++ block) rest
        ⟨r.value, block :: r.used, acc :: r.sumInputs,
          s.2 + r.sumWork, 0, 1 + r.tests, 1 + r.spineCases⟩

/-- A selected label sum is forced once; later labels retain their thunks. -/
def cachedAux (s : Int) (acc : List Int) (labels : List Label) : Run :=
  if 0 < s then
    ⟨acc, [], [], 0, 0, 1, 0⟩
  else
    match labels with
    | [] => ⟨acc, [], [], 0, 0, 1, 1⟩
    | p :: rest =>
        let t := p.1 ()
        let r := cachedAux (s + t.1) (acc ++ p.2) rest
        ⟨r.value, p.2 :: r.used, p.2 :: r.sumInputs,
          t.2 + r.sumWork, 1 + r.scalarAdds, 1 + r.tests, 1 + r.spineCases⟩

def plain (blocks : List (List Int)) : Run := plainAux [] blocks

def cached (blocks : List (List Int)) : Run := cachedAux 0 [] (lazyLabels blocks)

theorem plainAux_value (acc : List Int) (blocks : List (List Int)) :
    (plainAux acc blocks).value = Sequences.Accumulation.collapseAux acc blocks := by
  induction blocks generalizing acc with
  | nil => simp [plainAux, Sequences.Accumulation.collapseAux]; split <;> rfl
  | cons block rest ih =>
      simp only [plainAux, Steepness.sumRun_value, Sequences.Accumulation.collapseAux]
      split <;> simp_all

theorem cachedAux_value (s : Int) (acc : List Int) (labels : List Label) :
    (cachedAux s acc labels).value =
      (Sequences.Accumulation.cachedRun List.append (acc, Multiplicative.ofAdd s)
        (eagerLabels labels)).1 := by
  induction labels generalizing s acc with
  | nil =>
      simp [cachedAux, eagerLabels, Sequences.Accumulation.cachedRun,
        SquareKit.GuardedFold.run]
      split <;> rfl
  | cons p rest ih =>
      simp only [cachedAux, eagerLabels, List.map_cons,
        Sequences.Accumulation.cachedRun, SquareKit.GuardedFold.run,
        Sequences.OrderedSummary.appendCache]
      by_cases h : 0 < s
      · simp [h]
      · simpa [h, Sequences.Accumulation.cachedRun, eagerLabels] using
          ih (s + (p.1 ()).1) (acc ++ p.2)

theorem plain_value (blocks : List (List Int)) :
    (plain blocks).value = Sequences.Accumulation.collapse blocks := plainAux_value [] blocks

theorem cached_value (blocks : List (List Int)) :
    (cached blocks).value = Sequences.Accumulation.collapseCached blocks := by
  simp only [cached, cachedAux_value, eagerLabels_lazyLabels,
    Sequences.Accumulation.collapseCached, Sequences.Accumulation.cachedResult]
  rfl

theorem values_equal (blocks : List (List Int)) :
    (cached blocks).value = (plain blocks).value := by
  rw [cached_value, plain_value, (Sequences.Accumulation.cachedResult_refines blocks).2]

theorem cached_correct (blocks : List (List Int)) :
    Sequences.Accumulation.CollapseSpec [] blocks (cached blocks).value := by
  rw [cached_value]
  exact Sequences.Accumulation.collapseCached_correct blocks

theorem plainAux_value_shape (acc : List Int) (blocks : List (List Int)) :
    (plainAux acc blocks).value = acc ++ (plainAux acc blocks).used.flatten := by
  induction blocks generalizing acc with
  | nil => simp [plainAux]; split <;> simp
  | cons block rest ih =>
      simp only [plainAux]
      split
      · simp
      · simpa [List.append_assoc] using ih (acc ++ block)

theorem plainAux_used_prefix (acc : List Int) (blocks : List (List Int)) :
    ∃ rest, blocks = (plainAux acc blocks).used ++ rest := by
  induction blocks generalizing acc with
  | nil => simp [plainAux]; split <;> simp
  | cons block rest ih =>
      simp only [plainAux]
      split
      · exact ⟨block :: rest, rfl⟩
      · obtain ⟨suffix, h⟩ := ih (acc ++ block)
        exact ⟨suffix, congrArg (List.cons block) h⟩

theorem plainAux_sumInputs_length (acc : List Int) (blocks : List (List Int)) :
    (plainAux acc blocks).sumInputs.length = (plainAux acc blocks).used.length + 1 := by
  induction blocks generalizing acc with
  | nil => simp [plainAux]; split <;> rfl
  | cons block rest ih =>
      simp only [plainAux]
      split <;> simp_all

theorem plainAux_tests (acc : List Int) (blocks : List (List Int)) :
    (plainAux acc blocks).tests = (plainAux acc blocks).used.length + 1 := by
  induction blocks generalizing acc with
  | nil => simp [plainAux]; split <;> rfl
  | cons block rest ih =>
      simp only [plainAux]
      split <;> simp_all [Nat.add_comm]

theorem plainAux_sumWork (acc : List Int) (blocks : List (List Int)) :
    (plainAux acc blocks).sumWork =
      ((plainAux acc blocks).sumInputs.map (fun xs => 2 * xs.length + 1)).sum := by
  induction blocks generalizing acc with
  | nil => simp [plainAux, Steepness.sumRun_work]; split <;> rfl
  | cons block rest ih =>
      simp only [plainAux]
      split <;> simp_all [Steepness.sumRun_work]

theorem plainAux_sumInputs_le_output (acc : List Int) (blocks : List (List Int)) :
    ∀ xs ∈ (plainAux acc blocks).sumInputs,
      xs.length ≤ (plainAux acc blocks).value.length := by
  induction blocks generalizing acc with
  | nil => simp [plainAux]; split <;> simp
  | cons block rest ih =>
      simp only [plainAux]
      split
      · simp
      · intro xs hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · rw [plainAux_value_shape]
          simp
        · exact ih (acc ++ block) xs hx

theorem sumInputs_work_le (inputs : List (List Int)) (n : Nat)
    (h : ∀ xs ∈ inputs, xs.length ≤ n) :
    (inputs.map (fun xs => 2 * xs.length + 1)).sum ≤ inputs.length * (2 * n + 1) := by
  induction inputs with
  | nil => simp
  | cons xs inputs ih =>
      have hx := h xs (by simp)
      have ht := ih (fun ys hy => h ys (by simp [hy]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul,
        Nat.one_mul]
      omega

theorem plainAux_sumWork_le_output (acc : List Int) (blocks : List (List Int)) :
    (plainAux acc blocks).sumWork ≤
      ((plainAux acc blocks).used.length + 1) *
        (2 * (plainAux acc blocks).value.length + 1) := by
  rw [plainAux_sumWork, ← plainAux_sumInputs_length]
  exact sumInputs_work_le _ _ (plainAux_sumInputs_le_output acc blocks)

theorem plain_sumWork_le (blocks : List (List Int)) :
    (plain blocks).sumWork ≤ (blocks.length + 1) * (2 * blocks.flatten.length + 1) := by
  obtain ⟨suffix, hp⟩ := plainAux_used_prefix [] blocks
  have hl := congrArg List.length hp
  simp only [List.length_append] at hl
  have hn := congrArg (fun xss : List (List Int) => xss.flatten.length) hp
  simp only [List.flatten_append, List.length_append] at hn
  have hu : (plainAux [] blocks).used.length ≤ blocks.length := by
    omega
  have hv : (plainAux [] blocks).value.length ≤ blocks.flatten.length := by
    rw [plainAux_value_shape]
    simp only [List.nil_append]
    omega
  exact Nat.le_trans (plainAux_sumWork_le_output [] blocks)
    (Nat.mul_le_mul (by omega) (by omega))

theorem cachedAux_value_shape (s : Int) (acc : List Int) (labels : List Label) :
    (cachedAux s acc labels).value = acc ++ (cachedAux s acc labels).used.flatten := by
  induction labels generalizing s acc with
  | nil => simp [cachedAux]; split <;> simp
  | cons p rest ih =>
      simp only [cachedAux]
      split
      · simp
      · simpa [List.append_assoc] using ih (s + (p.1 ()).1) (acc ++ p.2)

theorem cachedAux_sumInputs (s : Int) (acc : List Int) (labels : List Label) :
    (cachedAux s acc labels).sumInputs = (cachedAux s acc labels).used := by
  induction labels generalizing s acc with
  | nil => simp [cachedAux]; split <;> rfl
  | cons p rest ih => simp only [cachedAux]; split <;> simp_all

theorem cachedAux_scalarAdds (s : Int) (acc : List Int) (labels : List Label) :
    (cachedAux s acc labels).scalarAdds = (cachedAux s acc labels).used.length := by
  induction labels generalizing s acc with
  | nil => simp [cachedAux]; split <;> rfl
  | cons p rest ih => simp only [cachedAux]; split <;> simp_all [Nat.add_comm]

theorem cachedAux_tests (s : Int) (acc : List Int) (labels : List Label) :
    (cachedAux s acc labels).tests = (cachedAux s acc labels).used.length + 1 := by
  induction labels generalizing s acc with
  | nil => simp [cachedAux]; split <;> rfl
  | cons p rest ih => simp only [cachedAux]; split <;> simp_all [Nat.add_comm]

theorem cachedAux_spineCases_le (s : Int) (acc : List Int) (labels : List Label) :
    (cachedAux s acc labels).spineCases ≤ (cachedAux s acc labels).used.length + 1 := by
  induction labels generalizing s acc with
  | nil => simp [cachedAux]; split <;> simp
  | cons p rest ih =>
      simp only [cachedAux]
      split
      · simp
      · have h := ih (s + (p.1 ()).1) (acc ++ p.2)
        simp only [List.length_cons]
        omega

theorem cachedAux_used_prefix (s : Int) (acc : List Int) (blocks : List (List Int)) :
    ∃ rest, blocks = (cachedAux s acc (lazyLabels blocks)).used ++ rest := by
  induction blocks generalizing s acc with
  | nil => simp [lazyLabels, cachedAux]; split <;> simp
  | cons block rest ih =>
      simp only [lazyLabels_eq_map, List.map_cons, cachedAux]
      split
      · exact ⟨block :: rest, rfl⟩
      · obtain ⟨suffix, h⟩ := ih (s + (Steepness.sumRun block).1) (acc ++ block)
        rw [lazyLabels_eq_map] at h
        exact ⟨suffix, congrArg (List.cons block) h⟩

theorem cachedAux_sumWork (s : Int) (acc : List Int) (blocks : List (List Int)) :
    (cachedAux s acc (lazyLabels blocks)).sumWork =
      2 * (cachedAux s acc (lazyLabels blocks)).used.flatten.length +
        (cachedAux s acc (lazyLabels blocks)).used.length := by
  induction blocks generalizing s acc with
  | nil => simp [lazyLabels, cachedAux]; split <;> rfl
  | cons block rest ih =>
      simp only [lazyLabels_eq_map, List.map_cons, cachedAux]
      split
      · rfl
      · have h := ih (s + (Steepness.sumRun block).1) (acc ++ block)
        rw [lazyLabels_eq_map] at h
        simp only [Steepness.sumRun_work, List.flatten_cons, List.length_append,
          List.length_cons]
        omega

theorem cached_sumWork (blocks : List (List Int)) :
    (cached blocks).sumWork =
      2 * (cached blocks).used.flatten.length + (cached blocks).used.length :=
  cachedAux_sumWork 0 [] blocks

theorem cached_sumWork_le (blocks : List (List Int)) :
    (cached blocks).sumWork ≤ 2 * blocks.flatten.length + blocks.length := by
  obtain ⟨suffix, hp⟩ := cachedAux_used_prefix 0 [] blocks
  have hl := congrArg List.length hp
  simp only [List.length_append] at hl
  have hn := congrArg (fun xss : List (List Int) => xss.flatten.length) hp
  simp only [List.flatten_append, List.length_append] at hn
  rw [cached_sumWork]
  simp only [cached]
  omega

/-- The scalar comparison precedes and can avoid even the outer spine case. -/
theorem cachedAux_positive (s : Int) (acc : List Int) (labels : List Label)
    (h : 0 < s) : cachedAux s acc labels = ⟨acc, [], [], 0, 0, 1, 0⟩ := by
  cases labels <;> simp [cachedAux, h]

theorem plainAux_positive (acc : List Int) (blocks : List (List Int))
    (h : 0 < acc.sum) :
    plainAux acc blocks = ⟨acc, [], [acc], 2 * acc.length + 1, 0, 1, 0⟩ := by
  cases blocks <;> simp [plainAux, Steepness.sumRun_value, Steepness.sumRun_work, h]

/-- In Exercise1.19's best case no event depends on the discarded suffix. -/
theorem cached_first_positive (block : List Int) (suffix : List (List Int))
    (h : 0 < block.sum) :
    cached (block :: suffix) =
      ⟨block, [block], [block], 2 * block.length + 1, 1, 2, 1⟩ := by
  simp only [cached, lazyLabels_eq_map, List.map_cons, cachedAux,
    Int.lt_irrefl, ↓reduceIte, List.nil_append, Steepness.sumRun_value,
    Steepness.sumRun_work, Int.zero_add]
  rw [cachedAux_positive _ _ _ h]
  rfl

theorem plain_first_positive (block : List Int) (suffix : List (List Int))
    (h : 0 < block.sum) :
    plain (block :: suffix) =
      ⟨block, [block], [[], block], 2 * block.length + 2, 0, 2, 1⟩ := by
  simp only [plain, plainAux, Steepness.sumRun_value, List.sum_nil,
    Int.lt_irrefl, ↓reduceIte, List.nil_append, Steepness.sumRun_work, List.length_nil]
  rw [plainAux_positive block suffix h]
  simp [Nat.add_comm]; omega

theorem best_case_same_sum_additions (block : List Int) (suffix : List (List Int))
    (h : 0 < block.sum) :
    ((cached (block :: suffix)).sumInputs.map List.length).sum =
      ((plain (block :: suffix)).sumInputs.map List.length).sum := by
  rw [cached_first_positive block suffix h, plain_first_positive block suffix h]
  simp

theorem cachedAux_used_eq_plain (acc : List Int) (blocks : List (List Int)) :
    (cachedAux acc.sum acc (lazyLabels blocks)).used = (plainAux acc blocks).used := by
  induction blocks generalizing acc with
  | nil => simp [lazyLabels, cachedAux, plainAux, Steepness.sumRun_value]; split <;> rfl
  | cons block rest ih =>
      simp only [lazyLabels_eq_map, List.map_cons, cachedAux, plainAux,
        Steepness.sumRun_value]
      split
      · rfl
      · have h := ih (acc ++ block)
        simpa [lazyLabels_eq_map] using congrArg (List.cons block) h

theorem cached_used_eq_plain (blocks : List (List Int)) :
    (cached blocks).used = (plain blocks).used := cachedAux_used_eq_plain [] blocks

/-- The actual trace witnesses the independent first-positive-prefix condition.
This retains consumed empty blocks, which flattening alone would lose. -/
theorem plainAux_selected (acc : List Int) (blocks : List (List Int)) :
    ∃ remaining, blocks = (plainAux acc blocks).used ++ remaining ∧
      Sequences.Accumulation.NonpositiveBefore acc.sum (plainAux acc blocks).used ∧
      (remaining = [] ∨ 0 < (plainAux acc blocks).value.sum) := by
  induction blocks generalizing acc with
  | nil =>
      rw [plainAux]
      split <;> exact ⟨[], rfl, True.intro, Or.inl rfl⟩
  | cons block blocks ih =>
      rw [plainAux]
      simp only [Steepness.sumRun_value]
      by_cases h : 0 < acc.sum
      · simp only [h, ↓reduceIte]
        exact ⟨block :: blocks, rfl, True.intro, Or.inr True.intro⟩
      · simp only [h, ↓reduceIte]
        obtain ⟨remaining, hb, hn, hs⟩ := ih (acc ++ block)
        refine ⟨remaining, congrArg (List.cons block) hb, ⟨by omega, ?_⟩, hs⟩
        simpa only [List.sum_append] using hn

theorem cached_selected (blocks : List (List Int)) :
    ∃ remaining, blocks = (cached blocks).used ++ remaining ∧
      Sequences.Accumulation.NonpositiveBefore 0 (cached blocks).used ∧
      (remaining = [] ∨ 0 < (cached blocks).value.sum) := by
  have h := plainAux_selected [] blocks
  change ∃ remaining, blocks = (plain blocks).used ++ remaining ∧
    Sequences.Accumulation.NonpositiveBefore 0 (plain blocks).used ∧
    (remaining = [] ∨ 0 < (plain blocks).value.sum) at h
  simpa only [cached_used_eq_plain, values_equal] using h

/-- All-zero singleton blocks reach every test, including the terminal one. -/
theorem plainAux_zeroBlocks_work (n : Nat) (acc : List Int) (h : acc.sum ≤ 0) :
    (plainAux acc (List.replicate n [0])).sumWork =
      (n + 1) * (2 * acc.length + n + 1) := by
  induction n generalizing acc with
  | zero =>
      have hn : ¬ 0 < acc.sum := by omega
      simp [plainAux, Steepness.sumRun_value, Steepness.sumRun_work, hn]
  | succ n ih =>
      have hn : ¬ 0 < acc.sum := by omega
      have ht : (acc ++ [0]).sum ≤ 0 := by simpa using h
      have hw := ih (acc ++ [0]) ht
      simp only [List.replicate_succ, plainAux, Steepness.sumRun_value,
        hn, ↓reduceIte, Steepness.sumRun_work, hw, List.length_append,
        List.length_cons, List.length_nil] at *
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul,
        Nat.mul_zero] at *
      omega

theorem plain_zeroBlocks_work (n : Nat) :
    (plain (List.replicate n [0])).sumWork = (n + 1) * (n + 1) := by
  simpa [plain] using plainAux_zeroBlocks_work n [] (by simp)

theorem cachedAux_zeroBlocks_used (n : Nat) (acc : List Int) (h : acc.sum ≤ 0) :
    (cachedAux acc.sum acc (lazyLabels (List.replicate n [0]))).used =
      List.replicate n [0] := by
  induction n generalizing acc with
  | zero => simp [lazyLabels, cachedAux]; split <;> rfl
  | succ n ih =>
      have hn : ¬ 0 < acc.sum := by omega
      have ht : (acc ++ [0]).sum ≤ 0 := by simpa using h
      have hu := ih (acc ++ [0]) ht
      simp only [List.replicate_succ, lazyLabels_eq_map, List.map_cons,
        cachedAux, hn, ↓reduceIte, Steepness.sumRun_value, List.sum_cons,
        List.sum_nil, Int.add_zero]
      simpa [lazyLabels_eq_map] using congrArg (List.cons [0]) hu

theorem cached_zeroBlocks_work (n : Nat) :
    (cached (List.replicate n [0])).sumWork = 3 * n := by
  rw [cached_sumWork]
  have hu := cachedAux_zeroBlocks_used n [] (by simp)
  change (cached (List.replicate n [0])).used = List.replicate n [0] at hu
  have hf : (List.replicate n [(0 : Int)]).flatten.length = n := by
    induction n <;> simp_all [List.replicate_succ]
  rw [hu, hf, List.length_replicate]
  omega

theorem quadratic_sum_work_witness (n : Nat) :
    ∃ blocks : List (List Int), blocks.length = n ∧ blocks.flatten.length = n ∧
      n * n ≤ (plain blocks).sumWork ∧ (cached blocks).sumWork = 3 * n := by
  refine ⟨List.replicate n [0], by simp, ?_, ?_, cached_zeroBlocks_work n⟩
  · induction n <;> simp_all [List.replicate_succ]
  · rw [plain_zeroBlocks_work]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

end Resources.CollapseDemand
