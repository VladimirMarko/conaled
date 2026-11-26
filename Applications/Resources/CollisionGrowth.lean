import Applications.Resources.Growth
import Applications.Resources.CollisionHistory
import Applications.Resources.CollisionRedBlack
import Applications.Resources.PositiveTrie
import Applications.Numerals.PositiveArithmetic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

/-!
# Independent parameters and bounded-key collision growth

Natural keys use the half-open interval `0 ≤ key < 2 * n`. The shifted positive
encoding has numeric value `key + 1`. These numerical bounds account for that
offset, but do not assign a cost to constructing the encoding. Real asymptotic
statements are consequences of explicit natural operation-count bounds.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.CollisionGrowth

open Numerals.PositiveKeys Numerals.PositiveArithmetic

/-- A positive small-size correction for both encoded-key length plus its
constant dispatch and the balanced-tree distinct-key logarithm. -/
def logScale (n : Nat) : Nat := 2 + (2 * n + 1).log2

theorem logScale_ge_two (n : Nat) : 2 ≤ logScale n := by
  simp only [logScale]
  omega

/-- The exact shifted value is used before bounding the key length. -/
theorem encoded_bitLength_le (n key : Nat) (bound : key < 2 * n) :
    bitLength (encode key) + 1 ≤ logScale n := by
  rw [bitLength_eq_log2, numeric_encode]
  have monotone : (key + 1).log2 ≤ (2 * n + 1).log2 := by
    simp only [Nat.log2_eq_log_two]
    exact Nat.log_mono_right (by omega)
  dsimp [logScale]
  omega

/-- Signed magnitude uses the same corrected scale. The positive encoding of
the absolute magnitude is a mathematical size bound, not a conversion run. -/
theorem bZ_add_one_le_logScale (n : Nat) (key : ZNum)
    (bound : Int.natAbs (key : Int) < 2 * n) :
    CollisionHistory.bZ key + 1 ≤ logScale n := by
  have length : CollisionHistory.bZ key ≤ bitLength (encode (Int.natAbs (key : Int))) := by
    apply max_le
    · exact bitLength_pos _
    · rw [bitLength_eq_size, numeric_encode]
      exact Nat.size_le_size (Nat.le_succ _)
  exact (Nat.add_le_add_right length 1).trans (encoded_bitLength_le n _ bound)

theorem natCast_signed_bitLength_le (n key : Nat) (bound : key < 2 * n) :
    CollisionHistory.bZ (key : ZNum) + 1 ≤ logScale n := by
  apply bZ_add_one_le_logScale n (key : ZNum)
  simpa only [ZNum.of_natCast, Int.natAbs_natCast] using bound

theorem natCast_signed_injective : Function.Injective (fun n : Nat => (n : ZNum)) := by
  intro m n same
  have observed := congrArg (fun z : ZNum => (z : Int)) same
  simpa only [ZNum.of_natCast, Int.natCast_inj] using observed

/-- Distinct keys may be fewer than input occurrences; the two quantities are
kept separate until this explicit upper-bound specialization. -/
theorem distinct_log_le (n distinct : Nat) (bound : distinct ≤ n) :
    1 + (distinct + 1).log2 ≤ logScale n := by
  have monotone : (distinct + 1).log2 ≤ (2 * n + 1).log2 := by
    simp only [Nat.log2_eq_log_two]
    exact Nat.log_mono_right (by omega)
  dsimp [logScale]
  omega

/-- A single logarithmic factor controls the corrected natural logarithm from
index two. No assertion involving `log 0` is used in an operation bound. -/
theorem logScale_cast_le (n : Nat) (large : 2 ≤ n) :
    (logScale n : ℝ) ≤ 5 * Real.logb 2 n := by
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast large
  have positive : (0 : ℝ) < n := by linarith
  have one : (1 : ℝ) ≤ Real.logb 2 n := by
    calc
      1 = Real.logb 2 (2 : ℝ) := (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ Real.logb 2 n := Real.logb_le_logb_of_le (by norm_num) (by norm_num) hn
  have floor := Real.log2_le_logb (2 * n + 1)
  have enlarge : Real.logb 2 ((2 * n + 1 : Nat) : ℝ) ≤
      Real.logb 2 (4 * (n : ℝ)) := by
    apply Real.logb_le_logb_of_le (by norm_num)
    · positivity
    · push_cast
      linarith
  have product : Real.logb 2 (4 * (n : ℝ)) = 2 + Real.logb 2 n := by
    rw [Real.logb_mul (by norm_num) (ne_of_gt positive)]
    have four : Real.logb 2 (4 : ℝ) = 2 := by
      calc
        Real.logb 2 (4 : ℝ) = Real.logb 2 ((2 : ℝ) ^ 2) := by norm_num
        _ = 2 := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; norm_num
    rw [four]
  dsimp [logScale]
  push_cast
  linarith

/-- An explicit corrected polynomial/logarithmic operation bound gives the
ordinary real asymptotic statement. The exponents identify which source stage
is being instantiated; its measured-program bound remains a separate premise. -/
theorem isBigO_of_scale_bound (work : Nat → Nat) (coefficient start power logs : Nat)
    (bound : ∀ n, start ≤ n →
      work n ≤ coefficient * ((n + 1) ^ power * logScale n ^ logs)) :
    Asymptotics.IsBigO Filter.atTop (fun n => (work n : ℝ))
      (fun n => (n : ℝ) ^ power * Real.logb 2 n ^ logs) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨(coefficient : ℝ) * (2 ^ power * 5 ^ logs),
    Filter.eventually_atTop.mpr ⟨max start 2, fun n hn => ?_⟩⟩
  have hstart : start ≤ n := (Nat.le_max_left _ _).trans hn
  have htwo : 2 ≤ n := (Nat.le_max_right _ _).trans hn
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast htwo
  have hp : ((n + 1 : Nat) : ℝ) ≤ 2 * (n : ℝ) := by
    push_cast
    linarith
  have hl := logScale_cast_le n htwo
  have hlog : 0 ≤ Real.logb 2 n :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n by omega))
  have bp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((n + 1 : Nat) : ℝ)) hp power
  have bl := pow_le_pow_left₀ (Nat.cast_nonneg (logScale n)) hl logs
  have castBound : (work n : ℝ) ≤
      (coefficient : ℝ) * ((((n + 1 : Nat) : ℝ) ^ power) * (logScale n : ℝ) ^ logs) := by
    exact_mod_cast bound n hstart
  rw [Real.norm_natCast, Real.norm_of_nonneg (mul_nonneg (by positivity) (pow_nonneg hlog _))]
  calc
    (work n : ℝ) ≤
        (coefficient : ℝ) * ((((n + 1 : Nat) : ℝ) ^ power) * (logScale n : ℝ) ^ logs) := castBound
    _ ≤ (coefficient : ℝ) * ((2 * (n : ℝ)) ^ power * (5 * Real.logb 2 n) ^ logs) :=
      mul_le_mul_of_nonneg_left (mul_le_mul bp bl (by positivity) (by positivity))
        (Nat.cast_nonneg coefficient)
    _ = (coefficient : ℝ) * (2 ^ power * 5 ^ logs) *
        ((n : ℝ) ^ power * Real.logb 2 n ^ logs) := by
      simp only [mul_pow]
      ring

/-- The textbook's distinct interval supplies this finite lower expression.
The estimate is retained separately from the proof that a measured family
actually incurs it; arbitrary inputs are not asserted to have cubic cost. -/
theorem cubic_le_four_lower (n : Nat) (large : 2 ≤ n) :
    n ^ 3 ≤ 4 * ((n + 1) * n * (n - 1) / 2) := by
  have pred : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have remainder := Nat.mod_add_div ((n + 1) * n * (n - 1)) 2
  have remainder_lt := Nat.mod_lt ((n + 1) * n * (n - 1)) (by decide : 0 < 2)
  have square : 4 ≤ n * n := Nat.mul_le_mul large large
  have cube := Nat.mul_le_mul_right n square
  have product : (n + 1) * n * (n - 1) + n = n ^ 3 := by
    nlinarith
  nlinarith

/-- A proved interval-family lower bound yields the reverse asymptotic bound.
Together with that same family's cubic upper bound this is a tight-family
statement, not a universal lower bound for every workload. -/
theorem cubic_isBigO_of_lower (work : Nat → Nat)
    (lower : ∀ n, (n + 1) * n * (n - 1) / 2 ≤ work n) :
    Asymptotics.IsBigO Filter.atTop (fun n : Nat => (n : ℝ) ^ 3) (fun n => (work n : ℝ)) := by
  have estimate := Resources.isBigO_of_nat_bound (fun n => n ^ 3) work 4 2
    (fun n hn => (cubic_le_four_lower n hn).trans (Nat.mul_le_mul_left 4 (lower n)))
  simpa only [Nat.cast_pow] using estimate

/-- Work of the actual unary-equality update history, including its literal
first-operand-recursive `counter + 1` and all separately observed overhead. -/
def unaryWork (keys : List Nat) : Nat := CollisionHistory.total (CollisionHistory.unaryRun keys).2

theorem unaryWork_bound (n : Nat) (keys : List Nat) (length : keys.length ≤ n)
    (keyBound : ∀ key ∈ keys, key < 2 * n) :
    unaryWork keys ≤ 4 * (n + 1) ^ 3 := by
  have distinct : keys.toFinset.card ≤ n := keys.toFinset_card_le.trans length
  have bound := CollisionHistory.unaryRun_total_le keys (2 * n)
    (fun key inside => Nat.le_of_lt (keyBound key inside))
  have pair := Nat.mul_le_mul length distinct
  have comparisons := Nat.mul_le_mul_right (2 * n + 1) pair
  have counter := Nat.mul_le_mul length (Nat.add_le_add_right length 1)
  have linear := Nat.mul_le_mul_left 4 length
  have nonnegative := Nat.zero_le (n ^ 3)
  dsimp [unaryWork]
  nlinarith

theorem unary_isBigO (inputs : Nat → List Nat)
    (length : ∀ n, (inputs n).length ≤ n)
    (keyBound : ∀ n key, key ∈ inputs n → key < 2 * n) :
    Asymptotics.IsBigO Filter.atTop (fun n => (unaryWork (inputs n) : ℝ))
      (fun n => (n : ℝ) ^ 3) := by
  have bound := isBigO_of_scale_bound (fun n => unaryWork (inputs n)) 4 0 3 0
    (fun n _ => by simpa only [pow_zero, mul_one] using
      unaryWork_bound n (inputs n) (length n) (keyBound n))
  simpa only [pow_zero, mul_one] using bound

/-- The signed-binary history on already represented natural-key values.
Input conversion is not an operation of the measured collision client. -/
def signedHistoryWork (keys : List Nat) : Nat :=
  CollisionHistory.total
    (CollisionHistory.signedRun (keys.map (fun key : Nat => (key : ZNum)))).2

theorem signedHistoryWork_bound (n : Nat) (keys : List Nat) (length : keys.length ≤ n)
    (keyBound : ∀ key ∈ keys, key < 2 * n) :
    signedHistoryWork keys ≤ 8 * ((n + 1) ^ 2 * logScale n) := by
  let signed := keys.map (fun key : Nat => (key : ZNum))
  have bits : ∀ key ∈ signed, CollisionHistory.bZ key ≤ logScale n := by
    intro key member
    obtain ⟨natural, inside, rfl⟩ := List.mem_map.mp member
    have bound := natCast_signed_bitLength_le n natural (keyBound natural inside)
    omega
  have size : signed.length ≤ n := by simpa only [signed, List.length_map] using length
  have distinct : signed.toFinset.card ≤ n := signed.toFinset_card_le.trans size
  have scale := logScale_ge_two n
  have one : 1 ≤ logScale n := by omega
  have pair := Nat.mul_le_mul size distinct
  have comparisons := Nat.mul_le_mul pair (show logScale n + 1 ≤ 2 * logScale n by omega)
  have tests := Nat.mul_le_mul_left (n * n) one
  have linear := Nat.mul_le_mul size one
  have polynomial : 5 * n * n + 6 * n + 1 ≤ 8 * (n + 1) ^ 2 := by nlinarith
  have scaled := Nat.mul_le_mul_right (logScale n) polynomial
  have bound := CollisionHistory.signedRun_total_le signed (logScale n) bits
  dsimp [signedHistoryWork]
  change CollisionHistory.total (CollisionHistory.signedRun signed).2 ≤ _
  nlinarith

theorem signedHistoryWork_isBigO (inputs : Nat → List Nat)
    (length : ∀ n, (inputs n).length ≤ n)
    (keyBound : ∀ n key, key ∈ inputs n → key < 2 * n) :
    Asymptotics.IsBigO Filter.atTop (fun n => (signedHistoryWork (inputs n) : ℝ))
      (fun n => (n : ℝ) ^ 2 * Real.logb 2 n) := by
  have bound := isBigO_of_scale_bound (fun n => signedHistoryWork (inputs n)) 8 0 2 1
    (fun n _ => by simpa only [pow_one] using
      signedHistoryWork_bound n (inputs n) (length n) (keyBound n))
  simpa only [pow_one] using bound

/-- A family of already represented signed keys, indexed by natural values.
The map specifies the input values; its conversion work is outside the counted
collision run. -/
def redBlackWork (keys : List Nat) : Nat :=
  CollisionRedBlack.totalWork (fun _ => 1)
    (CollisionRedBlack.signedCollisions (keys.map (fun key : Nat => (key : ZNum)))).2

/-- Half-open bounded natural keys supply both binary magnitude and distinct
cardinality bounds. The actual operation bound includes all counter work. -/
theorem redBlackWork_bound (n : Nat) (keys : List Nat) (length : keys.length ≤ n)
    (keyBound : ∀ key ∈ keys, key < 2 * n) :
    redBlackWork keys ≤ 180 * ((n + 1) * logScale n ^ 2) := by
  let signed := keys.map (fun key : Nat => (key : ZNum))
  have bits : ∀ key ∈ signed, CollisionHistory.bZ key ≤ logScale n := by
    intro key member
    obtain ⟨natural, inside, rfl⟩ := List.mem_map.mp member
    have bound := natCast_signed_bitLength_le n natural (keyBound natural inside)
    omega
  have size : signed.length ≤ n := by simpa only [signed, List.length_map] using length
  have distinct := signed.toFinset_card_le.trans size
  have logarithm := distinct_log_le n signed.toFinset.card distinct
  have scale := logScale_ge_two n
  have bound := CollisionRedBlack.signedCollisions_totalWork_majorant signed (logScale n) bits
  have first := Nat.mul_le_mul_right
    (90 * (logScale n + 1) * (1 + (signed.toFinset.card + 1).log2)) (Nat.add_le_add_right size 1)
  have second := Nat.mul_le_mul_left (90 * (n + 1) * (logScale n + 1)) logarithm
  have third := Nat.mul_le_mul_left (90 * (n + 1) * logScale n)
    (show logScale n + 1 ≤ 2 * logScale n by omega)
  dsimp [redBlackWork]
  change CollisionRedBlack.totalWork (fun _ => 1) (CollisionRedBlack.signedCollisions signed).2 ≤ _
  nlinarith

theorem redBlackWork_isBigO (inputs : Nat → List Nat)
    (length : ∀ n, (inputs n).length ≤ n)
    (keyBound : ∀ n key, key ∈ inputs n → key < 2 * n) :
    Asymptotics.IsBigO Filter.atTop (fun n => (redBlackWork (inputs n) : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n ^ 2) := by
  have bound := isBigO_of_scale_bound (fun n => redBlackWork (inputs n)) 180 0 1 2
    (fun n _ => by simpa only [pow_one] using redBlackWork_bound n (inputs n) (length n) (keyBound n))
  simpa only [pow_one] using bound

/-- Actual native-positive trie work. The shifted encoding specifies the
represented input; constructing it is outside this work observation. -/
def trieWork (keys : List Nat) : Nat :=
  PositiveTrie.totalWork (PositiveTrie.collisionsRun (keys.map encode)).2

theorem trieWork_bound (n : Nat) (keys : List Nat) (length : keys.length ≤ n)
    (keyBound : ∀ key ∈ keys, key < 2 * n) :
    trieWork keys ≤ 6 * ((n + 1) * logScale n) := by
  have bits : ∀ key ∈ keys.map encode, bitLength key ≤ logScale n := by
    intro key member
    obtain ⟨natural, inside, rfl⟩ := List.mem_map.mp member
    have bound := encoded_bitLength_le n natural (keyBound natural inside)
    omega
  have bound := PositiveTrie.collisionsRun_totalWork_le_of_bitLength_le
    (keys.map encode) (logScale n) bits
  simp only [List.length_map] at bound
  have scale := logScale_ge_two n
  have product := Nat.mul_le_mul length (show logScale n + 1 ≤ 2 * logScale n by omega)
  dsimp [trieWork]
  nlinarith

theorem trie_isBigO (inputs : Nat → List Nat)
    (length : ∀ n, (inputs n).length ≤ n)
    (keyBound : ∀ n key, key ∈ inputs n → key < 2 * n) :
    Asymptotics.IsBigO Filter.atTop (fun n => (trieWork (inputs n) : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n) := by
  have bound := isBigO_of_scale_bound (fun n => trieWork (inputs n)) 6 0 1 1
    (fun n _ => by simpa only [pow_one] using
      trieWork_bound n (inputs n) (length n) (keyBound n))
  simpa only [pow_one] using bound

/-- All four measured clients compute the same independent repetition count
after their stated injective input observations. Their costs remain distinct. -/
theorem represented_counts (keys : List Nat) :
    (CollisionHistory.unaryRun keys).1.1 = Search.Collisions.count keys ∧
    ((CollisionHistory.signedRun (keys.map (fun key : Nat => (key : ZNum)))).1.1 : Nat) =
      Search.Collisions.count keys ∧
    ((CollisionRedBlack.signedCollisions (keys.map (fun key : Nat => (key : ZNum)))).1.1 : Nat) =
      Search.Collisions.count keys ∧
    (PositiveTrie.collisionsRun (keys.map encode)).1 = Search.Collisions.count keys := by
  refine ⟨CollisionHistory.unaryRun_count keys, ?_, ?_, ?_⟩
  · rw [CollisionHistory.signedRun_count]
    exact Search.Collisions.count_map _ natCast_signed_injective keys
  · rw [CollisionRedBlack.signedCollisions_correct]
    exact Search.Collisions.count_map _ natCast_signed_injective keys
  · rw [PositiveTrie.collisionsRun_value]
    exact Search.Collisions.count_map _ encode_injective keys

/-- The distinct source lower family obeys the same half-open key contract,
including its empty index. -/
theorem interval_key_bound (n key : Nat) (member : key ∈ List.range' n n) :
    key < 2 * n := by
  obtain ⟨index, before, value⟩ := List.mem_range'.mp member
  omega

theorem unary_interval_bounds (n : Nat) :
    (n + 1) * n * (n - 1) / 2 ≤ unaryWork (List.range' n n) ∧
      unaryWork (List.range' n n) ≤ 4 * (n + 1) ^ 3 := by
  refine ⟨CollisionHistory.unaryRun_interval_lower n, ?_⟩
  exact unaryWork_bound n (List.range' n n) (by simp) (interval_key_bound n)

/-- Tight cubic work on this explicit distinct interval family. Other input
families, and the other three realizations, are not given this lower bound. -/
theorem unary_interval_isTheta :
    Asymptotics.IsTheta Filter.atTop
      (fun n : Nat => (unaryWork (List.range' n n) : ℝ)) (fun n => (n : ℝ) ^ 3) := by
  refine ⟨unary_isBigO (fun n => List.range' n n) (by intro n; simp) interval_key_bound, ?_⟩
  exact cubic_isBigO_of_lower (fun n => unaryWork (List.range' n n))
    (fun n => (unary_interval_bounds n).1)

end Resources.CollisionGrowth
