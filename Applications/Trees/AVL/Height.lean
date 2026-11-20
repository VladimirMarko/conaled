import Applications.Trees.AVL.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Fibonacci lower bounds and exact logarithmic height for AVL shapes.
The bounds count external leaves, including one leaf for the empty tree.
A concrete Fibonacci-tree program attains the lower bound at each height.
Stored-height statements require the existing recursive cached AVL invariant.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.AVL
universe u
variable {α : Type u}

/-- Recursive height balance forces the source Fibonacci external-leaf bound. -/
theorem fib_height_le_numLeaves (t : BinaryTree α) (h : Balanced t) :
    Nat.fib (t.height + 2) ≤ t.numLeaves := by
  revert h
  induction t with
  | nil =>
      intro _
      simp
  | node a l r ihl ihr =>
      intro h
      rcases (balanced_node a l r).mp h with ⟨hl, hr, hlr, hrl⟩
      change Nat.fib (max l.height r.height + 1 + 2) ≤ l.numLeaves + r.numLeaves
      rcases le_total l.height r.height with hlr' | hrl'
      · rw [max_eq_right hlr']
        have hf : Nat.fib (r.height + 1) ≤ Nat.fib (l.height + 2) :=
          Nat.fib_mono (by omega)
        calc
          Nat.fib (r.height + 1 + 2) =
              Nat.fib (r.height + 1) + Nat.fib (r.height + 2) := by
            simpa only [Nat.add_assoc] using (Nat.fib_add_two (n := r.height + 1))
          _ ≤ Nat.fib (l.height + 2) + Nat.fib (r.height + 2) :=
            Nat.add_le_add_right hf _
          _ ≤ l.numLeaves + r.numLeaves := Nat.add_le_add (ihl hl) (ihr hr)
      · rw [max_eq_left hrl']
        have hf : Nat.fib (l.height + 1) ≤ Nat.fib (r.height + 2) :=
          Nat.fib_mono (by omega)
        calc
          Nat.fib (l.height + 1 + 2) =
              Nat.fib (l.height + 1) + Nat.fib (l.height + 2) := by
            simpa only [Nat.add_assoc] using (Nat.fib_add_two (n := l.height + 1))
          _ ≤ Nat.fib (r.height + 2) + Nat.fib (l.height + 2) :=
            Nat.add_le_add_right hf _
          _ ≤ r.numLeaves + l.numLeaves := Nat.add_le_add (ihr hr) (ihl hl)
          _ = l.numLeaves + r.numLeaves := Nat.add_comm _ _

/-- The source cached invariant supplies shape balance after annotation erasure. -/
theorem fib_height_le_numLeaves_of_valid (t : BinaryTree (α × Nat)) (h : Valid t) :
    Nat.fib (t.height + 2) ≤ t.numLeaves := by
  simpa only [Cached.height_erase, Cached.numLeaves_erase] using
    fib_height_le_numLeaves (Cached.erase t) h.1

/-- The source two-step argument, with both initial cases and natural powers. -/
theorem goldenRatio_pow_le_fib (n : Nat) :
    Real.goldenRatio ^ n ≤ (Nat.fib (n + 2) : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one =>
      calc
        Real.goldenRatio ^ 1 = Real.goldenRatio := pow_one _
        _ ≤ 2 := Real.goldenRatio_lt_two.le
        _ = (Nat.fib (1 + 2) : ℝ) := by norm_num
  | more n ihn ihn1 =>
      have hp : Real.goldenRatio ^ (n + 2) =
          Real.goldenRatio ^ (n + 1) + Real.goldenRatio ^ n := by
        linarith [Real.goldenRatio_pow_sub_goldenRatio_pow n]
      have hf : Nat.fib (n + 1 + 2) + Nat.fib (n + 2) = Nat.fib (n + 2 + 2) := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (Nat.fib_add_two (n := n + 2)).symm
      calc
        Real.goldenRatio ^ (n + 2) =
            Real.goldenRatio ^ (n + 1) + Real.goldenRatio ^ n := hp
        _ ≤ (Nat.fib (n + 1 + 2) : ℝ) + (Nat.fib (n + 2) : ℝ) :=
          add_le_add ihn1 ihn
        _ = (Nat.fib (n + 2 + 2) : ℝ) := by
          simpa only [Nat.cast_add] using congrArg (fun k : Nat => (k : ℝ)) hf

/-- Exponential leaf growth depends only on the balanced shape. -/
theorem goldenRatio_pow_height_le_numLeaves (t : BinaryTree α) (h : Balanced t) :
    Real.goldenRatio ^ t.height ≤ (t.numLeaves : ℝ) :=
  (goldenRatio_pow_le_fib t.height).trans (Nat.cast_le.mpr (fib_height_le_numLeaves t h))

theorem goldenRatio_pow_height_le_numLeaves_of_valid
    (t : BinaryTree (α × Nat)) (h : Valid t) :
    Real.goldenRatio ^ t.height ≤ (t.numLeaves : ℝ) := by
  simpa only [Cached.height_erase, Cached.numLeaves_erase] using
    goldenRatio_pow_height_le_numLeaves (Cached.erase t) h.1

/-- The exact coefficient is retained; the empty shape has log of one, hence zero. -/
theorem height_le_logb_numLeaves (t : BinaryTree α) (h : Balanced t) :
    (t.height : ℝ) ≤ (1 / Real.logb 2 Real.goldenRatio) *
      Real.logb 2 (t.numLeaves : ℝ) := by
  have hbase : (1 : ℝ) < 2 := by norm_num
  have hleaves : (0 : ℝ) < (t.numLeaves : ℝ) :=
    Nat.cast_pos.mpr (BinaryTree.numLeaves_pos t)
  have hlog := (Real.logb_le_logb hbase
    (pow_pos Real.goldenRatio_pos t.height) hleaves).mpr
    (goldenRatio_pow_height_le_numLeaves t h)
  rw [Real.logb_pow] at hlog
  have hden : 0 < Real.logb 2 Real.goldenRatio :=
    Real.logb_pos hbase Real.one_lt_goldenRatio
  have hquot : (t.height : ℝ) ≤
      Real.logb 2 (t.numLeaves : ℝ) / Real.logb 2 Real.goldenRatio :=
    (le_div_iff₀ hden).mpr hlog
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hquot

theorem height_le_logb_numLeaves_of_valid (t : BinaryTree (α × Nat)) (h : Valid t) :
    (t.height : ℝ) ≤ (1 / Real.logb 2 Real.goldenRatio) *
      Real.logb 2 (t.numLeaves : ℝ) := by
  simpa only [Cached.height_erase, Cached.numLeaves_erase] using
    height_le_logb_numLeaves (Cached.erase t) h.1

/-- Internal-node size enters the logarithm only after adding one. -/
theorem height_le_logb_numNodes_add_one (t : BinaryTree α) (h : Balanced t) :
    (t.height : ℝ) ≤ (1 / Real.logb 2 Real.goldenRatio) *
      Real.logb 2 ((t.numNodes : ℝ) + 1) := by
  simpa only [BinaryTree.numLeaves_eq_numNodes_succ, Nat.cast_add, Nat.cast_one] using
    height_le_logb_numLeaves t h

theorem height_le_logb_numNodes_add_one_of_valid
    (t : BinaryTree (α × Nat)) (h : Valid t) :
    (t.height : ℝ) ≤ (1 / Real.logb 2 Real.goldenRatio) *
      Real.logb 2 ((t.numNodes : ℝ) + 1) := by
  simpa only [BinaryTree.numLeaves_eq_numNodes_succ, Nat.cast_add, Nat.cast_one] using
    height_le_logb_numLeaves_of_valid t h

/-- Reading the root cache is sound here because validity includes cache correctness. -/
theorem fib_ht_le_numLeaves (t : BinaryTree (α × Nat)) (h : Valid t) :
    Nat.fib (ht t + 2) ≤ t.numLeaves := by
  rw [ht_eq_height t h]
  exact fib_height_le_numLeaves_of_valid t h

theorem ht_le_logb_numLeaves (t : BinaryTree (α × Nat)) (h : Valid t) :
    (ht t : ℝ) ≤ (1 / Real.logb 2 Real.goldenRatio) *
      Real.logb 2 (t.numLeaves : ℝ) := by
  rw [ht_eq_height t h]
  exact height_le_logb_numLeaves_of_valid t h

/-- Exact rational bounds obtained from the defining quadratic, without decimal evaluation. -/
private theorem goldenRatio_rational_bounds :
    (809 / 500 : ℝ) < Real.goldenRatio ∧ Real.goldenRatio < (16181 / 10000 : ℝ) := by
  have hpos := Real.one_lt_goldenRatio
  have hsquare := Real.goldenRatio_sq
  constructor
  · by_contra h
    have hle : Real.goldenRatio ≤ (809 / 500 : ℝ) := le_of_not_gt h
    have hm : 0 ≤ ((809 / 500 : ℝ) - Real.goldenRatio) *
        ((809 / 500 : ℝ) + Real.goldenRatio - 1) :=
      mul_nonneg (sub_nonneg.mpr hle) (by linarith)
    nlinarith
  · by_contra h
    have hle : (16181 / 10000 : ℝ) ≤ Real.goldenRatio := le_of_not_gt h
    have hm : 0 ≤ (Real.goldenRatio - (16181 / 10000 : ℝ)) *
        (Real.goldenRatio + (16181 / 10000 : ℝ) - 1) :=
      mul_nonneg (sub_nonneg.mpr hle) (by linarith)
    nlinarith

private theorem goldenRatio_pow_thirty_six_lt :
    Real.goldenRatio ^ 36 < (2 : ℝ) ^ 25 := by
  have hid := Real.goldenRatio_mul_fib_succ_add_fib 35
  norm_num at hid
  calc
    Real.goldenRatio ^ 36 = Real.goldenRatio * 14930352 + 9227465 := by
      simpa only [mul_comm] using hid.symm
    _ < (16181 / 10000 : ℝ) * 14930352 + 9227465 :=
      add_lt_add_left (mul_lt_mul_of_pos_right goldenRatio_rational_bounds.2
        (by norm_num : (0 : ℝ) < 14930352)) (9227465 : ℝ)
    _ < (2 : ℝ) ^ 25 := by norm_num

private theorem two_pow_fifty_nine_lt :
    (2 : ℝ) ^ 59 < Real.goldenRatio ^ 85 := by
  have hid := Real.goldenRatio_mul_fib_succ_add_fib 84
  norm_num at hid
  calc
    (2 : ℝ) ^ 59 < (809 / 500 : ℝ) * 259695496911122585 + 160500643816367088 := by
      norm_num
    _ < Real.goldenRatio * 259695496911122585 + 160500643816367088 :=
      add_lt_add_left (mul_lt_mul_of_pos_right goldenRatio_rational_bounds.1
        (by norm_num : (0 : ℝ) < 259695496911122585)) (160500643816367088 : ℝ)
    _ = Real.goldenRatio ^ 85 := by simpa only [mul_comm] using hid

/-- The printed approximation rounds to 1.44, which is strictly below the exact coefficient. -/
theorem height_coefficient_bounds :
    (1440 / 1000 : ℝ) < 1 / Real.logb 2 Real.goldenRatio ∧
      1 / Real.logb 2 Real.goldenRatio < (1441 / 1000 : ℝ) := by
  have hden : 0 < Real.log Real.goldenRatio := Real.log_pos Real.one_lt_goldenRatio
  have hl := Real.log_lt_log (pow_pos Real.goldenRatio_pos 36) goldenRatio_pow_thirty_six_lt
  have hu := Real.log_lt_log (pow_pos (by norm_num : (0 : ℝ) < 2) 59) two_pow_fifty_nine_lt
  simp only [Real.log_pow, Nat.cast_ofNat] at hl hu
  have hlo : (36 / 25 : ℝ) < Real.log 2 / Real.log Real.goldenRatio :=
    (lt_div_iff₀ hden).mpr (by linarith)
  have hhi : Real.log 2 / Real.log Real.goldenRatio < (85 / 59 : ℝ) :=
    (div_lt_iff₀ hden).mpr (by linarith)
  have heq : 1 / Real.logb 2 Real.goldenRatio =
      Real.log 2 / Real.log Real.goldenRatio := by
    rw [one_div, Real.inv_logb]
    rfl
  rw [heq]
  constructor
  · calc
      (1440 / 1000 : ℝ) = 36 / 25 := by norm_num
      _ < Real.log 2 / Real.log Real.goldenRatio := hlo
  · exact hhi.trans (by norm_num)

/-- The source's executable unannotated Fibonacci tree, in label/left/right order. -/
def fibTree : Nat → BinaryTree Unit
  | 0 => .nil
  | 1 => .node () .nil .nil
  | n + 2 => .node () (fibTree (n + 1)) (fibTree n)

@[simp] theorem fibTree_zero : fibTree 0 = .nil := rfl
@[simp] theorem fibTree_one : fibTree 1 = .node () .nil .nil := rfl

theorem fibTree_add_two (n : Nat) :
    fibTree (n + 2) = .node () (fibTree (n + 1)) (fibTree n) := rfl

private theorem fibTree_spec (n : Nat) :
    Balanced (fibTree n) ∧ (fibTree n).height = n ∧
      (fibTree n).numLeaves = Nat.fib (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [balanced_node, Nat.fib_add_two]
  | more n ihn ihn1 =>
      refine ⟨?_, ?_, ?_⟩
      · rw [fibTree_add_two, balanced_node]
        refine ⟨ihn1.1, ihn.1, ?_, ?_⟩
        · simp only [ihn1.2.1, ihn.2.1]
          omega
        · simp only [ihn1.2.1, ihn.2.1]
          omega
      · simp only [fibTree_add_two, BinaryTree.height, ihn1.2.1, ihn.2.1]
        omega
      · rw [fibTree_add_two, BinaryTree.numLeaves, ihn1.2.2, ihn.2.2]
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (Nat.fib_add_two (n := n + 2)).symm

/-- The witness has the same recursive shape invariant as every other AVL tree. -/
theorem balanced_fibTree (n : Nat) : Balanced (fibTree n) := (fibTree_spec n).1

theorem height_fibTree (n : Nat) : (fibTree n).height = n := (fibTree_spec n).2.1

theorem numLeaves_fibTree (n : Nat) : (fibTree n).numLeaves = Nat.fib (n + 2) :=
  (fibTree_spec n).2.2

/-- Internal nodes are exactly one fewer than the source external-leaf count. -/
theorem numNodes_fibTree_add_one (n : Nat) :
    (fibTree n).numNodes + 1 = Nat.fib (n + 2) :=
  (BinaryTree.numLeaves_eq_numNodes_succ (fibTree n)).symm.trans (numLeaves_fibTree n)

/-- The attained minimum sequence has the source two-step sum recurrence. -/
theorem numLeaves_fibTree_add_two (n : Nat) :
    (fibTree (n + 2)).numLeaves =
      (fibTree (n + 1)).numLeaves + (fibTree n).numLeaves := rfl

/-- The executable witness attains the minimum at the actual height of any balanced shape. -/
theorem fibTree_minimal (t : BinaryTree α) (h : Balanced t) :
    (fibTree t.height).numLeaves ≤ t.numLeaves := by
  rw [numLeaves_fibTree]
  exact fib_height_le_numLeaves t h

theorem fibTree_minimal_of_valid (t : BinaryTree (α × Nat)) (h : Valid t) :
    (fibTree t.height).numLeaves ≤ t.numLeaves := by
  rw [numLeaves_fibTree]
  exact fib_height_le_numLeaves_of_valid t h

/-- Node minimality is derived by translating the leaf comparison on both trees. -/
theorem fibTree_numNodes_minimal (t : BinaryTree α) (h : Balanced t) :
    (fibTree t.height).numNodes ≤ t.numNodes := by
  have hl := fibTree_minimal t h
  simp only [BinaryTree.numLeaves_eq_numNodes_succ] at hl
  omega

theorem fibTree_numNodes_minimal_of_valid (t : BinaryTree (α × Nat)) (h : Valid t) :
    (fibTree t.height).numNodes ≤ t.numNodes := by
  have hl := fibTree_minimal_of_valid t h
  simp only [BinaryTree.numLeaves_eq_numNodes_succ] at hl
  omega

/-- Existing correct decoration supplies a source-valid attaining witness. -/
theorem valid_annotate_fibTree (n : Nat) : Valid (annotate (fibTree n)) :=
  (valid_annotate_iff (fibTree n)).mpr (balanced_fibTree n)

theorem height_annotate_fibTree (n : Nat) : (annotate (fibTree n)).height = n := by
  have he := Cached.height_erase (annotate (fibTree n))
  rw [erase_annotate] at he
  exact he.symm.trans (height_fibTree n)

theorem numLeaves_annotate_fibTree (n : Nat) :
    (annotate (fibTree n)).numLeaves = Nat.fib (n + 2) := by
  have he := Cached.numLeaves_erase (annotate (fibTree n))
  rw [erase_annotate] at he
  exact he.symm.trans (numLeaves_fibTree n)

/-- The minimum is attained for every height over a concrete, inhabited shape carrier. -/
theorem exists_balanced_height_numLeaves (n : Nat) :
    ∃ t : BinaryTree Unit,
      Balanced t ∧ t.height = n ∧ t.numLeaves = Nat.fib (n + 2) :=
  ⟨fibTree n, balanced_fibTree n, height_fibTree n, numLeaves_fibTree n⟩

theorem exists_valid_height_numLeaves (n : Nat) :
    ∃ t : BinaryTree (Unit × Nat),
      Valid t ∧ t.height = n ∧ t.numLeaves = Nat.fib (n + 2) :=
  ⟨annotate (fibTree n), valid_annotate_fibTree n, height_annotate_fibTree n,
    numLeaves_annotate_fibTree n⟩

end Trees.AVL
