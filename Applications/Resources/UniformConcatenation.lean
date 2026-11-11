import Applications.Resources.ListFusion

/-!
# Uniform-block specializations of the actual concatenation executors

The existing value-producing executions are reused unchanged.
Adapted from the recovered Chapter02 UniformConcatenation evidence; see
`docs/research/uniform-concatenation.md` for dispositions and source limits.
Exact formulas retain the outer traversal cost even when block length is zero.
Uniform two-parameter growth bounds state their nondegenerate domains explicitly.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.UniformConcatenation

open ListFusion
universe u v
variable {α : Type u}

def Uniform (n : Nat) (xss : List (List α)) : Prop := ∀ xs ∈ xss, xs.length = n

theorem length_flatten_uniform (n : Nat) (xss : List (List α)) (h : Uniform n xss) :
    xss.flatten.length = xss.length * n := by
  induction xss with
  | nil => simp [List.flatten]
  | cons xs xss ih =>
      have hx := h xs (by simp)
      have ht : Uniform n xss := fun ys hy => h ys (by simp [hy])
      simp only [List.flatten_cons, List.length_append, ih ht, hx, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem prefixMass_uniform (n k : Nat) (xss : List (List α)) (h : Uniform n xss) :
    2 * prefixMass k xss + xss.length * n =
      2 * xss.length * k + xss.length * xss.length * n := by
  induction xss generalizing k with
  | nil => simp [prefixMass]
  | cons xs xss ih =>
      have hx := h xs (by simp)
      have ht : Uniform n xss := fun ys hy => h ys (by simp [hy])
      have hr := ih (k + n) ht
      simp only [Nat.mul_add] at hr
      simp only [prefixMass, hx, List.length_cons, Nat.add_mul, Nat.mul_add,
        Nat.one_mul, Nat.mul_one]
      simp only [Nat.mul_assoc] at hr ⊢
      omega

theorem concat1_uniform_exact (n : Nat) (xss : List (List α)) (h : Uniform n xss) :
    (concat1 xss).2 = 2 * xss.length * n + 2 * xss.length + 1 := by
  rw [concat1_work, length_flatten_uniform n xss h, Nat.mul_assoc]

theorem concat2Acc_uniform_exact (n : Nat) (acc : List α) (xss : List (List α))
    (h : Uniform n xss) :
    (concat2Acc acc xss).2 + xss.length * n =
      2 * xss.length * acc.length + xss.length * xss.length * n + 2 * xss.length + 1 := by
  have hp := prefixMass_uniform n acc.length xss h
  rw [concat2Acc_work]
  omega

theorem concat2_uniform_exact (n : Nat) (xss : List (List α)) (h : Uniform n xss) :
    (concat2 xss).2 + xss.length * n =
      xss.length * xss.length * n + 2 * xss.length + 1 := by
  simpa [concat2] using concat2Acc_uniform_exact n [] xss h

/-- Uniform Θ(m*n), with lower constant 2 and upper constant 5. -/
theorem concat1_uniform_theta (n : Nat) (xss : List (List α)) (h : Uniform n xss)
    (hm : 1 ≤ xss.length) (hn : 1 ≤ n) :
    2 * (xss.length * n) ≤ (concat1 xss).2 ∧
      (concat1 xss).2 ≤ 5 * (xss.length * n) := by
  have he := concat1_uniform_exact n xss h
  have hmn : xss.length ≤ xss.length * n := by
    simpa using Nat.mul_le_mul_left xss.length hn
  simp only [Nat.mul_assoc] at he
  omega

/-- Uniform Θ(m²*n), with lower constant 1/2 and upper constant 3.
The multiplication form of the lower bound avoids rational rounding. -/
theorem concat2_uniform_theta (n : Nat) (xss : List (List α)) (h : Uniform n xss)
    (hm : 2 ≤ xss.length) (hn : 1 ≤ n) :
    xss.length * xss.length * n ≤ 2 * (concat2 xss).2 ∧
      (concat2 xss).2 ≤ 3 * (xss.length * xss.length * n) := by
  have he := concat2_uniform_exact n xss h
  have hmn : xss.length ≤ xss.length * n := by
    simpa using Nat.mul_le_mul_left xss.length hn
  have htwo : 2 * (xss.length * n) ≤ xss.length * xss.length * n := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (xss.length * n) hm
  omega

theorem empty_blocks_exact (m : Nat) :
    (concat1 (List.replicate m ([] : List α))).2 = 2 * m + 1 ∧
      (concat2 (List.replicate m ([] : List α))).2 = 2 * m + 1 := by
  have hu : Uniform 0 (List.replicate m ([] : List α)) := by
    intro xs hx
    have he := (List.mem_replicate.mp hx).2
    simp [he]
  have h₁ := concat1_uniform_exact 0 (List.replicate m ([] : List α)) hu
  have h₂ := concat2_uniform_exact 0 (List.replicate m ([] : List α)) hu
  simpa using And.intro h₁ h₂

theorem concat2_single_block (xs : List α) : (concat2 [xs]).2 = 3 := by
  simp [concat2_work, prefixMass]

/-- A single block prevents a uniform positive lower bound proportional to n. -/
theorem single_block_lower_obstruction (c : Nat) :
    ∃ xs : List Nat, c * (concat2 [xs]).2 < xs.length := by
  refine ⟨List.replicate (3 * c + 1) 0, ?_⟩
  rw [concat2_single_block, List.length_replicate]
  omega

/-- The left-associated producer followed by the same full consumer. -/
def foldLeftConcat {β : Type v} (c : Nat) (f : α → β → β) (e : β)
    (xss : List (List α)) : Measured β Nat :=
  bind (concat2 xss) (ListExecution.foldr c f e)

theorem foldLeftConcat_value {β : Type v} (c : Nat) (f : α → β → β) (e : β)
    (xss : List (List α)) :
    (foldLeftConcat c f e xss).1 = xss.flatten.foldr f e := by
  simp [foldLeftConcat, bind, ListExecution.foldr_value, concat2_value]

theorem pipeline_values {β : Type v} (c : Nat) (f : α → β → β) (e : β)
    (xss : List (List α)) :
    (foldConcat c f e xss).1 = (foldLeftConcat c f e xss).1 := by
  rw [foldConcat_value, foldLeftConcat_value]

theorem foldConcat_uniform_work {β : Type v} (c n : Nat) (f : α → β → β) (e : β)
    (xss : List (List α)) (h : Uniform n xss) :
    (foldConcat c f e xss).2 = (3+c)*xss.length*n + 2*xss.length+2 := by
  simp only [foldConcat, bind, ListExecution.foldr_work, concat1_value]
  rw [concat1_uniform_exact n xss h, length_flatten_uniform n xss h]
  simp only [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
  omega

theorem foldLeftConcat_uniform_work {β : Type v} (c n : Nat) (f : α → β → β) (e : β)
    (xss : List (List α)) (h : Uniform n xss) :
    (foldLeftConcat c f e xss).2 =
      (xss.length*xss.length+c*xss.length)*n + 2*xss.length+2 := by
  have hc := concat2_uniform_exact n xss h
  simp only [foldLeftConcat, bind, ListExecution.foldr_work, concat2_value]
  rw [length_flatten_uniform n xss h]
  simp only [Nat.add_mul, Nat.mul_assoc, Nat.one_mul] at *
  omega

theorem uniform_fusion_saving {β : Type v} (c n : Nat) (f : α → β → β) (e : β)
    (xss : List (List α)) (h : Uniform n xss) :
    (foldConcat c f e xss).2 =
      (foldConcatFused c f e xss).2 + 2*xss.length*n+1 := by
  rw [fold_concat_fusion_saving, length_flatten_uniform n xss h]
  simp [Nat.mul_assoc]

theorem foldLeftConcat_single {β : Type v} (c : Nat) (f : α → β → β) (e : β)
    (xs : List α) :
    (foldLeftConcat c f e [xs]).2 = (1+c)*xs.length+4 := by
  simp only [foldLeftConcat, bind, ListExecution.foldr_work, concat2_value]
  rw [concat2_single_block]
  simp
  omega

theorem no_blocks : concat1 ([] : List (List α)) = ([],1) ∧
    concat2 ([] : List (List α)) = ([],1) := by
  exact ⟨rfl, rfl⟩

end Resources.UniformConcatenation
