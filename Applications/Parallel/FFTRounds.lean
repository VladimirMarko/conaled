import Applications.Parallel.FFTEntropy

/-! Input dependence for parallel matching rounds. -/
namespace Applications.Parallel.FFTUnitary

open scoped BigOperators Matrix

variable {N : ℕ}

/-- A coordinate outside every gate in a list is unchanged. -/
theorem gates_mul_outside (gs : List (Gate N)) (i : Fin N)
    (hi : ∀ g ∈ gs, ∀ t, i ≠ g.coordinate t)
    (M : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    ((Round.gatesUnitary gs : Matrix (Fin N) (Fin N) ℂ) * M) i j = M i j := by
  induction gs generalizing M with
  | nil => simp [Round.gatesUnitary]
  | cons g gs ih =>
    change (((Round.gatesUnitary gs : Matrix (Fin N) (Fin N) ℂ) * g.matrix) * M) i j = _
    rw [Matrix.mul_assoc, ih (fun h hh => hi h (List.mem_cons_of_mem _ hh))]
    exact gate_mul_outside g M i (hi g (by simp)) j

/-- Within a matching, a gate sees its two original inputs, unaffected by other gates. -/
theorem matching_mul_coordinate (gs : List (Gate N))
    (hd : gs.Pairwise (fun g h => ∀ a b, g.coordinate a ≠ h.coordinate b))
    (g : Gate N) (hg : g ∈ gs) (t : Fin 2)
    (M : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    ((Round.gatesUnitary gs : Matrix (Fin N) (Fin N) ℂ) * M) (g.coordinate t) j =
      ∑ b, g.block t b * M (g.coordinate b) j := by
  induction gs generalizing M with
  | nil => simp at hg
  | cons h hs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hd
    change (((Round.gatesUnitary hs : Matrix (Fin N) (Fin N) ℂ) * h.matrix) * M)
      (g.coordinate t) j = _
    rw [Matrix.mul_assoc]
    rcases List.mem_cons.mp hg with rfl | hg
    · rw [gates_mul_outside hs (g.coordinate t)
        (fun q hq b => hhead q hq t b)]
      exact gate_mul_coordinate g M t j
    · rw [ih htail hg]
      apply Finset.sum_congr rfl
      intro b _
      rw [gate_mul_outside h M (g.coordinate b)
        (fun a he => hhead g hg a b he.symm)]

noncomputable def rowSupport (M : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun j => M i j ≠ 0)

@[simp] theorem mem_rowSupport (M : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    j ∈ rowSupport M i ↔ M i j ≠ 0 := by
  classical
  simp [rowSupport]

/-- One disjoint round can at most double the number of possible input dependencies. -/
theorem round_support_bound (r : Round N) (M : Matrix (Fin N) (Fin N) ℂ)
    (K : ℕ) (hM : ∀ i, (rowSupport M i).card ≤ K) (i : Fin N) :
    (rowSupport ((r.unitary : Matrix (Fin N) (Fin N) ℂ) * M) i).card ≤ 2 * K := by
  classical
  by_cases hi : ∃ g ∈ r.gates, ∃ t, i = g.coordinate t
  · obtain ⟨g, hg, t, rfl⟩ := hi
    have hs : rowSupport ((r.unitary : Matrix (Fin N) (Fin N) ℂ) * M) (g.coordinate t) ⊆
        rowSupport M (g.coordinate 0) ∪ rowSupport M (g.coordinate 1) := by
      intro j hj
      by_contra hn
      simp only [Finset.mem_union, mem_rowSupport, not_or, not_not] at hn
      apply (mem_rowSupport _ _ _).mp hj
      change ((Round.gatesUnitary r.gates : Matrix (Fin N) (Fin N) ℂ) * M)
        (g.coordinate t) j = 0
      rw [matching_mul_coordinate r.gates r.disjoint g hg t M j]
      simp [Fin.sum_univ_two, hn.1, hn.2]
    calc
      _ ≤ (rowSupport M (g.coordinate 0) ∪ rowSupport M (g.coordinate 1)).card :=
        Finset.card_le_card hs
      _ ≤ (rowSupport M (g.coordinate 0)).card + (rowSupport M (g.coordinate 1)).card :=
        Finset.card_union_le _ _
      _ ≤ 2 * K := by have h0 := hM (g.coordinate 0); have h1 := hM (g.coordinate 1); omega
  · have ho : ∀ g ∈ r.gates, ∀ t, i ≠ g.coordinate t := by
      intro g hg t he
      exact hi ⟨g, hg, t, he⟩
    have he : rowSupport ((r.unitary : Matrix (Fin N) (Fin N) ℂ) * M) i =
        rowSupport M i := by
      ext j
      simp only [mem_rowSupport]
      rw [show ((r.unitary : Matrix (Fin N) (Fin N) ℂ) * M) i j = M i j from
        gates_mul_outside r.gates i ho M j]
    rw [he]
    exact (hM i).trans (by omega)

theorem step_support_bound (s : Step N) (M : Matrix (Fin N) (Fin N) ℂ)
    (K : ℕ) (hM : ∀ i, (rowSupport M i).card ≤ K) (i : Fin N) :
    (rowSupport ((s.unitary : Matrix (Fin N) (Fin N) ℂ) * M) i).card ≤
      2 ^ s.roundCount * K := by
  cases s with
  | round r => simpa [Step.roundCount, Step.unitary] using round_support_bound r M K hM i
  | permute p =>
    change (rowSupport ((1 : Matrix (Fin N) (Fin N) ℂ).submatrix p (Equiv.refl _) * M) i).card ≤ _
    rw [Matrix.one_submatrix_mul]
    change (rowSupport M (p i)).card ≤ 2 ^ 0 * K
    simpa using hM (p i)

theorem program_support_bound_aux (p : Program N) (M : Matrix (Fin N) (Fin N) ℂ)
    (K : ℕ) (hM : ∀ i, (rowSupport M i).card ≤ K) (i : Fin N) :
    (rowSupport ((p.unitary : Matrix (Fin N) (Fin N) ℂ) * M) i).card ≤
      2 ^ p.roundCount * K := by
  induction p generalizing M K with
  | nil => simpa [Program.unitary, Program.roundCount] using hM i
  | cons s ss ih =>
    have h := ih ((s.unitary : Matrix (Fin N) (Fin N) ℂ) * M)
      (2 ^ s.roundCount * K) (step_support_bound s M K hM)
    change (rowSupport (((Program.unitary ss : Matrix (Fin N) (Fin N) ℂ) *
      (s.unitary : Matrix (Fin N) (Fin N) ℂ)) * M) i).card ≤ _
    rw [Matrix.mul_assoc]
    convert h using 1
    simp [Program.roundCount, pow_add]
    ring

@[simp] theorem rowSupport_one (i : Fin N) :
    rowSupport (1 : Matrix (Fin N) (Fin N) ℂ) i = {i} := by
  classical
  ext j
  simp [rowSupport, Matrix.one_apply, eq_comm]

/-- After r disjoint rounds, each output depends on at most 2^r original inputs. -/
theorem program_support_bound (p : Program N) (i : Fin N) :
    (rowSupport (p.unitary : Matrix (Fin N) (Fin N) ℂ) i).card ≤ 2 ^ p.roundCount := by
  simpa using program_support_bound_aux p (1 : Matrix (Fin N) (Fin N) ℂ) 1
    (fun i => by simp) i

end Applications.Parallel.FFTUnitary
