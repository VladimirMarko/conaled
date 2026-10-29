import Applications.Parallel.MeasuredScan
import Applications.Optimization.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Lower bounds for shared free-word prefix circuits

The competitors are arbitrary output wires, not scan recipes. Identity gates
may remain. The mixed bound counts the total's gates and the distinct prefix
outputs; their overlap lies on the path of the first input letter.
-/
namespace Applications.Parallel
namespace Wire

/-- Symbolic interpretation at independent input letters. -/
def word : Wire → List Nat
  | .input i => [i]
  | .one => []
  | .mul a b => a.word ++ b.word

theorem word_eq_eval (w : Wire) :
    FreeMonoid.ofList w.word = w.eval FreeMonoid.of := by
  induction w with
  | input => rfl
  | one => rfl
  | mul a b ha hb => exact congrArg₂ (· * ·) ha hb

/-- Symbolic words determine evaluation under every monoid interpretation. -/
theorem eval_eq_word_prod {M : Type*} [Monoid M] (v : Nat → M) (w : Wire) :
    w.eval v = (w.word.map v).prod := by
  induction w with
  | input => simp [eval, word]
  | one => rfl
  | mul a b ha hb => simp [eval, word, List.prod_append, ha, hb]

/-- A retained gate's letters occur in the enclosing wire. -/
theorem mem_word_of_gate {w g : Wire} (hg : g ∈ w.gates) {i : Nat}
    (hi : i ∈ g.word) : i ∈ w.word := by
  induction w with
  | input => simp [gates] at hg
  | one => simp [gates] at hg
  | mul a b ha hb =>
    simp only [gates, Finset.mem_insert, Finset.mem_union] at hg
    rcases hg with rfl | hg | hg
    · exact hi
    · exact List.mem_append_left _ (ha hg)
    · exact List.mem_append_right _ (hb hg)

theorem arrival_le_of_gate {w g : Wire} (hg : g ∈ w.gates) (t : Nat → Nat) :
    g.arrival t ≤ w.arrival t := by
  induction w with
  | input => simp [gates] at hg
  | one => simp [gates] at hg
  | mul a b ha hb =>
    simp only [gates, Finset.mem_insert, Finset.mem_union] at hg
    rcases hg with rfl | hg | hg
    · exact le_rfl
    · exact (ha hg).trans (by simp [arrival]; omega)
    · exact (hb hg).trans (by simp [arrival]; omega)

theorem mul_not_mem_child_gates (a b : Wire) :
    .mul a b ∉ a.gates ∧ .mul a b ∉ b.gates := by
  constructor <;> intro h
  · have := arrival_le_of_gate h (fun _ => 0)
    have := (child_rank_lt a b).1
    omega
  · have := arrival_le_of_gate h (fun _ => 0)
    have := (child_rank_lt a b).2
    omega

/-- Empty-word gates cannot help construct a nonempty prefix. -/
def liveGates (w : Wire) : Finset Wire := w.gates.filter (fun g => g.word ≠ [])

private theorem live_disjoint {a b : Wire} (hn : (a.word ++ b.word).Nodup) :
    Disjoint a.liveGates b.liveGates := by
  apply Finset.disjoint_left.mpr
  intro g ha hb
  simp only [liveGates, Finset.mem_filter] at ha hb
  obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil g.word ha.2
  exact List.disjoint_left.mp hn.disjoint (mem_word_of_gate ha.1 hi)
    (mem_word_of_gate hb.1 hi)

theorem length_le_liveGates (w : Wire) (hn : w.word.Nodup) :
    w.word.length ≤ w.liveGates.card + 1 := by
  induction w with
  | input => simp [word, liveGates, gates]
  | one => simp [word]
  | mul a b ha hb =>
    change (a.word ++ b.word).Nodup at hn
    have hla := ha hn.of_append_left
    have hlb := hb hn.of_append_right
    by_cases he : (.mul a b : Wire).word = []
    · simp [he]
    · have hf : .mul a b ∉ a.liveGates ∪ b.liveGates := by
        have h := mul_not_mem_child_gates a b
        simp only [Finset.mem_union, liveGates, Finset.mem_filter]
        tauto
      have hc : (.mul a b : Wire).liveGates.card =
          a.liveGates.card + b.liveGates.card + 1 := by
        change ((insert (.mul a b) (a.gates ∪ b.gates)).filter
          (fun g => g.word ≠ [])).card = _
        rw [Finset.filter_insert, ite_eq_left he, Finset.filter_union]
        exact (Finset.card_insert_of_notMem hf).trans
          (congrArg (· + 1) (Finset.card_union_of_disjoint (live_disjoint hn)))
      simp only [word, List.length_append]
      rw [hc]
      omega

/-- Count the gates whose result contains a particular input letter. -/
def letterGates (i : Nat) (w : Wire) : Finset Wire :=
  w.gates.filter (fun g => i ∈ g.word)

private theorem letterGates_eq_empty {i : Nat} {w : Wire} (h : i ∉ w.word) :
    w.letterGates i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro g hg
  simp only [letterGates, Finset.mem_filter] at hg
  exact h (mem_word_of_gate hg.1 hg.2)

/-- In a word without repeated letters, all gates containing one letter lie
on a single path. This remains true in the presence of identity gates. -/
theorem letterGates_card_le (i : Nat) (w : Wire) (hn : w.word.Nodup) :
    (w.letterGates i).card ≤ w.arrival (fun _ => 0) := by
  induction w with
  | input => simp [letterGates, gates, arrival]
  | one => simp [letterGates, gates, arrival]
  | mul a b ha hb =>
    change (a.word ++ b.word).Nodup at hn
    have hla := ha hn.of_append_left
    have hlb := hb hn.of_append_right
    by_cases hi : i ∈ (.mul a b : Wire).word
    · have he : (.mul a b : Wire).letterGates i =
          insert (.mul a b) (a.letterGates i ∪ b.letterGates i) := by
        change (insert (.mul a b) (a.gates ∪ b.gates)).filter
          (fun g => i ∈ g.word) = _
        rw [Finset.filter_insert, ite_eq_left hi, Finset.filter_union]
        rfl
      rw [he]
      by_cases hia : i ∈ a.word
      · have hib : i ∉ b.word := fun h => List.disjoint_left.mp hn.disjoint hia h
        rw [letterGates_eq_empty hib, Finset.union_empty]
        have hc := Finset.card_insert_le (.mul a b) (a.letterGates i)
        simp only [arrival]
        omega
      · rw [letterGates_eq_empty hia, Finset.empty_union]
        have hc := Finset.card_insert_le (.mul a b) (b.letterGates i)
        simp only [arrival]
        omega
    · rw [letterGates_eq_empty hi]
      simp

/-- Binary fan-in alone bounds the number of letter occurrences at each depth. -/
theorem length_le_pow_depth (w : Wire) :
    w.word.length ≤ 2 ^ w.arrival (fun _ => 0) := by
  induction w with
  | input => simp [word, arrival]
  | one => simp [word]
  | mul a b ha hb =>
    have hpa : 2 ^ a.arrival (fun _ => 0) ≤
        2 ^ max (a.arrival (fun _ => 0)) (b.arrival (fun _ => 0)) :=
      Nat.pow_le_pow_right (by decide) (le_max_left _ _)
    have hpb : 2 ^ b.arrival (fun _ => 0) ≤
        2 ^ max (a.arrival (fun _ => 0)) (b.arrival (fun _ => 0)) :=
      Nat.pow_le_pow_right (by decide) (le_max_right _ _)
    simp only [word, List.length_append, arrival, pow_succ]
    omega

end Wire

namespace SharedCircuit

private theorem mem_union_fold (g : Wire) (xs : List (Finset Wire)) (s : Finset Wire) :
    g ∈ xs.foldl (· ∪ ·) s ↔ g ∈ s ∨ ∃ t ∈ xs, g ∈ t := by
  induction xs generalizing s with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldl_cons, ih, Finset.mem_union, List.mem_cons]
    aesop

theorem mem_gates_iff (c : SharedCircuit) (g : Wire) :
    g ∈ c.gates ↔ ∃ w ∈ c.outputs, g ∈ w.gates := by
  simp [gates, mem_union_fold]

theorem gates_subset_of_output {c : SharedCircuit} {w : Wire} (hw : w ∈ c.outputs) :
    w.gates ⊆ c.gates := by
  intro g hg
  exact (mem_gates_iff c g).mpr ⟨w, hw, hg⟩

private theorem foldl_max_le (xs : List Nat) (a k : Nat) :
    xs.foldl max a ≤ k ↔ a ≤ k ∧ ∀ b ∈ xs, b ≤ k := by
  induction xs generalizing a with
  | nil => simp
  | cons b bs ih => simp [List.foldl_cons, ih, and_assoc]

theorem arrival_le_depth {c : SharedCircuit} {w : Wire} (hw : w ∈ c.outputs) :
    w.arrival (fun _ => 0) ≤ c.depth := by
  have h := (foldl_max_le (c.arrivals (fun _ => 0)) 0 c.depth).mp le_rfl
  exact h.2 _ (List.mem_map.mpr ⟨w, hw, rfl⟩)

/-- All inclusive prefixes of independent ordered letters occur at output ports.
Additional ports, raw identity gates and arbitrary sharing are permitted. -/
def ComputesPrefixes (c : SharedCircuit) (n : Nat) : Prop :=
  ∀ k : Fin n, ∃ w ∈ c.outputs, w.word = List.range (k.val + 1)

/-- The free-word specification implies prefix correctness for every monoid. -/
theorem prefix_eval {c : SharedCircuit} {n : Nat} (h : c.ComputesPrefixes n)
    {M : Type*} [Monoid M] (v : Nat → M) (k : Fin n) :
    ∃ w ∈ c.outputs, w.eval v = ((List.range (k.val+1)).map v).prod := by
  obtain ⟨w, hw, he⟩ := h k
  exact ⟨w, hw, by rw [Wire.eval_eq_word_prod, he]⟩

/-- The nontrivial prefix outputs are distinct retained gates containing letter zero. -/
theorem prefix_gates {c : SharedCircuit} {n : Nat} (h : c.ComputesPrefixes n) :
    ∃ P : Finset Wire, P.card = n - 1 ∧ P ⊆ c.gates ∧
      ∀ w ∈ P, 0 ∈ w.word := by
  classical
  have hex (k : Fin (n-1)) : ∃ w ∈ c.outputs, w.word = List.range (k.val + 2) := by
    have hk := k.isLt
    simpa only [Nat.add_assoc] using h ⟨k.val + 1, by omega⟩
  let out (k : Fin (n-1)) : Wire := Classical.choose (hex k)
  have ho (k : Fin (n-1)) : out k ∈ c.outputs ∧ (out k).word = List.range (k.val+2) :=
    Classical.choose_spec (hex k)
  have hinj : Function.Injective out := by
    intro i j hij
    have hi := congrArg List.length (ho i).2
    have hj := congrArg List.length (ho j).2
    simp only [List.length_range] at hi hj
    rw [hij] at hi
    apply Fin.ext
    omega
  refine ⟨Finset.univ.image out, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj]
    simp
  · intro w hw
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hw
    apply gates_subset_of_output (ho k).1
    have hl := congrArg List.length (ho k).2
    cases he : out k with
    | input i => simp [he, Wire.word] at hl
    | one => simp [he, Wire.word] at hl
    | mul a b => simp [Wire.gates]
  · intro w hw
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hw
    rw [(ho k).2]
    simp

/-- Work alone must provide every distinct nontrivial prefix. -/
theorem prefix_work_lower {c : SharedCircuit} {n : Nat} (h : c.ComputesPrefixes n) :
    n - 1 ≤ c.work := by
  obtain ⟨P, hc, hs, _⟩ := prefix_gates h
  rw [← hc]
  exact Finset.card_le_card hs

/-- A bounded-fan-in circuit cannot combine n independent inputs below this depth. -/
theorem prefix_depth_lower {c : SharedCircuit} {n : Nat} (h : c.ComputesPrefixes n) :
    n ≤ 2 ^ c.depth := by
  by_cases hn : n = 0
  · simp [hn]
  · obtain ⟨w, hw, he⟩ := h ⟨n-1, by omega⟩
    have hl := w.length_le_pow_depth
    rw [he, List.length_range] at hl
    have hl' : n ≤ 2 ^ w.arrival (fun _ => 0) := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hl
    exact hl'.trans (Nat.pow_le_pow_right (by decide) (arrival_le_depth hw))

/-- The free-monoid mixed lower bound, for all raw structural circuits.
The total has at least n-1 gates; only depth-many can also be prefix outputs. -/
theorem prefix_work_depth_lower {c : SharedCircuit} {n : Nat}
    (h : c.ComputesPrefixes n) : 2*n - 2 ≤ c.work + c.depth := by
  by_cases hn : n = 0
  · simp [hn]
  · obtain ⟨t, ht, he⟩ := h ⟨n-1, by omega⟩
    have he' : t.word = List.range n := by simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using he
    have hnodup : t.word.Nodup := he' ▸ List.nodup_range
    have htotal := t.length_le_liveGates hnodup
    rw [he', List.length_range] at htotal
    obtain ⟨P, hP, hPc, hletters⟩ := prefix_gates h
    have htc : t.liveGates ⊆ c.gates :=
      (Finset.filter_subset _ _).trans (gates_subset_of_output ht)
    have hinter : t.liveGates ∩ P ⊆ t.letterGates 0 := by
      intro g hg
      obtain ⟨hgt, hgp⟩ := Finset.mem_inter.mp hg
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hgt).1, hletters g hgp⟩
    have hd : (t.liveGates ∩ P).card ≤ c.depth :=
      (Finset.card_le_card hinter).trans ((t.letterGates_card_le 0 hnodup).trans (arrival_le_depth ht))
    have hu : (t.liveGates ∪ P).card ≤ c.work :=
      Finset.card_le_card (Finset.union_subset htc hPc)
    have hc := Finset.card_union_add_card_inter t.liveGates P
    rw [hP] at hc
    omega

/-- A finite checking interface for the same symbolic prefix specification. -/
theorem computesPrefixes_iff (c : SharedCircuit) (n : Nat) :
    c.ComputesPrefixes n ↔
      ∀ k : Fin n, List.range (k.val+1) ∈ c.outputs.map Wire.word := by
  simp only [ComputesPrefixes, List.mem_map]

/-- Attaining the mixed bound certifies a global least sum in this circuit class. -/
theorem sum_minimizer_of_bound {c : SharedCircuit} {n : Nat}
    (h : c.ComputesPrefixes n) (he : c.work + c.depth = 2*n-2) :
    c ∈ Optimization.minimizers {q | q.ComputesPrefixes n} (fun q => q.work + q.depth) := by
  refine ⟨h, ?_⟩
  intro q hq
  change c.work + c.depth ≤ q.work + q.depth
  rw [he]
  exact prefix_work_depth_lower hq

/-- Equality in the sum lower bound also rules out coordinatewise improvements. -/
theorem pareto_of_bound {c : SharedCircuit} {n : Nat}
    (h : c.ComputesPrefixes n) (he : c.work + c.depth = 2*n-2) :
    c ∈ Optimization.pareto {q | q.ComputesPrefixes n} (fun q => (q.work, q.depth)) := by
  refine ⟨h, ?_⟩
  intro q hq hle
  have hb := prefix_work_depth_lower hq
  obtain ⟨hw, hd⟩ := hle
  change q.work ≤ c.work at hw
  change q.depth ≤ c.depth at hd
  change c.work ≤ q.work ∧ c.depth ≤ q.depth
  constructor <;> omega

end SharedCircuit
end Applications.Parallel
