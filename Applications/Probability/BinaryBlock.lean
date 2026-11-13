import Applications.Probability.CoinSuffix

/-!
# Finite binary blocks from an independent tape

The most significant bit is read first. Every bit word has one numeric code,
and each code has exactly the probability of its finite tape cylinder.
-/
namespace Applications.Probability.BinaryBlock
open CoinPaths CoinSuffix MeasureTheory
open scoped ENNReal

/-- Decode a finite word in the order in which the machine reads it. -/
def decode : (k : ℕ) → (Fin k → Bool) → ℕ
  | 0, _ => 0
  | k+1, f => (if f 0 then 2^k else 0) + decode k (fun i => f i.succ)

theorem decode_lt (k : ℕ) (f : Fin k → Bool) : decode k f < 2^k := by
  induction k with
  | zero => simp [decode]
  | succ k ih =>
    have h := ih (fun i => f i.succ)
    simp only [decode,pow_succ]
    split <;> omega

theorem decode_injective (k : ℕ) : Function.Injective (decode k) := by
  induction k with
  | zero => intro f g _; exact Subsingleton.elim _ _
  | succ k ih =>
    intro f g h
    have hf := decode_lt k (fun i => f i.succ)
    have hg := decode_lt k (fun i => g i.succ)
    have hhead : f 0=g 0 := by
      cases hf0 : f 0 <;> cases hg0 : g 0 <;> simp [decode,hf0,hg0] at h ⊢ <;> omega
    have htail : (fun i : Fin k => f i.succ) = (fun i : Fin k => g i.succ) := by
      apply ih
      simpa only [decode,hhead,Nat.add_left_cancel_iff] using h
    funext i
    refine Fin.cases hhead (fun j => congrFun htail j) i

/-- The decoder covers every code in the exact block range. -/
theorem decode_surjective (k : ℕ) :
    Function.Surjective (fun f : Fin k → Bool => (⟨decode k f,decode_lt k f⟩ : Fin (2^k))) := by
  apply ((Fintype.bijective_iff_injective_and_card _).mpr ⟨?_,?_⟩).surjective
  · intro f g h
    exact decode_injective k (congrArg Fin.val h)
  · simp

/-- Read a block at an arbitrary cursor. -/
def read (ω : Tape) (s k : ℕ) : ℕ := decode k (fun i => ω (s+i))

theorem read_lt (ω : Tape) (s k : ℕ) : read ω s k < 2^k := decode_lt _ _

theorem read_zero (ω : Tape) (s : ℕ) : read ω s 0=0 := rfl

theorem read_succ (ω : Tape) (s k : ℕ) :
    read ω s (k+1) = (if ω s then 2^k else 0) + read ω (s+1) k := by
  simp [read,decode,Fin.val_succ,Nat.add_left_comm,Nat.add_comm]

theorem read_suffix (ω : Tape) (s k : ℕ) : read (suffix s ω) 0 k=read ω s k := by
  simp [read,suffix]

/-- Read bits form exactly one finite coordinate cylinder. -/
theorem word_eq_cylinder (s k : ℕ) (f : Fin k → Bool) :
    {ω : Tape | (fun i : Fin k => ω (s+i))=f} =
      Set.pi (Finset.Ico s (s+k)) (fun i =>
        {if h : s ≤ i ∧ i < s+k then f ⟨i-s,by omega⟩ else false}) := by
  ext ω
  simp only [Set.mem_ofPred_eq,Set.mem_pi,Finset.mem_coe,Finset.mem_Ico,Set.mem_singleton_iff]
  constructor
  · intro h i hi
    simp only [dite_eq_left hi]
    have := congrFun h ⟨i-s,by omega⟩
    simpa [Nat.add_sub_of_le hi.1] using this
  · intro h
    funext i
    simpa using h (s+i) ⟨by omega,by have := i.isLt; omega⟩

theorem read_eq_word (s k : ℕ) (f : Fin k → Bool) :
    {ω | read ω s k=decode k f} = {ω : Tape | (fun i : Fin k => ω (s+i))=f} := by
  ext ω
  exact (decode_injective k).eq_iff

theorem measurable_read (s k : ℕ) : Measurable (fun ω => read ω s k) := by
  exact (measurable_of_countable (decode k)).comp (by fun_prop)

/-- Every code has probability 2^-k, including the empty block. -/
theorem read_mass (s k : ℕ) (a : Fin (2^k)) :
    law {ω | read ω s k=a.val} = (2⁻¹ : ℝ≥0∞)^k := by
  obtain ⟨f,hf⟩ := decode_surjective k a
  have hv := congrArg Fin.val hf
  rw [← hv,read_eq_word,word_eq_cylinder]
  rw [cylinder_mass]
  simp

theorem read_congr {ω η : Tape} {s k : ℕ}
    (h : ∀ i, s ≤ i → i<s+k → ω i=η i) : read ω s k=read η s k := by
  unfold read
  congr 1
  funext i
  exact h (s+i) (by omega) (by have := i.isLt; omega)

/-- Any predicate on one decoded block depends only on that block's prefix. -/
theorem read_prefix (s k : ℕ) (P : ℕ → Prop) :
    PrefixEvent (s+k) {ω | P (read ω s k)} := by
  intro ω η h
  change P (read ω s k) ↔ P (read η s k)
  rw [show read ω s k=read η s k from read_congr (fun i _ hi => h i hi)]

theorem read_suffix_add (ω : Tape) (s t k : ℕ) :
    read (suffix s ω) t k=read ω (s+t) k := by
  simp [read,suffix,Nat.add_assoc]

/-- All rejected codes are counted, including when several codes exceed the
bound. This is a finite union of distinct block-code cylinders. -/
theorem reject_mass (s k n : ℕ) (hn : n ≤ 2^k) :
    law {ω | n ≤ read ω s k} = (2^k-n : ℕ) * (2⁻¹ : ℝ≥0∞)^k := by
  let code (i : Fin (2^k-n)) : Fin (2^k) := ⟨n+i,by have := i.isLt; omega⟩
  have he : {ω | n ≤ read ω s k} =
      ⋃ i : Fin (2^k-n), {ω | read ω s k=(code i).val} := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · intro h
      refine ⟨⟨read ω s k-n,by have := read_lt ω s k; omega⟩,?_⟩
      dsimp [code]
      omega
    · rintro ⟨i,h⟩; dsimp [code] at h; omega
  rw [he,measure_iUnion]
  · simp [read_mass,tsum_fintype]
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    exact hij (Fin.ext (by dsimp [code] at hi hj; omega))
  · intro i
    exact (measurable_read s k) (measurableSet_singleton _)

end Applications.Probability.BinaryBlock
