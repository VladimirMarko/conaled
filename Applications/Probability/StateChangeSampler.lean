import Applications.Probability.InitializedProducerWork

/-! The jump kernel and its invariant initialization. Operational adequacy for
the existing state-change filter is developed separately from this table. -/
namespace Applications.Probability.StateChangeSampler
open scoped BigOperators
variable {α : Type} [Fintype α] [DecidableEq α]

def exit (t : Table α α) (x : α) : ℚ := 1-t.entry x x

theorem off_diagonal_sum (t : Table α α) (x : α) :
    (∑ y, if x=y then 0 else t.entry x y)=exit t x := by
  have h (y : α) : (if x=y then 0 else t.entry x y)=
      t.entry x y-(if x=y then t.entry x x else 0) := by
    by_cases he : x=y
    · subst y; simp
    · simp [he]
  simp_rw [h]
  rw [Finset.sum_sub_distrib,t.sum_row]
  simp [exit]

/-- Each output is a change of state. Positivity is required at every state. -/
def jump (t : Table α α) (positive : ∀ x, 0<exit t x) : Table α α where
  entry x y := if x=y then 0 else t.entry x y / exit t x
  nonneg x y := by
    split_ifs
    · exact le_rfl
    · exact div_nonneg (t.nonneg x y) (positive x).le
  sum_row x := by
    have h (y : α) : (if x=y then 0 else t.entry x y / exit t x)=
        (if x=y then 0 else t.entry x y) / exit t x := by
      split_ifs <;> simp
    simp_rw [h]
    rw [← Finset.sum_div,off_diagonal_sum,div_self (ne_of_gt (positive x))]

def normalizer (t : Table α α) (initial : Table Unit α) : ℚ :=
  ∑ x, initial.entry () x * exit t x

omit [DecidableEq α] in
theorem normalizer_pos (t : Table α α) (positive : ∀ x, 0<exit t x)
    (initial : Table Unit α) : 0<normalizer t initial := by
  have hex : ∃ x, 0 < initial.entry () x := by
    by_contra h
    push Not at h
    have hz (x : α) : initial.entry () x=0 := le_antisymm (h x) (initial.nonneg () x)
    have hs := initial.sum_row ()
    simp [hz] at hs
  obtain ⟨x,hx⟩ := hex
  exact lt_of_lt_of_le (mul_pos hx (positive x))
    (Finset.single_le_sum (fun y _ => mul_nonneg (initial.nonneg () y) (positive y).le)
      (Finset.mem_univ x))

/-- The invariant distribution of the jump chain is proportional to pi(x)e(x).
It is not in general the invariant distribution of the unsuppressed chain. -/
def tilted (t : Table α α) (positive : ∀ x, 0<exit t x)
    (initial : Table Unit α) : Table Unit α where
  entry _ x := initial.entry () x * exit t x / normalizer t initial
  nonneg _ x := div_nonneg (mul_nonneg (initial.nonneg () x) (positive x).le)
    (normalizer_pos t positive initial).le
  sum_row _ := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (normalizer_pos t positive initial))

theorem tilted_stationary (t : Table α α) (positive : ∀ x, 0<exit t x)
    (initial : Table Unit α)
    (stationary : ∀ y, ∑ x, initial.entry () x * t.entry x y=initial.entry () y)
    (y : α) :
    (∑ x, (tilted t positive initial).entry () x * (jump t positive).entry x y)=
      (tilted t positive initial).entry () y := by
  have hn := ne_of_gt (normalizer_pos t positive initial)
  have h (x : α) : (tilted t positive initial).entry () x * (jump t positive).entry x y=
      (initial.entry () x * t.entry x y -
        (if x=y then initial.entry () y * t.entry y y else 0)) / normalizer t initial := by
    by_cases he : x=y
    · subst x; simp [jump]
    · simp only [tilted,jump,he,ite_false,sub_zero]
      field_simp [ne_of_gt (positive x),hn]
  simp_rw [h]
  rw [← Finset.sum_div,Finset.sum_sub_distrib,stationary]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  change (initial.entry () y-initial.entry () y*t.entry y y)/normalizer t initial=
    initial.entry () y*(1-t.entry y y)/normalizer t initial
  congr 1
  ring

section Operational
omit [Fintype α]
open CoinPaths TableProducer
variable {p : α → PreparedRow α} {ω : Tape}

/-- A first change retains every suppressed row return and its work. The first
row may already be partially evaluated; subsequent rows use returned cursors. -/
inductive ChangeTrace (p : α → PreparedRow α) (ω : Tape) (x : α) :
    PreparedRow.State → α → ℕ → ℕ → Prop
  | change {q a t k} (row : Progress.Evaluates ((p x).step ω) q (a,t) k)
      (different : a ≠ x) : ChangeTrace p ω x q a t k
  | self {q t i a u j} (row : Progress.Evaluates ((p x).step ω) q (x,t) i)
      (rest : ChangeTrace p ω x ((p x).start t) a u j) :
      ChangeTrace p ω x q a u (i+j)

private theorem change_of_row {x a : α} {q : PreparedRow.State} {t k : ℕ}
    (h : Progress.Evaluates ((p x).step ω) q (a,t) k) (ha : a ≠ x) :
    Progress.Evaluates (changes p ω) (x,q) (a,start p a t) k := by
  induction k generalizing q with
  | zero => cases h
  | succ k ih =>
    cases h with
    | done e => exact .done (by simp [changes,step,e,ha])
    | next e h => exact .next (by simp [changes,step,e]) (ih h)

private theorem self_before_change {x a : α} {q : PreparedRow.State} {t u i j : ℕ}
    (h : Progress.Evaluates ((p x).step ω) q (x,t) i)
    (rest : Progress.Evaluates (changes p ω) (start p x t) (a,start p a u) j) :
    Progress.Evaluates (changes p ω) (x,q) (a,start p a u) (i+j) := by
  induction i generalizing q with
  | zero => cases h
  | succ i ih =>
    cases h with
    | done e => simpa [Nat.add_comm] using
        Progress.Evaluates.next (show changes p ω (x,_) = .inr (start p x t) by
          simp [changes,step,e]) rest
    | next e h => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        Progress.Evaluates.next (show changes p ω (x,_) = .inr (x,_) by
          simp [changes,step,e]) (ih h)

theorem ChangeTrace.evaluates {x a : α} {q : PreparedRow.State} {t k : ℕ}
    (h : ChangeTrace p ω x q a t k) :
    Progress.Evaluates (changes p ω) (x,q) (a,start p a t) k := by
  induction h with
  | change row different => exact change_of_row row different
  | self row rest ih => exact self_before_change row ih

omit [DecidableEq α] in
private theorem ChangeTrace.prepend {x a : α} {q q' : PreparedRow.State} {t k : ℕ}
    (e : (p x).step ω q = .inr q') (h : ChangeTrace p ω x q' a t k) :
    ChangeTrace p ω x q a t (k+1) := by
  cases h with
  | change row different => exact .change (.next e row) different
  | self row rest => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ChangeTrace.self (.next e row) rest

/-- Every actual filtered return decomposes into completed self rows followed
by its first distinct return. No restart or replacement coin tape is used. -/
theorem trace_of_change {x a : α} {q : PreparedRow.State} {z : State α} {k : ℕ}
    (h : Progress.Evaluates (changes p ω) (x,q) (a,z) k) :
    ∃ t, z=start p a t ∧ ChangeTrace p ω x q a t k := by
  induction k generalizing x q with
  | zero => cases h
  | succ k ih =>
    cases h with
    | done e =>
      cases hr : (p x).step ω q with
      | inl r =>
        rcases r with ⟨b,t⟩
        by_cases hb : b=x
        · simp [changes,step,hr,hb] at e
        · simp only [changes,step,hr,hb,ite_false,Sum.inl.injEq,Prod.mk.injEq] at e
          rcases e with ⟨rfl,rfl⟩
          exact ⟨t,rfl,.change (.done hr) hb⟩
      | inr q' => simp [changes,step,hr] at e
    | next e rest =>
      cases hr : (p x).step ω q with
      | inl r =>
        rcases r with ⟨b,t⟩
        by_cases hb : b=x
        · subst b
          simp only [changes,step,hr,ite_true,Sum.inr.injEq] at e
          subst e
          obtain ⟨u,hz,ht⟩ := ih rest
          exact ⟨u,hz,by simpa [Nat.add_comm] using ChangeTrace.self (.done hr) ht⟩
        · simp [changes,step,hr,hb] at e
      | inr q' =>
        simp only [changes,step,hr,Sum.inr.injEq] at e
        subst e
        obtain ⟨t,hz,ht⟩ := ih rest
        exact ⟨t,hz,ht.prepend hr⟩

omit [DecidableEq α] in
theorem ChangeTrace.different {x a : α} {q : PreparedRow.State} {t k : ℕ}
    (h : ChangeTrace p ω x q a t k) : a ≠ x := by
  induction h with
  | change _ different => exact different
  | self _ _ ih => exact ih

/-- Actual ordered outputs of the existing filter, with finite work witnesses. -/
def prefixEvent (p : α → PreparedRow α) (x : α) (s : ℕ) (ys : List α) : Set Tape :=
  {ω | ∃ z k, Progress.Delivers (changes p ω) (start p x s) ys z k}

theorem prefix_nil (p : α → PreparedRow α) (x : α) (s : ℕ) :
    prefixEvent p x s []=Set.univ := by
  ext ω
  exact ⟨fun _ => Set.mem_univ _,fun _ => ⟨_,0,.nil _⟩⟩

theorem prefix_cons (p : α → PreparedRow α) (x a : α) (s : ℕ) (ys : List α)
    (ω : Tape) : ω ∈ prefixEvent p x s (a::ys) ↔
      ∃ t k, ChangeTrace p ω x ((p x).start s) a t k ∧
        ω ∈ prefixEvent p a t ys := by
  constructor
  · rintro ⟨z,k,h⟩
    cases h with
    | cons first rest =>
      obtain ⟨t,rfl,ht⟩ := trace_of_change first
      exact ⟨t,_,ht,_,_,rest⟩
  · rintro ⟨t,k,h,z,j,rest⟩
    exact ⟨z,k+j,.cons h.evaluates rest⟩

theorem prefix_same (p : α → PreparedRow α) (x : α) (s : ℕ) (ys : List α) :
    prefixEvent p x s (x::ys)=∅ := by
  ext ω
  simp only [Set.mem_empty_iff_false,iff_false]
  intro h
  obtain ⟨t,k,h,_⟩ := (prefix_cons _ _ _ _ _ _).mp h
  exact h.different rfl

/-- Split at the first completed raw row. The self branch preserves the same
requested output prefix and starts at that row's actual returned cursor. -/
theorem prefix_first_row (p : α → PreparedRow α) (x a : α) (s : ℕ)
    (ys : List α) (ω : Tape) : ω ∈ prefixEvent p x s (a::ys) ↔
      (∃ t k, Progress.Evaluates ((p x).step ω) ((p x).start s) (x,t) k ∧
        ω ∈ prefixEvent p x t (a::ys)) ∨
      (a ≠ x ∧ ∃ t k, Progress.Evaluates ((p x).step ω) ((p x).start s) (a,t) k ∧
        ω ∈ prefixEvent p a t ys) := by
  constructor
  · intro h
    obtain ⟨t,k,h,rest⟩ := (prefix_cons _ _ _ _ _ _).mp h
    cases h with
    | change row different => exact .inr ⟨different,_,_,row,rest⟩
    | self row tail => exact .inl ⟨_,_,row,(prefix_cons _ _ _ _ _ _).mpr ⟨_,_,tail,rest⟩⟩
  · rintro (⟨t,k,row,rest⟩ | ⟨different,t,k,row,rest⟩)
    · obtain ⟨u,j,tail,rest⟩ := (prefix_cons _ _ _ _ _ _).mp rest
      exact (prefix_cons _ _ _ _ _ _).mpr ⟨u,k+j,.self row tail,rest⟩
    · exact (prefix_cons _ _ _ _ _ _).mpr ⟨t,k,.change row different,rest⟩

open MeasureTheory in
 theorem measurableSteps (p : α → PreparedRow α) :
    ProbabilityProgress.MeasurableSteps (changes p) := by
  intro q r
  have he : {ω | changes p ω q=r} =
      ({ω : Tape | ω q.2.1=false} ∩ {ω | changes p (fun _ => false) q=r}) ∪
      ({ω : Tape | ω q.2.1=true} ∩ {ω | changes p (fun _ => true) q=r}) := by
    ext ω
    cases hb : ω q.2.1 <;>
      simp [changes,step,PreparedRow.step,Progress.mapReturn,BoundedUniform.step,hb]
  rw [he]
  have hm : Measurable (fun ω : Tape => ω q.2.1) := measurable_pi_apply q.2.1
  exact ((hm (measurableSet_singleton false)).inter (MeasurableSet.const _)).union
    ((hm (measurableSet_singleton true)).inter (MeasurableSet.const _))

open MeasureTheory in
 theorem measurable_prefix [Countable α] (p : α → PreparedRow α) (x : α) (s : ℕ)
    (ys : List α) : MeasurableSet (prefixEvent p x s ys) := by
  simp only [prefixEvent,Set.ofPred_exists]
  exact MeasurableSet.iUnion fun z => MeasurableSet.iUnion fun k =>
    ProbabilityProgress.measurable_delivers _ (measurableSteps p) _ _ _ _

omit [DecidableEq α] in
private theorem row_shift (r : PreparedRow α) (ω : Tape) (offset s t k : ℕ) (a : α) :
    Progress.Evaluates (r.step (CoinSuffix.suffix offset ω)) (r.start s) (a,t) k ↔
      Progress.Evaluates (r.step ω) (r.start (offset+s)) (a,offset+t) k := by
  simp only [r.evaluates_iff,BoundedUniform.accept_suffix_iff,Nat.add_assoc,
    Nat.add_left_cancel_iff]

omit [DecidableEq α] in
private theorem row_unshift (r : PreparedRow α) (ω : Tape) (offset s t k : ℕ) (a : α)
    (h : Progress.Evaluates (r.step ω) (r.start (offset+s)) (a,t) k) :
    ∃ u, t=offset+u ∧
      Progress.Evaluates (r.step (CoinSuffix.suffix offset ω)) (r.start s) (a,u) k := by
  obtain ⟨j,c,hc,ha,ht,hk⟩ := (r.evaluates_iff _ _ _ _ _).mp h
  refine ⟨s+BoundedUniform.width r.total*(j+1),by omega,?_⟩
  apply (row_shift r ω offset s _ k a).mpr
  simpa only [← Nat.add_assoc,← ht] using h

omit [DecidableEq α] in
theorem ChangeTrace.shift {x a : α} {s t k : ℕ} (offset : ℕ)
    (h : ChangeTrace p (CoinSuffix.suffix offset ω) x ((p x).start s) a t k) :
    ChangeTrace p ω x ((p x).start (offset+s)) a (offset+t) k := by
  generalize he : (p x).start s=q at h
  induction h generalizing s with
  | change row different =>
    rw [← he] at row
    exact .change ((row_shift _ _ _ _ _ _ _).mp row) different
  | self row rest ih =>
    rw [← he] at row
    exact .self ((row_shift _ _ _ _ _ _ _).mp row) (ih rfl)

omit [DecidableEq α] in
theorem ChangeTrace.unshift {x a : α} {s t k : ℕ} (offset : ℕ)
    (h : ChangeTrace p ω x ((p x).start (offset+s)) a t k) :
    ∃ u, t=offset+u ∧ ChangeTrace p (CoinSuffix.suffix offset ω) x ((p x).start s) a u k := by
  generalize he : (p x).start (offset+s)=q at h
  induction h generalizing s with
  | change row different =>
    rw [← he] at row
    obtain ⟨u,hu,hr⟩ := row_unshift _ _ _ _ _ _ _ row
    exact ⟨u,hu,.change hr different⟩
  | self row rest ih =>
    rw [← he] at row
    obtain ⟨v,hv,hr⟩ := row_unshift _ _ _ _ _ _ _ row
    obtain ⟨u,hu,ht⟩ := ih (s := v) (by rw [hv])
    exact ⟨u,hu,.self hr ht⟩

theorem prefix_shift (p : α → PreparedRow α) (offset : ℕ) (x : α) (s : ℕ)
    (ys : List α) (ω : Tape) :
    CoinSuffix.suffix offset ω ∈ prefixEvent p x s ys ↔
      ω ∈ prefixEvent p x (offset+s) ys := by
  induction ys generalizing x s with
  | nil => simp [prefix_nil]
  | cons a ys ih =>
    simp only [prefix_cons]
    constructor
    · rintro ⟨t,k,h,rest⟩
      exact ⟨offset+t,k,h.shift offset,(ih _ _).mp rest⟩
    · rintro ⟨t,k,h,rest⟩
      obtain ⟨u,rfl,ht⟩ := h.unshift offset
      exact ⟨u,k,ht,(ih _ _).mpr rest⟩

open MeasureTheory
open scoped ENNReal

theorem prefix_mass_shift [Countable α] (p : α → PreparedRow α) (x : α)
    (s : ℕ) (ys : List α) : law (prefixEvent p x s ys)=law (prefixEvent p x 0 ys) := by
  have he : prefixEvent p x s ys=CoinSuffix.suffix s ⁻¹' prefixEvent p x 0 ys := by
    ext ω
    simpa only [Set.mem_preimage,Nat.add_zero] using (prefix_shift p s x 0 ys ω).symm
  rw [he,← Measure.map_apply (CoinSuffix.measurable_suffix s) (measurable_prefix p x 0 ys),
    CoinSuffix.suffix_law]

private def rowThen (r : PreparedRow α) (s : ℕ) (a : α) (B : Set Tape) : Set Tape :=
  {ω | ∃ t k, Progress.Evaluates (r.step ω) (r.start s) (a,t) k ∧
    CoinSuffix.suffix t ω ∈ B}

omit [DecidableEq α] in
private theorem measurable_rowThen (r : PreparedRow α) (s : ℕ) (a : α)
    (B : Set Tape) (hB : MeasurableSet B) : MeasurableSet (rowThen r s a B) := by
  simp only [rowThen,Set.ofPred_exists,Set.ofPred_and]
  exact MeasurableSet.iUnion fun t => MeasurableSet.iUnion fun k =>
    (ProbabilityProgress.measurable_evaluates _ r.measurableSteps _ _ _).inter
      ((CoinSuffix.measurable_suffix t) hB)

/-- Freshness is applied to the actual first row return in each branch, including
the suppressed branch whose remaining request is unchanged. -/
theorem prefix_first_row_mass [Countable α] (p : α → PreparedRow α) (x a : α)
    (s : ℕ) (ys : List α) (ha : a ≠ x) :
    law (prefixEvent p x s (a::ys))=
      law ((p x).returns s x)*law (prefixEvent p x 0 (a::ys)) +
      law ((p x).returns s a)*law (prefixEvent p a 0 ys) := by
  have he : prefixEvent p x s (a::ys)=
      rowThen (p x) s x (prefixEvent p x 0 (a::ys)) ∪
      rowThen (p x) s a (prefixEvent p a 0 ys) := by
    ext ω
    rw [prefix_first_row]
    simp only [Set.mem_union,rowThen,Set.mem_ofPred_eq,
      prefix_shift,Nat.add_zero]
    constructor
    · rintro (h | ⟨_,h⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨ha,h⟩
  have hd : Disjoint (rowThen (p x) s x (prefixEvent p x 0 (a::ys)))
      (rowThen (p x) s a (prefixEvent p a 0 ys)) := by
    apply Set.disjoint_left.mpr
    rintro ω ⟨t,k,ht,_⟩ ⟨u,j,hu,_⟩
    exact ha (congrArg Prod.fst (hu.unique ht).1)
  rw [he,measure_union hd (measurable_rowThen _ _ _ _ (measurable_prefix _ _ _ _))]
  exact congrArg₂ (·+·) ((p x).stopped_mass _ _ _ (measurable_prefix _ _ _ _))
    ((p x).stopped_mass _ _ _ (measurable_prefix _ _ _ _))

end Operational
section Laws
open CoinPaths MeasureTheory
open scoped ENNReal

omit [DecidableEq α] in
private theorem path_nonneg (t : Table α α) (x : α) (ys : List α) :
    0 ≤ RowChain.pathMass t x ys := by
  induction ys generalizing x with
  | nil => exact zero_le_one
  | cons a ys ih => exact mul_nonneg (t.nonneg x a) (ih a)

private theorem mass_real (q : ℚ) (hq : 0 ≤ q) : (mass q).toReal=(q : ℝ) :=
  ENNReal.toReal_ofReal (by exact_mod_cast hq)

/-- The complete ordered law of the actual state-change filter. The renewal
identity is solved using positive exit probability; no replacement sampler is run. -/
theorem prefix_mass (t : Table α α) (positive : ∀ x,0<exit t x)
    (p : α → PreparedRow α)
    (hp : ∀ x s a, law ((p x).returns s a)=mass (t.entry x a))
    (x : α) (s : ℕ) (ys : List α) :
    law (prefixEvent p x s ys)=mass (RowChain.pathMass (jump t positive) x ys) := by
  induction ys generalizing x s with
  | nil => simp [prefix_nil,RowChain.pathMass]
  | cons a ys ih =>
    by_cases ha : a=x
    · subst a
      simp [prefix_same,RowChain.pathMass,jump]
    · have h := prefix_first_row_mass p x a 0 ys ha
      rw [hp,hp,ih] at h
      rw [prefix_mass_shift p x s]
      have hf : law (prefixEvent p x 0 (a::ys)) ≠ ∞ := measure_ne_top _ _
      have hp0 : mass (t.entry x x) ≠ ∞ := ENNReal.ofReal_ne_top
      have hp1 : mass (t.entry x a) ≠ ∞ := ENNReal.ofReal_ne_top
      have htail : mass (RowChain.pathMass (jump t positive) a ys) ≠ ∞ := ENNReal.ofReal_ne_top
      have hr := congrArg ENNReal.toReal h
      rw [ENNReal.toReal_add (ENNReal.mul_ne_top hp0 hf) (ENNReal.mul_ne_top hp1 htail),
        ENNReal.toReal_mul,ENNReal.toReal_mul,mass_real _ (t.nonneg x x),
        mass_real _ (t.nonneg x a),mass_real _ (path_nonneg _ _ _)] at hr
      apply (ENNReal.toReal_eq_toReal_iff' hf ENNReal.ofReal_ne_top).mp
      change (law (prefixEvent p x 0 (a::ys))).toReal =
        (mass (RowChain.pathMass (jump t positive) x (a::ys))).toReal
      rw [mass_real _ (path_nonneg _ _ _)]
      simp only [RowChain.pathMass,jump,Ne.symm ha,ite_false,Rat.cast_mul,Rat.cast_div]
      have he : (0 : ℝ) < 1-(t.entry x x : ℝ) := by
        exact_mod_cast positive x
      simp only [exit,Rat.cast_sub,Rat.cast_one]
      change _ = (t.entry x a : ℝ)/(1-(t.entry x x : ℝ))*_
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff (ne_of_gt he)).mpr
      change (law (prefixEvent p x 0 (a::ys))).toReal * (1-(t.entry x x : ℝ)) =
        (t.entry x a : ℝ) * (RowChain.pathMass (jump t positive) a ys : ℝ)
      nlinarith only [hr]

/-- A fixed-length observation of actual ordered changes. -/
def observation (p : α → PreparedRow α) (n : ℕ) (x : α) (s : ℕ)
    (B : Set (List α)) : Set Tape :=
  {ω | ∃ ys, ys.length=n ∧ ys ∈ B ∧ ω ∈ prefixEvent p x s ys}

omit [Fintype α] [DecidableEq α] in
private theorem delivery_same_length {S : Type} {f : Progress.Producer S α}
    {q z z' : S} {ys zs : List α} {k l : ℕ}
    (h : Progress.Delivers f q ys z k) (h' : Progress.Delivers f q zs z' l)
    (hlen : ys.length=zs.length) : ys=zs := by
  have he := h.coherent h'
  rw [← hlen,List.take_length,List.take_of_length_le (le_of_eq hlen.symm)] at he
  exact he

/-- Equality of finite observation laws follows from disjoint actual deliveries.
The reference jump sampler is used only to identify the measure, not as execution. -/
theorem observation_mass (t : Table α α) (positive : ∀ x,0<exit t x)
    (p : α → PreparedRow α)
    (hp : ∀ x s a, law ((p x).returns s a)=mass (t.entry x a))
    {m : ℕ} (e : Fin m ≃ α) (n : ℕ) (x : α) (s : ℕ) (B : Set (List α)) :
    law (observation p n x s B) =
      law {ω | ∃ ys, ys.length=n ∧ ys ∈ B ∧
        ω ∈ TableProducer.prefixEvent ((jump t positive).prepare e) x s ys} := by
  classical
  let E (ys : List α) := if ys.length=n ∧ ys ∈ B then prefixEvent p x s ys else ∅
  let F (ys : List α) := if ys.length=n ∧ ys ∈ B then
      TableProducer.prefixEvent ((jump t positive).prepare e) x s ys else ∅
  have he : observation p n x s B=⋃ ys,E ys := by
    ext ω; simp only [observation,Set.mem_ofPred_eq,Set.mem_iUnion,E]
    simp only [Set.mem_ite_empty_right,and_assoc]
  have hf : {ω | ∃ ys, ys.length=n ∧ ys ∈ B ∧
      ω ∈ TableProducer.prefixEvent ((jump t positive).prepare e) x s ys}=⋃ ys,F ys := by
    ext ω; simp only [Set.mem_ofPred_eq,Set.mem_iUnion,F]
    simp only [Set.mem_ite_empty_right,and_assoc]
  have hdE : Pairwise (fun ys zs => Disjoint (E ys) (E zs)) := by
    intro ys zs hne
    by_cases hy : ys.length=n ∧ ys ∈ B
    · by_cases hz : zs.length=n ∧ zs ∈ B
      · simp only [E,hy,hz,true_and,ite_true]
        apply Set.disjoint_left.mpr
        rintro ω ⟨z,k,h⟩ ⟨z',l,h'⟩
        exact hne (delivery_same_length h h' (hy.1.trans hz.1.symm))
      · simp [E,hz]
    · simp [E,hy]
  have hdF : Pairwise (fun ys zs => Disjoint (F ys) (F zs)) := by
    intro ys zs hne
    by_cases hy : ys.length=n ∧ ys ∈ B
    · by_cases hz : zs.length=n ∧ zs ∈ B
      · simp only [F,hy,hz,true_and,ite_true]
        apply Set.disjoint_left.mpr
        rintro ω ⟨z,k,h⟩ ⟨z',l,h'⟩
        exact hne (delivery_same_length h h' (hy.1.trans hz.1.symm))
      · simp [F,hz]
    · simp [F,hy]
  have hmE (ys : List α) : MeasurableSet (E ys) := by
    by_cases h : ys.length=n ∧ ys ∈ B
    · simpa only [E,h,true_and,ite_true] using measurable_prefix p x s ys
    · simp [E,h]
  have hmF (ys : List α) : MeasurableSet (F ys) := by
    by_cases h : ys.length=n ∧ ys ∈ B
    · simp only [F,h,true_and,ite_true,TableProducer.prefix_eq]
      exact RowChain.measurable_returns _ _ _ _ _
    · simp [F,h]
  rw [he,hf,measure_iUnion hdE hmE,measure_iUnion hdF hmF]
  apply tsum_congr
  intro ys
  by_cases h : ys.length=n ∧ ys ∈ B
  · simp only [E,F,h,true_and,ite_true,prefix_mass t positive p hp,TableProducer.prefix_mass]
  · simp [E,F,h]

theorem measurable_observation (p : α → PreparedRow α) (n : ℕ) (x : α)
    (s : ℕ) (B : Set (List α)) : MeasurableSet (observation p n x s B) := by
  simp only [observation,Set.ofPred_exists,Set.ofPred_and]
  exact MeasurableSet.iUnion fun ys => (MeasurableSet.const _).inter
    ((MeasurableSet.const _).inter (measurable_prefix p x s ys))

/-- Positive exit at each state makes every finite change prefix productive on
almost every tape. The original machine and its partial row states are retained. -/
theorem almostSureProductive (t : Table α α) (positive : ∀ x,0<exit t x)
    (p : α → PreparedRow α)
    (hp : ∀ x s a, law ((p x).returns s a)=mass (t.entry x a))
    {m : ℕ} (e : Fin m ≃ α) (x : α) (s : ℕ) :
    ProbabilityProgress.AlmostSureProductive law (TableProducer.changes p)
      (fun _ => TableProducer.start p x s) := by
  intro n
  have hRef := TableProducer.almostSureProductive (jump t positive) e x s n
  have hRef' : ∀ᵐ ω ∂law, ∃ ys, ys.length=n ∧ ys ∈ (Set.univ : Set (List α)) ∧
      ω ∈ TableProducer.prefixEvent ((jump t positive).prepare e) x s ys := by
    filter_upwards [hRef] with ω h
    obtain ⟨ys,z,k,hlen,hd⟩ := h
    exact ⟨ys,hlen,Set.mem_univ _,z,k,hd⟩
  have hmass : law (observation p n x s Set.univ)=1 := by
    rw [observation_mass t positive p hp e]
    apply (mem_ae_iff_prob_eq_one ?_).mp hRef'
    simp only [Set.ofPred_exists,Set.ofPred_and]
    apply MeasurableSet.iUnion
    intro ys
    apply (MeasurableSet.const _).inter
    apply (MeasurableSet.const _).inter
    rw [TableProducer.prefix_eq]
    exact RowChain.measurable_returns _ _ _ _ _
  have h := (mem_ae_iff_prob_eq_one (measurable_observation p n x s Set.univ)).mpr hmass
  filter_upwards [h] with ω h
  obtain ⟨ys,hlen,_,z,k,hd⟩ := h
  exact ⟨ys,z,k,hlen,hd⟩

/-- Drop n completed changes and observe a block, still on the same execution. -/
def blockEvent (p : α → PreparedRow α) (n : ℕ) (x : α) (s : ℕ)
    (ys : List α) : Set Tape := observation p (n+ys.length) x s {zs | zs.drop n=ys}

theorem block_mass (t : Table α α) (positive : ∀ x,0<exit t x)
    (p : α → PreparedRow α)
    (hp : ∀ x s a, law ((p x).returns s a)=mass (t.entry x a))
    {m : ℕ} (e : Fin m ≃ α) (n : ℕ) (x : α) (s : ℕ) (ys : List α) :
    law (blockEvent p n x s ys)=
      law (TableProducer.blockEvent ((jump t positive).prepare e) n x s ys) :=
  observation_mass t positive p hp e _ _ _ _

theorem stationary_blocks (t : Table α α) (positive : ∀ x,0<exit t x)
    (p : α → PreparedRow α)
    (hp : ∀ x s a, law ((p x).returns s a)=mass (t.entry x a))
    {m : ℕ} (e : Fin m ≃ α) (initial : Table Unit α)
    (stationary : ∀ y, ∑ x, initial.entry () x*t.entry x y=initial.entry () y)
    (n s : ℕ) (ys : List α) :
    (∑ x, mass ((tilted t positive initial).entry () x)*law (blockEvent p n x s ys))=
      ∑ x, mass ((tilted t positive initial).entry () x)*
        mass (RowChain.pathMass (jump t positive) x ys) := by
  simp_rw [block_mass t positive p hp e]
  apply TableProducer.stationary_blocks
  intro y
  simp_rw [← mass_mul _ _ ((tilted t positive initial).nonneg () _)]
  rw [← mass_sum _ _ (fun x _ => mul_nonneg ((tilted t positive initial).nonneg () x)
    ((jump t positive).nonneg x y)),tilted_stationary t positive initial stationary]

/-- Initialization is itself a completed row draw. Its actual returned cursor
starts the filtered chain; the initial sample is hidden before n changes. -/
def initializedBlock (r : PreparedRow α) (p : α → PreparedRow α)
    (n s : ℕ) (ys : List α) : Set Tape :=
  {ω | ∃ a u k, Progress.Evaluates (r.step ω) (r.start s) (a,u) k ∧
    ω ∈ blockEvent p n a u ys}

omit [Fintype α] in
theorem block_shift (p : α → PreparedRow α) (n : ℕ) (x : α) (s : ℕ)
    (ys : List α) (ω : Tape) :
    CoinSuffix.suffix s ω ∈ blockEvent p n x 0 ys ↔ ω ∈ blockEvent p n x s ys := by
  simp only [blockEvent,observation,Set.mem_ofPred_eq,prefix_shift,Nat.add_zero]

theorem measurable_block (p : α → PreparedRow α) (n : ℕ) (x : α) (s : ℕ)
    (ys : List α) : MeasurableSet (blockEvent p n x s ys) :=
  measurable_observation p _ _ _ _

/-- Full block observation after the actual initialization draw, not a separate
initial mixture. Freshness is applied at its random stopping cursor. -/
theorem initializedBlock_mass (r : PreparedRow α) (p : α → PreparedRow α)
    (n s : ℕ) (ys : List α) :
    law (initializedBlock r p n s ys)=∑ a,
      law (r.returns s a)*law (blockEvent p n a 0 ys) := by
  have he : initializedBlock r p n s ys=⋃ a : α, rowThen r s a (blockEvent p n a 0 ys) := by
    ext ω
    simp only [initializedBlock,rowThen,Set.mem_ofPred_eq,Set.mem_iUnion,block_shift]
  have hd : Pairwise (fun a b => Disjoint (rowThen r s a (blockEvent p n a 0 ys))
      (rowThen r s b (blockEvent p n b 0 ys))) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    rintro ω ⟨u,k,ha,_⟩ ⟨v,l,hb,_⟩
    exact hab (congrArg Prod.fst (ha.unique hb).1)
  rw [he,measure_iUnion hd (fun a => measurable_rowThen _ _ _ _ (measurable_block _ _ _ _ _)),
    tsum_fintype]
  exact Finset.sum_congr rfl fun a _ => r.stopped_mass _ _ _ (measurable_block _ _ _ _ _)

/-- Executed tilted initialization supplies stationary ordered change blocks
under every finite observation shift. Initialization is not counted as a change. -/
theorem initialized_stationary_blocks (t : Table α α) (positive : ∀ x,0<exit t x)
    (p : α → PreparedRow α)
    (hp : ∀ x s a, law ((p x).returns s a)=mass (t.entry x a))
    {m : ℕ} (e : Fin m ≃ α) (initial : Table Unit α)
    (stationary : ∀ y, ∑ x, initial.entry () x*t.entry x y=initial.entry () y)
    (n s : ℕ) (ys : List α) :
    law (initializedBlock ((tilted t positive initial).prepare e ()) p n s ys)=
      ∑ x, mass ((tilted t positive initial).entry () x)*
        mass (RowChain.pathMass (jump t positive) x ys) := by
  rw [initializedBlock_mass]
  simp_rw [Table.prepare_returns_mass]
  exact stationary_blocks t positive p hp e initial stationary n 0 ys

/-- A completed change followed by an arbitrary observation of the remaining
coin tape. The cursor is the actual change return, including suppressed rows. -/
def changeThen (p : α → PreparedRow α) (x : α) (s : ℕ) (a : α)
    (B : Set Tape) : Set Tape :=
  {ω | ∃ u k, ChangeTrace p ω x ((p x).start s) a u k ∧ CoinSuffix.suffix u ω ∈ B}

omit [Fintype α] in
theorem trace_iff_evaluates (p : α → PreparedRow α) (ω : Tape) (x a : α)
    (q : PreparedRow.State) (u k : ℕ) :
    ChangeTrace p ω x q a u k ↔
      Progress.Evaluates (TableProducer.changes p ω) (x,q)
        (a,TableProducer.start p a u) k := by
  constructor
  · exact ChangeTrace.evaluates
  · intro h
    obtain ⟨v,he,ht⟩ := trace_of_change h
    have hv : u=v := congrArg (fun z => z.2.1) he
    subst v
    exact ht

theorem measurable_changeThen (p : α → PreparedRow α) (x : α) (s : ℕ) (a : α)
    (B : Set Tape) (hB : MeasurableSet B) : MeasurableSet (changeThen p x s a B) := by
  simp only [changeThen,Set.ofPred_exists,Set.ofPred_and,trace_iff_evaluates]
  exact MeasurableSet.iUnion fun u => MeasurableSet.iUnion fun k =>
    (ProbabilityProgress.measurable_evaluates _ (measurableSteps p) _ _ _).inter
      ((CoinSuffix.measurable_suffix u) hB)

private theorem suffix_add (ω : Tape) (s u : ℕ) :
    CoinSuffix.suffix u (CoinSuffix.suffix s ω)=CoinSuffix.suffix (s+u) ω := by
  funext i
  simp [CoinSuffix.suffix,Nat.add_assoc]

omit [Fintype α] [DecidableEq α] in
theorem changeThen_shift (p : α → PreparedRow α) (offset : ℕ) (x a : α)
    (s : ℕ) (B : Set Tape) (ω : Tape) :
    CoinSuffix.suffix offset ω ∈ changeThen p x s a B ↔
      ω ∈ changeThen p x (offset+s) a B := by
  constructor
  · rintro ⟨u,k,h,hB⟩
    exact ⟨offset+u,k,h.shift offset,by simpa only [suffix_add] using hB⟩
  · rintro ⟨u,k,h,hB⟩
    obtain ⟨v,rfl,ht⟩ := h.unshift offset
    exact ⟨v,k,ht,by simpa only [suffix_add] using hB⟩

theorem changeThen_mass_shift (p : α → PreparedRow α) (x a : α) (s : ℕ)
    (B : Set Tape) (hB : MeasurableSet B) :
    law (changeThen p x s a B)=law (changeThen p x 0 a B) := by
  have he : changeThen p x s a B=CoinSuffix.suffix s ⁻¹' changeThen p x 0 a B := by
    ext ω
    simpa only [Set.mem_preimage,Nat.add_zero] using (changeThen_shift p s x a 0 B ω).symm
  rw [he,← Measure.map_apply (CoinSuffix.measurable_suffix s) (measurable_changeThen p x 0 a B hB),
    CoinSuffix.suffix_law]

omit [Fintype α] [DecidableEq α] in
theorem changeThen_first_row (p : α → PreparedRow α) (x a : α) (s : ℕ)
    (B : Set Tape) (ha : a≠x) :
    changeThen p x s a B = rowThen (p x) s x (changeThen p x 0 a B) ∪ rowThen (p x) s a B := by
  ext ω
  simp only [Set.mem_union,rowThen,Set.mem_ofPred_eq,changeThen_shift,Nat.add_zero]
  constructor
  · rintro ⟨u,k,h,hB⟩
    cases h with
    | change row different => exact Or.inr ⟨_,_,row,hB⟩
    | self row rest => exact Or.inl ⟨_,_,row,_,_,rest,hB⟩
  · rintro (⟨u,k,row,v,l,tail,hB⟩ | ⟨u,k,row,hB⟩)
    · exact ⟨v,k+l,.self row tail,hB⟩
    · exact ⟨u,k,.change row ha,hB⟩

/-- Freshness at the actual first-change cursor, despite the unbounded number
of suppressed raw transitions. This is proved by the same renewal equation. -/
theorem change_stopped_mass (t : Table α α) (positive : ∀ x,0<exit t x)
    (p : α → PreparedRow α)
    (hp : ∀ x s a, law ((p x).returns s a)=mass (t.entry x a))
    (x a : α) (s : ℕ) (B : Set Tape) (hB : MeasurableSet B) :
    law (changeThen p x s a B)=mass ((jump t positive).entry x a)*law B := by
  by_cases ha : a=x
  · subst a
    have he : changeThen p x s x B=∅ := by
      ext ω
      exact ⟨fun ⟨_,_,h,_⟩ => h.different rfl,fun h => h.elim⟩
    simp [he,jump]
  · have hd : Disjoint (rowThen (p x) 0 x (changeThen p x 0 a B)) (rowThen (p x) 0 a B) := by
      apply Set.disjoint_left.mpr
      rintro ω ⟨u,k,h,_⟩ ⟨v,l,h',_⟩
      exact ha (congrArg Prod.fst (h'.unique h).1)
    have h := congrArg law (changeThen_first_row p x a 0 B ha)
    rw [measure_union hd (measurable_rowThen _ _ _ _ hB)] at h
    unfold rowThen at h
    rw [(p x).stopped_mass _ _ _ (measurable_changeThen p x 0 a B hB),
      (p x).stopped_mass _ _ _ hB,hp,hp] at h
    rw [changeThen_mass_shift p x a s B hB]
    have hf : law (changeThen p x 0 a B) ≠ ∞ := measure_ne_top _ _
    have hfB : law B ≠ ∞ := measure_ne_top _ _
    have h0 : mass (t.entry x x) ≠ ∞ := ENNReal.ofReal_ne_top
    have h1 : mass (t.entry x a) ≠ ∞ := ENNReal.ofReal_ne_top
    have hr := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top h0 hf) (ENNReal.mul_ne_top h1 hfB),
      ENNReal.toReal_mul,ENNReal.toReal_mul,mass_real _ (t.nonneg x x),
      mass_real _ (t.nonneg x a)] at hr
    apply (ENNReal.toReal_eq_toReal_iff' hf (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfB)).mp
    change (law (changeThen p x 0 a B)).toReal =
      (mass ((jump t positive).entry x a)*law B).toReal
    rw [ENNReal.toReal_mul,mass_real _ ((jump t positive).nonneg x a)]
    simp only [jump,Ne.symm ha,ite_false,Rat.cast_div,exit,Rat.cast_sub,Rat.cast_one]
    have he : (0 : ℝ)<1-(t.entry x x : ℝ) := by exact_mod_cast positive x
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (ne_of_gt he)).mpr
    nlinarith only [hr]

/-- Evaluation-form freshness for consumers of the operational producer API. -/
theorem change_stopped_mass_evaluates (t : Table α α) (positive : ∀ x,0<exit t x)
    (p : α → PreparedRow α)
    (hp : ∀ x s a, law ((p x).returns s a)=mass (t.entry x a))
    (x a : α) (s : ℕ) (B : Set Tape) (hB : MeasurableSet B) :
    law {ω | ∃ u k, Progress.Evaluates (TableProducer.changes p ω)
      (TableProducer.start p x s) (a,TableProducer.start p a u) k ∧
        CoinSuffix.suffix u ω ∈ B}=mass ((jump t positive).entry x a)*law B := by
  simpa only [changeThen,trace_iff_evaluates,TableProducer.start] using
    change_stopped_mass t positive p hp x a s B hB

end Laws
end Applications.Probability.StateChangeSampler
