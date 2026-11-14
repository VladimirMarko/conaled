import Applications.Probability.TableSamplerComposition

/-!
# Finite chains on one tape

Each transition uses the current row and the previous returned cursor. The
returned list retains the whole path. A zero-draw chain has one administrative
return step; that step does not inspect a bit.
-/
namespace Applications.Probability.RowChain
open CoinPaths MeasureTheory
open scoped ENNReal
variable {α : Type}

/-- At each level, either run the current row or retain its result while running
the rest of the chain. -/
def State (α : Type) : ℕ → Type
  | 0 => α × ℕ
  | n+1 => Sum (α × PreparedRow.State) (α × State α n)

def start (p : α → PreparedRow α) : (n : ℕ) → α → ℕ → State α n
  | 0,x,s => (x,s)
  | _n+1,x,s => .inl (x,(p x).start s)

def step (p : α → PreparedRow α) (ω : Tape) :
    (n : ℕ) → Progress.Machine (State α n) (List α × ℕ)
  | 0 => fun (_,s) => .inl ([],s)
  | n+1 => Progress.sequential
      (Progress.family (fun x => (p x).step ω))
      (Progress.family (fun a => Progress.mapReturn (fun r => (a::r.1,r.2)) (step p ω n)))
      (fun a => (a.1,start p n a.1 a.2))

/-- Operational chain traces, retaining each intermediate cursor and work
through the recursive derivations. -/
inductive Trace (p : α → PreparedRow α) (ω : Tape) :
    ℕ → α → ℕ → List α → ℕ → ℕ → Prop
  | zero (x : α) (s : ℕ) : Trace p ω 0 x s [] s 1
  | next {n x s a t i ys u j}
      (first : Progress.Evaluates ((p x).step ω) ((p x).start s) (a,t) i)
      (rest : Trace p ω n a t ys u j) : Trace p ω (n+1) x s (a::ys) u (i+j)

theorem evaluates_of_trace {p : α → PreparedRow α} {ω : Tape} {n x s ys t k}
    (h : Trace p ω n x s ys t k) :
    Progress.Evaluates (step p ω n) (start p n x s) (ys,t) k := by
  induction h with
  | zero x s => exact .done rfl
  | @next n x s a t i ys u j h rest ih =>
    exact Progress.sequential_evaluates (Progress.family_evaluates h)
      (Progress.family_evaluates (Progress.mapReturn_evaluates ih))

theorem trace_of_evaluates {p : α → PreparedRow α} {ω : Tape} {n x s ys t k}
    (h : Progress.Evaluates (step p ω n) (start p n x s) (ys,t) k) :
    Trace p ω n x s ys t k := by
  induction n generalizing x s ys t k with
  | zero =>
    cases h with
    | done e =>
      simp only [step] at e
      rcases e with ⟨rfl,rfl⟩
      exact .zero x s
    | next e _ => simp [step,start] at e
  | succ n ih =>
    obtain ⟨⟨a,u⟩,i,j,hi,hj,hk⟩ := Progress.sequential_left_inv h
    have hf := Progress.family_evaluates_inv hi
    have hs := Progress.family_evaluates_inv hj
    obtain ⟨⟨zs,v⟩,hz,he⟩ := Progress.mapReturn_evaluates_inv hs
    simp only [Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    subst k
    exact .next hf (ih hz)

theorem trace_length {p : α → PreparedRow α} {ω : Tape} {n x s ys t k}
    (h : Trace p ω n x s ys t k) : ys.length=n := by
  induction h with
  | zero => rfl
  | next h rest ih => simp [ih]

/-- The terminal administrative return is the only transition not reading a bit. -/
theorem trace_work {p : α → PreparedRow α} {ω : Tape} {n x s ys t k}
    (h : Trace p ω n x s ys t k) : t+1=s+k := by
  induction h with
  | zero => rfl
  | next h rest ih =>
    obtain ⟨r,a,ha,hb,ht,hk⟩ := (PreparedRow.evaluates_iff _ _ _ _ _ _).mp h
    omega

/-- The entire output path, observed through genuine finite derivations. -/
def returns (p : α → PreparedRow α) (n : ℕ) (x : α) (s : ℕ) (ys : List α) : Set Tape :=
  {ω | ∃ t k, Trace p ω n x s ys t k}

theorem returns_operational (p : α → PreparedRow α) (n : ℕ) (x : α) (s : ℕ) (ys : List α) :
    returns p n x s ys={ω | ∃ t k, Progress.Evaluates (step p ω n) (start p n x s) (ys,t) k} := by
  ext ω
  exact ⟨fun ⟨t,k,h⟩ => ⟨t,k,evaluates_of_trace h⟩,
    fun ⟨t,k,h⟩ => ⟨t,k,trace_of_evaluates h⟩⟩

theorem returns_zero (p : α → PreparedRow α) (x : α) (s : ℕ) (ys : List α) (ω : Tape) :
    ω∈returns p 0 x s ys ↔ ys=[] := by
  constructor
  · rintro ⟨t,k,h⟩; cases h; rfl
  · rintro rfl; exact ⟨s,1,.zero x s⟩

theorem returns_nil_succ (p : α → PreparedRow α) (n : ℕ) (x : α) (s : ℕ) :
    returns p (n+1) x s []=∅ := by
  ext ω
  simp only [returns,Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
  rintro ⟨t,k,h⟩
  have := trace_length h
  simp at this

theorem returns_cons (p : α → PreparedRow α) (n : ℕ) (x a : α) (s : ℕ)
    (ys : List α) (ω : Tape) :
    ω∈returns p (n+1) x s (a::ys) ↔
      ∃ t k, Progress.Evaluates ((p x).step ω) ((p x).start s) (a,t) k ∧
        ω∈returns p n a t ys := by
  constructor
  · rintro ⟨u,l,h⟩
    cases h with
    | next hf hr => exact ⟨_,_,hf,_,_,hr⟩
  · rintro ⟨t,k,h,u,l,j⟩
    exact ⟨u,k+l,.next h j⟩

theorem returns_cons_atoms (p : α → PreparedRow α) (n : ℕ) (x a : α) (s : ℕ)
    (ys : List α) (ω : Tape) :
    ω∈returns p (n+1) x s (a::ys) ↔
      ∃ r, ∃ c : Fin (p x).total,
        BoundedUniform.Accept (p x).total ω s r c ∧ (p x).select c=a ∧
        ω∈returns p n a (s+BoundedUniform.width (p x).total*(r+1)) ys := by
  rw [returns_cons]
  constructor
  · rintro ⟨t,k,h,hr⟩
    obtain ⟨r,c,hc,ha,ht,hk⟩ := ((p x).evaluates_iff _ _ _ _ _).mp h
    subst t
    exact ⟨r,c,hc,ha,hr⟩
  · rintro ⟨r,c,hc,ha,hr⟩
    exact ⟨_,_,((p x).evaluates_iff _ _ _ _ _).mpr ⟨r,c,hc,ha,rfl,rfl⟩,hr⟩

theorem returns_shift (p : α → PreparedRow α) (n : ℕ) (x : α) (s v : ℕ)
    (ys : List α) (ω : Tape) :
    CoinSuffix.suffix s ω∈returns p n x v ys ↔ ω∈returns p n x (s+v) ys := by
  induction n generalizing x v ys with
  | zero => simp only [returns_zero]
  | succ n ih =>
    cases ys with
    | nil => simp [returns_nil_succ]
    | cons a ys =>
      simp only [returns_cons_atoms,BoundedUniform.accept_suffix_iff,ih,Nat.add_assoc]

theorem measurable_returns (p : α → PreparedRow α) (n : ℕ) (x : α) (s : ℕ)
    (ys : List α) : MeasurableSet (returns p n x s ys) := by
  induction n generalizing x s ys with
  | zero =>
    have he : returns p 0 x s ys={ω : Tape | ys=[]} := Set.ext (returns_zero p x s ys)
    rw [he]; exact MeasurableSet.const _
  | succ n ih =>
    cases ys with
    | nil => rw [returns_nil_succ]; exact MeasurableSet.empty
    | cons a ys =>
      have he : returns p (n+1) x s (a::ys)=⋃ t, ⋃ k,
          {ω | Progress.Evaluates ((p x).step ω) ((p x).start s) (a,t) k} ∩
            returns p n a t ys := by
        ext ω; simp only [returns_cons,Set.mem_iUnion,Set.mem_inter_iff,Set.mem_ofPred_eq]
      rw [he]
      exact MeasurableSet.iUnion fun t => MeasurableSet.iUnion fun k =>
        (ProbabilityProgress.measurable_evaluates _ (p x).measurableSteps _ _ _).inter (ih _ _ _)

/-- The full path law factors in transition order. Each factorization uses
freshness at the preceding actual returned cursor. -/
theorem returns_cons_mass (p : α → PreparedRow α) (n : ℕ) (x a : α) (s : ℕ)
    (ys : List α) :
    law (returns p (n+1) x s (a::ys))=
      law ((p x).returns s a)*law (returns p n a 0 ys) := by
  have he : returns p (n+1) x s (a::ys)={ω | ∃ t k,
      Progress.Evaluates ((p x).step ω) ((p x).start s) (a,t) k ∧
        CoinSuffix.suffix t ω∈returns p n a 0 ys} := by
    ext ω
    simp only [returns_cons,returns_shift,Nat.add_zero,Set.mem_ofPred_eq]
  rw [he]
  exact (p x).stopped_mass s a _ (measurable_returns p n a 0 ys)

/-- Rational path mass retains the complete ordered sequence of outcomes. -/
def pathMass [Fintype α] (t : Table α α) : α → List α → ℚ
  | _,[] => 1
  | x,a::ys => t.entry x a * pathMass t a ys

theorem table_path_mass [Fintype α] [DecidableEq α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (n : ℕ) (x : α) (s : ℕ) (ys : List α)
    (hlen : ys.length=n) :
    law (returns (t.prepare e) n x s ys)=mass (pathMass t x ys) := by
  induction ys generalizing n x s with
  | nil =>
    have : n=0 := by simpa using hlen.symm
    subst n
    have he : returns (t.prepare e) 0 x s []=Set.univ := by
      ext ω; simp [returns_zero]
    simp only [List.length_nil]
    rw [he,measure_univ]; simp [pathMass]
  | cons a ys ih =>
    have : n=ys.length+1 := hlen.symm
    subst n
    simp only [List.length_cons]
    rw [returns_cons_mass,t.prepare_returns_mass,ih _ _ _ rfl,pathMass,
      mass_mul _ _ (t.nonneg x a)]

/-- Last state after a path; the empty path retains the input. -/
def finalState : α → List α → α
  | x,[] => x
  | _,a::ys => finalState a ys

def finalEvent (p : α → PreparedRow α) (n : ℕ) (x : α) (s : ℕ) (z : α) : Set Tape :=
  {ω | ∃ ys, ω∈returns p n x s ys ∧ finalState x ys=z}

theorem final_zero (p : α → PreparedRow α) (x z : α) (s : ℕ) :
    finalEvent p 0 x s z={_ω : Tape | x=z} := by
  ext ω
  simp only [finalEvent,Set.mem_ofPred_eq,returns_zero]
  constructor
  · rintro ⟨ys,rfl,h⟩; exact h
  · intro h; exact ⟨[],rfl,h⟩

theorem final_cons (p : α → PreparedRow α) (n : ℕ) (x z : α) (s : ℕ) (ω : Tape) :
    ω∈finalEvent p (n+1) x s z ↔ ∃ a t k,
      Progress.Evaluates ((p x).step ω) ((p x).start s) (a,t) k ∧
      ω∈finalEvent p n a t z := by
  constructor
  · rintro ⟨ys,hy,hz⟩
    cases ys with
    | nil => rw [returns_nil_succ] at hy; exact False.elim hy
    | cons a ys =>
      obtain ⟨t,k,h,hr⟩ := (returns_cons _ _ _ _ _ _ _).mp hy
      exact ⟨a,t,k,h,ys,hr,hz⟩
  · rintro ⟨a,t,k,h,ys,hr,hz⟩
    exact ⟨a::ys,(returns_cons _ _ _ _ _ _ _).mpr ⟨t,k,h,hr⟩,hz⟩

theorem final_shift (p : α → PreparedRow α) (n : ℕ) (x z : α) (s : ℕ) (ω : Tape) :
    CoinSuffix.suffix s ω∈finalEvent p n x 0 z ↔ ω∈finalEvent p n x s z := by
  simp only [finalEvent,Set.mem_ofPred_eq,returns_shift,Nat.add_zero]

theorem measurable_final [Countable α] (p : α → PreparedRow α) (n : ℕ)
    (x z : α) (s : ℕ) : MeasurableSet (finalEvent p n x s z) := by
  have he : finalEvent p n x s z=⋃ ys : List α,
      returns p n x s ys ∩ {ω : Tape | finalState x ys=z} := by
    ext ω; simp [finalEvent]
  rw [he]
  exact MeasurableSet.iUnion fun ys => (measurable_returns p n x s ys).inter (MeasurableSet.const _)

theorem final_succ_mass [Fintype α] (p : α → PreparedRow α) (n : ℕ)
    (x z : α) (s : ℕ) :
    law (finalEvent p (n+1) x s z)=∑ a,
      law ((p x).returns s a)*law (finalEvent p n a 0 z) := by
  have he : finalEvent p (n+1) x s z=⋃ a : α, {ω | ∃ t k,
      Progress.Evaluates ((p x).step ω) ((p x).start s) (a,t) k ∧
        CoinSuffix.suffix t ω∈finalEvent p n a 0 z} := by
    ext ω; simp only [Set.mem_iUnion,Set.mem_ofPred_eq,final_cons,final_shift]
  have hm (a : α) : MeasurableSet {ω | ∃ t k,
      Progress.Evaluates ((p x).step ω) ((p x).start s) (a,t) k ∧
        CoinSuffix.suffix t ω∈finalEvent p n a 0 z} := by
    simp only [Set.ofPred_exists,Set.ofPred_and]
    exact MeasurableSet.iUnion fun t => MeasurableSet.iUnion fun k =>
      (ProbabilityProgress.measurable_evaluates _ (p x).measurableSteps _ _ _).inter
        ((CoinSuffix.measurable_suffix t) (measurable_final p n a z 0))
  rw [he,measure_iUnion]
  · simp only [tsum_fintype]
    exact Finset.sum_congr rfl fun a _ => (p x).stopped_mass s a _ (measurable_final p n a z 0)
  · intro a b hab
    apply Set.disjoint_left.mpr
    rintro ω ⟨t,k,ha,_⟩ ⟨u,l,hb,_⟩
    exact hab (congrArg Prod.fst (ha.unique hb).1)
  · exact hm

/-- Iterated operational transitions recover the existing composed rational table. -/
theorem table_final_mass [Fintype α] [DecidableEq α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (n : ℕ) (x z : α) (s : ℕ) :
    law (finalEvent (t.prepare e) n x s z)=mass ((t.steps n).entry x z) := by
  induction n generalizing x s with
  | zero =>
    rw [final_zero]
    by_cases h : x=z <;> simp [h,Table.steps,Table.deterministic]
  | succ n ih =>
    rw [final_succ_mass]
    simp_rw [t.prepare_returns_mass,ih,← mass_mul _ _ (t.nonneg _ _)]
    rw [← mass_sum _ _ (fun a _ => mul_nonneg (t.nonneg x a) ((t.steps n).nonneg a z))]
    -- The operational recursion starts with t; table iteration associates the other way.
    congr 1
    clear ih
    induction n generalizing x z with
    | zero => simp [Table.steps,Table.comp,Table.deterministic]
    | succ n ih =>
      simp only [Table.steps,Table.comp]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [← mul_assoc,← Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [ih]
      rfl

theorem termination_eq (p : α → PreparedRow α) (n : ℕ) (x : α) (s : ℕ) :
    ProbabilityProgress.termination (fun ω => step p ω n) (start p n x s)=
      ⋃ z, finalEvent p n x s z := by
  ext ω
  constructor
  · rintro ⟨⟨ys,t⟩,k,h⟩
    exact Set.mem_iUnion.mpr ⟨finalState x ys,ys,⟨t,k,trace_of_evaluates h⟩,rfl⟩
  · intro h
    obtain ⟨z,ys,⟨t,k,hy⟩,_⟩ := Set.mem_iUnion.mp h
    exact ⟨(ys,t),k,evaluates_of_trace hy⟩

theorem final_disjoint (p : α → PreparedRow α) (n : ℕ) (x : α) (s : ℕ) :
    Pairwise (fun y z => Disjoint (finalEvent p n x s y) (finalEvent p n x s z)) := by
  intro y z hyz
  apply Set.disjoint_left.mpr
  rintro ω ⟨ys,⟨t,k,hy⟩,ey⟩ ⟨zs,⟨u,l,hz⟩,ez⟩
  have he : ys=zs := congrArg Prod.fst ((evaluates_of_trace hy).unique (evaluates_of_trace hz)).1
  subst zs
  exact hyz (ey.symm.trans ez)

theorem table_termination_mass [Fintype α] [DecidableEq α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (n : ℕ) (x : α) (s : ℕ) :
    law (ProbabilityProgress.termination (fun ω => step (t.prepare e) ω n)
      (start (t.prepare e) n x s))=1 := by
  rw [termination_eq,measure_iUnion (final_disjoint _ _ _ _)
    (fun z => measurable_final _ _ _ _ _)]
  simp only [tsum_fintype,table_final_mass]
  rw [← mass_sum _ _ (fun z _ => (t.steps n).nonneg x z),(t.steps n).sum_row,mass_one]

theorem table_ae_terminates [Fintype α] [DecidableEq α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (n : ℕ) (x : α) (s : ℕ) :
    ∀ᵐ ω ∂law, Progress.Terminates (step (t.prepare e) ω n) (start (t.prepare e) n x s) := by
  apply (mem_ae_iff_prob_eq_one ?_).mpr (table_termination_mass t e n x s)
  rw [termination_eq]
  exact MeasurableSet.iUnion fun z => measurable_final _ _ _ _ _

theorem table_divergence_mass [Fintype α] [DecidableEq α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (n : ℕ) (x : α) (s : ℕ) :
    law (ProbabilityProgress.termination (fun ω => step (t.prepare e) ω n)
      (start (t.prepare e) n x s))ᶜ=0 := by
  rw [prob_compl_eq_one_sub,table_termination_mass,tsub_self]
  rw [termination_eq]
  exact MeasurableSet.iUnion fun z => measurable_final _ _ _ _ _

end Applications.Probability.RowChain
