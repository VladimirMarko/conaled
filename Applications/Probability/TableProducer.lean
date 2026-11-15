import Applications.Probability.TableSamplerIteration
import Applications.Probability.Productivity

/-!
# Resumable rational Markov producers

One state retains the semantic state and the row sampler's cursor, remaining
block width and accumulated code. Every completed transition emits, including
self-transitions. Silent steps only continue the current rejection sampler.
-/
namespace Applications.Probability.TableProducer
open CoinPaths MeasureTheory
variable {α : Type}

abbrev State (α : Type) := α × PreparedRow.State

def start (p : α → PreparedRow α) (x : α) (s : ℕ) : State α := (x,(p x).start s)

def step (p : α → PreparedRow α) (ω : Tape) : Progress.Producer (State α) α := fun (x,q) =>
  match (p x).step ω q with
  | .inl (a,t) => .inl (a,start p a t)
  | .inr q' => .inr (x,q')

/-- The next emission is exactly one row execution, at the same bit cost. -/
theorem evaluates_of_row {p : α → PreparedRow α} {ω : Tape} {x : α}
    {q : PreparedRow.State} {a : α} {t k : ℕ}
    (h : Progress.Evaluates ((p x).step ω) q (a,t) k) :
    Progress.Evaluates (step p ω) (x,q) (a,start p a t) k := by
  induction k generalizing q with
  | zero => cases h
  | succ k ih =>
    cases h with
    | done e => exact .done (by simp [step,e])
    | next e h => exact .next (by simp [step,e]) (ih h)

theorem row_of_evaluates {p : α → PreparedRow α} {ω : Tape} {x : α}
    {q : PreparedRow.State} {a : α} {z : State α} {k : ℕ}
    (h : Progress.Evaluates (step p ω) (x,q) (a,z) k) :
    ∃ t, Progress.Evaluates ((p x).step ω) q (a,t) k ∧ z=start p a t := by
  induction k generalizing x q with
  | zero => cases h
  | succ k ih =>
    cases h with
    | done e =>
      cases hr : (p x).step ω q with
      | inl r =>
        rcases r with ⟨b,t⟩
        simp only [step,hr,Sum.inl.injEq,Prod.mk.injEq] at e
        rcases e with ⟨rfl,rfl⟩
        exact ⟨t,.done hr,rfl⟩
      | inr q' => simp [step,hr] at e
    | next e h =>
      cases hr : (p x).step ω q with
      | inl r => simp [step,hr] at e
      | inr q' =>
        simp only [step,hr,Sum.inr.injEq] at e
        subst e
        obtain ⟨t,ht,hz⟩ := ih h
        exact ⟨t,.next hr ht,hz⟩

private theorem trace_pos {p : α → PreparedRow α} {ω : Tape} {n x s ys t k}
    (h : RowChain.Trace p ω n x s ys t k) : 0<k := by
  have he := RowChain.evaluates_of_trace h
  cases he <;> omega

/-- The finite-chain machine has one final administrative step. The producer
has none: its cost is exactly the number of bits inspected. -/
theorem delivers_of_trace {p : α → PreparedRow α} {ω : Tape} {n x s ys t k}
    (h : RowChain.Trace p ω n x s ys t k) :
    Progress.Delivers (step p ω) (start p x s) ys
      (start p (RowChain.finalState x ys) t) (k-1) := by
  induction h with
  | zero x s => exact .nil _
  | @next n x s a t i ys u j first rest ih =>
    have hj : 1≤j := trace_pos rest
    simpa [start,RowChain.finalState,show i+j-1=i+(j-1) by omega] using
      Progress.Delivers.cons (evaluates_of_row first) ih

theorem trace_of_delivers {p : α → PreparedRow α} {ω : Tape} {x s ys z k}
    (h : Progress.Delivers (step p ω) (start p x s) ys z k) :
    ∃ t, z=start p (RowChain.finalState x ys) t ∧
      RowChain.Trace p ω ys.length x s ys t (k+1) := by
  generalize he : start p x s=v at h
  induction h generalizing x s with
  | nil v => subst v; exact ⟨s,rfl,.zero x s⟩
  | @cons v u z a ys i j first rest ih =>
    subst v
    obtain ⟨t,hr,rfl⟩ := row_of_evaluates first
    obtain ⟨u,hz,htrace⟩ := ih rfl
    exact ⟨u,hz,by simpa [Nat.add_assoc] using RowChain.Trace.next hr htrace⟩

theorem delivers_work {p : α → PreparedRow α} {ω : Tape} {x s ys z k}
    (h : Progress.Delivers (step p ω) (start p x s) ys z k) : z.2.1=s+k := by
  obtain ⟨t,hz,ht⟩ := trace_of_delivers h
  have hw := RowChain.trace_work ht
  subst z
  change t=s+k
  omega

theorem measurableSteps (p : α → PreparedRow α) :
    ProbabilityProgress.MeasurableSteps (step p) := by
  intro q r
  have he : {ω | step p ω q=r} =
      ({ω : Tape | ω q.2.1=false} ∩ {ω | step p (fun _ => false) q=r}) ∪
      ({ω : Tape | ω q.2.1=true} ∩ {ω | step p (fun _ => true) q=r}) := by
    ext ω
    cases hb : ω q.2.1 <;>
      simp [step,PreparedRow.step,Progress.mapReturn,BoundedUniform.step,hb]
  rw [he]
  have hm : Measurable (fun ω : Tape => ω q.2.1) := measurable_pi_apply q.2.1
  exact ((hm (measurableSet_singleton false)).inter (MeasurableSet.const _)).union
    ((hm (measurableSet_singleton true)).inter (MeasurableSet.const _))

/-- The emitted prefix event observes one producer, without restarting between outputs. -/
def prefixEvent (p : α → PreparedRow α) (x : α) (s : ℕ) (ys : List α) : Set Tape :=
  {ω | ∃ z k, Progress.Delivers (step p ω) (start p x s) ys z k}

theorem prefix_eq (p : α → PreparedRow α) (x : α) (s : ℕ) (ys : List α) :
    prefixEvent p x s ys=RowChain.returns p ys.length x s ys := by
  ext ω
  constructor
  · rintro ⟨z,k,h⟩
    obtain ⟨t,_,ht⟩ := trace_of_delivers h
    exact ⟨t,k+1,ht⟩
  · rintro ⟨t,k,h⟩
    exact ⟨_,_,delivers_of_trace h⟩

/-- The row return law is the only representation assumption for path laws. -/
theorem prefix_mass_rows [Fintype α] [DecidableEq α]
    (t : Table α α) (p : α → PreparedRow α)
    (hp : ∀ x s a, law ((p x).returns s a)=mass (t.entry x a))
    (x : α) (s : ℕ) (ys : List α) :
    law (prefixEvent p x s ys)=mass (RowChain.pathMass t x ys) := by
  rw [prefix_eq]
  exact RowChain.rows_path_mass t p hp _ _ _ _ rfl

theorem prefix_mass [Fintype α] [DecidableEq α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (x : α) (s : ℕ) (ys : List α) :
    law (prefixEvent (t.prepare e) x s ys)=mass (RowChain.pathMass t x ys) :=
  prefix_mass_rows t (t.prepare e) (t.prepare_returns_mass e) x s ys

/-- Endpoint observation after exactly n emissions. -/
def endpointEvent (p : α → PreparedRow α) (n : ℕ) (x : α) (s : ℕ) (y : α) : Set Tape :=
  {ω | ∃ ys z k, ys.length=n ∧ Progress.Delivers (step p ω) (start p x s) ys z k ∧ z.1=y}

theorem endpoint_eq (p : α → PreparedRow α) (n : ℕ) (x : α) (s : ℕ) (y : α) :
    endpointEvent p n x s y=RowChain.finalEvent p n x s y := by
  ext ω
  constructor
  · rintro ⟨ys,z,k,hlen,h,hz⟩
    obtain ⟨t,rfl,ht⟩ := trace_of_delivers h
    exact ⟨ys,⟨t,k+1,hlen ▸ ht⟩,hz⟩
  · rintro ⟨ys,⟨t,k,h⟩,hy⟩
    exact ⟨ys,_,_,RowChain.trace_length h,delivers_of_trace h,hy⟩

theorem endpoint_mass [Fintype α] [DecidableEq α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (n : ℕ) (x y : α) (s : ℕ) :
    law (endpointEvent (t.prepare e) n x s y)=mass ((t.steps n).entry x y) := by
  rw [endpoint_eq,RowChain.table_final_mass]

/-- Positive prepared rows suffice for productive finite observations. The
construction of their multiplicities need not be a particular rational algorithm. -/
theorem almostSureProductive_rows [Countable α] (p : α → PreparedRow α)
    (x : α) (s : ℕ) :
    ProbabilityProgress.AlmostSureProductive law (step p) (fun _ => start p x s) := by
  intro n
  induction n generalizing x s with
  | zero => exact Filter.Eventually.of_forall fun _ => ⟨[],_,0,rfl,.nil _⟩
  | succ n ih =>
    have hc : ∀ᵐ ω ∂law, ∀ a u, ∃ ys z k, ys.length=n ∧
        Progress.Delivers (step p ω) (start p a u) ys z k :=
      (ae_all_iff).mpr fun a => (ae_all_iff).mpr fun u => ih a u
    filter_upwards [(p x).ae_terminates s,hc] with ω hi hp
    obtain ⟨⟨a,u⟩,i,hi⟩ := hi
    obtain ⟨ys,z,k,hlen,hp⟩ := hp a u
    exact ⟨a::ys,z,i+k,by simp [hlen],.cons (evaluates_of_row hi) hp⟩

theorem almostSureProductive [Fintype α] [DecidableEq α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (x : α) (s : ℕ) :
    ProbabilityProgress.AlmostSureProductive law (step (t.prepare e))
      (fun _ => start (t.prepare e) x s) :=
  almostSureProductive_rows (t.prepare e) x s

theorem ae_coherent_prefixes [Fintype α] [DecidableEq α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (x : α) (s : ℕ) :
    ∀ᵐ ω ∂law, ∃ prefixes : ℕ → List α,
      (∀ n, (prefixes n).length=n ∧ ∃ z k,
        Progress.Delivers (step (t.prepare e) ω) (start (t.prepare e) x s) (prefixes n) z k) ∧
      ∀ i j, (prefixes i).take j=(prefixes j).take i :=
  ProbabilityProgress.ae_coherent_prefixes _ _ _ (almostSureProductive t e x s)

/-- A different observation policy: completed self-transitions become silent.
This does not observe MH acceptance flags and has no unconditional productivity law. -/
def changes [DecidableEq α] (p : α → PreparedRow α) (ω : Tape) :
    Progress.Producer (State α) α := fun z =>
  match step p ω z with
  | .inl (a,z') => if a=z.1 then .inr z' else .inl (a,z')
  | .inr z' => .inr z'

/-- On a singleton semantic space every completed transition is suppressed. -/
theorem changes_not_productive [DecidableEq α] [Subsingleton α]
    (p : α → PreparedRow α) (ω : Tape) (z : State α) :
    ¬Progress.Productive (changes p ω) z := by
  intro h
  obtain ⟨ys,t,k,hlen,hd⟩ := h 1
  cases hd with
  | nil => simp at hlen
  | cons first rest =>
    have he : changes p ω=(fun z => .inr (match step p ω z with
        | .inl (_,z') => z'
        | .inr z' => z')) := by
      funext z
      cases hs : step p ω z with
      | inl a => simp [changes,hs,Subsingleton.elim a.1 z.1]
      | inr z' => simp [changes,hs]
    rw [he] at first
    exact Progress.silent_no_evaluation _ first

end Applications.Probability.TableProducer
