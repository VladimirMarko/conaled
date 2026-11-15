import Applications.Probability.InitializedProducer
import Applications.Probability.SamplerExpectedWork

/-! Measured initialization reuses the existing workload through an exact phase
representation. `none` selects the initial row; every emitted value is `some a`.
No weight, rejection block, bit cursor or output occurrence is changed. -/
namespace Applications.Probability.InitializedProducerWork
open CoinPaths MeasureTheory SamplerWork SamplerWorkload SamplerExpectedWork
open scoped ENNReal
variable {α : Type}

/-- Relabel outcomes without preparing another row or changing its ticket space. -/
def tag (r : PreparedRow α) : PreparedRow (Option α) :=
  { r with outcome := fun i => some (r.outcome i) }

def rows (r : PreparedRow α) (p : α → PreparedRow α) : Option α → PreparedRow (Option α)
  | none => tag r
  | some a => tag (p a)

def encode : InitializedProducer.State α → TableProducer.State (Option α)
  | .inl q => (none,q)
  | .inr (a,q) => (some a,q)

def decode : TableProducer.State (Option α) → InitializedProducer.State α
  | (none,q) => .inl q
  | (some a,q) => .inr (a,q)

@[simp] theorem decode_encode (z : InitializedProducer.State α) : decode (encode z)=z := by
  cases z with
  | inl q => rfl
  | inr z => cases z; rfl

@[simp] theorem encode_decode (z : TableProducer.State (Option α)) : encode (decode z)=z := by
  rcases z with ⟨a,q⟩
  cases a <;> rfl

@[simp] theorem tag_start (r : PreparedRow α) (s : ℕ) : (tag r).start s=r.start s := rfl

@[simp] theorem tag_step (r : PreparedRow α) (ω : Tape) (q : PreparedRow.State) :
    (tag r).step ω q=Sum.map (fun (a,t) => (some a,t)) id (r.step ω q) := by
  unfold PreparedRow.step Progress.mapReturn
  dsimp only [tag]
  cases BoundedUniform.step r.total ω q <;> rfl

@[simp] theorem encode_start (r : PreparedRow α) (p : α → PreparedRow α) (s : ℕ) :
    encode (InitializedProducer.start r s)=TableProducer.start (rows r p) none s := rfl

/-- Every bit step commutes with the phase representation, even at partial or
rejected blocks. This is operational equality on each tape, not equality in law. -/
theorem step_encode (r : PreparedRow α) (p : α → PreparedRow α) (ω : Tape)
    (z : InitializedProducer.State α) :
    TableProducer.step (rows r p) ω (encode z)=
      Sum.map (fun (a,q) => (some a,encode q)) encode (InitializedProducer.step r p ω z) := by
  cases z with
  | inl q =>
    simp only [encode,TableProducer.step,rows,tag_step,InitializedProducer.step]
    cases r.step ω q <;> rfl
  | inr z =>
    rcases z with ⟨a,q⟩
    simp only [encode,TableProducer.step,rows,tag_step,InitializedProducer.step]
    cases (p a).step ω q <;> rfl

theorem evaluates_encode {r : PreparedRow α} {p : α → PreparedRow α} {ω : Tape}
    {z q : InitializedProducer.State α} {a : α} {k : ℕ}
    (h : Progress.Evaluates (InitializedProducer.step r p ω) z (a,q) k) :
    Progress.Evaluates (TableProducer.step (rows r p) ω) (encode z) (some a,encode q) k := by
  induction k generalizing z with
  | zero => cases h
  | succ k ih =>
    cases h with
    | done h => exact .done (by rw [step_encode,h]; rfl)
    | next h rest => exact .next (by rw [step_encode,h]; rfl) (ih rest)

theorem delivers_encode {r : PreparedRow α} {p : α → PreparedRow α} {ω : Tape}
    {z q : InitializedProducer.State α} {ys : List α} {k : ℕ}
    (h : Progress.Delivers (InitializedProducer.step r p ω) z ys q k) :
    Progress.Delivers (TableProducer.step (rows r p) ω) (encode z) (ys.map some) (encode q) k := by
  induction h with
  | nil => exact .nil _
  | cons first rest ih => exact .cons (evaluates_encode first) ih


/-- Every phase-machine return comes from a native initialized-producer return;
no `none` output or extra terminating execution is introduced. -/
theorem evaluates_decode {r : PreparedRow α} {p : α → PreparedRow α} {ω : Tape}
    {z : InitializedProducer.State α} {q : TableProducer.State (Option α)}
    {b : Option α} {k : ℕ}
    (h : Progress.Evaluates (TableProducer.step (rows r p) ω) (encode z) (b,q) k) :
    ∃ a z', b=some a ∧ q=encode z' ∧
      Progress.Evaluates (InitializedProducer.step r p ω) z (a,z') k := by
  induction k generalizing z with
  | zero => cases h
  | succ k ih =>
    cases h with
    | done h =>
      rw [step_encode] at h
      cases hs : InitializedProducer.step r p ω z with
      | inl v =>
        rcases v with ⟨a,z'⟩
        simp only [hs,Sum.map_inl,Sum.inl.injEq,Prod.mk.injEq] at h
        exact ⟨a,z',h.1.symm,h.2.symm,.done hs⟩
      | inr z' => simp [hs] at h
    | next h rest =>
      rw [step_encode] at h
      cases hs : InitializedProducer.step r p ω z with
      | inl v => simp [hs] at h
      | inr z' =>
        simp only [hs,Sum.map_inr,Sum.inr.injEq] at h
        subst h
        obtain ⟨a,u,hb,hq,hu⟩ := ih rest
        exact ⟨a,u,hb,hq,.next hs hu⟩

theorem delivers_decode {r : PreparedRow α} {p : α → PreparedRow α} {ω : Tape}
    {z : InitializedProducer.State α} {q : TableProducer.State (Option α)}
    {bs : List (Option α)} {k : ℕ}
    (h : Progress.Delivers (TableProducer.step (rows r p) ω) (encode z) bs q k) :
    ∃ ys z', bs=ys.map some ∧ q=encode z' ∧
      Progress.Delivers (InitializedProducer.step r p ω) z ys z' k := by
  induction bs generalizing z q k with
  | nil => cases h; exact ⟨[],z,rfl,rfl,.nil _⟩
  | cons b bs ih =>
    cases h with
    | cons first rest =>
      obtain ⟨a,u,rfl,rfl,hu⟩ := evaluates_decode first
      obtain ⟨ys,v,rfl,rfl,hv⟩ := ih rest
      exact ⟨a::ys,v,rfl,rfl,.cons hu hv⟩

/-- A loader charges its actual initial row or continuation preparation. The
phase tag is an outcome interpretation; its declared outcome cost is priced
by the row tariff, and chronological output handling by the finish tariff. -/
def loader (first : Resources.Measured (PreparedRow α) ℕ) (later : Loader α) : Loader (Option α)
  | none => (tag first.1,first.2)
  | some a => (tag (later a).1,(later a).2)

theorem loader_value (r : PreparedRow α) (p : α → PreparedRow α)
    (first : Resources.Measured (PreparedRow α) ℕ) (later : Loader α)
    (hf : first.1=r) (hl : ∀ a,(later a).1=p a) (a : Option α) :
    (loader first later a).1=rows r p a := by
  cases a <;> simp [loader,rows,hf,hl]

/-- The measured workload includes initialization among its outputs and retains
its exact final state. It also loads the next row after the final emission. -/
theorem workload_delivery (r : PreparedRow α) (p : α → PreparedRow α)
    (first : Resources.Measured (PreparedRow α) ℕ) (later : Loader α)
    (hf : first.1=r) (hl : ∀ a,(later a).1=p a)
    (τ : Tariff) (o : Overhead) (ω : Tape) (s : ℕ)
    {ys : List α} {z : InitializedProducer.State α} {k : ℕ}
    (h : Progress.Delivers (InitializedProducer.step r p ω) (InitializedProducer.start r s) ys z k) :
    (workload (loader first later) τ o ω none s k false).1=(ys.map some,encode z) :=
  workload_delivers _ _ (loader_value r p first later hf hl) τ o ω none s
    (delivers_encode h) false

/-- Pausing during initialization or a subsequent draw retains the same cached
row, accumulated output list and partial rejection block; initialization is not replayed. -/
theorem resume (first : Resources.Measured (PreparedRow α) ℕ) (later : Loader α)
    (τ : Tariff) (o : Overhead) (ω : Tape) (xs ys : List Unit)
    (z : SamplerWorkload.State (Option α)) :
    Resources.run (tick (loader first later) τ o ω) (xs++ys) z=
      Resources.bind (Resources.run (tick (loader first later) τ o ω) xs z)
        (Resources.run (tick (loader first later) τ o ω) ys) :=
  SamplerWorkload.resume _ _ _ _ _ _ _

/-- `n` counts transitions after initialization. Thus even `n=0` requests one
sample, and setup, initial row loading and initial bit consumption all count. -/
noncomputable def charged (r : PreparedRow α) (p : α → PreparedRow α)
    (first : Resources.Measured (PreparedRow α) ℕ) (later : Loader α)
    (τ : Tariff) (o : Overhead) (setup n s : ℕ) : Tape → ℝ≥0∞ :=
  chargedWork (loader first later) (rows r p) τ o setup (n+1) none s false

theorem charged_delivery (r : PreparedRow α) (p : α → PreparedRow α)
    (first : Resources.Measured (PreparedRow α) ℕ) (later : Loader α)
    (τ : Tariff) (o : Overhead) (setup s : ℕ) {ω : Tape}
    {a : α} {ys : List α} {z : InitializedProducer.State α} {k : ℕ}
    (h : Progress.Delivers (InitializedProducer.step r p ω)
      (InitializedProducer.start r s) (a::ys) z k) :
    charged r p first later τ o setup ys.length s ω=
      setup+(workload (loader first later) τ o ω none s k false).2 := by
  simpa [charged] using chargedWork_of_delivers (loader first later) (rows r p)
    τ o setup none s false (delivers_encode h)


/-- Failure to initialize remains infinite completion work, even for zero tariffs. -/
theorem charged_initial_divergence (r : PreparedRow α) (p : α → PreparedRow α)
    (first : Resources.Measured (PreparedRow α) ℕ) (later : Loader α)
    (τ : Tariff) (o : Overhead) (setup n s : ℕ) (ω : Tape)
    (h : ¬Progress.Terminates (r.step ω) (r.start s)) :
    charged r p first later τ o setup n s ω=∞ := by
  apply chargedWork_of_divergence
  rintro ⟨bs,q,k,hlen,hd⟩
  obtain ⟨ys,z,he,_,hy⟩ := delivers_decode (z := InitializedProducer.start r s) hd
  rw [he,List.length_map] at hlen
  cases ys with
  | nil => simp at hlen
  | cons a ys =>
    cases hy with
    | cons first rest =>
      obtain ⟨u,hu,_⟩ := InitializedProducer.initial_of_evaluates first
      exact h ⟨(a,u),_,hu⟩

theorem expected_bound [Fintype α] [DecidableEq α]
    (r : PreparedRow α) (p : α → PreparedRow α)
    (first : Resources.Measured (PreparedRow α) ℕ) (later : Loader α)
    (hf : first.1=r) (hl : ∀ a,(later a).1=p a)
    (τ : Tariff) (o : Overhead) (setup n s : ℕ) :
    (∫⁻ ω,charged r p first later τ o setup n s ω ∂law)≤
      (baseCost (loader first later) τ o setup (n+1) none false+
        2*(n+1)*((n+1)*maxWidth (rows r p))*drawCap (loader first later) (rows r p) τ o : ℕ) :=
  expected_rows_charged_le _ _ (loader_value r p first later hf hl) τ o setup (n+1) none s false

theorem expected_finite [Fintype α] [DecidableEq α]
    (r : PreparedRow α) (p : α → PreparedRow α)
    (first : Resources.Measured (PreparedRow α) ℕ) (later : Loader α)
    (hf : first.1=r) (hl : ∀ a,(later a).1=p a)
    (τ : Tariff) (o : Overhead) (setup n s : ℕ) :
    (∫⁻ ω,charged r p first later τ o setup n s ω ∂law)<∞ :=
  (expected_bound r p first later hf hl τ o setup n s).trans_lt (ENNReal.natCast_lt_top _)

theorem budget_risk [Fintype α] [DecidableEq α]
    (r : PreparedRow α) (p : α → PreparedRow α)
    (first : Resources.Measured (PreparedRow α) ℕ) (later : Loader α)
    (hf : first.1=r) (hl : ∀ a,(later a).1=p a)
    (τ : Tariff) (o : Overhead) (setup n s retry : ℕ) :
    law {ω | ¬charged r p first later τ o setup n s ω≤
      (baseCost (loader first later) τ o setup (n+1) none false+
        (n+1)*(maxWidth (rows r p)*retry)*drawCap (loader first later) (rows r p) τ o : ℕ)}≤
      (n+1)*(2⁻¹ : ℝ≥0∞)^retry := by
  simpa only [charged,Nat.cast_add,Nat.cast_one] using
    rows_charged_deadline _ _ (loader_value r p first later hf hl) τ o setup (n+1) none s retry false

end Applications.Probability.InitializedProducerWork
