import Applications.Probability.TableSamplerComposition

/-!
# Declared work for exact row sampling

Work is a tariff model of source operations. Natural arithmetic has a declared
price independent of operand bit length; array access and outcome interpretation
have separate prices. Lookup includes evaluation of a supplied weight callback;
prepared tables use stored arrays. Store includes array construction bookkeeping
per entry. Structural recursion, proof casts, and the meter's own bookkeeping are
outside this model. Preparation evaluates entries explicitly and stores weights;
Table.compile retains prepared rows for repeated draws. No wall-clock, arithmetic
bit-complexity, or physical random-source guarantee follows.
-/
namespace Applications.Probability.SamplerWork
open CoinPaths MeasureTheory
open scoped ENNReal

/-- Prices are natural numbers, hence nonnegative. `entry` includes evaluation
of the supplied table-entry/enumeration function; `projection` prices reading a
rational numerator or denominator. `logarithm` prices Nat.clog as an abstract
operation, not its internal bit complexity. -/
structure Tariff where
  bit : ℕ
  arithmetic : ℕ
  lookup : ℕ
  store : ℕ
  outcome : ℕ
  entry : ℕ
  projection : ℕ
  logarithm : ℕ

/-- A source product loop with one charged multiplication per entry. -/
def productMeter : (m : ℕ) → (Fin m → ℕ) → ℕ × ℕ
  | 0,_ => (1,0)
  | m+1,f =>
    let r := productMeter m (fun i => f i.castSucc)
    (r.1*f (Fin.last m),r.2+1)

theorem productMeter_value (m : ℕ) (f : Fin m → ℕ) :
    (productMeter m f).1=∏ i,f i := by
  induction m with
  | zero => simp [productMeter]
  | succ m ih => simp [productMeter,ih,Fin.prod_univ_castSucc]

theorem productMeter_count (m : ℕ) (f : Fin m → ℕ) :
    (productMeter m f).2=m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [productMeter,ih]

/-- Measured preparation computes the denominator product, then materializes
weights. Each weight charges conversion, quotient and multiplication. -/
def prepareMetered {α β : Type} [Fintype β] {m : ℕ}
    (t : Table α β) (e : Fin m ≃ β) (x : α) (τ : Tariff) : PreparedRow β × ℕ :=
  let q := fun i => t.entry x (e i)
  let d := productMeter m (fun i => (q i).den)
  let data := Array.ofFn (fun i => ((q i).num.toNat*(d.1/(q i).den),(3 : ℕ)))
  let row : PreparedRow β :=
    { size := m
      weight := fun i => (data[i.val]'(by simp [data])).1
      outcome := e
      total := d.1
      total_eq := by
        dsimp [data,d]
        simp only [Array.getElem_ofFn,productMeter_value]
        exact (RationalWeights.sum_weight q (fun i => t.nonneg x (e i))
          ((e.sum_comp (t.entry x)).trans (t.sum_row x))).symm
      positive := by
        dsimp [d]
        rw [productMeter_value]
        exact RationalWeights.denominator_pos q }
  (row,(d.2+∑ i : Fin m, (data[i.val]'(by simp [data])).2)*τ.arithmetic+
    3*m*(τ.entry+τ.projection)+m*τ.store)

theorem prepareMetered_value {α β : Type} [Fintype β] {m : ℕ}
    (t : Table α β) (e : Fin m ≃ β) (x : α) (τ : Tariff) :
    (prepareMetered t e x τ).1=t.prepare e x := by
  simp [prepareMetered,Table.prepare,productMeter_value,RationalWeights.denominator]

theorem prepareMetered_cost {α β : Type} [Fintype β] {m : ℕ}
    (t : Table α β) (e : Fin m ≃ β) (x : α) (τ : Tariff) :
    (prepareMetered t e x τ).2=4*m*τ.arithmetic+3*m*(τ.entry+τ.projection)+m*τ.store := by
  simp [prepareMetered,productMeter_count]
  ring_nf
  simp

/-- One addition and one weight lookup per summand. -/
def sumMeter : (m : ℕ) → (Fin m → ℕ) → ℕ × ℕ
  | 0,_ => (0,0)
  | m+1,f =>
    let r := sumMeter m (fun i => f i.castSucc)
    (r.1+f (Fin.last m),r.2+1)

theorem sumMeter_value (m : ℕ) (f : Fin m → ℕ) : (sumMeter m f).1=∑ i,f i := by
  induction m with
  | zero => simp [sumMeter]
  | succ m ih => simp [sumMeter,ih,Fin.sum_univ_castSucc]

theorem sumMeter_count (m : ℕ) (f : Fin m → ℕ) : (sumMeter m f).2=m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [sumMeter,ih]

/-- Measured interval lookup. Prefix sums charge every weight read and addition;
right branches also subtract the prefix. Proof casts carry no runtime charge. -/
def selectMeter (τ : Tariff) : (m : ℕ) → (w : Fin m → ℕ) →
    Fin (∑ i,w i) → ((i : Fin m) × Fin (w i)) × ℕ
  | 0,w,k => Fin.elim0 (Fin.cast (by simp) k)
  | m+1,w,k =>
    let scan := sumMeter m (fun i => w i.castSucc)
    let cut := scan.1
    if h : k.val<cut then
      let r := selectMeter τ m (fun i => w i.castSucc) ⟨k.val,by simpa [cut,scan,sumMeter_value] using h⟩
      (⟨r.1.1.castSucc,r.1.2⟩,r.2+scan.2*(τ.arithmetic+τ.lookup)+τ.arithmetic)
    else
      (⟨Fin.last m,⟨k.val-cut,by
        have hk : k.val<(∑ i : Fin m,w i.castSucc)+w (Fin.last m) := by
          simpa only [Fin.sum_univ_castSucc] using k.isLt
        dsimp [cut,scan] at h ⊢
        simp only [sumMeter_value] at h ⊢
        omega⟩⟩,scan.2*(τ.arithmetic+τ.lookup)+2*τ.arithmetic)

/-- The measured algorithm selects exactly the existing interval equivalence. -/
theorem selectMeter_encode (τ : Tariff) (m : ℕ) (w : Fin m → ℕ) (k : Fin (∑ i,w i)) :
    finSigmaFinEquiv (selectMeter τ m w k).1=k := by
  induction m with
  | zero => exact Fin.elim0 (Fin.cast (by simp) k)
  | succ m ih =>
    simp only [selectMeter,sumMeter_value,sumMeter_count]
    split
    · rename_i h
      apply Fin.ext
      have hi := congrArg Fin.val (ih (fun i => w i.castSucc) ⟨k.val,h⟩)
      simp only [finSigmaFinEquiv_apply] at hi ⊢
      convert hi using 1
      congr 1
    · rename_i h
      apply Fin.ext
      rw [finSigmaFinEquiv_apply]
      change (∑ i : Fin m,w i.castSucc)+(k.val-∑ i : Fin m,w i.castSucc)=k.val
      omega

theorem selectMeter_value (τ : Tariff) (m : ℕ) (w : Fin m → ℕ) (k : Fin (∑ i,w i)) :
    (selectMeter τ m w k).1=finSigmaFinEquiv.symm k :=
  finSigmaFinEquiv.injective ((selectMeter_encode τ m w k).trans (finSigmaFinEquiv.apply_symm_apply k).symm)

theorem selectMeter_bound (τ : Tariff) (m : ℕ) (w : Fin m → ℕ) (k : Fin (∑ i,w i)) :
    (selectMeter τ m w k).2≤m*(m+2)*(τ.arithmetic+τ.lookup) := by
  induction m with
  | zero => exact Fin.elim0 (Fin.cast (by simp) k)
  | succ m ih =>
    simp only [selectMeter,sumMeter_value,sumMeter_count]
    split
    · rename_i h
      have hi := ih (fun i => w i.castSucc) ⟨k.val,h⟩
      nlinarith [Nat.zero_le τ.lookup]
    · change m*(τ.arithmetic+τ.lookup)+2*τ.arithmetic≤_
      calc
        _ ≤ (m+2)*(τ.arithmetic+τ.lookup) := by nlinarith
        _ ≤ (m+1)*(m+1+2)*(τ.arithmetic+τ.lookup) :=
          Nat.mul_le_mul_right _ (by nlinarith)

/-- Meter a machine without changing its return, state evolution, or transition count.
The accumulator is instrumentation; its own bookkeeping is not recursively charged. -/
def meter {S A : Type} (f : Progress.Machine S A) (charge : S → ℕ) :
    Progress.Machine (S × ℕ) (A × ℕ) := fun (s,c) =>
  match f s with
  | .inl a => .inl (a,c+charge s)
  | .inr t => .inr (t,c+charge s)

theorem meter_evaluates {S A : Type} {f : Progress.Machine S A} {charge : S → ℕ}
    {s : S} {a : A} {k M : ℕ} (h : Progress.Evaluates f s a k)
    (hb : ∀ s, charge s≤M) (c : ℕ) :
    ∃ w, Progress.Evaluates (meter f charge) (s,c) (a,w) k ∧ w≤c+k*M := by
  induction h generalizing c with
  | @done s a he => exact ⟨c+charge s,.done (by simp [meter,he]),by have := hb s; omega⟩
  | @next s t a k he h ih =>
    obtain ⟨w,hw,hbound⟩ := ih (c+charge s)
    exact ⟨w,.next (by simp [meter,he]) hw,by have := hb s; nlinarith⟩

theorem meter_evaluates_inv {S A : Type} {f : Progress.Machine S A} {charge : S → ℕ}
    {s : S} {a : A} {k c w : ℕ}
    (h : Progress.Evaluates (meter f charge) (s,c) (a,w) k) :
    Progress.Evaluates f s a k := by
  induction k using Nat.strong_induction_on generalizing s c w with
  | h k ih =>
    cases h with
    | done he =>
      cases hf : f s with
      | inl b =>
        simp only [meter,hf,Sum.inl.injEq,Prod.mk.injEq] at he
        rcases he with ⟨rfl,_⟩
        exact .done hf
      | inr t => simp [meter,hf] at he
    | @next _ u _ l he h =>
      cases hf : f s with
      | inl b => simp [meter,hf] at he
      | inr t =>
        simp only [meter,hf,Sum.inr.injEq] at he
        subst u
        exact .next hf (ih l (by omega) h)

/-- Measured selection executes the certified interval algorithm once. -/
def rowSelect {β : Type} (p : PreparedRow β) (τ : Tariff) (a : Fin p.total) : β × ℕ :=
  let r := selectMeter τ p.size p.weight (Fin.cast p.total_eq a)
  (p.outcome r.1.1,r.2+τ.outcome)

theorem rowSelect_value {β : Type} (p : PreparedRow β) (τ : Tariff) (a : Fin p.total) :
    (rowSelect p τ a).1=p.select a := by
  simp [rowSelect,selectMeter_value,PreparedRow.select]

def selectionBound {β : Type} (p : PreparedRow β) (τ : Tariff) : ℕ :=
  p.size*(p.size+2)*(τ.arithmetic+τ.lookup)+τ.outcome

theorem rowSelect_bound {β : Type} (p : PreparedRow β) (τ : Tariff) (a : Fin p.total) :
    (rowSelect p τ a).2≤selectionBound p τ :=
  Nat.add_le_add_right (selectMeter_bound τ _ _ _) _

/-- Initial width computation: one clog and one maximum comparison. -/
def initialization (τ : Tariff) : ℕ := τ.logarithm+τ.arithmetic

/-- One bit read, accumulator multiply/add, cursor increment, remaining comparison. -/
def bitBase (τ : Tariff) : ℕ := τ.bit+4*τ.arithmetic

/-- A conservative per-bit envelope includes a reset or the entire final selection.
Only their actual branch is charged by measuredStep. -/
def perBitBound {β : Type} (p : PreparedRow β) (τ : Tariff) : ℕ :=
  bitBase τ+τ.arithmetic+initialization τ+selectionBound p τ

def sourceCharge {β : Type} (p : PreparedRow β) (τ : Tariff) (ω : Tape)
    (q : PreparedRow.State) : ℕ :=
  match BoundedUniform.step p.total ω q with
  | .inl a => bitBase τ+τ.arithmetic+(rowSelect p τ a.1).2
  | .inr _ => bitBase τ+τ.arithmetic+if q.2.1≤1 then initialization τ else 0

/-- Executable charged sampler. It calls the measured selector once on acceptance;
it does not run an unmeasured selection followed by a second counting pass. -/
def measuredStep {β : Type} (p : PreparedRow β) (τ : Tariff) (ω : Tape) :
    Progress.Machine (PreparedRow.State × ℕ) ((β × ℕ) × ℕ) := fun (q,c) =>
  match BoundedUniform.step p.total ω q with
  | .inl a =>
    let r := rowSelect p τ a.1
    .inl ((r.1,a.2),c+bitBase τ+τ.arithmetic+r.2)
  | .inr q' => .inr (q',c+bitBase τ+τ.arithmetic+if q.2.1≤1 then initialization τ else 0)

theorem measuredStep_eq {β : Type} (p : PreparedRow β) (τ : Tariff) (ω : Tape) :
    measuredStep p τ ω=meter (p.step ω) (sourceCharge p τ ω) := by
  funext qc
  rcases qc with ⟨q,c⟩
  cases h : BoundedUniform.step p.total ω q with
  | inl a => simp [measuredStep,meter,PreparedRow.step,Progress.mapReturn,sourceCharge,h,
      rowSelect_value,Nat.add_assoc]
  | inr q' => simp [measuredStep,meter,PreparedRow.step,Progress.mapReturn,sourceCharge,h,Nat.add_assoc]

theorem sourceCharge_bound {β : Type} (p : PreparedRow β) (τ : Tariff) (ω : Tape)
    (q : PreparedRow.State) : sourceCharge p τ ω q≤perBitBound p τ := by
  cases h : BoundedUniform.step p.total ω q with
  | inl a =>
    simp only [sourceCharge,h]
    have := rowSelect_bound p τ a.1
    unfold perBitBound
    omega
  | inr q' =>
    simp only [sourceCharge,h]
    unfold perBitBound
    split <;> omega

theorem measured_evaluates {β : Type} (p : PreparedRow β) (τ : Tariff) {ω : Tape}
    {s : ℕ} {a : β} {t k : ℕ}
    (h : Progress.Evaluates (p.step ω) (p.start s) (a,t) k) :
    ∃ w, Progress.Evaluates (measuredStep p τ ω) (p.start s,initialization τ) ((a,t),w) k ∧
      w ≤ initialization τ+k*perBitBound p τ := by
  rw [measuredStep_eq]
  exact meter_evaluates h (sourceCharge_bound p τ ω) (initialization τ)

theorem measured_evaluates_inv {β : Type} (p : PreparedRow β) (τ : Tariff) {ω : Tape}
    {s : ℕ} {a : β} {t k w : ℕ}
    (h : Progress.Evaluates (measuredStep p τ ω) (p.start s,initialization τ) ((a,t),w) k) :
    Progress.Evaluates (p.step ω) (p.start s) (a,t) k := by
  rw [measuredStep_eq] at h
  exact meter_evaluates_inv h

/-- No instrumented return has met the declared work budget. This includes
infinite runs; it does not identify budget exhaustion with divergence. -/
def timeout {β : Type} (p : PreparedRow β) (charge : Tape → PreparedRow.State → ℕ)
    (initial s budget : ℕ) : Set Tape := {ω | ¬∃ a t w k,
      Progress.Evaluates (meter (p.step ω) (charge ω)) (p.start s,initial) ((a,t),w) k ∧ w≤budget}

theorem timeout_subset {β : Type} (p : PreparedRow β)
    (charge : Tape → PreparedRow.State → ℕ) (M initial s fuel : ℕ)
    (hb : ∀ ω q, charge ω q≤M) :
    timeout p charge initial s (initial+fuel*M) ⊆
      {ω | Progress.search (p.step ω) fuel (p.start s)=none} := by
  intro ω h
  cases hs : Progress.search (p.step ω) fuel (p.start s) with
  | none => exact hs
  | some r =>
    rcases r with ⟨⟨a,t⟩,k⟩
    obtain ⟨w,hw,hcost⟩ := meter_evaluates (Progress.search_sound hs) (hb ω) initial
    have hk := ProbabilityProgress.search_cost_le hs
    exact False.elim (h ⟨a,t,w,k,hw,hcost.trans (by nlinarith)⟩)

/-- Any nonnegative source tariff bounded per bit inherits a work-budget tail.
Concrete row charges below discharge the bound from their executed branches. -/
theorem timeout_mass_le {β : Type} (p : PreparedRow β)
    (charge : Tape → PreparedRow.State → ℕ) (M initial s fuel : ℕ)
    (hb : ∀ ω q, charge ω q≤M) :
    law (timeout p charge initial s (initial+fuel*M))≤
      BoundedUniform.rejection p.total^(fuel/BoundedUniform.width p.total) := by
  exact (measure_mono (timeout_subset p charge M initial s fuel hb)).trans_eq
    (p.search_timeout_mass s fuel)

/-- Actual charged execution misses this budget with at most the exact bit-fuel
tail. Initialization, natural arithmetic, weight reads and final interpretation
are included. Preparation is the separate prepareMetered charge above. -/
theorem measured_timeout_mass_le {β : Type} (p : PreparedRow β) (τ : Tariff) (s fuel : ℕ) :
    law {ω | ¬∃ a t w k,
      Progress.Evaluates (measuredStep p τ ω) (p.start s,initialization τ) ((a,t),w) k ∧
        w ≤ initialization τ+fuel*perBitBound p τ}≤
      BoundedUniform.rejection p.total^(fuel/BoundedUniform.width p.total) := by
  simp only [measuredStep_eq]
  exact timeout_mass_le p (sourceCharge p τ) (perBitBound p τ) (initialization τ) s fuel
    (sourceCharge_bound p τ)

end Applications.Probability.SamplerWork
