import Applications.Probability.RetainedSampler
import Examples.SamplerSubstitution

/-! The represented Boolean function client runs on one coin tape. -/
namespace Examples.OperationalSamplerSubstitution
open Applications.Probability MeasureTheory
open scoped ENNReal

def fairTable : Table Unit Bool where
  entry _ _ := 1/2
  nonneg _ _ := by norm_num
  sum_row _ := by norm_num [Fintype.sum_bool]

abbrev fairRow := fairTable.prepare finTwoEquiv ()

theorem fair_mass (s : ℕ) (b : Bool) :
    CoinPaths.law (fairRow.returns s b)=(2⁻¹ : ℝ≥0∞) := by
  rw [Table.prepare_returns_mass]
  norm_num [fairTable,mass,ENNReal.ofReal_div_of_pos]

def machine (ω : CoinPaths.Tape) :=
  RetainedSampler.step fairRow (fun _ => fairRow) (fun _ _ => fairRow) ω

abbrev State := Sum PreparedRow.State
  ((Bool × ℕ) × Sum PreparedRow.State ((Bool × ℕ) × PreparedRow.State))

def initial (s : ℕ) : State := Sum.inl (fairRow.start s)

def event (s : ℕ) (b t u : Bool) :=
  RetainedSampler.event fairRow (fun _ => fairRow) (fun _ _ => fairRow) s b t u

/-- Every full input triple has its independently expected mass, at any cursor. -/
theorem event_mass (s : ℕ) (b t u : Bool) :
    CoinPaths.law (event s b t u)=(8⁻¹ : ℝ≥0∞) := by
  rw [event,RetainedSampler.event_mass,fair_mass,fair_mass,fair_mass]
  norm_num [← ENNReal.mul_inv]

def selected (r : (Bool × ℕ) × (Bool × ℕ) × (Bool × ℕ)) :
    (Bool × Bool × Bool × Bool) × ℕ :=
  (SamplerClient.selected r.1.1 r.2.1.1 r.2.2.1,r.2.2.2)

/-- The sampled code is retained; both calls use it through the original client. -/
def client (ω : CoinPaths.Tape) := Progress.mapReturn selected (machine ω)

def exampleTape (i : ℕ) : Bool := decide (i=2 ∨ i=4)

example : Progress.search (machine exampleTape) 6 (initial 0)=
    some (((false,2),(true,4),(true,6)),6) := by decide +kernel

example : Progress.search (client exampleTape) 6 (initial 0)=
    some (((false,true,true,false),6),6) := by decide +kernel

example : Progress.search (client exampleTape) 5 (initial 0)=none := by decide +kernel

theorem client_ae (s : ℕ) : ∀ᵐ ω ∂CoinPaths.law,
    Progress.Terminates (client ω) (initial s) := by
  filter_upwards [RetainedSampler.ae_terminates fairRow (fun _ => fairRow)
    (fun _ _ => fairRow) s] with ω h
  obtain ⟨a,k,h⟩ := h
  exact ⟨selected a,k,Progress.mapReturn_evaluates h⟩

noncomputable def seedLaw (s : ℕ) : Measure ((Bool × Bool) × Bool) :=
  RetainedSampler.valueLaw fairRow (fun _ => fairRow) (fun _ _ => fairRow) s

theorem seedLaw_eq (s : ℕ) :
    seedLaw s = (SamplerClient.fair.prod SamplerClient.fair).prod SamplerClient.fair := by
  simp only [seedLaw,RetainedSampler.valueLaw,RetainedSampler.event_mass,fair_mass,
    Fintype.sum_prod_type,Fintype.sum_bool,SamplerClient.fair,Measure.add_prod,
    Measure.prod_add,Measure.prod_smul_left,Measure.prod_smul_right,Measure.dirac_prod_dirac,
    smul_add,smul_smul]
  norm_num [← ENNReal.mul_inv]
  ac_rfl

noncomputable def nativeLaw (s : ℕ) : Measure (Bool × Bool × Bool × Bool) :=
  (seedLaw s).map (fun z => SamplerClient.selected z.1.1 z.1.2 z.2)

/-- Equality of the complete operational record law with the independent client
specification, before any call-result or function observation is projected away. -/
theorem nativeLaw_eq (s : ℕ) : nativeLaw s =
    ((SamplerClient.fair.prod SamplerClient.fair).prod SamplerClient.fair).map
      (fun z => SamplerClient.selected z.1.1 z.1.2 z.2) := by
  rw [nativeLaw,seedLaw_eq]

theorem nativeLaw_apply (s : ℕ) (B : Set (Bool × Bool × Bool × Bool))
    (hB : MeasurableSet B) : nativeLaw s B = CoinPaths.law {ω | ∃ z k,
      Progress.Evaluates (client ω) (initial s) z k ∧ z.1 ∈ B} := by
  rw [nativeLaw,Measure.map_apply (measurable_of_countable _) hB,seedLaw,
    RetainedSampler.valueLaw_apply _ _ _ _ _ ((measurable_of_countable _) hB)]
  congr 1
  ext ω
  constructor
  · rintro ⟨z,k,h,hB⟩
    exact ⟨selected z,k,Progress.mapReturn_evaluates h,hB⟩
  · rintro ⟨z,k,h,hB⟩
    obtain ⟨a,ha,rfl⟩ := Progress.mapReturn_evaluates_inv h
    exact ⟨a,k,ha,hB⟩

abbrev functionObservation := QuasiBorel.prod
  (QuasiBorel.prod SamplerSubstitution.functions SamplerSubstitution.bit)
  SamplerSubstitution.bit

/-- Interpret an explicit finite function code; no representation is selected
by classical choice. The complete function remains in the result. -/
def interpret (z : Bool × Bool × Bool × Bool) : functionObservation :=
  ((SamplerSubstitution.sampled z.1,z.2.2.1),z.2.2.2)

theorem interpret_selected (b t u : Bool) :
    interpret (SamplerClient.selected b t u) =
      QuasiBorel.retainedTwo SamplerSubstitution.sampled SamplerSubstitution.query
        SamplerSubstitution.next ((b,t),u) := rfl

theorem whole_function_law (s : ℕ) :
    @Measure.map _ functionObservation _ (QuasiBorel.sigma functionObservation)
      interpret (nativeLaw s) =
      QuasiBorel.law ((SamplerClient.fair.prod SamplerClient.fair).prod SamplerClient.fair)
        (QuasiBorel.retainedTwo SamplerSubstitution.sampled SamplerSubstitution.query
          SamplerSubstitution.next) := by
  let : MeasurableSpace functionObservation := QuasiBorel.sigma functionObservation
  rw [nativeLaw,Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    seedLaw_eq]
  rfl

/-- Reuse the public represented substitution theorem for the whole function
observation. No seed, tape, cursor or work equality is asserted. -/
theorem whole_function_replacement (s : ℕ) :
    @Measure.map _ functionObservation _ (QuasiBorel.sigma functionObservation)
      interpret (nativeLaw s) =
      QuasiBorel.law ((SamplerClient.fair.prod SamplerClient.fair).prod SamplerClient.fair)
        (QuasiBorel.retainedTwo SamplerSubstitution.recodedTwice SamplerSubstitution.query
          SamplerSubstitution.next) :=
  (whole_function_law s).trans SamplerSubstitution.twice_replaced

/-- Copying the sampled function code requires only one actual draw. -/
def copied (ω : CoinPaths.Tape) := Progress.mapReturn
  (fun z : Bool × ℕ => ((z.1,z.1),z.2)) (fairRow.step ω)

theorem copied_off_diagonal (s : ℕ) : CoinPaths.law {ω | ∃ t k,
    Progress.Evaluates (copied ω) (fairRow.start s) ((false,true),t) k}=0 := by
  have he : {ω | ∃ t k, Progress.Evaluates (copied ω) (fairRow.start s)
      ((false,true),t) k}=∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
    rintro ⟨t,k,h⟩
    obtain ⟨⟨b,u⟩,_,he⟩ := Progress.mapReturn_evaluates_inv h
    cases b <;> simp at he
  rw [he,measure_empty]

theorem copied_diagonal (s : ℕ) (b : Bool) : CoinPaths.law {ω | ∃ t k,
    Progress.Evaluates (copied ω) (fairRow.start s) ((b,b),t) k}=(2⁻¹ : ℝ≥0∞) := by
  have he : {ω | ∃ t k, Progress.Evaluates (copied ω) (fairRow.start s)
      ((b,b),t) k}=fairRow.returns s b := by
    ext ω
    constructor
    · rintro ⟨t,k,h⟩
      obtain ⟨⟨a,u⟩,ha,he⟩ := Progress.mapReturn_evaluates_inv h
      have hab : a=b := congrArg (fun z => z.1.1) he
      subst a
      exact ⟨u,k,ha⟩
    · rintro ⟨t,k,h⟩
      exact ⟨t,k,Progress.mapReturn_evaluates h⟩
  rw [he,fair_mass]

theorem resampled_joint_mass (s : ℕ) (b c : Bool) : CoinPaths.law {ω | ∃ t u k,
    Progress.Evaluates (fairRow.pairStep (fun _ => fairRow) ω) (.inl (fairRow.start s))
      ((b,t),(c,u)) k}=(4⁻¹ : ℝ≥0∞) := by
  rw [PreparedRow.pair_joint_mass,fair_mass,fair_mass]
  norm_num [← ENNReal.mul_inv]

/-- Resampling uses the first draw's returned cursor, so the separating event
has mass 1/4 despite the same individual function-code distributions. -/
theorem resampled_off_diagonal (s : ℕ) : CoinPaths.law {ω | ∃ t u k,
    Progress.Evaluates (fairRow.pairStep (fun _ => fairRow) ω) (.inl (fairRow.start s))
      ((false,t),(true,u)) k}=(4⁻¹ : ℝ≥0∞) := by
  exact resampled_joint_mass s false true

theorem reused_off_diagonal (s : ℕ) : CoinPaths.law {ω | ∃ t u k,
    Progress.Evaluates (fairRow.reusedPairStep s ω) (.inl (fairRow.start s))
      ((false,t),(true,u)) k}=0 :=
  fairRow.reused_off_diagonal s false true (by decide)

example : Progress.search (copied exampleTape) 2 (fairRow.start 0)=
    some (((false,false),2),2) := by decide +kernel

example : Progress.search (fairRow.pairStep (fun _ => fairRow) exampleTape)
    4 (.inl (fairRow.start 0))=some (((false,2),(true,4)),4) := by decide +kernel

example : Progress.search (fairRow.reusedPairStep 0 exampleTape)
    4 (.inl (fairRow.start 0))=some (((false,2),(false,2)),4) := by decide +kernel

/-- Different finite codes denote different complete functions. -/
theorem function_code_injective : Function.Injective SamplerSubstitution.sampled := by
  intro a b h
  have hfalse := congrArg (fun f : SamplerSubstitution.functions => f false) h
  simpa [SamplerSubstitution.sampled,SamplerSubstitution.xorHom,
    QuasiBorel.curry,SamplerClient.function] using hfalse

example : SamplerSubstitution.sampled false ≠ SamplerSubstitution.sampled true :=
  fun h => Bool.false_ne_true (function_code_injective h)

/-- A non-dyadic continuation retains both earlier inputs and uses their
returned cursor; it is not replaced by a one-bit abstract noise source. -/
def biasedTable : Table Unit Bool where
  entry _ b := if b then 2/3 else 1/3
  nonneg _ b := by cases b <;> norm_num
  sum_row _ := by norm_num [Fintype.sum_bool]

abbrev biasedRow := biasedTable.prepare finTwoEquiv ()

def dependentRow (b t : Bool) :=
  if SamplerClient.function b t then biasedRow else fairRow

example : CoinPaths.law (RetainedSampler.event fairRow (fun _ => fairRow)
    (fun _ _ => biasedRow) 0 false true true)=(1/6 : ℝ≥0∞) := by
  rw [RetainedSampler.event_mass,Table.prepare_returns_mass,Table.prepare_returns_mass,
    Table.prepare_returns_mass]
  change mass (1/2) * (mass (1/2) * mass (2/3)) = _
  rw [← mass_mul (1/2) (2/3) (by norm_num),
    ← mass_mul (1/2) ((1/2)*(2/3)) (by norm_num)]
  norm_num [mass,ENNReal.ofReal_div_of_pos]

/-- 00,10 produce false,true. 1111 is rejected; 0110 then produces true. -/
def rejectedTape (i : ℕ) : Bool := decide (i = 2 ∨ (4 ≤ i ∧ i < 8) ∨ i = 9 ∨ i = 10)

example : Progress.search (RetainedSampler.step fairRow (fun _ => fairRow)
    (fun _ _ => biasedRow) rejectedTape) 12 (initial 0)=
    some (((false,2),(true,4),(true,12)),12) := by decide +kernel

example : Progress.search (RetainedSampler.step fairRow (fun _ => fairRow)
    (fun _ _ => biasedRow) rejectedTape) 11 (initial 0)=none := by decide +kernel

example : CoinPaths.law (RetainedSampler.event fairRow (fun _ => fairRow)
    dependentRow 0 false false true)=(8⁻¹ : ℝ≥0∞) := by
  rw [RetainedSampler.event_mass]
  change CoinPaths.law (fairRow.returns 0 false) *
    (CoinPaths.law (fairRow.returns 0 false) * CoinPaths.law (fairRow.returns 0 true)) = _
  simp only [fair_mass]
  norm_num [← ENNReal.mul_inv]

example : Progress.search (RetainedSampler.step fairRow (fun _ => fairRow)
    dependentRow rejectedTape) 12 (initial 0)=
    some (((false,2),(true,4),(true,12)),12) := by decide +kernel

end Examples.OperationalSamplerSubstitution
