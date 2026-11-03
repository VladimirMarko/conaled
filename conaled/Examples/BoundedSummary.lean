import Applications.Resources.BoundedSummary

/-! Checked capability, semantic and resource comparisons for #239. -/
namespace Examples.BoundedSummary
open Sequences.BoundedSummary Sequences.BoundedSummary.Buffer
open Resources.BoundedSummary

def two : Buffer 2 := push (push (empty 2) true (by decide)) false (by decide)
def one : Buffer 2 := push (empty 2) true (by decide)
def four : List Bool := [true,false,true,true]
def unit : Tariff := {}
def expensiveWrites : Tariff := {cacheWrite := 2}
def expensiveReads : Tariff := {cacheRead := 10}

example : decode two = [true,false] := by
  rw [two,decode_push,decode_push,decode_empty]; rfl
example : query two = parity [true,false] := by
  rw [query_correct,two,decode_push,decode_push,decode_empty]; rfl
example : tryPush two true = (two,false) := overflow two true rfl
example : tryPush (empty 0) false = (empty 0,false) := overflow _ _ rfl
example : Valid (cache two) := cache_valid two
example : ¬ Valid (two,⟨false⟩) := by
  change ¬ (True ∧ (⟨false⟩ : Parity) = parity two.decode)
  decide

/-- The actual client replies include both parity and ordered full history. -/
example : (trace plainStep [.append true,.append false,.query,.observe,.append true] (empty 2)).2 =
    [.appended true,.appended true,.summary ⟨true⟩,.sequence [true,false],.appended false] := by
  have h := congrArg Prod.snd (plain_trace
    [.append true,.append false,.query,.observe,.append true] (empty 2))
  exact h.trans (by decide)

example :
    ((trace plainStep (batch four) (empty 4)).1.decode,(trace plainStep (batch four) (empty 4)).2) =
    ((trace cachedStep (batch four) (cache (empty 4))).1.1.decode,
      (trace cachedStep (batch four) (cache (empty 4))).2) := traces_equal _ _

example :
    ((trace plainStep (everyPrefix four) (empty 4)).1.decode,
      (trace plainStep (everyPrefix four) (empty 4)).2) =
    ((trace cachedStep (everyPrefix four) (cache (empty 4))).1.1.decode,
      (trace cachedStep (everyPrefix four) (cache (empty 4))).2) := traces_equal _ _

example : two.decode.inits.map List.length = [0,1,2] := prefix_elimination two

/-- The same factorization reaches the existing symmetric-prefix consumer. -/
example (s : Sequences.Symmetric.SymList Bool) (h : Sequences.Symmetric.Inv s)
    (obs : Sequences.Symmetric.fromSL s = two.decode) :
    ((Sequences.Symmetric.prefixLengths (α := Bool)).impl s).down = [0,1,2] := by
  rw [Sequences.OrderedSummary.symmetric_prefix_summary s h,obs,
    Sequences.OrderedSummary.summary_length]
  rfl

/-- Ordered words expose information lost by the finite parity cache. -/
example : Sequences.OrderedSummary.summary FreeMonoid.of two.decode =
    FreeMonoid.ofList [true,false] := by
  change FreeMonoid.lift FreeMonoid.of two.decode = _
  rfl
example : parity [true,false] = parity [false,true] ∧
    ([true,false] : List Bool) ≠ [false,true] := by decide
example : ([false] : List Bool).length = [true].length ∧ ([false] : List Bool) ≠ [true] := by decide
example : ¬ ∃ answer : Unit → List Bool, answer () = [false] ∧ answer () = [true] :=
  stateless_impossible

example : (Resources.run (liftM (plainM unit)) (everyPrefix four) (empty 4,[])).1 =
    trace plainStep (everyPrefix four) (empty 4) := plain_erasure _ _ _
example : (Resources.run (liftM (cachedM unit)) (everyPrefix four) (cache (empty 4),[])).1 =
    trace cachedStep (everyPrefix four) (cache (empty 4)) := cached_erasure _ _ _

/-- Array append baseline is three units: capacity check, slot write, counter write. -/
example : (Resources.run (liftM (plainM unit)) (batch four) (empty 4,[])).2 = 21 := by
  rw [plain_cost]; decide
example : (Resources.run (liftM (cachedM unit)) (batch four) (cache (empty 4),[])).2 = 21 := by
  rw [cached_cost _ _ _ (cache_valid _)]; decide
example : total false unit 4 (batch four) = 26 ∧ total true unit 4 (batch four) = 27 := by decide
example : total false unit 4 (everyPrefix four) = 41 ∧ total true unit 4 (everyPrefix four) = 30 := by decide
example : total true expensiveWrites 4 (batch four) = 32 ∧
    total false expensiveWrites 4 (batch four) = 26 := by decide
example : total true expensiveReads 4 (everyPrefix four) = 66 ∧
    total false expensiveReads 4 (everyPrefix four) = 41 := by decide
example : total false unit 4 (four.map Command.append) = 17 ∧
    total true unit 4 (four.map Command.append) = 26 := by decide
example : total false unit 0 [] = 1 ∧ total true unit 0 [] = 2 := by decide

/-- Full output has identical scan/emit operations in these two implementations. -/
example : (plainM unit .observe two).2 = 5 ∧ (cachedM unit .observe (cache two)).2 = 5 := by
  rw [plainM_exact,cachedM_exact]; decide

example : Valid (convert unit one).1 := convert_valid _ _
example : (convert unit one).1.1.decode = [true] := by rw [convert_exact]; rfl
example : (convert unit one).2 = 8 := by rw [convert_exact]; decide

/-- Cached future queries save four units, but the copying conversion costs eight. -/
example : (Resources.run (liftM (plainM unit)) [.query,.query] (one,[])).2 = 6 ∧
    (Resources.bind (convert unit one)
      (fun c => Resources.run (liftM (cachedM unit)) [.query,.query] (c,[]))).2 = 10 := by
  constructor
  · rw [plain_cost]; decide
  · simp only [Resources.bind,convert_exact]
    rw [cached_cost _ _ _ (cache_valid _)]; decide

example : retained false 4 = 5 ∧ retained true 4 = 6 ∧ conversionPeak 4 = 11 := by decide
example : retained false 4 ≤ conversionPeak 4 ∧ retained true 4 ≤ conversionPeak 4 := peak_covers _
example := sequential unit (four.map Command.append) [.query] (empty 4)
example := change_units 3 unit (everyPrefix four) (empty 4)

def tieTariff : Tariff := {cacheRead := 2}
def tieWork : List Command := [.append true,.query,.query,.query]

theorem tie_plain : Candidate.plain ∈ Optimization.minimizers eligible (candidateCost tieTariff 1 tieWork) := by
  refine ⟨by simp [eligible], ?_⟩
  intro c hc
  cases c with
  | plain => change candidateCost tieTariff 1 tieWork .plain ≤ candidateCost tieTariff 1 tieWork .plain; exact Nat.le_refl _
  | cached => decide
  | stateless => exact False.elim (hc rfl)

theorem tie_cached : Candidate.cached ∈ Optimization.minimizers eligible (candidateCost tieTariff 1 tieWork) := by
  refine ⟨by simp [eligible], ?_⟩
  intro c hc
  cases c with
  | plain => decide
  | cached => change candidateCost tieTariff 1 tieWork .cached ≤ candidateCost tieTariff 1 tieWork .cached; exact Nat.le_refl _
  | stateless => exact False.elim (hc rfl)

example : Optimization.Attained eligible (candidateCost tieTariff 1 tieWork) := ⟨.plain,tie_plain⟩
example : candidateCost tieTariff 1 tieWork .plain = 14 ∧ candidateCost tieTariff 1 tieWork .cached = 14 := by decide
example : Candidate.stateless ∉ Optimization.minimizers eligible (candidateCost unit 4 (everyPrefix four)) :=
  unavailable _ _ _

def workSpace : Candidate → Nat × Nat
  | .plain => (total false unit 4 (everyPrefix four),retained false 4)
  | .cached => (total true unit 4 (everyPrefix four),retained true 4)
  | .stateless => (0,0)

theorem incomparable : ¬ workSpace .plain ≤ workSpace .cached ∧ ¬ workSpace .cached ≤ workSpace .plain := by decide

theorem plain_pareto : Candidate.plain ∈ Optimization.pareto eligible workSpace := by
  refine ⟨by simp [eligible], ?_⟩
  intro c hc hle
  cases c with
  | plain => exact le_refl _
  | cached => exact False.elim (incomparable.2 hle)
  | stateless => exact False.elim (hc rfl)

theorem cached_pareto : Candidate.cached ∈ Optimization.pareto eligible workSpace := by
  refine ⟨by simp [eligible], ?_⟩
  intro c hc hle
  cases c with
  | plain => exact False.elim (incomparable.1 hle)
  | cached => exact le_refl _
  | stateless => exact False.elim (hc rfl)

example : Valid (trace cachedStep [.append true,.append false,.append true] (cache (empty 2))).1 :=
  cached_trace_valid _ _ (cache_valid _)

example : Within 4 (batch four) [] := admitted_within (by change appends _ ≤ 4; decide)
example : Admitted 4 (four.map Command.append) :=
  admitted_prefix (ys := [.query]) (by change appends _ ≤ 4; decide)
example : spec 2 (.append false) [true] = ([true,false],.appended true) :=
  accepted_append _ _ (by decide)

example : (plainProgram unit 4 (everyPrefix four)).2 = 41 := by rw [plainProgram_cost]; decide
example : (cachedProgram unit 4 (everyPrefix four)).2 = 30 := by rw [cachedProgram_cost]; decide
example : operationPeak true 2 two.size.val ≤ retained true 2 + (2+1)+2 := operation_peak_bound _ _
example : conversionWorkingPeak 4 = 16 := by decide

example : Candidate.plain ∈ Optimization.minimizers (admittedCandidates 1 tieWork)
    (candidateCost tieTariff 1 tieWork) := by
  rw [admitted_candidates (show Admitted 1 tieWork from by change appends _ ≤ 1; decide)]
  exact tie_plain
example : Candidate.cached ∈ Optimization.pareto (admittedCandidates 4 (everyPrefix four)) workSpace := by
  rw [admitted_candidates (show Admitted 4 (everyPrefix four) from by change appends _ ≤ 4; decide)]
  exact cached_pareto
example : admittedCandidates 0 [.append true] = ∅ := by
  ext c
  simp [admittedCandidates,Admitted,appends]

example : ¬ ∃ reply : Command → Reply, ∀ cs, Admitted 1 cs →
    statelessReplies reply cs = (trace (spec 1) cs []).2 := no_stateless_trace

end Examples.BoundedSummary
