import Applications.FRP.RegionalPendingResources

/-! A local policy client for the actual shared producer/consumer continuation.
It reuses charged evidence validation from #486. Selection cannot authorize a
migration: the chosen executor still passes the public transfer admission. -/
namespace FRPSpec.Regional.Pending
open Applications.Circuits

structure Candidate where
  cut : Cut
  kind : Migration.Kind
  deriving DecidableEq

def Candidate.name (c : Candidate) : String :=
  Selection.cutName c.cut ++ "/" ++ Migration.kindText c.kind

def candidates : List Candidate :=
  [.fused,.split,.checked].flatMap fun cut => [.delay,.redundant].map fun kind => ⟨cut,kind⟩

def Candidate.consumerWork (c : Candidate) : Nat := match c.cut with
  | .fused => jointBody.work
  | .split => Indefinite.delay.body.work + Circuit.not.work + Circuit.xor.work
  | .checked => Indefinite.delay.body.work + Circuit.not.work + Circuit.xor.work + 4

/-- Complete transaction score: one rich producer, the actual selected consumer
subgraph, encoded residual updates, bounded protocol and adapter charges. -/
def Candidate.staticWork (c : Candidate) : Nat :=
  Rich.dispatches Rich.code ((),Sum.inl false) + c.consumerWork +
  4 * retainedCells c.cut + 8 * 14 + 12

def Candidate.eligible (r : Requirements) (c : Candidate) : Prop :=
  supported r ∧ serviceCapacity c.cut ≤ r.capacity
instance (r : Requirements) (c : Candidate) : Decidable (c.eligible r) :=
  inferInstanceAs (Decidable (_ ∧ _))

def inspectCandidates (r : Requirements) : List Candidate → List Candidate × List Selection.Event
  | [] => ([],[])
  | c::cs =>
    let assessed := Selection.conjunction (Selection.probe (decide (supported r)) 3) fun _ =>
      (decide (serviceCapacity c.cut ≤ r.capacity),[.admission (retainedCells c.cut)])
    let rest := inspectCandidates r cs
    (if assessed.1 then c::rest.1 else rest.1,assessed.2 ++ rest.2)

def policyContext (r : Requirements) (workload : String) (cs : List Candidate) : Optimization.Choice.Context :=
  ⟨"pending-shared-v1","Lean-modeled-cells",workload,"shared-F/D+N/join",
    "two-slots-four-events-owner-confirmation-v2",
    [r.capacity,r.protocol,if r.ordered then 1 else 0,if r.finiteWaits then 1 else 0],cs.map Candidate.name⟩

def candidateScore (e : Option Optimization.Choice.Epoch) (valid : Bool) (c : Candidate) :
    Nat × List Selection.Event := match e with
  | some epoch => if valid then
      epoch.samples.foldr (fun sample rest =>
        (if sample.candidate == c.name then sample.elapsedNs + rest.1 else rest.1,
         Selection.Event.rank (sample.candidate.length+c.name.length)::rest.2)) (0,[])
    else (c.staticWork,[.rank 1])
  | none => (c.staticWork,[.rank 1])

def rankCandidates (score : Candidate → Nat × List Selection.Event) :
    List Candidate → Option Candidate × List Selection.Event
  | [] => (none,[])
  | c::cs =>
    let rest := rankCandidates score cs
    match rest.1 with
    | none => (some c,rest.2 ++ [.rank 0])
    | some d =>
      let left := score c
      let right := score d
      (some (if left.1 ≤ right.1 then c else d),rest.2 ++ left.2 ++ right.2 ++ [.rank 0])

def propose (s : Session) (r : Requirements) (workload : String)
    (e : Option Optimization.Choice.Epoch := none) (cs : List Candidate := candidates) : Outcome :=
  if s.prepared.isSome then reject s .frozen else
  if !s.permitted then reject s .throttled else
  let assessed := inspectCandidates r cs
  let ctx := policyContext r workload assessed.1
  let validation := match e with
    | none => (false,[])
    | some epoch => Selection.validateEpoch epoch ctx
  let ranked := rankCandidates (candidateScore e validation.1) assessed.1
  let bill := Selection.bill ([.feature (Selection.contextSize ctx)] ++ assessed.2 ++ validation.2 ++ ranked.2)
  match ranked.1 with
  | none => ⟨⟨s.active,none,false⟩,.unsupported,none,none,none,[.policy bill]⟩
  | some c =>
    let out := prepare s s.active.cut c.cut c.kind r true true false
    {out with events := .policy bill :: out.events}

@[simp] theorem inspectCandidates_value (r : Requirements) (cs : List Candidate) :
    (inspectCandidates r cs).1 = cs.filter (fun c => decide (c.eligible r)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [inspectCandidates,List.filter_cons,ih,Selection.conjunction_value,Selection.probe]
    have test : (decide (supported r) && decide (serviceCapacity c.cut ≤ r.capacity)) =
        decide (c.eligible r) := by
      by_cases h : supported r <;> simp [Candidate.eligible,h]
    rw [test]

theorem rankCandidates_value (score : Candidate → Nat × List Selection.Event) (cs : List Candidate) :
    (rankCandidates score cs).1 = Optimization.Thinning.argmin (fun c => (score c).1) cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases h : (rankCandidates score cs).1 <;>
      simp only [rankCandidates,Optimization.Thinning.argmin,← ih,h]

end FRPSpec.Regional.Pending
