import Applications.FRP.RegionalSelection

/-! Accounting for session installation and observed ticks. These are declared
logical operation tariffs, not Lean heap cells or elapsed nanoseconds. -/
namespace FRPSpec.Regional.Selection
open Progress Progress.Feedback Optimization.Choice

/-- Every operation is charged with its actual payload size. In particular an
untrusted epoch is not assigned a constant validation charge. -/
inductive Event where
  | feature (characters : Nat)
  | admission (nodes : Nat)
  | validate (payload : Nat)
  | rank (payload : Nat)
  | prepare (retained : Nat)
  | execute (work : Nat)
  | observe (cells : Nat)
  deriving Repr, DecidableEq

def Event.charge : Event → Nat
  | .feature n => n + 1
  | .admission n => n + 5
  | .validate payload => 1 + payload
  | .rank m => 1 + m
  | .prepare n => 1 + n
  | .execute n => n
  | .observe n => n

def bill (events : List Event) : Nat := (events.map Event.charge).sum

def contextSize (c : Context) : Nat :=
  c.implementation.length + c.target.length + c.workload.length + c.site.length +
  c.protocol.length + c.requirements.length + (c.catalog.map String.length).sum

def planNodes : Plan A B → Nat
  | .seq p q | .par p q => 1 + planNodes p + planNodes q
  | _ => 1

/-- A charged operation records its actual execution. Traversal combinators
below accumulate these records on the path actually taken. -/
abbrev Charged (α : Type) := α × List Event

def probe (value : Bool) (payload : Nat := 1) : Charged Bool :=
  (value,[.validate payload])
def conjunction (a : Charged Bool) (b : Unit → Charged Bool) : Charged Bool :=
  if a.1 then let next := b (); (next.1,a.2 ++ next.2) else (false,a.2)
@[simp] theorem conjunction_value (a : Charged Bool) (b : Unit → Charged Bool) :
    (conjunction a b).1 = (a.1 && (b ()).1) := by
  simp only [conjunction]; split <;> simp_all

def allChecks (f : α → Charged Bool) : List α → Charged Bool
  | [] => (true,[])
  | x::xs => conjunction (f x) (fun _ => allChecks f xs)
@[simp] theorem allChecks_value (f : α → Charged Bool) (xs : List α) :
    (allChecks f xs).1 = xs.all (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [allChecks,ih]

def countChecks (f : α → Charged Bool) : List α → Nat × List Event
  | [] => (0,[])
  | x::xs => let h := f x; let t := countChecks f xs
            ((if h.1 then 1 else 0) + t.1,h.2 ++ t.2)
@[simp] theorem countChecks_value (f : α → Charged Bool) (xs : List α) :
    (countChecks f xs).1 = (xs.filter fun x => (f x).1).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [countChecks,List.filter_cons]; split <;> simp_all [Nat.add_comm]

def containsCheck (name : String) (xs : List String) : Charged Bool :=
  let absent := allChecks (fun x => probe (x != name) (x.length + name.length)) xs
  (!absent.1,absent.2)
@[simp] theorem containsCheck_value (name : String) (xs : List String) :
    (containsCheck name xs).1 = xs.contains name := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [containsCheck,allChecks_value,probe,List.all_cons] at *
    by_cases h : name = x
    · subst x; simp_all
    · have hx : x ≠ name := Ne.symm h
      simp_all [Bool.not_and]

def uniqueCheck : List String → Charged Bool
  | [] => (true,[])
  | x::xs => let found := containsCheck x xs
            conjunction (!found.1,found.2) (fun _ => uniqueCheck xs)
@[simp] theorem uniqueCheck_value (xs : List String) :
    (uniqueCheck xs).1 = decide xs.Nodup := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [uniqueCheck,ih]

/-- Validation traverses the deserialized evidence itself, including duplicate
and missing samples. Rejection stops subsequent checks and retains its bill. -/
def validateEpoch (e : Epoch) (ctx : Context) : Charged Bool :=
  conjunction (probe (e.context == ctx) (contextSize e.context + contextSize ctx)) fun _ =>
  conjunction (probe (e.repetitions == 1)) fun _ =>
  conjunction (uniqueCheck ctx.catalog) fun _ =>
  conjunction (probe (e.samples.length == ctx.catalog.length)
    (e.samples.length + ctx.catalog.length)) fun _ =>
  conjunction (allChecks (fun s =>
    conjunction (probe (s.context == ctx) (contextSize s.context + contextSize ctx)) fun _ =>
    conjunction (probe s.success) fun _ =>
    conjunction (containsCheck s.candidate ctx.catalog) fun _ =>
    probe (s.repetition < 1)) e.samples) fun _ =>
  allChecks (fun c =>
    let counted := countChecks (fun s =>
      conjunction (probe (s.candidate == c) (s.candidate.length + c.length)) fun _ =>
      probe (s.repetition == 0)) e.samples
    (counted.1 == 1,counted.2 ++ [.validate 1])) ctx.catalog

theorem validateEpoch_value (e : Epoch) (ctx : Context) :
    (validateEpoch e ctx).1 = e.complete ctx 1 := by
  simp [validateEpoch,probe,Epoch.complete,Bool.and_assoc]

/-- Runtime requirements short-circuit before structural plan analysis. Each
analysis operation records the plan or checkpoint list actually inspected. -/
def assessCandidate (r : Requirements) (c : Sites) : Charged Bool :=
  conjunction (probe (r.protocol == 1)) fun _ =>
  conjunction (probe r.ordered) fun _ =>
  conjunction (probe r.finiteWaits) fun _ =>
  conjunction (c.plan.analyzed,[.admission (planNodes c.plan)]) fun _ =>
  (decide (c.plan.storage ≤ r.capacity),[.admission c.plan.checkpoints.length])
@[simp] theorem assessCandidate_value (r : Requirements) (c : Sites) :
    (assessCandidate r c).1 = decide (eligible r c) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  simp [assessCandidate,probe,eligible]

/-- The admission traversal evaluates the completed plan at each site pair. -/
def inspect (r : Requirements) : List Sites → List Sites × List Event
  | [] => ([],[])
  | c::cs => let tested := assessCandidate r c
             let rest := inspect r cs
             (if tested.1 then c::rest.1 else rest.1,tested.2 ++ rest.2)
@[simp] theorem inspect_value (r : Requirements) (cs : List Sites) :
    (inspect r cs).1 = cs.filter (fun c => decide (eligible r c)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [inspect,List.filter_cons,ih,assessCandidate_value]

/-- Evidence score extraction charges every examined sample. -/
def totalScore (e : Epoch) (c : Sites) : Nat × List Event :=
  e.samples.foldr (fun s rest =>
    (if s.candidate == c.name then s.elapsedNs + rest.1 else rest.1,
     Event.rank (s.candidate.length + c.name.length) :: rest.2)) (0,[])
theorem totalScore_value (e : Epoch) (c : Sites) : (totalScore e c).1 = e.total c.name := by
  unfold totalScore Epoch.total
  induction e.samples with
  | nil => rfl
  | cons s ss ih => simp only [List.foldr_cons,List.filter_cons]; split <;> simp_all

def rank (score : Sites → Nat × List Event) : List Sites → Option Sites × List Event
  | [] => (none,[])
  | c::cs =>
    let rest := rank score cs
    match rest.1 with
    | none => (some c,rest.2 ++ [.rank 0])
    | some d =>
      let left := score c
      let right := score d
      (some (if left.1 ≤ right.1 then c else d),rest.2 ++ left.2 ++ right.2 ++ [.rank 0])
theorem rank_value (score : Sites → Nat × List Event) (cs : List Sites) :
    (rank score cs).1 = Optimization.Thinning.argmin (fun c => (score c).1) cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases h : (rank score cs).1 <;> simp only [rank,Optimization.Thinning.argmin,← ih,h]

def preparedScores (e : Option Epoch) (ctx : Context) :
    (Sites → Nat × List Event) × List Event :=
  match e with
  | none => ((fun c => (c.plan.work,[.rank (planNodes c.plan)])),[])
  | some epoch =>
    let validated := validateEpoch epoch ctx
    ((fun c => if validated.1 then totalScore epoch c else
      (c.plan.work,[.rank (planNodes c.plan)])),validated.2)
@[simp] theorem preparedScores_value (e : Option Epoch) (ctx : Context) (c : Sites) :
    ((preparedScores e ctx).1 c).1 =
      policyScore ctx 1 Sites.name (fun c => c.plan.work) e c := by
  cases e with
  | none => rfl
  | some epoch =>
    simp only [preparedScores,validateEpoch_value,policyScore]
    split <;> simp_all [totalScore_value]

def prepareResult (choice : Option Sites) (events : List Event) : Option Session × List Event :=
  match choice with
  | none => (none,events)
  | some c => (some (Session.start c),events ++ [.prepare c.plan.retained])
@[simp] theorem prepareResult_value (choice) (events) :
    (prepareResult choice events).1.map Session.sites = choice := by
  cases choice <;> rfl

/-- Actual traversals produce both the installed session and its operation log. -/
def installation (r : Requirements) (w : String) (e : Option Epoch)
    (cs : List Sites := catalog) : Option Session × List Event :=
  let assessed := inspect r cs
  let ctx := {context r w with catalog := assessed.1.map Sites.name}
  let scored := preparedScores e ctx
  let ranked := rank scored.1 assessed.1
  let events := [.feature (contextSize (context r w))] ++ assessed.2 ++ scored.2 ++ ranked.2
  prepareResult ranked.1 events

theorem installation_selected (r : Requirements) (w : String) (e) (cs) :
    (installation r w e cs).1.map Session.sites = select r w e cs := by
  simp only [installation,prepareResult_value,rank_value,inspect_value,preparedScores_value]
  rfl

/-- Tick execution and observation have separate events. Adapter work is already
included in Plan.stepWork, including copies and redundant boundary checks. -/
def Session.tick (s : Session) (x : Input × Input) : (Bool × Bool) × Session × List Event :=
  let result := s.sites.plan.machine.step (x,s.state)
  (result.1,⟨s.sites,result.2⟩,[.execute (s.sites.plan.stepWork x s.state),.observe 2])

theorem Session.tick_bill (s : Session) (x : Input × Input) :
    bill (s.tick x).2.2 = s.sites.plan.stepWork x s.state + 2 := by
  simp [Session.tick,bill,Event.charge]

theorem Session.tick_bound (s : Session) (x : Input × Input) :
    bill (s.tick x).2.2 ≤ s.sites.plan.work + 2 := by
  rw [s.tick_bill]
  exact Nat.add_le_add_right (s.sites.plan.stepWork_le x s.state) 2

/-- A supplied fallback passes the same whole-plan requirements. -/
def withFallback (r : Requirements) (w : String) (e : Option Epoch)
    (cs : List Sites) (fallback : Sites) : Option Sites :=
  match select r w e cs with
  | some c => some c
  | none => if eligible r fallback then some fallback else none

/-- Fallback attempts reuse the actual admission traversal and retain rejected
installation costs. A fallback cannot waive the whole-plan requirement. -/
def installationFallback (r : Requirements) (w : String) (e : Option Epoch)
    (cs : List Sites) (fallback : Sites) : Option Session × List Event :=
  let primary := installation r w e cs
  match primary.1 with
  | some session => (some session,primary.2)
  | none =>
    let assessed := inspect r [fallback]
    prepareResult assessed.1.head? (primary.2 ++ assessed.2)

theorem installationFallback_selected (r : Requirements) (w : String) (e)
    (cs : List Sites) (fallback : Sites) :
    (installationFallback r w e cs fallback).1.map Session.sites = withFallback r w e cs fallback := by
  have h := installation_selected r w e cs
  cases hi : (installation r w e cs).1 with
  | none =>
    simp only [hi,Option.map_none] at h
    simp only [installationFallback,hi,withFallback,← h,prepareResult_value,inspect_value]
    by_cases hf : eligible r fallback <;> simp [hf]
  | some session =>
    simp only [hi,Option.map_some] at h
    simp [installationFallback,hi,withFallback,← h]

/-- Proof association is indexed by the actual program, observation, parameters
and backend. No string name or ranking score stands in for this proof. -/
structure Certificate (r : Requirements) (c : Sites) : Prop where
  analysis : c.plan.analyzed = true
  storage : c.plan.storage ≤ r.capacity
  semantics : ∀ s xs,
    (run c.plan.machine.mealy s xs).1 = (run oracle.mealy (c.observe s) xs).1 ∧
    c.observe (run c.plan.machine.mealy s xs).2 = (run oracle.mealy (c.observe s) xs).2

theorem selected_certificate {r : Requirements} {w} {e} {cs} {c : Sites}
    (h : select r w e cs = some c) : Certificate r c := by
  have hc : eligible r c := Optimization.Choice.choose_contract (eligible r)
    (fun _ _ hc => hc) h
  exact ⟨hc.2.2.2.1,hc.2.2.2.2,c.continuation⟩

end FRPSpec.Regional.Selection
