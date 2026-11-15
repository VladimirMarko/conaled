import Applications.Optimization.Choice.Selection

/-! Offline evidence ranks a finite catalog. A complete epoch has one successful
sample per candidate and repetition, under an exact declared context. Missing or
invalid evidence falls back for the entire catalog, never by mixing measured
nanoseconds with modeled scores. Context equality does not certify clock or
hardware accuracy. Selection correctness does not depend on that accuracy. -/
namespace Optimization.Choice

structure Context where
  implementation : String
  target : String
  workload : String
  site : String
  protocol : String
  requirements : List Nat
  catalog : List String
  deriving DecidableEq, BEq, Repr

structure Sample where
  candidate : String
  repetition : Nat
  elapsedNs : Nat
  success : Bool
  context : Context
  deriving DecidableEq, BEq, Repr

structure Epoch where
  context : Context
  repetitions : Nat
  samples : List Sample
  deriving DecidableEq, BEq, Repr

def Epoch.start (context : Context) (repetitions : Nat) : Epoch :=
  ⟨context, repetitions, []⟩

/-- Observations are explicitly supplied; selection does not explore silently.
Rejected records leave the old immutable epoch available to its caller. -/
def Epoch.record (epoch : Epoch) (context : Context) (sample : Sample) : Except String Epoch := do
  if context != epoch.context then throw "context mismatch"
  if sample.context != context then throw "observation context mismatch"
  if epoch.repetitions == 0 then throw "zero repetitions"
  if !decide epoch.context.catalog.Nodup then throw "duplicate candidate IDs"
  if !epoch.context.catalog.contains sample.candidate then throw "unknown candidate"
  if sample.repetition >= epoch.repetitions then throw "repetition out of range"
  if !sample.success then throw "failed observation"
  if epoch.samples.any (fun s => s.candidate == sample.candidate && s.repetition == sample.repetition)
    then throw "duplicate observation"
  return { epoch with samples := epoch.samples ++ [sample] }

/-- Validate deserialized epochs too; going through `record` is not trusted. -/
def Epoch.complete (epoch : Epoch) (context : Context) (repetitions : Nat) : Bool :=
  epoch.context == context && epoch.repetitions == repetitions && repetitions > 0 &&
  decide context.catalog.Nodup &&
  epoch.samples.length == context.catalog.length * repetitions &&
  epoch.samples.all (fun s => s.context == context && s.success && context.catalog.contains s.candidate &&
    s.repetition < repetitions) &&
  context.catalog.all (fun c => (List.range repetitions).all (fun r =>
    (epoch.samples.filter (fun s => s.candidate == c && s.repetition == r)).length == 1))

def Epoch.total (epoch : Epoch) (candidate : String) : Nat :=
  ((epoch.samples.filter (fun s => s.candidate == candidate)).map Sample.elapsedNs).sum

/-- A single evidence decision for the whole catalog. Equal repetition counts
make totals comparable; no probabilistic performance guarantee is claimed. -/
def policyScore {C : Type*} (context : Context) (repetitions : Nat)
    (identify : C → String) (fixed : C → Nat) (evidence : Option Epoch) : C → Nat :=
  match evidence with
  | some e => if e.complete context repetitions then fun c => e.total (identify c) else fixed
  | none => fixed

def admittedContext {C : Type*} (catalog : List C) (admitted : C → Prop)
    [DecidablePred admitted] (identify : C → String) (context : Context) : Context :=
  { context with catalog := (catalog.filter fun c => decide (admitted c)).map identify }

def choose {C : Type*} (catalog : List C) (admitted : C → Prop) [DecidablePred admitted]
    (identify : C → String) (context : Context) (repetitions : Nat)
    (fixed : C → Nat) (evidence : Option Epoch) : Option C :=
  select catalog admitted
    (policyScore (admittedContext catalog admitted identify context) repetitions identify fixed evidence)

theorem choose_contract {C : Type*} {catalog : List C} {admitted : C → Prop}
    [DecidablePred admitted] {identify : C → String} {context : Context} {repetitions : Nat}
    {fixed : C → Nat} {evidence : Option Epoch} {c : C} (contract : C → Prop)
    (laws : ∀ x ∈ catalog, admitted x → contract x)
    (h : choose catalog admitted identify context repetitions fixed evidence = some c) : contract c :=
  selected_contract contract laws h

theorem choose_admitted {C : Type*} {catalog : List C} {admitted : C → Prop}
    [DecidablePred admitted] {identify : C → String} {context : Context} {repetitions : Nat}
    {fixed : C → Nat} {evidence : Option Epoch} {c : C}
    (h : choose catalog admitted identify context repetitions fixed evidence = some c) :
    c ∈ catalog ∧ admitted c := (selected h).1

end Optimization.Choice
