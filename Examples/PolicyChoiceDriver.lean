import Examples.PolicyChoiceClients
import Lean

/-! Bounded JSON caller for the shared policy module and actual client operations.
`run` performs correctness checks without reading a clock. `sample` is explicit
exploration; metadata declares the measurement context rather than proving it. -/
namespace Examples.PolicyChoiceDriver
open Lean Optimization.Choice
open Applications.Parallel

deriving instance ToJson, FromJson for Context
deriving instance ToJson, FromJson for Sample
deriving instance ToJson, FromJson for Epoch

structure Request where
  client : String
  mode : String := "select"
  variant : String := "nested"
  power : Nat := 4
  nodes : Nat := 17
  queries : Nat := 32
  seed : Nat := 0
  depthLimit : Option Nat := none
  startup : Option Nat := none
  deadline : Nat := 1000000
  capacity : Nat := 10000000
  peak : Nat := 10000000
  repetitions : Nat := 1
  target : String := "unspecified-host"
  evidence : Option Epoch := none
  sample : Option Sample := none
  candidate : Option String := none
  repetition : Nat := 0

def field {A : Type} [FromJson A] (json : Json) (name : String) (fallback : A) : Except String A :=
  match json.getObjVal? name with
  | .ok value => fromJson? value
  | .error _ => .ok fallback

def decodeRequest (json : Json) : Except String Request := do
  return {
    client := ← json.getObjValAs? String "client"
    mode := ← field json "mode" "select"
    variant := ← field json "variant" "nested"
    power := ← field json "power" 4
    nodes := ← field json "nodes" 17
    queries := ← field json "queries" 32
    seed := ← field json "seed" 0
    depthLimit := ← field json "depthLimit" none
    startup := ← field json "startup" none
    deadline := ← field json "deadline" 1000000
    capacity := ← field json "capacity" 10000000
    peak := ← field json "peak" 10000000
    repetitions := ← field json "repetitions" 1
    target := ← field json "target" "unspecified-host"
    evidence := ← field json "evidence" none
    sample := ← field json "sample" none
    candidate := ← field json "candidate" none
    repetition := ← field json "repetition" 0 }

structure Execution where
  outputs : List Nat
  total : Nat
  conversionNs : Nat
  preparationNs : Nat
  queryNs : Nat
  validationNs : Nat
  modeledPreparation : Nat
  modeledQueries : Nat
  deriving ToJson

def Execution.executionNs (e : Execution) := e.conversionNs + e.preparationNs + e.queryNs

/-- With timing disabled no clock is read. Runtime timings are not modeled work. -/
@[noinline] def timed {A : Type} (enabled : Bool) (action : Unit → IO A) : IO (A × Nat) := do
  if !enabled then return (← action (), 0)
  let before ← IO.monoNanosNow
  let value ← action ()
  let after ← IO.monoNanosNow
  return (value, after - before)

/-- Diagnostic cost of six empty instrumented phases. It is reported separately,
not subtracted from any candidate duration. -/
def instrumentationProbe (enabled : Bool) : IO Nat := do
  if !enabled then return 0
  let before ← IO.monoNanosNow
  for _ in [:6] do
    let _ ← timed true (fun _ => pure ())
  return (← IO.monoNanosNow) - before

structure Job where
  context : Context
  select : Option Epoch → Option String
  execute : String → Bool → IO Execution

def baseContext (r : Request) (implementation : String) : Context :=
  { implementation := implementation ++ ":Lean-" ++ Lean.versionString
    target := r.target ++ ":lean-run"
    workload := String.intercalate ":" [r.client,r.variant,toString r.power,toString r.nodes,
      toString r.queries,toString r.seed]
    site := r.client
    protocol := "phased-conversion-prepare-query-v1;rotated-order;one-warmup"
    requirements := []
    catalog := [] }

def scanInputs (size seed : Nat) : List (Multiplicative Nat) :=
  (List.range size).map fun i => Multiplicative.ofAdd ((i+seed) % 13)

def executeScan (p : ScanPlan) (seed : Nat) (clock : Bool) : IO Execution := do
  let xs := scanInputs p.shape.size seed
  let (input, conversion) ← timed clock (fun _ => pure (p.shape.load xs))
  let (answer, query) ← timed clock (fun _ => pure (p.scanner.run input))
  let (output, flattening) ← timed clock (fun _ => pure (p.shape.flatten answer.1))
  let (_, validation) ← timed clock fun _ => do
    unless (output,answer.2) == sequential 1 xs do throw (IO.userError "scan disagreement")
  return ⟨output.map Multiplicative.toAdd, answer.2.toAdd, conversion+flattening, 0,
    query, validation, 0, 0⟩

def scanJob (r : Request) (implementation : String) : Except String Job := do
  if r.power == 0 || r.power > 8 then throw "scan power must be 1 through 8"
  let (catalog, frames, size) ← if r.variant == "nested" then
      pure (PolicyChoiceClients.Scan.catalog, Examples.ScanSearch.appendLeaf, 9)
    else if r.variant == "powers" then
      pure ([ScanPlan.pair.rightPow r.power, ScanPlan.pair.leftPow r.power], [], 2^r.power)
    else throw "unknown scan variant"
  let base := baseContext r implementation
  let ctx := admittedContext catalog (PolicyChoice.admitted frames size r.depthLimit)
    PolicyChoice.identify (PolicyChoice.scope frames size r.depthLimit base)
  return {
    context := ctx
    select := fun evidence => (PolicyChoice.choose catalog frames size r.depthLimit base
      r.repetitions (fun _ => 0) evidence).map PolicyChoice.identify
    execute := fun id clock => do
      let some p := catalog.find? (fun p => PolicyChoice.identify p == id)
        | throw (IO.userError "unknown scan candidate")
      executeScan (ScanSearch.plug frames p) r.seed clock }

open Sequences.LCA in
/-- Generate actual trees, so admission of Euler inputs comes from conversion. -/
def fixtureTree (variant : String) : Nat → Tree
  | 0 => .singleton
  | k+1 => if variant == "chain" then .attach .singleton (fixtureTree variant k)
    else if variant == "star" then .attach (fixtureTree variant k) .singleton
    else if k % 2 == 0 then .attach .singleton (fixtureTree variant k)
    else .attach (fixtureTree variant k) .singleton

open Sequences.LCA in
def treeQueries (t : Tree) (count seed : Nat) : List (TreeReduction.Query t.size) :=
  (List.range count).map fun i =>
    (⟨(i+seed)%t.size, Nat.mod_lt _ (Tree.size_pos t)⟩,
     ⟨(i*7+seed+1)%t.size, Nat.mod_lt _ (Tree.size_pos t)⟩)

open Sequences.LCA in
def executeTree (t : Tree) (count seed : Nat) (c : StrategySelection.Strategy)
    (clock : Bool) : IO Execution := do
  let source : TreeReduction.Source t.size := ⟨t,rfl⟩
  let qs := treeQueries t count seed
  let (converted, conversion) ← timed clock (fun _ => pure ((TreeReduction.reduction t.size).convert source))
  let backend := StrategySelection.realize (TreeReduction.tourSize t.size) c
  let (prepared, preparation) ← timed clock (fun _ => pure (backend.prepare converted.1.2))
  let (answered, query) ← timed clock (fun _ => pure (Resources.Prepared.queries
    (Sequences.LCA.PolicyChoice.treeOps t.size c) (converted.1.1,prepared.1) qs))
  let (_, validation) ← timed clock fun _ => do
    unless answered.1 == qs.map (TreeReduction.sourceLCA source) do
      throw (IO.userError "tree disagreement")
  return ⟨answered.1, answered.1.sum, conversion, preparation, query, validation,
    converted.2 + prepared.2, answered.2⟩

open Sequences.LCA in
def treeJob (r : Request) (implementation : String) : Except String Job := do
  if r.nodes == 0 || r.nodes > 257 || r.queries > 1024 then throw "tree workload limit"
  if !(["chain","star","branching"].contains r.variant) then throw "unknown tree variant"
  let t := fixtureTree r.variant (r.nodes-1)
  let source : TreeReduction.Source t.size := ⟨t,rfl⟩
  let req : Resources.Prepared.Requirements := ⟨r.startup,r.deadline,0,r.capacity,r.peak⟩
  let base := baseContext r implementation
  let ctx := admittedContext Sequences.LCA.PolicyChoice.catalog
    (fun c => Resources.Prepared.Feasible req (Sequences.LCA.PolicyChoice.treeProfile t.size c) source)
    Sequences.LCA.PolicyChoice.identify
    (Sequences.LCA.PolicyChoice.scope t.size req {base with site := base.site ++ ":tree"})
  return {
    context := ctx
    select := fun evidence => (Sequences.LCA.PolicyChoice.chooseTree req source base r.repetitions
      (Sequences.LCA.PolicyChoice.modeledTotal (TreeReduction.tourSize t.size) r.queries) evidence).map
        Sequences.LCA.PolicyChoice.identify
    execute := fun id clock => do
      let some c := Sequences.LCA.PolicyChoice.catalog.find? (fun c => Sequences.LCA.PolicyChoice.identify c == id)
        | throw (IO.userError "unknown tree candidate")
      executeTree t r.queries r.seed c clock }

def makeJob (r : Request) (implementation : String) : Except String Job := do
  if r.repetitions == 0 || r.repetitions > 20 then throw "repetitions must be 1 through 20"
  if r.client == "scan" then scanJob r implementation
  else if r.client == "tree" then treeJob r implementation
  else throw "unknown client"

def handle (r : Request) (implementation : String) : IO Json := do
  let clock := r.mode == "sample"
  if clock && (implementation == "unrecorded" || r.target == "unspecified-host") then
    throw (IO.userError "sampling requires CONALED_CHOICE_IMPLEMENTATION and target")
  let probe ← instrumentationProbe clock
  let start ← if clock then IO.monoNanosNow else pure 0
  let (job, features) ← timed clock (fun _ => IO.ofExcept (makeJob r implementation))
  let (selected, selection) ← timed clock (fun _ => pure (job.select r.evidence))
  let used := r.evidence.any (fun e => e.complete job.context r.repetitions)
  let fields := [("status",toJson "ok"),("context",toJson job.context),
    ("chosen",toJson selected),("evidenceUsed",toJson used)]
  if r.mode == "select" then return Json.mkObj fields
  if r.mode == "record" then
    let some observation := r.sample | throw (IO.userError "record requires sample")
    let epoch := r.evidence.getD (Epoch.start job.context r.repetitions)
    let next ← IO.ofExcept (epoch.record job.context observation)
    return Json.mkObj (fields ++ [("epoch",toJson next)])
  if r.mode != "run" && r.mode != "sample" && r.mode != "explore" then throw (IO.userError "unknown mode")
  let chosen := if clock || r.mode == "explore" then r.candidate else selected
  let some id := chosen | return Json.mkObj (fields ++ [("execution",Json.null)])
  unless job.context.catalog.contains id do throw (IO.userError "candidate is not admitted")
  if clock && r.repetition >= r.repetitions then throw (IO.userError "repetition out of range")
  let execution ← job.execute id clock
  let elapsed ← if clock then do pure ((← IO.monoNanosNow) - start) else pure 0
  let observation : Sample := ⟨id,r.repetition,execution.executionNs,true,job.context⟩
  let extra := [("executed",toJson id),("execution",toJson execution),
    ("featureNs",toJson features),("selectionNs",toJson selection),
    ("endToEndNs",toJson elapsed),("instrumentationProbeNs",toJson probe),
    ("otherNs",toJson (elapsed - (features + selection + execution.executionNs + execution.validationNs)))]
  return Json.mkObj (fields ++ extra ++ if clock then [("sample",toJson observation)] else [])

/-- A bounded JSONL session keeps execution warm without retaining observations.
The caller explicitly sends evidence back when it wants to use it. -/
def drive (implementation : String) : Nat → IO UInt32
  | 0 => pure 2
  | fuel+1 => do
    let input ← (← IO.getStdin).getLine
    if input.isEmpty then return 0
    let result ← try
      let json ← IO.ofExcept (Json.parse input)
      let req ← IO.ofExcept (decodeRequest json)
      handle req implementation
    catch err => pure (Json.mkObj [("status",toJson "error"),("error",toJson err.toString)])
    let output ← IO.getStdout
    output.putStrLn result.compress
    output.flush
    drive implementation fuel

def runDriver : IO UInt32 := do
  let implementation := (← IO.getEnv "CONALED_CHOICE_IMPLEMENTATION").getD "unrecorded"
  drive implementation 4096

end Examples.PolicyChoiceDriver
