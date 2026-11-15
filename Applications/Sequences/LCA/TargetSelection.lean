import Applications.Sequences.LCA.TargetBackend
import Applications.Sequences.LCA.StrategySelection

/-! The phase comparison includes the installed backend's actual preparation
and allocated-bank costs. Direct and sparse candidates reuse their existing
certified operations. Selection remains relative to this finite catalog. -/
namespace Sequences.LCA.TargetSelection
open Resources.Prepared TreeReduction
open StrategySelection (Strategy)
variable {m width : Nat}

def Rep (m width : Nat) : Strategy → Type
  | .direct => Input m
  | .sparse => SparseCatalog.State m
  | .shared => TargetBackend.State m width

def realize (hw : TargetBackend.Config m width) : (c : Strategy) →
    Ops (Input m) (Nat × Nat) Nat (Rep m width c)
  | .direct => Catalog.direct m
  | .sparse => SparseCatalog.ops m
  | .shared => TargetBackend.ops hw

def valid (hw : TargetBackend.Config m width) : (c : Strategy) → Input m → Rep m width c → Prop
  | .direct => fun s r => r=s
  | .sparse => SparseCatalog.Valid
  | .shared => TargetBackend.Valid hw

def budget (m : Nat) (c : Strategy) : Profile Unit :=
  match c with
  | .shared =>
    {preparation := fun _ => 32768*m, query := fun _ => 57, maintenance := fun _ => 0,
      retained := fun _ => 512*m, peak := fun _ => 2048*m}
  | c => StrategySelection.budget m c

def profile (m : Nat) (c : Strategy) : Profile (Input m) where
  preparation _ := (budget m c).preparation ()
  query _ := (budget m c).query ()
  maintenance _ := (budget m c).maintenance ()
  retained _ := (budget m c).retained ()
  peak _ := (budget m c).peak ()

def storage (hw : TargetBackend.Config m width) : (c : Strategy) → Storage (Input m) (Rep m width c)
  | .direct => Catalog.directStorage m
  | .sparse => SparseCatalog.storage m
  | .shared => TargetBackend.storage hw

theorem laws (hw : TargetBackend.Config m width) (c : Strategy) :
    Laws (@Backend.spec m) (realize hw c) (valid hw c) := by
  cases c
  · exact Catalog.direct_laws m
  · exact SparseCatalog.laws m
  · exact TargetBackend.laws hw

theorem bounds (hw : TargetBackend.Config m width) (c : Strategy) :
    Bounds (realize hw c) (valid hw c) (storage hw c) (profile m c) := by
  cases c
  · exact Catalog.direct_bounds m
  · exact SparseCatalog.bounds m
  · exact TargetBackend.bounds hw

def choose (_hw : TargetBackend.Config m width) (requirements : Requirements) (_input : Input m) : Option Strategy :=
  Resources.Prepared.select StrategySelection.catalog (budget m) requirements ()
    (fun c => (budget m c).preparation ())

theorem chosen_correct (hw : TargetBackend.Config m width)
    {requirements : Requirements} {input : Input m} {c : Strategy}
    (h : choose hw requirements input = some c) (q : Nat × Nat) :
    ((realize hw c).answer ((realize hw c).prepare input).1 q).1 = Backend.spec input q :=
  selected_agreement (realize hw) (valid hw) (fun c _ => laws hw c)
    (show Resources.Prepared.select StrategySelection.catalog (profile m) requirements input
      (fun c => (profile m c).preparation input) = some c from h) q

theorem chosen_deadline (hw : TargetBackend.Config m width)
    {requirements : Requirements} {input : Input m} {c : Strategy}
    (h : choose hw requirements input = some c) (q : Nat × Nat) :
    ((realize hw c).answer ((realize hw c).prepare input).1 q).2 ≤ requirements.deadline :=
  response_deadline (bounds hw c)
    (selected (show Resources.Prepared.select StrategySelection.catalog (profile m) requirements input
      (fun c => (profile m c).preparation input) = some c from h)).1.2
    ((laws hw c).prepare input) q

example (hw : TargetBackend.Config 17 width) (input : Input 17) : choose hw
    {startup := some 0, deadline := 183, maintenance := 0, capacity := 34, peak := 46}
    input = some .direct := by
  change Resources.Prepared.select StrategySelection.catalog (budget _) _ () _ = _
  decide

example (hw : TargetBackend.Config 17 width) (input : Input 17) : choose hw
    {startup := none, deadline := 57, maintenance := 0, capacity := 612, peak := 8704}
    input = some .sparse := by
  change Resources.Prepared.select StrategySelection.catalog (budget _) _ () _ = _
  decide

-- The installed implementation deliberately reserves a large output bank.
-- Its conservative constant requires a much larger size before ordinary
-- sparse storage exceeds the shared candidate's certified linear budget.
set_option maxRecDepth 4096 in
example (hw : TargetBackend.Config (2^512) width) (input : Input (2^512)) : choose hw
    {startup := none, deadline := 57, maintenance := 0,
      capacity := 512*(2^512), peak := 2048*(2^512)} input = some .shared := by
  change Resources.Prepared.select StrategySelection.catalog (budget _) _ () _ = _
  decide

example (hw : TargetBackend.Config 17 width) (input : Input 17) : choose hw
    {startup := none, deadline := 15, maintenance := 0, capacity := 612, peak := 8704}
    input = none := by
  change Resources.Prepared.select StrategySelection.catalog (budget _) _ () _ = _
  decide

end Sequences.LCA.TargetSelection
