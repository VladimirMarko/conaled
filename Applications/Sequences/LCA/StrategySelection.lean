import Applications.Sequences.LCA.BackendBounds
import Applications.Sequences.LCA.SparseCatalog

set_option autoImplicit false
set_option warningAsError true

namespace Sequences.LCA.StrategySelection
open Resources.Prepared TreeReduction

inductive Strategy where
  | direct | sparse | shared
  deriving DecidableEq, Repr

def Rep (m : Nat) : Strategy → Type
  | .direct => Input m
  | .sparse => SparseCatalog.State m
  | .shared => Backend.State m

def realize (m : Nat) : (c : Strategy) → Ops (Input m) (Nat × Nat) Nat (Rep m c)
  | .direct => Catalog.direct m
  | .sparse => SparseCatalog.ops m
  | .shared => Backend.ops m

def valid (m : Nat) : (c : Strategy) → Input m → Rep m c → Prop
  | .direct => fun s r => r=s
  | .sparse => SparseCatalog.Valid
  | .shared => Backend.Valid

def budget (m : Nat) (c : Strategy) : Profile Unit where
  preparation _ := match c with
    | .direct => 0
    | .sparse => SparseCatalog.preparationWork m
    | .shared => 1024*m
  query _ := match c with | .direct => 10*m+13 | .sparse => 16 | .shared => 57
  maintenance _ := 0
  retained _ := match c with
    | .direct => 2*m
    | .sparse => SparseExecution.retainedSlots m (Nat.log 2 m)
    | .shared => 36*m
  peak _ := match c with
    | .direct => 2*m+12
    | .sparse => SparseExecution.retainedSlots m (Nat.log 2 m) + 3*m +
        8*(Nat.log 2 m+1) + 8*(m+1) + 64
    | .shared => 512*m

def profile (m : Nat) (c : Strategy) : Profile (Input m) where
  preparation _ := (budget m c).preparation ()
  query _ := (budget m c).query ()
  maintenance _ := (budget m c).maintenance ()
  retained _ := (budget m c).retained ()
  peak _ := (budget m c).peak ()

def storage (m : Nat) : (c : Strategy) → Storage (Input m) (Rep m c)
  | .direct => Catalog.directStorage m
  | .sparse => SparseCatalog.storage m
  | .shared => BackendBounds.storage m

theorem laws (m : Nat) (c : Strategy) : Laws (@Backend.spec m) (realize m c) (valid m c) := by
  cases c
  · exact Catalog.direct_laws m
  · exact SparseCatalog.laws m
  · exact Backend.laws m

theorem bounds (m : Nat) (c : Strategy) : Bounds (realize m c) (valid m c) (storage m c) (profile m c) := by
  cases c
  · exact Catalog.direct_bounds m
  · exact SparseCatalog.bounds m
  · exact BackendBounds.bounds m

def catalog : List Strategy := [.direct,.sparse,.shared]

/-- Choose minimum preparation work among the feasible certified strategies.
The minimizer is relative to this explicit three-element catalog. -/
def choose {m : Nat} (requirements : Requirements) (_input : Input m) : Option Strategy :=
  Resources.Prepared.select catalog (budget m) requirements () (fun c => (budget m c).preparation ())

theorem chosen_correct {m : Nat} {requirements : Requirements} {input : Input m} {c : Strategy}
    (h : choose requirements input = some c) (q : Nat × Nat) :
    ((realize m c).answer ((realize m c).prepare input).1 q).1 = Backend.spec input q :=
  selected_agreement (realize m) (valid m) (fun c _ => laws m c)
    (show Resources.Prepared.select catalog (profile m) requirements input
      (fun c => (profile m c).preparation input) = some c from h) q

theorem chosen_deadline {m : Nat} {requirements : Requirements} {input : Input m} {c : Strategy}
    (h : choose requirements input = some c) (q : Nat × Nat) :
    ((realize m c).answer ((realize m c).prepare input).1 q).2 ≤ requirements.deadline :=
  response_deadline (bounds m c)
    (selected (show Resources.Prepared.select catalog (profile m) requirements input
      (fun c => (profile m c).preparation input) = some c from h)).1.2
    ((laws m c).prepare input) q

-- Startup with no preparation budget selects direct scanning.
example (input : Input 17) : choose
    {startup := some 0, deadline := 183, maintenance := 0, capacity := 34, peak := 46}
    input = some .direct := by
  change Resources.Prepared.select catalog (budget _) _ () _ = _
  decide

-- For this small input the generic sparse table wins under a tight deadline.
example (input : Input 17) : choose
    {startup := none, deadline := 57, maintenance := 0, capacity := 612, peak := 8704}
    input = some .sparse := by
  change Resources.Prepared.select catalog (budget _) _ () _ = _
  decide

-- At a larger static size the ordinary sparse table exceeds the linear
-- retained budget. Shape sharing is feasible and scanning misses the deadline.
example (input : Input (2^40)) : choose
    {startup := none, deadline := 57, maintenance := 0, capacity := 36*(2^40), peak := 512*(2^40)}
    input = some .shared := by
  change Resources.Prepared.select catalog (budget _) _ () _ = _
  decide

example (input : Input 17) : choose
    {startup := none, deadline := 15, maintenance := 0, capacity := 612, peak := 8704}
    input = none := by
  change Resources.Prepared.select catalog (budget _) _ () _ = _
  decide

end Sequences.LCA.StrategySelection
