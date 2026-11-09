import Applications.Sequences.LCA.StrategySelection
import Applications.Optimization.Choice.Evidence

/-! Immutable service selection before preparation. Dependent representations
stay paired with their strategy. Policy improvement applies to later sessions,
not to already prepared state. -/
namespace Sequences.LCA.PolicyChoice
open Resources Resources.Prepared TreeReduction Optimization.Choice
open StrategySelection (Strategy)

def catalog : List Strategy := [.direct, .sparse]
def identify : Strategy → String
  | .direct => "direct"
  | .sparse => "sparse"
  | .shared => "shared"

def modeledTotal (m queries : Nat) (c : Strategy) : Nat :=
  (StrategySelection.budget m c).preparation () + queries * (StrategySelection.budget m c).query ()

def scope (m : Nat) (req : Requirements) (context : Context) : Context :=
  { context with
    site := context.site ++ ":prepared-rmq"
    requirements := [m, req.deadline, req.maintenance, req.capacity, req.peak] ++ req.startup.toList }

def choose {m : Nat} (req : Requirements) (input : Input m) (context : Context)
    (repetitions : Nat) (fixed : Strategy → Nat) (evidence : Option Epoch) : Option Strategy :=
  Optimization.Choice.choose catalog
    (fun c => Feasible req (StrategySelection.profile m c) input)
    identify (scope m req context) repetitions fixed evidence

/-- The preparation result remains in the chosen dependent representation. -/
def service {m : Nat} (c : Strategy) (input : Input m) (qs : List (Nat × Nat)) : Measured (List Nat) Nat :=
  Resources.bind ((StrategySelection.realize m c).prepare input)
    (fun state => queries (StrategySelection.realize m c) state qs)

theorem service_correct {m : Nat} (c : Strategy) (input : Input m) (qs : List (Nat × Nat)) :
    (service c input qs).1 = qs.map (Backend.spec input) :=
  queries_meaning (StrategySelection.laws m c) input _ ((StrategySelection.laws m c).prepare input) qs

theorem chosen_correct {m : Nat} {req : Requirements} {input : Input m} {context : Context}
    {repetitions : Nat} {fixed : Strategy → Nat} {evidence : Option Epoch} {c : Strategy}
    (h : choose req input context repetitions fixed evidence = some c) (qs : List (Nat × Nat)) :
    (service c input qs).1 = qs.map (Backend.spec input) :=
  choose_contract (fun c => (service c input qs).1 = qs.map (Backend.spec input))
    (fun c _ _ => service_correct c input qs) h

theorem chosen_query_bound {m : Nat} {req : Requirements} {input : Input m} {context : Context}
    {repetitions : Nat} {fixed : Strategy → Nat} {evidence : Option Epoch} {c : Strategy}
    (h : choose req input context repetitions fixed evidence = some c) (q : Nat × Nat) :
    ((StrategySelection.realize m c).answer ((StrategySelection.realize m c).prepare input).1 q).2 ≤ req.deadline :=
  response_deadline (StrategySelection.bounds m c)
    (Optimization.Choice.choose_admitted h).2 ((StrategySelection.laws m c).prepare input) q

/-- A backend choice lives inside the existing Euler reduction. Conversion and
query translation execute as part of the composite, with their existing laws. -/
def treeOps (n : Nat) (c : Strategy) :=
  (reduction n).apply (StrategySelection.realize (tourSize n) c)

theorem tree_laws (n : Nat) (c : Strategy) :
    Laws sourceLCA (treeOps n c)
      ((reduction n).Valid (StrategySelection.valid (tourSize n) c)) :=
  TreeReduction.laws Backend.spec (Backend.spec_correct _) _ _ (StrategySelection.laws _ c)

def treeService {n : Nat} (c : Strategy) (source : Source n) (qs : List (Query n)) :=
  Resources.bind ((treeOps n c).prepare source) (fun state => queries (treeOps n c) state qs)

theorem treeService_correct {n : Nat} (c : Strategy) (source : Source n) (qs : List (Query n)) :
    (treeService c source qs).1 = qs.map (sourceLCA source) :=
  queries_meaning (tree_laws n c) source _ ((tree_laws n c).prepare source) qs

def treeProfile (n : Nat) (c : Strategy) : Profile (Source n) :=
  (reduction n).profile (StrategySelection.profile (tourSize n) c) (capacity n)

def chooseTree {n : Nat} (req : Requirements) (source : Source n) (context : Context)
    (repetitions : Nat) (fixed : Strategy → Nat) (evidence : Option Epoch) : Option Strategy :=
  Optimization.Choice.choose catalog (fun c => Feasible req (treeProfile n c) source)
    identify (scope n req {context with site := context.site ++ ":tree"}) repetitions fixed evidence

theorem treeChosen_correct {n : Nat} {req : Requirements} {source : Source n}
    {context : Context} {repetitions : Nat} {fixed : Strategy → Nat}
    {evidence : Option Epoch} {c : Strategy}
    (h : chooseTree req source context repetitions fixed evidence = some c) (qs : List (Query n)) :
    (treeService c source qs).1 = qs.map (sourceLCA source) :=
  choose_contract (fun c => (treeService c source qs).1 = qs.map (sourceLCA source))
    (fun c _ _ => treeService_correct c source qs) h

theorem treeChosen_query_bound {n : Nat} {req : Requirements} {source : Source n}
    {context : Context} {repetitions : Nat} {fixed : Strategy → Nat}
    {evidence : Option Epoch} {c : Strategy}
    (h : chooseTree req source context repetitions fixed evidence = some c) (q : Query n) :
    ((treeOps n c).answer ((treeOps n c).prepare source).1 q).2 ≤ req.deadline :=
  response_deadline (TreeReduction.bounds n (StrategySelection.bounds (tourSize n) c))
    (Optimization.Choice.choose_admitted h).2 ((tree_laws n c).prepare source) q

end Sequences.LCA.PolicyChoice
