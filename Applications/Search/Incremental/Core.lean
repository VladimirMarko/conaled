import Applications.Search.Incremental.Semantics
import Applications.Optimization.SelectionTies

/-! Literal LPA* label and worklist operations. Fuel exhaustion is explicit;
termination and the public total interface are proved separately. -/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Incremental
variable {n : Nat}

abbrev Key := Cost ×ₗ Cost

def labelKey (h : Fin n → ℚ) (g r : Labels n) (v : Fin n) : Key :=
  let low := min (g v) (r v)
  toLex (low + (h v : Cost), low)

def key (w : Graph n) (start : Fin n) (h : Fin n → ℚ) (g : Labels n) : Fin n → Key :=
  labelKey h g (rhsValue w start g)

structure State (n : Nat) where
  g : Labels n
  rhs : Labels n
  queue : List (Fin n)

def Valid (w : Graph n) (start : Fin n) (s : State n) : Prop :=
  s.rhs = rhsValue w start s.g ∧ s.queue.Nodup ∧
    (∀ v, v ∈ s.queue ↔ s.g v ≠ s.rhs v) ∧ Nonnegative s.g

def refresh (w : Graph n) (start : Fin n) (s : State n) (v : Fin n) : State n :=
  let r := rhsValue w start s.g v
  { s with
    rhs := Function.update s.rhs v r
    queue := (s.queue.filter (· != v)) ++ if s.g v = r then [] else [v] }

def refreshMany (w : Graph n) (start : Fin n) (s : State n) (vs : List (Fin n)) : State n :=
  vs.foldl (refresh w start) s

def successors (w : Graph n) (u : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun v => w u v ≠ ⊤

def predecessors (w : Graph n) (v : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun u => w u v ≠ ⊤

def initial (start : Fin n) : State n :=
  { g := fun _ => ⊤, rhs := fun v => if v = start then 0 else ⊤, queue := [start] }

def select (h : Fin n → ℚ) (s : State n) : Option (Fin n) :=
  Optimization.Thinning.argmin (labelKey h s.g s.rhs) s.queue

def topKey (h : Fin n → ℚ) (s : State n) : Key :=
  ((select h s).map (labelKey h s.g s.rhs)).getD (toLex (⊤, ⊤))

def active (goal : Fin n) (h : Fin n → ℚ) (s : State n) : Prop :=
  topKey h s < labelKey h s.g s.rhs goal ∨ s.g goal ≠ s.rhs goal

instance (goal : Fin n) (h : Fin n → ℚ) (s : State n) : Decidable (active goal h s) :=
  inferInstanceAs (Decidable (_ ∨ _))

def expand (w : Graph n) (start : Fin n) (s : State n) (u : Fin n) : State n :=
  let over := s.rhs u < s.g u
  let g' := Function.update s.g u (if over then s.rhs u else ⊤)
  let s' := { s with g := g', queue := s.queue.filter (· != u) }
  refreshMany w start s' (if over then successors w u else u :: successors w u)

inductive Outcome (n : Nat) where
  | stopped : State n → Outcome n
  | exhausted : State n → Outcome n

/-- Both goal stopping and full drain use this literal transition loop. -/
def runWith (w : Graph n) (start : Fin n) (h : Fin n → ℚ)
    (cont : State n → Prop) [DecidablePred cont] : Nat → State n → Outcome n
  | fuel, s =>
    if cont s then
      match fuel, select h s with
      | k+1, some u => runWith w start h cont k (expand w start s u)
      | _, _ => .exhausted s
    else .stopped s

/-- Check the goal stopping rule before consuming fuel. -/
def run (w : Graph n) (start goal : Fin n) (h : Fin n → ℚ) : Nat → State n → Outcome n :=
  runWith w start h (active goal h)

def drain (w : Graph n) (start : Fin n) (h : Fin n → ℚ) : Nat → State n → Outcome n :=
  runWith w start h (fun s => select h s ≠ none)

@[simp] theorem refresh_g (w : Graph n) (start : Fin n) (s : State n) (v : Fin n) :
    (refresh w start s v).g = s.g := rfl

@[simp] theorem refreshMany_g (w : Graph n) (start : Fin n) (s : State n) (vs : List (Fin n)) :
    (refreshMany w start s vs).g = s.g := by
  induction vs generalizing s with
  | nil => rfl
  | cons v vs ih => exact ih (refresh w start s v)

@[simp] theorem expand_g (w : Graph n) (start : Fin n) (s : State n) (u : Fin n) :
    (expand w start s u).g =
      Function.update s.g u (if s.rhs u < s.g u then s.rhs u else ⊤) := by
  simp [expand]

theorem select_none (h : Fin n → ℚ) (s : State n) : select h s = none ↔ s.queue = [] :=
  Optimization.Thinning.argmin_eq_none_iff _ _

theorem select_spec (h : Fin n → ℚ) (s : State n) (u : Fin n)
    (hu : select h s = some u) :
    u ∈ s.queue ∧ ∀ v ∈ s.queue, labelKey h s.g s.rhs u ≤ labelKey h s.g s.rhs v :=
  Optimization.Thinning.argmin_correct _ _ _ hu

end Search.Incremental
