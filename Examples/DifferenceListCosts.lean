import Applications.Resources.DifferenceListCosts
import Mathlib.Tactic.NormNum

/-! Connected closure-creation and application observations.

Independent expected counts: composing two singleton-prefix callbacks applies
three closures. Building three items from identity creates seven closures and
one application costs seven; construction plus two applications costs 21.
Four self-composition extensions create five closures but later application
costs 31. These are observations of the explicit model, not compiler timings.
See `docs/research/fdsa-difference-list-costs.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.DifferenceListCosts
open Resources Resources.DifferenceListCosts
universe u
variable {α : Type u}

theorem ordered_composition :
    compose (singleton 1) (singleton 2) [9] = ([1, 2, 9], 3) := by
  apply Prod.ext
  · exact compose_rep (singleton 1) (singleton 2) [1] [2]
      (singleton_rep 1) (singleton_rep 2) [9]
  · exact compose_appCost (singleton 1) (singleton 2) 1 1
      (singleton_appCost 1) (singleton_appCost 2) [9]

/-- Standard DList append supplies the same ordered observation, separately
from the callback's charged application law. -/
theorem standard_composition_value (f g : Builder α) (prefix more : List α)
    (hf : Rep f prefix) (hg : Rep g more) :
    Batteries.DList.toList
        (toDList (compose f g) (prefix ++ more)
          (compose_rep f g prefix more hf hg)) =
      Batteries.DList.toList ((toDList f prefix hf) ++ (toDList g more hg)) := by
  rw [toList_toDList, Batteries.DList.toList_append, toList_toDList, toList_toDList]

/-- Capturing supplied callbacks charges neither of their application counts. -/
theorem expensive_capture (p q : Nat) (suffix : List α) :
    let f : Builder α := fun xs => (xs, p)
    let g : Builder α := fun xs => (xs, q)
    (createCompose f g).2 = 1 ∧
      ((createCompose f g).1 suffix).2 = p + q + 1 := by
  dsimp only
  constructor
  · rfl
  · change (compose (fun xs : List α => (xs, p)) (fun xs => (xs, q)) suffix).2 = _
    rw [compose_cost]
    change q + p + 1 = p + q + 1
    omega

/-- This client includes one construction followed by one actual application. -/
def materialize (items suffix : List α) : Measured (List α) Nat :=
  bind (build items) (fun f => f suffix)

theorem materialize_eq (items suffix : List α) :
    materialize items suffix = (items ++ suffix, 4 * items.length + 2) := by
  apply Prod.ext
  · change ((build items).1 suffix).1 = items ++ suffix
    exact build_rep items suffix
  · change (build items).2 + ((build items).1 suffix).2 = 4 * items.length + 2
    rw [build_cost, build_appCost items suffix]
    omega

theorem construction_application_split (items suffix : List α) :
    (build items).2 = 2 * items.length + 1 ∧
      ((build items).1 suffix).2 = 2 * items.length + 1 :=
  ⟨build_cost items, build_appCost items suffix⟩

/-- Both applications run after one construction; their returned lists are
retained independently and no materialized result is cached. -/
def materializeTwice (items firstSuffix secondSuffix : List α) :
    Measured (List α × List α) Nat :=
  bind (build items) fun f =>
    bind (f firstSuffix) fun first =>
      bind (f secondSuffix) fun second =>
        pure (first, second)

theorem materializeTwice_eq (items firstSuffix secondSuffix : List α) :
    materializeTwice items firstSuffix secondSuffix =
      ((items ++ firstSuffix, items ++ secondSuffix), 6 * items.length + 3) := by
  apply Prod.ext
  · change (((build items).1 firstSuffix).1, ((build items).1 secondSuffix).1) = _
    exact Prod.ext (build_rep items firstSuffix) (build_rep items secondSuffix)
  · change (build items).2 +
      (((build items).1 firstSuffix).2 + (((build items).1 secondSuffix).2 + 0)) = _
    rw [build_cost, build_appCost items firstSuffix, build_appCost items secondSuffix]
    omega

theorem duplicate_values :
    materialize ([3, 1, 3] : List Nat) [9] = ([3, 1, 3, 9], 14) :=
  materialize_eq _ _

theorem duplicate_values_twice :
    materializeTwice ([3, 1, 3] : List Nat) [9] [8, 8] =
      (([3, 1, 3, 9], [3, 1, 3, 8, 8]), 21) :=
  materializeTwice_eq _ _ _

theorem empty_payload_boundary :
    materialize ([] : List Empty) [] = ([], 2) ∧
      materializeTwice ([] : List Empty) [] [] = (([], []), 3) :=
  ⟨materialize_eq _ _, materializeTwice_eq _ _ _⟩

theorem singleton_boundary (a : α) (suffix : List α) :
    materialize [a] suffix = (a :: suffix, 6) := materialize_eq _ _

/-- The supplied singleton seed already exists at this program boundary. -/
def extendSingleton (a : α) (items suffix : List α) : Measured (List α) Nat :=
  bind (buildFrom items (singleton a)) (fun f => f suffix)

theorem extendSingleton_eq (a : α) (items suffix : List α) :
    extendSingleton a items suffix = ((a :: items) ++ suffix, 4 * items.length + 1) := by
  apply Prod.ext
  · change ((buildFrom items (singleton a)).1 suffix).1 = _
    exact buildFrom_rep items (singleton a) [a] (singleton_rep a) suffix
  · change (buildFrom items (singleton a)).2 +
      ((buildFrom items (singleton a)).1 suffix).2 = _
    rw [buildFrom_cost,
      buildFrom_appCost items (singleton a) 1 (singleton_appCost a) suffix]
    omega

/-- The existing fused push supplies this value, but the chosen explicit
composition model has its own application and construction observations. -/
theorem fused_push_value (a : α) (f : Builder α) (prefix suffix : List α)
    (rep : Rep f prefix) :
    ((pushRun a f).1 suffix).1 =
      (Batteries.DList.push (toDList f prefix rep) a).apply suffix := by
  rfl

/-- Charged identity preserves values but adds two invocation occurrences. -/
theorem identity_value_cost (f : Builder α) (suffix : List α) :
    (compose f empty suffix).1 = (f suffix).1 ∧
      (compose f empty suffix).2 = (f suffix).2 + 2 := by
  constructor
  · rfl
  · rw [compose_cost]
    change 1 + (f suffix).2 + 1 = (f suffix).2 + 2
    omega

/-- A growing composition history whose represented prefix remains empty. -/
def padded : Nat → Builder α
  | 0 => empty
  | n + 1 => compose (padded n) empty

theorem padded_rep (n : Nat) : Rep (padded (α := α) n) [] := by
  induction n with
  | zero => exact empty_rep
  | succ n ih =>
      exact compose_rep (padded n) empty [] [] ih empty_rep

theorem padded_appCost (n : Nat) : AppCost (padded (α := α) n) (2 * n + 1) := by
  induction n with
  | zero => exact empty_appCost
  | succ n ih =>
      intro suffix
      have count := compose_appCost (padded n) empty (2 * n + 1) 1 ih empty_appCost suffix
      change (compose (padded n) empty suffix).2 = 2 * (n + 1) + 1
      omega

theorem padded_empty_value (n : Nat) :
    Batteries.DList.toList (toDList (padded (α := α) n) [] (padded_rep n)) = [] :=
  toList_toDList _ _ _

/-- No affine expression in the common output length controls these histories. -/
theorem no_bound_from_output_length (K B : Nat) :
    ∃ n : Nat, K * ([] : List α).length + B < (padded (α := α) n []).2 := by
  refine ⟨B + 1, ?_⟩
  have count := padded_appCost (α := α) (B + 1) []
  simp only [List.length_nil, Nat.mul_zero, Nat.zero_add]
  omega

/-- A supplied closure is captured twice by one newly created composition.
Sharing its description does not memoize either later invocation. -/
def doubled : Nat → Measured (Builder α) Nat
  | 0 => createEmpty
  | n + 1 => bind (doubled n) (fun f => createCompose f f)

theorem doubled_creation (n : Nat) : (doubled (α := α) n).2 = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (doubled (α := α) n).2 + 1 = (n + 1) + 1
      rw [ih]

theorem doubled_rep (n : Nat) : Rep (doubled (α := α) n).1 [] := by
  induction n with
  | zero => exact empty_rep
  | succ n ih =>
      exact compose_rep (doubled n).1 (doubled n).1 [] [] ih ih

theorem doubled_application_add_one (n : Nat) (suffix : List α) :
    ((doubled n).1 suffix).2 + 1 = 2 ^ (n + 1) := by
  induction n generalizing suffix with
  | zero => rfl
  | succ n ih =>
      change (compose (doubled n).1 (doubled n).1 suffix).2 + 1 =
        2 ^ ((n + 1) + 1)
      rw [compose_cost, Nat.pow_succ]
      have inner := ih suffix
      have outer := ih (((doubled n).1 suffix).1)
      omega

theorem doubled_appCost (n : Nat) :
    AppCost (doubled (α := α) n).1 (2 ^ (n + 1) - 1) := by
  intro suffix
  have count := doubled_application_add_one n suffix
  omega

def materializeDoubled (n : Nat) (suffix : List α) : Measured (List α) Nat :=
  bind (doubled n) (fun f => f suffix)

theorem materializeDoubled_eq (n : Nat) (suffix : List α) :
    materializeDoubled n suffix = (suffix, n + 2 ^ (n + 1)) := by
  apply Prod.ext
  · exact doubled_rep n suffix
  · change (doubled n).2 + ((doubled n).1 suffix).2 = _
    rw [doubled_creation]
    have applied := doubled_application_add_one n suffix
    omega

theorem four_shared_closure_extensions :
    (doubled (α := Nat) 4).2 = 5 ∧
      (doubled 4).1 [9] = ([9], 31) := by
  refine ⟨doubled_creation 4, ?_⟩
  apply Prod.ext
  · exact doubled_rep 4 [9]
  · exact doubled_appCost 4 [9]

theorem four_shared_closure_extensions_materialized :
    materializeDoubled 4 ([9] : List Nat) = ([9], 36) :=
  materializeDoubled_eq _ _

end Examples.DifferenceListCosts
