import Applications.Resources.CallCount
import Applications.Resources.Workload
import Batteries.Data.DList.Lemmas

/-! Separate closure-creation and application observations for difference lists.

Creation captures already supplied callback values at a fixed unit tariff;
it does not invoke them or charge their earlier construction again. Application
charges one entry for identity, singleton and composition, using the existing
measured bind. The observation counts unfolded invocation occurrences, which
can exceed the number of creation events when callbacks are shared.

This is an explicit model, not a compiler-allocation or machine-time theorem.
The push operation uses composition with a singleton; its Batteries.DList.push
bridge preserves values, not the costs of Batteries' fused implementation.
Source scanner/control work is outside this observation. Provenance: FDSA
chapter 2, pp. 21–22; `docs/research/fdsa-reconstruction-map.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.DifferenceListCosts
universe u
variable {α : Type u}

abbrev Builder (α : Type u) := List α → Measured (List α) Nat

/-- The represented prefix is independent of the supplied suffix. -/
def Rep (f : Builder α) (prefix : List α) : Prop :=
  ∀ suffix, (f suffix).1 = prefix ++ suffix

/-- An application-cost contract covers every suffix, not only materialization at []. -/
def AppCost (f : Builder α) (k : Nat) : Prop :=
  ∀ suffix, (f suffix).2 = k

/-- Charged identity is a value identity, with one application entry. -/
def empty : Builder α := fun suffix => CallCount.tick (pure suffix)

def singleton (a : α) : Builder α := fun suffix => CallCount.tick (pure (a :: suffix))

/-- Apply g first and then f; the represented prefixes occur in f-then-g order. -/
def compose (f g : Builder α) : Builder α :=
  fun suffix => CallCount.tick (bind (g suffix) f)

@[simp] theorem empty_apply (suffix : List α) : empty suffix = (suffix, 1) := rfl

@[simp] theorem singleton_apply (a : α) (suffix : List α) :
    singleton a suffix = (a :: suffix, 1) := rfl

theorem empty_rep : Rep (empty : Builder α) [] := by
  intro suffix
  rfl

theorem empty_appCost : AppCost (empty : Builder α) 1 := by
  intro suffix
  rfl

theorem singleton_rep (a : α) : Rep (singleton a) [a] := by
  intro suffix
  rfl

theorem singleton_appCost (a : α) : AppCost (singleton a) 1 := by
  intro suffix
  rfl

theorem compose_value (f g : Builder α) (suffix : List α) :
    (compose f g suffix).1 = (f (g suffix).1).1 := by
  simp only [compose, CallCount.tick_value, bind_value]

/-- The second callback receives the actual value returned by the first. -/
theorem compose_cost (f g : Builder α) (suffix : List α) :
    (compose f g suffix).2 = (g suffix).2 + (f (g suffix).1).2 + 1 := rfl

theorem compose_rep (f g : Builder α) (prefixF prefixG : List α)
    (repF : Rep f prefixF) (repG : Rep g prefixG) :
    Rep (compose f g) (prefixF ++ prefixG) := by
  intro suffix
  simp only [compose_value, repF, repG, List.append_assoc]

theorem compose_appCost (f g : Builder α) (k l : Nat)
    (costF : AppCost f k) (costG : AppCost g l) :
    AppCost (compose f g) (k + l + 1) := by
  intro suffix
  rw [compose_cost, costG, costF]
  omega

/-- Create the empty callback without applying it. -/
def createEmpty : Measured (Builder α) Nat := CallCount.tick (pure empty)

/-- Capture one payload reference without traversing a suffix. -/
def createSingleton (a : α) : Measured (Builder α) Nat :=
  CallCount.tick (pure (singleton a))

/-- Capture two existing callback references without invoking either callback. -/
def createCompose (f g : Builder α) : Measured (Builder α) Nat :=
  CallCount.tick (pure (compose f g))

@[simp] theorem createEmpty_eq :
    (createEmpty : Measured (Builder α) Nat) = (empty, 1) := rfl

@[simp] theorem createSingleton_eq (a : α) : createSingleton a = (singleton a, 1) := rfl

@[simp] theorem createCompose_eq (f g : Builder α) :
    createCompose f g = (compose f g, 1) := rfl

/-- One singleton creation followed by one composition creation. -/
def pushRun (a : α) (f : Builder α) : Measured (Builder α) Nat :=
  bind (createSingleton a) (fun g => createCompose f g)

theorem pushRun_eq (a : α) (f : Builder α) :
    pushRun a f = (compose f (singleton a), 2) := rfl

theorem pushRun_rep (a : α) (f : Builder α) (prefix : List α) (rep : Rep f prefix) :
    Rep (pushRun a f).1 (prefix ++ [a]) := by
  simpa only [pushRun_eq] using compose_rep f (singleton a) prefix [a] rep (singleton_rep a)

theorem pushRun_appCost (a : α) (f : Builder α) (k : Nat) (cost : AppCost f k) :
    AppCost (pushRun a f).1 (k + 2) := by
  simpa only [pushRun_eq] using compose_appCost f (singleton a) k 1 cost (singleton_appCost a)

/-- Execute creation steps from an already supplied seed. Its earlier creation
and the executor's list traversal are outside this observation. -/
def buildFrom (items : List α) (f : Builder α) : Measured (Builder α) Nat :=
  run pushRun items f

@[simp] theorem buildFrom_nil (f : Builder α) : buildFrom [] f = (f, 0) := rfl

theorem buildFrom_cons (a : α) (items : List α) (f : Builder α) :
    buildFrom (a :: items) f =
      ((buildFrom items (compose f (singleton a))).1,
        2 + (buildFrom items (compose f (singleton a))).2) := by
  simp only [buildFrom, run_cons, pushRun_eq]

theorem buildFrom_cost (items : List α) (f : Builder α) :
    (buildFrom items f).2 = 2 * items.length := by
  induction items generalizing f with
  | nil => rfl
  | cons a items ih =>
      simp only [buildFrom_cons, ih, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

theorem buildFrom_rep (items : List α) (f : Builder α) (prefix : List α)
    (rep : Rep f prefix) : Rep (buildFrom items f).1 (prefix ++ items) := by
  induction items generalizing f prefix with
  | nil => simpa only [buildFrom_nil, List.append_nil] using rep
  | cons a items ih =>
      have next := compose_rep f (singleton a) prefix [a] rep (singleton_rep a)
      have rest := ih (compose f (singleton a)) (prefix ++ [a]) next
      simpa only [buildFrom_cons, List.append_assoc, List.cons_append, List.nil_append] using rest

theorem buildFrom_appCost (items : List α) (f : Builder α) (k : Nat)
    (cost : AppCost f k) : AppCost (buildFrom items f).1 (k + 2 * items.length) := by
  induction items generalizing f k with
  | nil => simpa only [buildFrom_nil, List.length_nil, Nat.mul_zero, Nat.add_zero] using cost
  | cons a items ih =>
      have next := compose_appCost f (singleton a) k 1 cost (singleton_appCost a)
      have rest := ih (compose f (singleton a)) (k + 1 + 1) next
      simpa only [buildFrom_cons, List.length_cons, Nat.mul_add, Nat.mul_one,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rest

/-- Include the initial identity's creation, then execute the same push sequence. -/
def build (items : List α) : Measured (Builder α) Nat :=
  bind createEmpty (buildFrom items)

theorem build_cost (items : List α) : (build items).2 = 2 * items.length + 1 := by
  change 1 + (buildFrom items (empty : Builder α)).2 = 2 * items.length + 1
  rw [buildFrom_cost, Nat.add_comm]

theorem build_rep (items : List α) : Rep (build items).1 items := by
  simpa only [build, createEmpty_eq, bind, List.nil_append] using
    buildFrom_rep items (empty : Builder α) [] empty_rep

theorem build_appCost (items : List α) : AppCost (build items).1 (2 * items.length + 1) := by
  simpa only [build, createEmpty_eq, bind, Nat.add_comm] using
    buildFrom_appCost items (empty : Builder α) 1 empty_appCost

/-- Erase only the observation, using the existing difference-list representation. -/
def toDList (f : Builder α) (prefix : List α) (rep : Rep f prefix) : Batteries.DList α where
  apply := fun suffix => (f suffix).1
  invariant := by
    intro suffix
    rw [rep suffix, rep [], List.append_nil]

@[simp] theorem toDList_apply (f : Builder α) (prefix : List α) (rep : Rep f prefix)
    (suffix : List α) : (toDList f prefix rep).apply suffix = (f suffix).1 := rfl

@[simp] theorem toList_toDList (f : Builder α) (prefix : List α) (rep : Rep f prefix) :
    (toDList f prefix rep).toList = prefix := by
  change (f []).1 = prefix
  simpa only [List.append_nil] using rep []

/-- The DList value forgets the closure's construction and application history. -/
theorem toDList_eq_ofList (f : Builder α) (prefix : List α) (rep : Rep f prefix) :
    toDList f prefix rep = Batteries.DList.ofList prefix := by
  simpa only [toList_toDList] using
    (Batteries.DList.ofList_toList (toDList f prefix rep)).symm

theorem toDList_compose (f g : Builder α) (prefixF prefixG : List α)
    (repF : Rep f prefixF) (repG : Rep g prefixG) :
    toDList (compose f g) (prefixF ++ prefixG) (compose_rep f g prefixF prefixG repF repG) =
      toDList f prefixF repF ++ toDList g prefixG repG := by
  calc
    toDList (compose f g) (prefixF ++ prefixG) (compose_rep f g prefixF prefixG repF repG) =
        Batteries.DList.ofList (prefixF ++ prefixG) := toDList_eq_ofList _ _ _
    _ = Batteries.DList.ofList
        ((toDList f prefixF repF ++ toDList g prefixG repG).toList) := by
      rw [Batteries.DList.toList_append, toList_toDList, toList_toDList]
    _ = toDList f prefixF repF ++ toDList g prefixG repG := Batteries.DList.ofList_toList _

/-- Correspondence with Batteries' fused push is a value theorem only. -/
theorem toDList_pushRun (a : α) (f : Builder α) (prefix : List α) (rep : Rep f prefix) :
    toDList (pushRun a f).1 (prefix ++ [a]) (pushRun_rep a f prefix rep) =
      Batteries.DList.push (toDList f prefix rep) a := by
  calc
    toDList (pushRun a f).1 (prefix ++ [a]) (pushRun_rep a f prefix rep) =
        Batteries.DList.ofList (prefix ++ [a]) := toDList_eq_ofList _ _ _
    _ = Batteries.DList.ofList ((Batteries.DList.push (toDList f prefix rep) a).toList) := by
      rw [Batteries.DList.toList_push, toList_toDList]
    _ = Batteries.DList.push (toDList f prefix rep) a := Batteries.DList.ofList_toList _

end Resources.DifferenceListCosts
