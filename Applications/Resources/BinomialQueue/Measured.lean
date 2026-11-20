import Applications.Search.BinomialQueue.Core
import Applications.Resources.Measured
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The dense source binomial queue with explicit observations

Every result is obtained from the source's actual recursive calls. The measured
comparator returns the Boolean used by those calls and its own work. Function
entries, comparisons, comparator work, cons and node expressions, and continuation
creation/application are distinct coordinates. Pairs, Options, nil trees and nil
lists are uncharged. Each named source wrapper has one entry charge. These are
syntactic prices, not statements about native allocation, stack or elapsed time.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.BinomialQueue

universe u
variable {K : Type u}

open Search.BinomialQueue
open scoped BigOperators

/-- Source entry coordinates remain separate, so `carry` entries exclude links. -/
inductive Metric where
  | emptyCalls | smashCalls | carryCalls | insertCalls | joinCalls
  | unzipCalls | heapDeleteMaxCalls | findMaxAuxCalls | findMaxCalls
  | deleteMaxAuxCalls | deleteMaxCalls | mergeCalls
  | comparisons | comparisonWork | cons | nodes | closures | applications
  deriving DecidableEq

instance instFintypeMetric : Fintype Metric where
  elems := {.emptyCalls, .smashCalls, .carryCalls, .insertCalls, .joinCalls,
    .unzipCalls, .heapDeleteMaxCalls, .findMaxAuxCalls, .findMaxCalls,
    .deleteMaxAuxCalls, .deleteMaxCalls, .mergeCalls, .comparisons,
    .comparisonWork, .cons, .nodes, .closures, .applications}
  complete metric := by cases metric <;> simp

abbrev Cost := Metric → Nat

/-- A charge at one coordinate of the ordinary pointwise additive observation. -/
def charge (metric : Metric) (amount : Nat) : Cost :=
  fun observed => if observed = metric then amount else 0

/-- One source entry together with the explicitly charged local expressions. -/
def bill (entry : Metric) (comparisons comparisonWork cons nodes closures applications : Nat) :
    Cost := charge entry 1 + charge .comparisons comparisons +
      charge .comparisonWork comparisonWork + charge .cons cons + charge .nodes nodes +
      charge .closures closures + charge .applications applications

/-- The sum of entries in all twelve named source functions. -/
def calls (work : Cost) : Nat :=
  work .emptyCalls + work .smashCalls + work .carryCalls + work .insertCalls +
    work .joinCalls + work .unzipCalls + work .heapDeleteMaxCalls +
    work .findMaxAuxCalls + work .findMaxCalls + work .deleteMaxAuxCalls +
    work .deleteMaxCalls + work .mergeCalls

/-- Arbitrary nonnegative prices for the independent observations. -/
def weighted (prices work : Cost) : Nat := ∑ metric, prices metric * work metric

/-- The common unit-comparison realization of the source Boolean parameter. -/
def unitComparator (greater : K → K → Bool) (x y : K) : Measured Bool Nat :=
  (greater x y, 1)

def emptyRun : Measured (Queue K) Cost := ([], bill .emptyCalls 0 0 0 0 0 0)

def smashRun (cmp : K → K → Measured Bool Nat) :
    BinaryTree K → BinaryTree K → Measured (BinaryTree K) Cost
  | .node x a .nil, .node y b .nil =>
      let tested := cmp x y
      (if tested.1 then .node x (.node y b a) .nil else .node y (.node x a b) .nil,
        bill .smashCalls 1 tested.2 0 2 0 0)
  | _, _ => (.nil, bill .smashCalls 0 0 0 0 0 0)

def carryRun (cmp : K → K → Measured Bool Nat) :
    Queue K → BinaryTree K → Measured (Queue K) Cost
  | [], .nil => ([], bill .carryCalls 0 0 0 0 0 0)
  | [], t => ([t], bill .carryCalls 0 0 1 0 0 0)
  | .nil :: q, t => (t :: q, bill .carryCalls 0 0 1 0 0 0)
  | t :: q, .nil => (t :: q, bill .carryCalls 0 0 1 0 0 0)
  | t :: q, c =>
      let linked := smashRun cmp c t
      let tail := carryRun cmp q linked.1
      (.nil :: tail.1, bill .carryCalls 0 0 1 0 0 0 + linked.2 + tail.2)

def insertRun (cmp : K → K → Measured Bool Nat) (key : K) (q : Queue K) :
    Measured (Queue K) Cost :=
  let result := carryRun cmp q (.node key .nil .nil)
  (result.1, bill .insertCalls 0 0 0 1 0 0 + result.2)

def joinRun (cmp : K → K → Measured Bool Nat) :
    Queue K → Queue K → BinaryTree K → Measured (Queue K) Cost
  | [], q, c =>
      let result := carryRun cmp q c
      (result.1, bill .joinCalls 0 0 0 0 0 0 + result.2)
  | p, [], c =>
      let result := carryRun cmp p c
      (result.1, bill .joinCalls 0 0 0 0 0 0 + result.2)
  | .nil :: p, .nil :: q, c =>
      let tail := joinRun cmp p q .nil
      (c :: tail.1, bill .joinCalls 0 0 1 0 0 0 + tail.2)
  | .nil :: p, q₀ :: q, .nil =>
      let tail := joinRun cmp p q .nil
      (q₀ :: tail.1, bill .joinCalls 0 0 1 0 0 0 + tail.2)
  | .nil :: p, q₀ :: q, c =>
      let linked := smashRun cmp c q₀
      let tail := joinRun cmp p q linked.1
      (.nil :: tail.1, bill .joinCalls 0 0 1 0 0 0 + linked.2 + tail.2)
  | p₀ :: p, .nil :: q, .nil =>
      let tail := joinRun cmp p q .nil
      (p₀ :: tail.1, bill .joinCalls 0 0 1 0 0 0 + tail.2)
  | p₀ :: p, .nil :: q, c =>
      let linked := smashRun cmp c p₀
      let tail := joinRun cmp p q linked.1
      (.nil :: tail.1, bill .joinCalls 0 0 1 0 0 0 + linked.2 + tail.2)
  | p₀ :: p, q₀ :: q, c =>
      let linked := smashRun cmp p₀ q₀
      let tail := joinRun cmp p q linked.1
      (c :: tail.1, bill .joinCalls 0 0 1 0 0 0 + linked.2 + tail.2)

/-- The source's closure is created before descent and applied on the return
path. The supplied continuation's own cost is retained at its actual argument. -/
def unzipRun : BinaryTree K → (Queue K → Measured (Queue K) Cost) →
    Measured (Queue K) Cost
  | .nil, cont =>
      let result := cont []
      (result.1, bill .unzipCalls 0 0 0 0 0 0 + result.2)
  | .node x a b, cont =>
      let result := unzipRun b (fun q =>
        let tail := cont q
        (.node x a .nil :: tail.1,
          charge .applications 1 + charge .cons 1 + charge .nodes 1 + tail.2))
      (result.1, bill .unzipCalls 0 0 0 0 1 0 + result.2)

/-- One application of the source identity continuation; no list traversal. -/
def identityRun (q : Queue K) : Measured (Queue K) Cost :=
  (q, charge .applications 1)

def heapDeleteMaxRun : BinaryTree K → Measured (Queue K) Cost
  | .node _ a .nil =>
      let result := unzipRun a identityRun
      (result.1, bill .heapDeleteMaxCalls 0 0 0 0 0 0 + result.2)
  | _ => ([], bill .heapDeleteMaxCalls 0 0 0 0 0 0)

def findMaxAuxRun (cmp : K → K → Measured Bool Nat) (current : K) :
    Queue K → Measured K Cost
  | [] => (current, bill .findMaxAuxCalls 0 0 0 0 0 0)
  | .nil :: q =>
      let result := findMaxAuxRun cmp current q
      (result.1, bill .findMaxAuxCalls 0 0 0 0 0 0 + result.2)
  | .node x _ _ :: q =>
      let tested := cmp x current
      let result := findMaxAuxRun cmp (if tested.1 then x else current) q
      (result.1, bill .findMaxAuxCalls 1 tested.2 0 0 0 0 + result.2)

def findMaxRun (cmp : K → K → Measured Bool Nat) : Queue K → Measured (Option K) Cost
  | [] => (none, bill .findMaxCalls 0 0 0 0 0 0)
  | .nil :: q =>
      let result := findMaxRun cmp q
      (result.1, bill .findMaxCalls 0 0 0 0 0 0 + result.2)
  | .node x _ _ :: q =>
      let result := findMaxAuxRun cmp x q
      (some result.1, bill .findMaxCalls 0 0 0 0 0 0 + result.2)

def deleteMaxAuxRun (cmp : K → K → Measured Bool Nat) (m : K) :
    Queue K → Measured (Queue K × Queue K) Cost
  | .nil :: p =>
      let result := deleteMaxAuxRun cmp m p
      ((.nil :: result.1.1, result.1.2),
        bill .deleteMaxAuxCalls 0 0 1 0 0 0 + result.2)
  | .node x a .nil :: p =>
      let tested := cmp m x
      if tested.1 then
        let result := deleteMaxAuxRun cmp m p
        ((.node x a .nil :: result.1.1, result.1.2),
          bill .deleteMaxAuxCalls 1 tested.2 1 1 0 0 + result.2)
      else
        let children := heapDeleteMaxRun (.node x a .nil)
        ((.nil :: p, children.1),
          bill .deleteMaxAuxCalls 1 tested.2 1 1 0 0 + children.2)
  | _ => (([], []), bill .deleteMaxAuxCalls 0 0 0 0 0 0)

def deleteMaxRun (cmp : K → K → Measured Bool Nat) (q : Queue K) :
    Measured (Option (K × Queue K)) Cost :=
  let found := findMaxRun cmp q
  match found.1 with
  | none => (none, bill .deleteMaxCalls 0 0 0 0 0 0 + found.2)
  | some m =>
      let removed := deleteMaxAuxRun cmp m q
      let joined := joinRun cmp removed.1.1 removed.1.2 .nil
      (some (m, joined.1),
        bill .deleteMaxCalls 0 0 0 0 0 0 + found.2 + removed.2 + joined.2)

def mergeRun (cmp : K → K → Measured Bool Nat) (p q : Queue K) :
    Measured (Queue K) Cost :=
  let result := joinRun cmp p q .nil
  (result.1, bill .mergeCalls 0 0 0 0 0 0 + result.2)

@[simp] theorem charge_apply (metric observed : Metric) (amount : Nat) :
    charge metric amount observed = if observed = metric then amount else 0 := rfl

/-- The ordinary additive projection used by shared trajectory accounting. -/
def coordinate (metric : Metric) : Cost →+ Nat where
  toFun work := work metric
  map_zero' := rfl
  map_add' _ _ := rfl

theorem weighted_add (prices left right : Cost) :
    weighted prices (left + right) = weighted prices left + weighted prices right := by
  simp [weighted, Nat.mul_add, Finset.sum_add_distrib]

theorem weighted_charge (prices : Cost) (metric : Metric) (amount : Nat) :
    weighted prices (charge metric amount) = prices metric * amount := by
  simp [weighted, charge, mul_ite]

theorem weighted_bill (prices : Cost) (entry : Metric)
    (comparisons comparisonWork cons nodes closures applications : Nat) :
    weighted prices (bill entry comparisons comparisonWork cons nodes closures applications) =
      prices entry + prices .comparisons * comparisons +
        prices .comparisonWork * comparisonWork + prices .cons * cons +
        prices .nodes * nodes + prices .closures * closures +
        prices .applications * applications := by
  simp only [bill, weighted_add, weighted_charge, Nat.mul_one]

theorem weighted_mono (prices left right : Cost) (bound : ∀ metric, left metric ≤ right metric) :
    weighted prices left ≤ weighted prices right := by
  exact Finset.sum_le_sum (fun metric _ => Nat.mul_le_mul_left _ (bound metric))

@[simp] theorem emptyRun_value : (emptyRun : Measured (Queue K) Cost).1 = empty := rfl

/-- No comparator law or shape invariant is used by erasure. -/
theorem smashRun_value (cmp : K → K → Measured Bool Nat) (t v : BinaryTree K) :
    (smashRun cmp t v).1 = smash (fun x y => (cmp x y).1) t v := by
  cases t with
  | nil => cases v <;> rfl
  | node x a b =>
      cases b <;> cases v with
      | nil => rfl
      | node y c d => cases d <;> rfl

theorem carryRun_value (cmp : K → K → Measured Bool Nat) (q : Queue K) (t : BinaryTree K) :
    (carryRun cmp q t).1 = carry (fun x y => (cmp x y).1) q t := by
  induction q generalizing t with
  | nil => cases t <;> rfl
  | cons head tail ih =>
      cases head <;> cases t <;>
        simp [carryRun, carry, ih, smashRun_value]

theorem insertRun_value (cmp : K → K → Measured Bool Nat) (key : K) (q : Queue K) :
    (insertRun cmp key q).1 = insert (fun x y => (cmp x y).1) key q :=
  carryRun_value cmp q (.node key .nil .nil)

theorem joinRun_value (cmp : K → K → Measured Bool Nat) (p q : Queue K) (c : BinaryTree K) :
    (joinRun cmp p q c).1 = join (fun x y => (cmp x y).1) p q c := by
  induction p generalizing q c with
  | nil => simp [joinRun, join, carryRun_value]
  | cons head tail ih =>
      cases q with
      | nil => simp [joinRun, join, carryRun_value]
      | cons other rest =>
          cases head <;> cases other <;> cases c <;>
            simp [joinRun, join, ih, smashRun_value]

theorem unzipRun_value (t : BinaryTree K) (cont : Queue K → Measured (Queue K) Cost) :
    (unzipRun t cont).1 = unzip t (fun q => (cont q).1) := by
  induction t generalizing cont with
  | nil => rfl
  | node x a b _ ih => simp only [unzipRun, unzip, ih]

@[simp] theorem identityRun_value (q : Queue K) : (identityRun q).1 = q := rfl

theorem heapDeleteMaxRun_value (t : BinaryTree K) :
    (heapDeleteMaxRun t).1 = heapDeleteMax t := by
  cases t with
  | nil => rfl
  | node x a b =>
      cases b with
      | nil => exact unzipRun_value a identityRun
      | node => rfl

theorem findMaxAuxRun_value (cmp : K → K → Measured Bool Nat) (current : K) (q : Queue K) :
    (findMaxAuxRun cmp current q).1 = findMaxAux (fun x y => (cmp x y).1) current q := by
  induction q generalizing current with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [findMaxAuxRun, findMaxAux, ih]

theorem findMaxRun_value (cmp : K → K → Measured Bool Nat) (q : Queue K) :
    (findMaxRun cmp q).1 = findMax (fun x y => (cmp x y).1) q := by
  induction q with
  | nil => rfl
  | cons head tail ih =>
      cases head <;> simp [findMaxRun, findMax, ih, findMaxAuxRun_value]

theorem deleteMaxAuxRun_value (cmp : K → K → Measured Bool Nat) (m : K) (q : Queue K) :
    (deleteMaxAuxRun cmp m q).1 = deleteMaxAux (fun x y => (cmp x y).1) m q := by
  induction q with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | nil => simp [deleteMaxAuxRun, deleteMaxAux, ih]
      | node x a b =>
          cases b with
          | nil =>
              cases test : (cmp m x).1 <;>
                simp [deleteMaxAuxRun, deleteMaxAux, test, ih, heapDeleteMaxRun_value]
          | node => rfl

theorem deleteMaxRun_value (cmp : K → K → Measured Bool Nat) (q : Queue K) :
    (deleteMaxRun cmp q).1 = deleteMax (fun x y => (cmp x y).1) q := by
  cases found : findMax (fun x y => (cmp x y).1) q <;>
    simp [deleteMaxRun, deleteMax, findMaxRun_value, found,
      joinRun_value, deleteMaxAuxRun_value]

theorem mergeRun_value (cmp : K → K → Measured Bool Nat) (p q : Queue K) :
    (mergeRun cmp p q).1 = merge (fun x y => (cmp x y).1) p q :=
  joinRun_value cmp p q .nil

/-- The erasure law can also be consumed against a separately named comparator. -/
theorem comparator_realizes (cmp : K → K → Measured Bool Nat) (greater : K → K → Bool)
    (realizes : ∀ x y, (cmp x y).1 = greater x y) :
    (fun x y => (cmp x y).1) = greater := by
  funext x y
  exact realizes x y

theorem insertRun_realizes (cmp : K → K → Measured Bool Nat) (greater : K → K → Bool)
    (realizes : ∀ x y, (cmp x y).1 = greater x y) (key : K) (q : Queue K) :
    (insertRun cmp key q).1 = insert greater key q := by
  rw [insertRun_value, comparator_realizes cmp greater realizes]

theorem deleteMaxRun_realizes (cmp : K → K → Measured Bool Nat) (greater : K → K → Bool)
    (realizes : ∀ x y, (cmp x y).1 = greater x y) (q : Queue K) :
    (deleteMaxRun cmp q).1 = deleteMax greater q := by
  rw [deleteMaxRun_value, comparator_realizes cmp greater realizes]

theorem mergeRun_realizes (cmp : K → K → Measured Bool Nat) (greater : K → K → Bool)
    (realizes : ∀ x y, (cmp x y).1 = greater x y) (p q : Queue K) :
    (mergeRun cmp p q).1 = merge greater p q := by
  rw [mergeRun_value, comparator_realizes cmp greater realizes]

end Resources.BinomialQueue
