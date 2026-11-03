import Applications.Resources.RandomAccess.Families
import Mathlib.Algebra.Group.Nat.Defs

/-! Actual measured consumers use the accepted valid carrier and square pasting.
No decoding or cache recomputation occurs between an update and lookup.
Provenance and statement review: `docs/research/adwh-random-access-costs.md`. -/
namespace Resources.RandomAccessCosts
open RandomAccess Squares
universe u
variable {α : Type u}

def measuredRepresentation (α : Type u) : Rep.{u} :=
  ⟨Measured (Carrier α) Nat, List α, fun r => fromRA r.1.val⟩

def measuredOption (α : Type u) : Rep.{u} :=
  ⟨Measured (Option α) Nat, Option α, Prod.fst⟩

def updateMeasured (k : Nat) (x : α) (ds : Carrier α) : Measured (Carrier α) Nat :=
  let next := updateRARun k x ds.val
  (⟨next.1, by rw [updateRARun_value]; exact valid_updateRA ds.property k x⟩, next.2)

def measuredUpdateSquare (k : Nat) (x : α) :
    Square (representation α) (measuredRepresentation α) where
  impl := updateMeasured k x
  spec := fun xs => xs.set k x
  commutes ds := updateRARun_refinement ds.property k x

def measuredLookupSquare (query : Nat) :
    Square (measuredRepresentation α) (measuredOption α) where
  impl r := bind r (fun ds => fetchRARun query ds.val)
  spec := fun (xs : List α) => xs[query]?
  commutes r := fetchRARun_refinement r.1.property query

def measuredUpdateQuery (k : Nat) (x : α) (query : Nat) :=
  Squares.compose (measuredLookupSquare query) (measuredUpdateSquare k x)

theorem measuredUpdateQuery_value (k : Nat) (x : α) (query : Nat) (ds : Carrier α) :
    ((measuredUpdateQuery k x query).impl ds).1 = ((fromRA ds.val).set k x)[query]? :=
  (measuredUpdateQuery k x query).commutes ds

theorem measuredUpdateQuery_cost (k : Nat) (x : α) (query : Nat) (ds : Carrier α) :
    ((measuredUpdateQuery k x query).impl ds).2 =
      (updateRARun k x ds.val).2 + (fetchRARun query (updateRARun k x ds.val).1).2 := rfl

theorem measuredUpdateQuery_bound (k : Nat) (x : α) (query : Nat) (ds : Carrier α) :
    ((measuredUpdateQuery k x query).impl ds).2 ≤ 4 * (fromRA ds.val).length.log2 + 6 := by
  have h₁ := updateRARun_log_bound ds.property k x
  have h₂ := fetchRARun_log_bound (valid_updateRA ds.property k x) query
  have hl : (fromRA (updateRA k x ds.val)).length = (fromRA ds.val).length := by
    rw [updateRA_refinement ds.property]; simp
  rw [hl] at h₂
  rw [measuredUpdateQuery_cost, updateRARun_value]
  omega

def bulkMeasured (us : List (Nat × α)) (ds : Carrier α) : Measured (Carrier α) Nat :=
  let result := bulkRun ds.val us
  (⟨result.1, by rw [bulkRun_value]; exact bulk_valid ds.property us⟩, result.2)

def bulkSquare (us : List (Nat × α)) : Square (representation α) (measuredRepresentation α) where
  impl := bulkMeasured us
  spec := fun xs => us.foldl (fun ys p => ys.set p.1 p.2) xs
  commutes ds := by
    change fromRA (bulkRun ds.val us).1 = us.foldl (fun xs p => xs.set p.1 p.2) (fromRA ds.val)
    rw [bulkRun_value, bulk_refinement ds.property]

def measuredSequence (α : Type u) : Rep.{u} :=
  ⟨Measured (List α) Nat, List α, Prod.fst⟩

def decodeMeasured : Square (measuredRepresentation α) (measuredSequence α) where
  impl r := (fromRA r.1.val, r.2)
  spec := id
  commutes _ := rfl

/-- Decoding is a semantic observation; its traversal is not charged as an update. -/
def observedBulk (us : List (Nat × α)) := Squares.compose decodeMeasured (bulkSquare us)

theorem observedBulk_value (us : List (Nat × α)) (ds : Carrier α) :
    ((observedBulk us).impl ds).1 = us.foldl (fun xs p => xs.set p.1 p.2) (fromRA ds.val) :=
  (observedBulk us).commutes ds

theorem observedBulk_cost (us : List (Nat × α)) (ds : Carrier α) :
    ((observedBulk us).impl ds).2 = (bulkRun ds.val us).2 := rfl

theorem observedBulk_bound (us : List (Nat × α)) (ds : Carrier α) :
    ((observedBulk us).impl ds).2 ≤ us.length * (2 * (fromRA ds.val).length.log2 + 4) :=
  bulkRun_log_bound ds.property us

theorem bulkRun_append (ds : RAList α) (us vs : List (Nat × α)) :
    bulkRun ds (us ++ vs) = bind (bulkRun ds us) (fun next => bulkRun next vs) :=
  run_append bulkStep us vs ds

/-- Additive tariffs commute with execution on the same actual updated states. -/
theorem bulkRun_reweight (tariff : Nat →+ Nat) (ds : RAList α) (us : List (Nat × α)) :
    reweight tariff (bulkRun ds us) =
      run (fun p ys => reweight tariff (bulkStep p ys)) us ds :=
  reweight_run tariff bulkStep us ds

end Resources.RandomAccessCosts
