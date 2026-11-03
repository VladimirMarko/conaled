import Applications.Resources.RandomAccess.EndCases
import Applications.Resources.RandomAccess.CacheCosts
import Applications.Resources.RandomAccess.Observation

/-! Finite end-operation accounting from checkpoint 233.
Provenance, source domains and statement review:
`docs/research/adwh-random-access-end-costs.md`. -/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RandomAccessCosts
open RandomAccess Squares
universe u
variable {α : Type u}

/-- Construction executes the reversed workload; the carrier records its invariant. -/
def constructionSquare : Square ⟨List α, List α, id⟩ (measuredRepresentation α) where
  impl xs := (⟨(toRARun xs).1, by rw [toRARun_value]; exact inv_toRA xs⟩, (toRARun xs).2)
  spec := id
  commutes xs := by change fromRA (toRARun xs).1 = xs; rw [toRARun_value, fromRA_toRA]

def drainMeasured (n : Nat) (ds : Carrier α) : Measured (List α × Carrier α) Nat :=
  let result := drainRun n ds.val
  ((result.1.1, ⟨result.1.2, (drainRun_spec n ds.property).1⟩), result.2)

def drainedRepresentation (α : Type u) : Rep.{u} :=
  ⟨Measured (List α × Carrier α) Nat, List α × List α,
    fun result => (result.1.1, fromRA result.1.2.val)⟩

def measuredDrainSquare (n : Nat) :
    Square (measuredRepresentation α) (drainedRepresentation α) where
  impl result := bind result (drainMeasured n)
  spec xs := (xs.take n, xs.drop n)
  commutes result := Prod.ext (drainRun_spec n result.1.property).2.1
    (drainRun_spec n result.1.property).2.2.1

def observedDrainRepresentation (α : Type u) : Rep.{u} :=
  ⟨Measured (List α × List α) Nat, List α × List α, Prod.fst⟩

def observeDrain : Square (drainedRepresentation α) (observedDrainRepresentation α) where
  impl result := ((result.1.1, fromRA result.1.2.val), result.2)
  spec := id
  commutes _ := rfl

/-- The actual constructed state is drained before decoding either result. -/
def constructDrain (n : Nat) : Square ⟨List α, List α, id⟩ (observedDrainRepresentation α) :=
  Squares.compose observeDrain (Squares.compose (measuredDrainSquare n) constructionSquare)

theorem constructDrain_value (n : Nat) (xs : List α) :
    ((constructDrain n).impl xs).1 = (xs.take n, xs.drop n) :=
  (constructDrain n).commutes xs

theorem constructDrain_cost (n : Nat) (xs : List α) :
    ((constructDrain n).impl xs).2 = (toRARun xs).2 + (drainRun n (toRARun xs).1).2 := rfl

theorem constructDrain_full (xs : List α) :
    ((constructDrain xs.length).impl xs).1 = (xs, []) := by
  simp [constructDrain_value]

theorem constructDrain_full_bound (xs : List α) :
    ((constructDrain xs.length).impl xs).2 ≤ 5 * xs.length := by
  have hc := toRARun_linear_bound xs
  have hd := (full_drain_linear_bounds (inv_toRA xs)).2
  rw [fromRA_toRA] at hd
  rw [constructDrain_cost, toRARun_value]
  omega

def measuredPushSquare (x : α) : Square (representation α) (measuredRepresentation α) where
  impl ds := (⟨(consRARun x ds.val).1, by
    rw [consRARun_value]; exact inv_consRA x ds.property⟩, (consRARun x ds.val).2)
  spec xs := x :: xs
  commutes ds := consRARun_refinement x ds.val

/-- This shares the established invariant-bearing pop; its cost is the literal borrow cost. -/
def popMeasured (ds : Carrier α) : Measured (Option (α × Carrier α)) Nat :=
  (unconsCarrier ds, (unconsRARun ds.val).2)

theorem popMeasured_execution (ds : Carrier α) :
    ((popMeasured ds).1.map (fun p => (p.1, p.2.val)), (popMeasured ds).2) =
      unconsRARun ds.val := by
  rw [unconsRARun_exact]
  unfold popMeasured unconsCarrier
  split <;> simp_all [unconsRARun_exact]

def observedPopRepresentation (α : Type u) : Rep.{u} :=
  ⟨Measured (Option (α × List α)) Nat, Option (α × List α), Prod.fst⟩

def measuredPopSquare : Square (measuredRepresentation α) (observedPopRepresentation α) where
  impl result :=
    let popped : Measured (Option (α × Carrier α)) Nat := bind result popMeasured
    (popped.1.map (fun (p : α × Carrier α) => (p.1, fromRA p.2.val)), popped.2)
  spec := unconsList
  commutes result := (unconsSquare (α := α)).commutes result.1

def observedPushPop (x : α) := Squares.compose measuredPopSquare (measuredPushSquare x)

theorem observedPushPop_value (x : α) (ds : Carrier α) :
    ((observedPushPop x).impl ds).1 = some (x, fromRA ds.val) :=
  (observedPushPop x).commutes ds

theorem observedPushPop_cost (x : α) (ds : Carrier α) :
    ((observedPushPop x).impl ds).2 = 2 * (consRARun x ds.val).2 := by
  change (pushPopRun x ds.val).2 = _
  rw [pushPopRun_exact x ds.property]

/-- Cached is sufficient here; balance and canonical digit ranks play no role. -/
def cachedTreeRepresentation (α : Type u) : Rep.{u} :=
  ⟨{t : Tree α // Cached t}, Bracketing.Tree α, fun t => erase t.val⟩

def eraseTreeSquare : Square (cachedTreeRepresentation α)
    ⟨Bracketing.Tree α, Bracketing.Tree α, id⟩ where
  impl t := erase t.val
  spec := id
  commutes _ := rfl

/-- ULift permits a small numerical observation of trees in any value universe. -/
def measuredSizeRepresentation : Rep.{u} :=
  ⟨ULift.{u} (Measured Nat Nat), ULift.{u} Nat, fun r => ⟨r.down.1⟩⟩

def structuralSizeSquare : Square ⟨Bracketing.Tree α, Bracketing.Tree α, id⟩
    measuredSizeRepresentation where
  impl t := ⟨structuralSizeRun t⟩
  spec t := ⟨Bracketing.size t⟩
  commutes t := congrArg ULift.up (structuralSizeRun_value t)

def observedStructuralSize (α : Type u) :=
  Squares.compose (structuralSizeSquare (α := α)) eraseTreeSquare

def cachedSizeSquare : Square (cachedTreeRepresentation α) measuredSizeRepresentation where
  impl t := ⟨cachedSizeRun t.val⟩
  spec t := ⟨Bracketing.size t⟩
  commutes t := by
    change ULift.up (cachedSizeRun t.val).1 = ULift.up (Bracketing.size (erase t.val))
    rw [cachedSizeRun_exact, cached_size_erasure t.val t.property]

theorem observedSize_comparison (t : {t : Tree α // Cached t}) :
    ((observedStructuralSize α).impl t).down.1 = (cachedSizeSquare.impl t).down.1 ∧
      ((observedStructuralSize α).impl t).down.2 + 1 =
        2 * (cachedSizeSquare.impl t).down.1 ∧
      (cachedSizeSquare.impl t).down.2 = 1 := size_run_comparison t.val t.property

end Resources.RandomAccessCosts
