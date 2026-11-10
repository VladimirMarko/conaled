import SquareKit.PartialSpine.Limits

/-!
# Seed-inclusive scans of finite and semantic spine observations

A known input constructor exposes the current accumulator. Unknown input is
strictly unknown; a known nil exposes the final accumulator and a completed end.
The independent finite contract uses ordinary `List.scanl`, and the infinite
contract uses ordinary folds of `Stream'.take` prefixes. Labels need no order.
-/

set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.PartialSpine

universe u v
variable {α : Type u} {β : Type v}

/-- Input-strict scan: one seed is exposed for each known input constructor. -/
def scanl (f : β → α → β) (e : β) : PartialSpine α → PartialSpine β
  | .bottom => .bottom
  | .nil => .cons e .nil
  | .cons a s => .cons e (scanl f (f e a) s)

/-- Completed input retains all n+1 ordinary scan values; an open prefix has
only n observable values because its final constructor is still unknown. -/
theorem view_scanl (f : β → α → β) (e : β) (s : PartialSpine α) :
    view (scanl f e s) =
      (if (view s).2 then (view s).1.scanl f e else ((view s).1.scanl f e).dropLast,
        (view s).2) := by
  induction s generalizing e with
  | bottom => rfl
  | nil => rfl
  | cons a s ih =>
    simp only [scanl, view, ih, List.scanl_cons]
    cases (view s).2 <;>
      simp [List.dropLast_cons_of_ne_nil List.scanl_ne_nil]

theorem scanl_monotone (f : β → α → β) (e : β) : Monotone (scanl f e) := by
  intro s t h
  induction h generalizing e with
  | bottom => exact bot_le
  | nil => exact le_rfl
  | cons a _ ih => exact Below.cons e (ih (f e a))

theorem scanl_ofList (f : β → α → β) (e : β) (xs : List α) :
    scanl f e (ofList xs) = ofList (xs.scanl f e) := by
  apply view_injective
  simp [view_scanl]

theorem scanl_openPrefix (f : β → α → β) (e : β) (xs : List α) :
    scanl f e (openPrefix xs) = openPrefix ((xs.scanl f e).dropLast) := by
  apply view_injective
  simp [view_scanl]

/-- The n-th state is specified independently by the first n standard input values. -/
def scanStates (f : β → α → β) (e : β) (σ : Stream' α) : Stream' β :=
  fun n => (σ.take n).foldl f e

@[simp] theorem scanStates_zero (f : β → α → β) (e : β) (σ : Stream' α) :
    scanStates f e σ 0 = e := rfl

theorem scanStates_succ (f : β → α → β) (e : β) (σ : Stream' α) (n : Nat) :
    scanStates f e σ (n + 1) = f (scanStates f e σ n) (σ n) := by
  change (σ.take (n + 1)).foldl f e = f ((σ.take n).foldl f e) (σ n)
  rw [Stream'.take_succ', List.foldl_append]
  rfl

/-- The shifted recurrence is derived from standard prefix folding. -/
theorem scanStates_shift (f : β → α → β) (e : β) (σ : Stream' α) (n : Nat) :
    scanStates f e σ (n + 1) =
      scanStates f (f e (σ 0)) (fun k => σ (k + 1)) n := by
  change (σ 0 :: Stream'.take n (fun k => σ (k + 1))).foldl f e =
    (Stream'.take n (fun k => σ (k + 1))).foldl f (f e (σ 0))
  rw [List.foldl_cons]

theorem scanStates_take (f : β → α → β) (e : β) (σ : Stream' α) (n : Nat) :
    (scanStates f e σ).take (n + 1) = (σ.take n).scanl f e := by
  induction n generalizing e σ with
  | zero => rfl
  | succ n ih =>
    change e :: Stream'.take (n + 1) (fun k => scanStates f e σ (k + 1)) =
      (σ 0 :: Stream'.take n (fun k => σ (k + 1))).scanl f e
    rw [List.scanl_cons]
    have shifted : (fun k => scanStates f e σ (k + 1)) =
        scanStates f (f e (σ 0)) (fun k => σ (k + 1)) :=
      funext (scanStates_shift f e σ)
    rw [shifted]
    exact congrArg (List.cons e) (ih (f e (σ 0)) (fun k => σ (k + 1)))

theorem scanStates_take_dropLast (f : β → α → β) (e : β) (σ : Stream' α) (n : Nat) :
    ((σ.take n).scanl f e).dropLast = (scanStates f e σ).take n := by
  rw [← scanStates_take f e σ n, Stream'.dropLast_take, Nat.add_one_sub_one]

/-- A finite open input prefix and its scan expose equally many labels. -/
theorem scanl_streamPrefix (f : β → α → β) (e : β) (σ : Stream' α) (n : Nat) :
    scanl f e (openPrefix (σ.take n)) = openPrefix ((scanStates f e σ).take n) := by
  rw [scanl_openPrefix, scanStates_take_dropLast]

namespace Observations

open Order
noncomputable section

private theorem principalScan_monotone (f : β → α → β) (e : β) :
    Monotone (fun s => Ideal.principal (PartialSpine.scanl f e s)) :=
  IdealCompletion.principal_monotone.comp (PartialSpine.scanl_monotone f e)

/-- Extend the finite scan through the existing coherent observation CPO. -/
def scanl (f : β → α → β) (e : β) (I : Observations α) : Observations β :=
  IdealCompletion.extend (fun s => Ideal.principal (PartialSpine.scanl f e s)) I

theorem scanl_continuous (f : β → α → β) (e : β) : ScottContinuous (scanl f e) :=
  IdealCompletion.extend_scottContinuous (principalScan_monotone f e)

theorem mem_scanl (f : β → α → β) (e : β) (I : Observations α) (q : PartialSpine β) :
    q ∈ scanl f e I ↔ ∃ s ∈ I, q ≤ PartialSpine.scanl f e s :=
  mem_extend_principal (PartialSpine.scanl f e) (PartialSpine.scanl_monotone f e) I q

theorem scanl_principal (f : β → α → β) (e : β) (s : PartialSpine α) :
    scanl f e (Ideal.principal s) = Ideal.principal (PartialSpine.scanl f e s) :=
  IdealCompletion.extend_principal (principalScan_monotone f e) s

@[simp] theorem scanl_bottom (f : β → α → β) (e : β) : scanl f e ⊥ = ⊥ :=
  scanl_principal f e .bottom

@[simp] theorem scanl_nil (f : β → α → β) (e : β) :
    scanl f e (Ideal.principal .nil) = cons e (Ideal.principal .nil) := by
  rw [scanl_principal, cons_principal]
  rfl

theorem scanl_cons (f : β → α → β) (e : β) (a : α) (I : Observations α) :
    scanl f e (cons a I) = cons e (scanl f (f e a) I) := by
  apply IdealCompletion.continuous_ext
    ((cons_continuous a).comp (scanl_continuous f e))
    ((scanl_continuous f (f e a)).comp (cons_continuous e)) (I := I)
  intro s
  change scanl f e (cons a (Ideal.principal s)) =
    cons e (scanl f (f e a) (Ideal.principal s))
  rw [cons_principal, scanl_principal, scanl_principal, cons_principal]
  rfl

theorem scanl_ofList (f : β → α → β) (e : β) (xs : List α) :
    scanl f e (Ideal.principal (ofList xs)) = Ideal.principal (ofList (xs.scanl f e)) := by
  rw [scanl_principal, PartialSpine.scanl_ofList]

theorem scanl_stream (f : β → α → β) (e : β) (σ : Stream' α) :
    scanl f e (stream σ) = stream (scanStates f e σ) := by
  apply Ideal.ext
  apply Set.ext
  intro q
  change q ∈ scanl f e (stream σ) ↔ q ∈ stream (scanStates f e σ)
  rw [mem_scanl]
  constructor
  · rintro ⟨s, ⟨n, hs⟩, hq⟩
    refine ⟨n, ?_⟩
    calc
      q ≤ PartialSpine.scanl f e s := hq
      _ ≤ PartialSpine.scanl f e (openPrefix (σ.take n)) :=
        PartialSpine.scanl_monotone f e hs
      _ = openPrefix ((scanStates f e σ).take n) := scanl_streamPrefix f e σ n
  · rintro ⟨n, hq⟩
    refine ⟨openPrefix (σ.take n), stream_observes_prefix σ n, ?_⟩
    rw [scanl_streamPrefix]
    exact hq

theorem scanl_stream_prefix (f : β → α → β) (e : β) (σ : Stream' α) (n : Nat) :
    openPrefix ((scanStates f e σ).take n) ∈ scanl f e (stream σ) := by
  rw [scanl_stream]
  exact stream_observes_prefix _ n

end
end Observations
end SquareKit.PartialSpine
