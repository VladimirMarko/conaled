import Applications.Uncomputation.Schedules

/-! Whole-client schedules: a repeated AND result surrounds an output-update
client. The client reads the first output and updates a third caller output.
High-demand mode computes a conjunction in scratch; low-demand mode copies
one bit. Allocation and logical costs use the existing schedule events. -/
namespace Uncomputation.Schedule

/-- Execute a segment with its current ownership, without resetting allocation. -/
def advance {n} (caller : Finset (Fin n)) (es : List (Event n))
    (s : (Fin n → Bool) × Finset (Fin n)) :=
  es.foldl (fun s e => s.bind (eventStep caller e)) (some s)

theorem advance_append {n} (caller : Finset (Fin n)) (xs ys : List (Event n)) (s) :
    advance caller (xs ++ ys) s = (advance caller xs s).bind (advance caller ys) := by
  simp only [advance, List.foldl_append]
  generalize xs.foldl (fun s e => s.bind (eventStep caller e)) (some s) = t
  cases t with
  | none => induction ys <;> simp_all
  | some t => rfl

/-- Segment contracts compose for any number of uses and arbitrary caller data. -/
theorem advance_repeat {n} {A : Type} (caller : Finset (Fin n)) (es : List (Event n))
    (embed : A → (Fin n → Bool) × Finset (Fin n)) (f : A → A)
    (h : ∀ a, advance caller es (embed a) = some (embed (f a))) (k : Nat) (a : A) :
    advance caller ((List.replicate k es).flatten) (embed a) =
      some (embed (f^[k] a)) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, List.flatten_cons, advance_append, h, Option.bind_some]
    rw [ih, Function.iterate_succ_apply]

theorem eventStep_value {n} (caller : Finset (Fin n)) (e : Event n) (s t)
    (h : eventStep caller e s = some t) : run e.gates s.1 = t.1 := by
  cases e <;> simp only [eventStep] at h
  all_goals split at h
  all_goals simp_all [Event.gates, run]
  all_goals cases h; rfl

theorem advance_value {n} (caller : Finset (Fin n)) (es : List (Event n)) (s t)
    (h : advance caller es s = some t) : run (es.flatMap Event.gates) s.1 = t.1 := by
  induction es generalizing s with
  | nil => simpa [advance, run] using congrArg (Option.map Prod.fst) h
  | cons e es ih =>
    rw [show e :: es = [e] ++ es from rfl, advance_append] at h
    change (eventStep caller e s).bind (advance caller es) = some t at h
    cases he : eventStep caller e s with
    | none => simp [he] at h
    | some u =>
      simp only [he, Option.bind_some] at h
      have hv := eventStep_value caller e s u he
      simpa [List.flatMap_cons, run, List.flatten_append, List.foldl_append, ← hv] using ih u h

namespace Client

def caller : Finset (Fin 8) := {0,1,2,3,4,5}
def input (v : Fin 6 → Bool) : Fin 8 → Bool := pairInput v

def compute : Gate 8 := ⟨[0,1],6⟩
def firstUse : Gate 8 := ⟨[6],2⟩
def lastUse : Gate 8 := ⟨[6],3⟩
def gapCompute (s : Fin 8) : Gate 8 := ⟨[2,0],s⟩
def gapUse (s : Fin 8) : Gate 8 := ⟨[s,1],4⟩
def lowUse : Gate 8 := ⟨[2],4⟩

def gap (high : Bool) (s : Fin 8) : List (Event 8) :=
  if high then [.acquire {s}, .layer [gapCompute s], .layer [gapUse s],
    .layer [gapCompute s], .release {s}] else [.layer [lowUse]]

def before (retain : Bool) : List (Event 8) :=
  [.acquire {6}, .layer [compute], .layer [firstUse]] ++
    if retain then [] else [.layer [compute], .release {6}]

def after (retain : Bool) : List (Event 8) :=
  (if retain then [] else [.acquire {6}, .layer [compute]]) ++
    [.layer [lastUse], .layer [compute], .release {6}]

def plan (retain high : Bool) (k : Nat) : List (Event 8) :=
  before retain ++ (List.replicate k (gap high (if retain then 7 else 6))).flatten ++ after retain

/-- Independent caller meaning. Outputs are arbitrary on entry. -/
def first (v : Fin 6 → Bool) := Function.update v 2 (xor (v 2) (v 0 && v 1))
def middle (high : Bool) (v : Fin 6 → Bool) :=
  Function.update v 4 (xor (v 4) (if high then (v 2 && v 0) && v 1 else v 2))
def last (v : Fin 6 → Bool) := Function.update v 3 (xor (v 3) (v 0 && v 1))
def output (high : Bool) (k : Nat) (v : Fin 6 → Bool) := last ((middle high)^[k] (first v))

def boundary (retain : Bool) (v : Fin 6 → Bool) : (Fin 8 → Bool) × Finset (Fin 8) :=
  (if retain then Function.update (input v) 6 (v 0 && v 1) else input v,
   if retain then caller ∪ {6} else caller)

theorem before_correct : ∀ retain v,
    advance caller (before retain) (input v, caller) = some (boundary retain (first v)) := by
  decide +kernel

theorem gap_correct : ∀ retain high v,
    advance caller (gap high (if retain then 7 else 6)) (boundary retain v) =
      some (boundary retain (middle high v)) := by
  decide +kernel

theorem after_correct : ∀ retain v,
    advance caller (after retain) (boundary retain v) = some (input (last v), caller) := by
  decide +kernel

/-- The same client family admits either schedule; scratch is clean and released. -/
theorem correct (retain high : Bool) (k : Nat) (v : Fin 6 → Bool) :
    execute caller (plan retain high k) (input v) = some (input (output high k v), caller) := by
  change advance caller (plan retain high k) (input v, caller) = _
  simp only [plan, advance_append, before_correct, Option.bind_some]
  rw [advance_repeat caller _ (boundary retain) (middle high) (gap_correct retain high)]
  simp only [Option.bind_some, after_correct, output]

def costs (es : List (Event 8)) : Nat × Nat × Nat × Nat :=
  (work (es.flatMap Event.gates), depth (es.flatMap Event.gates),
    peak (liveTrace es), (liveTrace es).getLast!)

theorem repeat_work {n} (es : List (Event n)) (k : Nat) :
    work (((List.replicate k es).flatten).flatMap Event.gates) =
      k * work (es.flatMap Event.gates) := by
  induction k with
  | zero => simp [work]
  | succ k ih =>
    simp only [List.replicate_succ, List.flatten_cons, List.flatMap_append, work,
      List.flatten_append, List.length_append] at *
    rw [ih]
    simp [Nat.succ_mul, Nat.add_comm]

theorem repeat_depth {n} (es : List (Event n)) (k : Nat) :
    depth (((List.replicate k es).flatten).flatMap Event.gates) =
      k * depth (es.flatMap Event.gates) := by
  induction k with
  | zero => simp [depth]
  | succ k ih =>
    simp only [List.replicate_succ, List.flatten_cons, List.flatMap_append, depth,
      List.length_append] at *
    rw [ih]
    simp [Nat.succ_mul, Nat.add_comm]

/-- Releasing and recomputing adds two gates and layers, independently of how
many client steps occupy the gap. -/
theorem work_depth (retain high : Bool) (k : Nat) :
    work ((plan retain high k).flatMap Event.gates) =
      (if retain then 4 else 6) + k * (if high then 3 else 1) ∧
    depth ((plan retain high k).flatMap Event.gates) =
      (if retain then 4 else 6) + k * (if high then 3 else 1) := by
  have hw : ∀ (xs ys : List (Event 8)), work ((xs ++ ys).flatMap Event.gates) =
      work (xs.flatMap Event.gates) + work (ys.flatMap Event.gates) := by
    intros; simp [work]
  have hd : ∀ (xs ys : List (Event 8)), depth ((xs ++ ys).flatMap Event.gates) =
      depth (xs.flatMap Event.gates) + depth (ys.flatMap Event.gates) := by
    intros; simp [depth]
  simp only [plan, hw, hd, repeat_work, repeat_depth]
  cases retain <;> cases high <;>
    simp [before, after, gap, Event.gates, work, depth] <;> omega

theorem low_costs : costs (plan true false 1) = (5,5,1,0) ∧
    costs (plan false false 1) = (7,7,1,0) := by decide

theorem high_costs : costs (plan true true 1) = (7,7,2,0) ∧
    costs (plan false true 1) = (9,9,1,0) := by decide

/-- The gap cannot acquire the still-retained wire, even when its value is zero. -/
theorem retained_wire_not_available :
    advance caller (gap true 6) (boundary true (fun _ => false)) = none := by decide

theorem run_correct (retain high : Bool) (k : Nat) (v : Fin 6 → Bool) :
    run ((plan retain high k).flatMap Event.gates) (input v) = input (output high k v) :=
  advance_value caller _ _ _ (correct retain high k v)

theorem gates_valid (retain high : Bool) (k : Nat) :
    ∀ g ∈ ((plan retain high k).flatMap Event.gates).flatten, g.valid := by
  have hl : ∀ e ∈ plan retain high k, ∀ l ∈ e.gates, ∀ g ∈ l, g.valid := by
    cases retain <;> cases high <;>
      intro e he <;>
      simp [plan, before, after, gap, List.mem_flatten, List.mem_replicate] at he <;>
      rcases he with h | h | h | h <;>
      simp_all [Event.gates, compute, firstUse, lastUse, lowUse, gapCompute, gapUse,
        Gate.valid] <;> aesop
  intro g hg
  obtain ⟨l, hl', hg⟩ := List.mem_flatten.mp hg
  obtain ⟨e, he, hl'⟩ := List.mem_flatMap.mp hl'
  exact hl e he l hl' g hg

def perm (retain high : Bool) (k : Nat) :=
  gatesPerm ((plan retain high k).flatMap Event.gates).flatten (gates_valid retain high k)

def firstPerm : (Fin 6 → Bool) ≃ (Fin 6 → Bool) where
  toFun := first
  invFun := first
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def middlePerm (high : Bool) : (Fin 6 → Bool) ≃ (Fin 6 → Bool) where
  toFun := middle high
  invFun := middle high
  left_inv := by cases high <;> decide +kernel
  right_inv := by cases high <;> decide +kernel

def lastPerm : (Fin 6 → Bool) ≃ (Fin 6 → Bool) where
  toFun := last
  invFun := last
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def outputPerm (high : Bool) (k : Nat) :=
  (firstPerm.trans ((middlePerm high) ^ k)).trans lastPerm

theorem outputPerm_apply (high : Bool) (k : Nat) (v) :
    outputPerm high k v = output high k v := by
  simp [outputPerm, output, firstPerm, lastPerm, Equiv.Perm.coe_pow, middlePerm]

/-- Whole-client coherence with an arbitrary untouched reference, including
amplitudes which do not factor into a client and reference tensor. -/
theorem coherent_reference {R : Type} [Fintype R] [DecidableEq R]
    (retain high : Bool) (k : Nat) (v : (Fin 6 → Bool) × R → ℂ) :
    coherent (Equiv.prodCongr (perm retain high k) (Equiv.refl R))
      (embedState (fun p => (input p.1, p.2)) v) =
    embedState (fun p => (input p.1, p.2))
      (coherent (Equiv.prodCongr (outputPerm high k) (Equiv.refl R)) v) := by
  apply coherent_embed
  intro p
  change (perm retain high k (input p.1), p.2) = (input (outputPerm high k p.1), p.2)
  congr 1
  simpa [perm, gatesPerm_apply, run, outputPerm_apply] using run_correct retain high k p.1

end Client
end Uncomputation.Schedule
