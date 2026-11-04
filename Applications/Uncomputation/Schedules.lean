import Applications.Uncomputation.Oracle

/-! Logical CNOT/Toffoli schedules with explicit wire ownership. Each layer is
checked for disjoint supports. Allocation/release events count scratch lifetime;
release is justified separately by the schedule's clean-state theorem. -/
namespace Uncomputation
namespace Schedule

structure Gate (n : Nat) where
  controls : List (Fin n)
  target : Fin n
  deriving DecidableEq

def Gate.support {n} (g : Gate n) : Finset (Fin n) :=
  insert g.target g.controls.toFinset

def Gate.valid {n} (g : Gate n) : Prop :=
  (g.controls.length = 1 ∨ g.controls.length = 2) ∧
  g.controls.Nodup ∧ g.target ∉ g.controls
instance {n} (g : Gate n) : Decidable g.valid := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def Gate.run {n} (g : Gate n) (v : Fin n → Bool) : Fin n → Bool :=
  Function.update v g.target (xor (v g.target) (g.controls.all v))

def run {n} (layers : List (List (Gate n))) (v : Fin n → Bool) : Fin n → Bool :=
  layers.flatten.foldl (fun s g => g.run s) v

def valid {n} (layers : List (List (Gate n))) : Prop :=
  ∀ layer ∈ layers, (∀ g ∈ layer, g.valid) ∧
    layer.Pairwise (fun g h => Disjoint g.support h.support)
instance {n} (layers : List (List (Gate n))) : Decidable (valid layers) :=
  inferInstanceAs (Decidable (∀ layer ∈ layers, _))

def work {n} (layers : List (List (Gate n))) := layers.flatten.length
def depth {n} (layers : List (List (Gate n))) := layers.length

def t8a : Gate 8 := ⟨[0,1],6⟩
def t8b : Gate 8 := ⟨[2,3],7⟩
def c8a : Gate 8 := ⟨[6],4⟩
def c8b : Gate 8 := ⟨[7],5⟩
def parallel : List (List (Gate 8)) := [[t8a,t8b],[c8a,c8b],[t8a,t8b]]

def t7a : Gate 7 := ⟨[0,1],6⟩
def t7b : Gate 7 := ⟨[2,3],6⟩
def c7a : Gate 7 := ⟨[6],4⟩
def c7b : Gate 7 := ⟨[6],5⟩
def serial : List (List (Gate 7)) := [[t7a],[c7a],[t7a],[t7b],[c7b],[t7b]]

/-- Two outputs share the same computed AND. -/
def t5 : Gate 5 := ⟨[0,1],4⟩
def c5a : Gate 5 := ⟨[4],2⟩
def c5b : Gate 5 := ⟨[4],3⟩
def retain : List (List (Gate 5)) := [[t5],[c5a],[c5b],[t5]]
def recompute : List (List (Gate 5)) := [[t5],[c5a],[t5],[t5],[c5b],[t5]]

theorem layers_disjoint : valid parallel ∧ valid serial ∧ valid retain ∧ valid recompute := by
  decide

theorem gate_costs : (work parallel, depth parallel) = (6,3) ∧
    (work serial, depth serial) = (6,6) ∧
    (work retain, depth retain) = (4,4) ∧
    (work recompute, depth recompute) = (6,6) := by decide

theorem Gate.involutive {n} (g : Gate n) (h : g.valid) : Function.Involutive g.run := by
  intro v
  have hc : g.controls.all (g.run v) = g.controls.all v := by
    rw [List.all_eq, List.all_eq]
    congr 1
    apply propext
    apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    have hn : i ≠ g.target := by intro he; subst i; exact h.2.2 hi
    simp [Gate.run, Function.update_of_ne hn]
  funext i
  by_cases hi : i = g.target
  · subst i
    simp only [Gate.run] at hc
    simp only [Gate.run, Function.update_self, hc]
    cases v g.target <;> cases g.controls.all v <;> rfl
  · simp [Gate.run, Function.update_of_ne hi]

def Gate.perm {n} (g : Gate n) (h : g.valid) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun := g.run
  invFun := g.run
  left_inv := g.involutive h
  right_inv := g.involutive h

def gatesPerm {n} (gs : List (Gate n)) (h : ∀ g ∈ gs, g.valid) :
    (Fin n → Bool) ≃ (Fin n → Bool) :=
  match gs with
  | [] => Equiv.refl _
  | g :: rest => (g.perm (h g (by simp))).trans
      (gatesPerm rest (fun k hk => h k (by simp [hk])))

theorem gatesPerm_apply {n} (gs : List (Gate n)) (h : ∀ g ∈ gs, g.valid) (v) :
    gatesPerm gs h v = gs.foldl (fun s g => g.run s) v := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih => exact ih _ _

def parallelPerm := gatesPerm parallel.flatten (by decide)
def serialPerm := gatesPerm serial.flatten (by decide)
def retainPerm := gatesPerm retain.flatten (by decide)
def recomputePerm := gatesPerm recompute.flatten (by decide)

/-- Six caller-owned wires: four inputs and two arbitrary outputs. -/
def pairInput (v : Fin 6 → Bool) : Fin 8 → Bool :=
  fun i => if h : i.val < 6 then v ⟨i.val,h⟩ else false

def pairInputSerial (v : Fin 6 → Bool) : Fin 7 → Bool :=
  fun i => if h : i.val < 6 then v ⟨i.val,h⟩ else false

def pairOutput (v : Fin 6 → Bool) : Fin 6 → Bool :=
  fun i => if i = 4 then xor (v 4) (v 0 && v 1)
    else if i = 5 then xor (v 5) (v 2 && v 3) else v i

theorem parallel_correct : ∀ v, run parallel (pairInput v) = pairInput (pairOutput v) := by
  decide +kernel

theorem serial_correct : ∀ v, run serial (pairInputSerial v) = pairInputSerial (pairOutput v) := by
  decide +kernel

def repeatedInput (v : Fin 4 → Bool) : Fin 5 → Bool :=
  fun i => if h : i.val < 4 then v ⟨i.val,h⟩ else false

def repeatedOutput (v : Fin 4 → Bool) : Fin 4 → Bool :=
  fun i => if i = 2 then xor (v 2) (v 0 && v 1)
    else if i = 3 then xor (v 3) (v 0 && v 1) else v i

theorem retain_correct : ∀ v, run retain (repeatedInput v) = repeatedInput (repeatedOutput v) := by
  decide +kernel

theorem recompute_correct : ∀ v, run recompute (repeatedInput v) = repeatedInput (repeatedOutput v) := by
  decide +kernel

/-- Allocation and clean release are boundary events, not gates. -/
inductive Event (n : Nat) where
  | acquire : Finset (Fin n) → Event n
  | release : Finset (Fin n) → Event n
  | layer : List (Gate n) → Event n

def Event.gates {n} : Event n → List (List (Gate n))
  | .layer gs => [gs]
  | _ => []

def parallelPlan : List (Event 8) :=
  [.acquire {6,7}, .layer [t8a,t8b], .layer [c8a,c8b], .layer [t8a,t8b], .release {6,7}]
def serialPlan : List (Event 7) :=
  [.acquire {6}, .layer [t7a], .layer [c7a], .layer [t7a], .release {6},
   .acquire {6}, .layer [t7b], .layer [c7b], .layer [t7b], .release {6}]
def retainPlan : List (Event 5) :=
  [.acquire {4}, .layer [t5], .layer [c5a], .layer [c5b], .layer [t5], .release {4}]
def recomputePlan : List (Event 5) :=
  [.acquire {4}, .layer [t5], .layer [c5a], .layer [t5], .release {4},
   .acquire {4}, .layer [t5], .layer [c5b], .layer [t5], .release {4}]

theorem plans_match : parallelPlan.flatMap Event.gates = parallel ∧
    serialPlan.flatMap Event.gates = serial ∧ retainPlan.flatMap Event.gates = retain ∧
    recomputePlan.flatMap Event.gates = recompute := by decide

/-- Caller-owned wires may never be acquired or released. A scratch acquire
requires zero on entry, and release checks zero again. No event resets data. -/
def eventStep {n} (caller : Finset (Fin n)) (e : Event n)
    (s : (Fin n → Bool) × Finset (Fin n)) : Option ((Fin n → Bool) × Finset (Fin n)) :=
  match e with
  | .acquire ws => if Disjoint ws s.2 ∧ Disjoint ws caller ∧ (∀ i ∈ ws, s.1 i = false)
      then some (s.1, s.2 ∪ ws) else none
  | .release ws => if ws ⊆ s.2 ∧ Disjoint ws caller ∧ (∀ i ∈ ws, s.1 i = false)
      then some (s.1, s.2 \ ws) else none
  | .layer gs => if valid [gs] ∧ (∀ g ∈ gs, g.support ⊆ s.2)
      then some (run [gs] s.1, s.2) else none

def execute {n} (caller : Finset (Fin n)) (es : List (Event n))
    (v : Fin n → Bool) := es.foldl (fun s e => s.bind (eventStep caller e)) (some (v,caller))

def caller8 : Finset (Fin 8) := {0,1,2,3,4,5}
def caller7 : Finset (Fin 7) := {0,1,2,3,4,5}
def caller5 : Finset (Fin 5) := {0,1,2,3}

theorem parallel_ownership : ∀ v, execute caller8 parallelPlan (pairInput v) =
    some (pairInput (pairOutput v), caller8) := by decide +kernel

theorem serial_ownership : ∀ v, execute caller7 serialPlan (pairInputSerial v) =
    some (pairInputSerial (pairOutput v), caller7) := by decide +kernel

theorem retain_ownership : ∀ v, execute caller5 retainPlan (repeatedInput v) =
    some (repeatedInput (repeatedOutput v), caller5) := by decide +kernel

theorem recompute_ownership : ∀ v, execute caller5 recomputePlan (repeatedInput v) =
    some (repeatedInput (repeatedOutput v), caller5) := by decide +kernel

/-- The live scratch set is derived from the same events whose validity is
checked by `execute`. Gate layers do not alter ownership. -/
def liveAfter {n} (s : Finset (Fin n)) : Event n → Finset (Fin n)
  | .acquire ws => s ∪ ws
  | .release ws => s \ ws
  | .layer _ => s

def liveTrace {n} (es : List (Event n)) :=
  (es.scanl liveAfter ∅).map Finset.card

def peak (live : List Nat) := live.foldl max 0

theorem workspace : (peak (liveTrace parallelPlan), (liveTrace parallelPlan).getLast!) = (2,0) ∧
    (peak (liveTrace serialPlan), (liveTrace serialPlan).getLast!) = (1,0) ∧
    (peak (liveTrace retainPlan), (liveTrace retainPlan).getLast!) = (1,0) ∧
    (peak (liveTrace recomputePlan), (liveTrace recomputePlan).getLast!) = (1,0) ∧
    caller8.card + peak (liveTrace parallelPlan) = 8 ∧
    caller7.card + peak (liveTrace serialPlan) = 7 ∧
    caller5.card + peak (liveTrace retainPlan) = 5 ∧
    caller5.card + peak (liveTrace recomputePlan) = 5 := by decide

theorem gap_workspace : (liveTrace retainPlan)[3]? = some 1 ∧
    (liveTrace recomputePlan)[5]? = some 0 := by decide

theorem basis_embeddings_injective : Function.Injective pairInput ∧
    Function.Injective pairInputSerial ∧ Function.Injective repeatedInput := by
  decide +kernel

end Schedule
end Uncomputation
