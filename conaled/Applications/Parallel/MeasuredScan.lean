import Applications.Parallel.ScanPlan
import Mathlib.Data.Finset.Card

/-!
# Shared monoid circuits for scan recipes

A wire names an expression node structurally. Equal nodes are shared, including
across output ports. The circuit retains precisely the binary nodes reachable
from its outputs; dead nodes are absent. Identity and input nodes, copying and
wiring are free. Each retained binary node costs one and has unit delay.
This is a circuit model, not a claim about the allocation of the Lean evaluator.
-/
namespace Applications.Parallel
universe u

namespace Shape

theorem map_zipWith (s : Shape) (h : C → D) (f : A → B → C)
    (x : s.Data A) (y : s.Data B) :
    s.map h (s.zipWith f x y) = s.zipWith (fun a b => h (f a b)) x y := by
  induction s with
  | empty => rfl
  | leaf => rfl
  | prod s t ih it => simp [map, zipWith, ih, it]

theorem zipWith_maps (s : Shape) (f : C → D → E) (g : A → C) (h : B → D)
    (x : s.Data A) (y : s.Data B) :
    s.zipWith f (s.map g x) (s.map h y) =
      s.zipWith (fun a b => f (g a) (h b)) x y := by
  induction s with
  | empty => rfl
  | leaf => rfl
  | prod s t ih it => simp [map, zipWith, ih, it]

theorem zipWith_map_right (s : Shape) (f : A → C → D) (g : B → C)
    (x : s.Data A) (y : s.Data B) :
    s.zipWith f x (s.map g y) = s.zipWith (fun a b => f a (g b)) x y := by
  induction s with
  | empty => rfl
  | leaf => rfl
  | prod s t ih it => simp [map, zipWith, ih, it]

theorem zipWith_map_left (s : Shape) (f : C → B → D) (g : A → C)
    (x : s.Data A) (y : s.Data B) :
    s.zipWith f (s.map g x) y = s.zipWith (fun a b => f (g a) b) x y := by
  induction s with
  | empty => rfl
  | leaf => rfl
  | prod s t ih it => simp [map, zipWith, ih, it]

theorem map_join (s t : Shape) (f : A → B) (x : s.Data (t.Data A)) :
    (s.subst t).map f (s.join t x) = s.join t (s.map (t.map f) x) := by
  induction s with
  | empty => rfl
  | leaf => rfl
  | prod s u ih iu => simp [map, join, subst, ih, iu]

theorem split_map (s t : Shape) (f : A → B) (x : (s.subst t).Data A) :
    s.split t ((s.subst t).map f x) = s.map (t.map f) (s.split t x) := by
  induction s with
  | empty => rfl
  | leaf => rfl
  | prod s u ih iu => simp [map, split, subst, ih, iu]

/-- Ordered input identifiers, starting at an arbitrary offset. -/
def inputs (s : Shape) (offset : Nat := 0) : s.Data Nat :=
  match s with
  | .empty => PUnit.unit
  | .leaf => offset
  | .prod s t => (s.inputs offset, t.inputs (offset + s.size))

@[simp] theorem flatten_inputs (s : Shape) (offset : Nat) :
    s.flatten (s.inputs offset) = List.range' offset s.size := by
  induction s generalizing offset with
  | empty => rfl
  | leaf => rfl
  | prod s t ih it => simp [inputs, flatten, size, ih, it]

end Shape

namespace ScanPlan

/-- Operations-only interpretation; no associativity is imposed on the target. -/
def runWith (e : A) (op : A → A → A) : (p : ScanPlan) → p.shape.Data A → p.shape.Data A × A
  | .empty, _ => (PUnit.unit, e)
  | .leaf, x => (e, x)
  | .prod p q, x =>
    let l := p.runWith e op x.1
    let r := q.runWith e op x.2
    ((l.1, q.shape.map (op l.2) r.1), op l.2 r.2)
  | .comp p q, x =>
    let locals := p.shape.map (q.runWith e op) (p.shape.split q.shape x)
    let totals := p.runWith e op (p.shape.map Prod.snd locals)
    (p.shape.join q.shape (p.shape.zipWith
      (fun t ys => q.shape.map (op t) ys) totals.1 (p.shape.map Prod.fst locals)), totals.2)

@[simp] theorem runWith_product (e : A) (op : A → A → A) (p q : ScanPlan)
    (x : p.shape.Data A) (y : q.shape.Data A) :
    (ScanPlan.prod p q).runWith e op (x, y) =
      (((p.runWith e op x).1, q.shape.map (op (p.runWith e op x).2) (q.runWith e op y).1),
       op (p.runWith e op x).2 (q.runWith e op y).2) := rfl

@[simp] theorem runWith_composition (e : A) (op : A → A → A) (p q : ScanPlan)
    (x : (p.shape.subst q.shape).Data A) :
    (ScanPlan.comp p q).runWith e op x =
      let locals := p.shape.map (q.runWith e op) (p.shape.split q.shape x)
      let totals := p.runWith e op (p.shape.map Prod.snd locals)
      (p.shape.join q.shape (p.shape.zipWith (fun t ys => q.shape.map (op t) ys)
        totals.1 (p.shape.map Prod.fst locals)), totals.2) := rfl

theorem runWith_scanner {M : Type u} [Monoid M] (p : ScanPlan) (x : p.shape.Data M) :
    p.runWith 1 (· * ·) x = p.scanner.run x := by
  induction p with
  | empty => rfl
  | leaf => rfl
  | prod p q ih iq =>
    simp only [runWith, scanner, Scanner.product, ih, iq]
    rfl
  | comp p q ih iq =>
    simp only [runWith, scanner, Scanner.compose, Shape.scanNestedWith]
    simp only [funext iq, ih]
    rfl

theorem runWith_map (p : ScanPlan) (e : A) (op : A → A → A)
    (e' : B) (op' : B → B → B) (f : A → B)
    (he : f e = e') (hop : ∀ a b, f (op a b) = op' (f a) (f b))
    (x : p.shape.Data A) :
    (p.shape.map f (p.runWith e op x).1, f (p.runWith e op x).2) =
      p.runWith e' op' (p.shape.map f x) := by
  induction p with
  | empty => exact Prod.ext rfl he
  | leaf => exact Prod.ext he rfl
  | prod p q ih iq =>
    have hl := ih x.1
    have hr := iq x.2
    simp only [shape, runWith, Shape.map]
    rw [← hl, ← hr]
    simp only [Shape.map_map, hop]
  | comp p q ih iq =>
    change (p.shape.subst q.shape).Data A at x
    simp only [shape, runWith, Shape.map_join, Shape.split_map]
    have hlocal : p.shape.map (q.runWith e' op')
        (p.shape.map (q.shape.map f) (p.shape.split q.shape x)) =
        p.shape.map (fun y => (q.shape.map f y.1, f y.2))
          (p.shape.map (q.runWith e op) (p.shape.split q.shape x)) := by
      simp only [Shape.map_map]
      apply Shape.map_congr
      intro a
      exact (iq a).symm
    rw [hlocal]
    simp only [Shape.map_map]
    have ht := ih (p.shape.map (fun a => (q.runWith e op a).2) (p.shape.split q.shape x))
    simp only [Shape.map_map] at ht
    rw [← ht]
    simp only [Shape.map_zipWith, Shape.map_map, hop, Shape.zipWith_map_right, Shape.zipWith_map_left]

end ScanPlan

/-- Structural node names make sharing explicit without assigning machine addresses. -/
inductive Wire where
  | input (index : Nat)
  | one
  | mul (left right : Wire)
  deriving DecidableEq, Repr

namespace Wire

def eval {M : Type u} [Monoid M] (inputs : Nat → M) : Wire → M
  | .input i => inputs i
  | .one => 1
  | .mul a b => eval inputs a * eval inputs b

/-- Eliminate either identity operand before allocating a binary gate. -/
def times : Wire → Wire → Wire
  | .one, b => b
  | a, .one => a
  | a, b => .mul a b

@[simp] theorem eval_times {M : Type u} [Monoid M] (inputs : Nat → M) (a b : Wire) :
    eval inputs (times a b) = eval inputs a * eval inputs b := by
  cases a <;> cases b <;> simp [times, eval]

/-- Reachable binary nodes, counting each shared node once. -/
def gates : Wire → Finset Wire
  | .input _ => ∅
  | .one => ∅
  | .mul a b => insert (.mul a b) (gates a ∪ gates b)

/-- Input arrival times are arbitrary. Identity is available at time zero. -/
def arrival (inputs : Nat → Nat) : Wire → Nat
  | .input i => inputs i
  | .one => 0
  | .mul a b => max (arrival inputs a) (arrival inputs b) + 1

@[simp] theorem gates_times_subset (a b : Wire) :
    gates (times a b) ⊆ gates (.mul a b) := by
  cases a <;> cases b <;> simp [times, gates]

theorem times_work_le (a b : Wire) :
    (gates (times a b)).card ≤ (gates (.mul a b)).card :=
  Finset.card_le_card (gates_times_subset a b)

theorem arrival_times_le (t : Nat → Nat) (a b : Wire) :
    arrival t (times a b) ≤ arrival t (.mul a b) := by
  cases a <;> cases b <;> simp [times, arrival]

@[simp] theorem arrival_mul (t : Nat → Nat) (a b : Wire) :
    arrival t (.mul a b) = max (arrival t a) (arrival t b) + 1 := rfl

/-- Every dependency edge decreases zero-input arrival rank, hence cannot cycle. -/
theorem child_rank_lt (a b : Wire) :
    arrival (fun _ => 0) a < arrival (fun _ => 0) (.mul a b) ∧
    arrival (fun _ => 0) b < arrival (fun _ => 0) (.mul a b) := by
  simp only [arrival]
  omega

/-- Identity is distinguished from an ordinary input arriving at time zero. -/
def timing (t : Nat → Nat) : Wire → Option Nat
  | .one => none
  | w => some (w.arrival t)

def timeMul : Option Nat → Option Nat → Option Nat
  | none, b => b
  | a, none => a
  | some a, some b => some (max a b + 1)

@[simp] theorem timing_times (t : Nat → Nat) (a b : Wire) :
    timing t (times a b) = timeMul (timing t a) (timing t b) := by
  cases a <;> cases b <;> rfl

@[simp] theorem timing_getD (t : Nat → Nat) (w : Wire) :
    (timing t w).getD 0 = arrival t w := by cases w <;> rfl

/-- A node is normalized when it contains no binary gate with an identity input. -/
def Normal : Wire → Prop
  | .input _ => True
  | .one => True
  | .mul a b => Normal a ∧ Normal b ∧ a ≠ .one ∧ b ≠ .one

theorem normal_times {a b : Wire} (ha : Normal a) (hb : Normal b) :
    Normal (times a b) := by
  cases a <;> cases b <;> simp_all [times, Normal]

end Wire

/-- Any finite collection of output wires denotes a shared acyclic circuit.
The last output need not be a scan total; the type is independent of recipes. -/
structure SharedCircuit where
  outputs : List Wire

namespace SharedCircuit

def gates (c : SharedCircuit) : Finset Wire := (c.outputs.map Wire.gates).foldl (· ∪ ·) ∅
def work (c : SharedCircuit) : Nat := c.gates.card
def arrivals (c : SharedCircuit) (t : Nat → Nat) : List Nat := c.outputs.map (Wire.arrival t)
def depth (c : SharedCircuit) : Nat := (c.arrivals (fun _ => 0)).foldl max 0
def eval {M : Type u} [Monoid M] (c : SharedCircuit) (v : Nat → M) : List M :=
  c.outputs.map (Wire.eval v)

end SharedCircuit

namespace ScanPlan

def circuit (p : ScanPlan) (inputs : p.shape.Data Wire) : p.shape.Data Wire × Wire :=
  p.runWith .one Wire.times inputs

theorem circuit_eval {M : Type u} [Monoid M] (p : ScanPlan)
    (v : Nat → M) (x : p.shape.Data Wire) :
    (p.shape.map (Wire.eval v) (p.circuit x).1, Wire.eval v (p.circuit x).2) =
      p.scanner.run (p.shape.map (Wire.eval v) x) := by
  rw [← runWith_scanner]
  exact p.runWith_map .one Wire.times 1 (· * ·) (Wire.eval v) rfl (Wire.eval_times v) x

theorem circuit_correct {M : Type u} [Monoid M] (p : ScanPlan)
    (v : Nat → M) (x : p.shape.Data Wire) :
    ((p.shape.flatten (p.circuit x).1).map (Wire.eval v), Wire.eval v (p.circuit x).2) =
      sequential 1 ((p.shape.flatten x).map (Wire.eval v)) := by
  have h := congrArg (fun y => (p.shape.flatten y.1, y.2)) (p.circuit_eval v x)
  simpa only [Shape.flatten_map, p.correct] using h.trans (p.correct _)

/-- Exact compositional timing, including identity bypass and nonuniform arrivals.
The same operations-only fold computes each child once and reuses its total. -/
theorem circuit_timing (p : ScanPlan) (t : Nat → Nat) (x : p.shape.Data Wire) :
    (p.shape.map (Wire.timing t) (p.circuit x).1, Wire.timing t (p.circuit x).2) =
      p.runWith none Wire.timeMul (p.shape.map (Wire.timing t) x) :=
  p.runWith_map Wire.one Wire.times none Wire.timeMul (Wire.timing t) rfl
    (Wire.timing_times t) x

def inputWires (p : ScanPlan) : p.shape.Data Wire := p.shape.map Wire.input (p.shape.inputs 0)

@[simp] theorem inputWires_flatten (p : ScanPlan) :
    p.shape.flatten p.inputWires = (List.range p.shape.size).map Wire.input := by
  simp [inputWires, List.range'_eq_map_range]

theorem canonical_correct {M : Type u} [Monoid M] (p : ScanPlan) (v : Nat → M) :
    ((p.shape.flatten (p.circuit p.inputWires).1).map (Wire.eval v),
      Wire.eval v (p.circuit p.inputWires).2) =
      sequential 1 ((List.range p.shape.size).map v) := by
  simpa only [inputWires_flatten, List.map_map, Function.comp_def, Wire.eval] using
    p.circuit_correct v p.inputWires

def outputs (p : ScanPlan) : List Wire :=
  p.shape.flatten (p.circuit p.inputWires).1 ++ [(p.circuit p.inputWires).2]

/-- Identity elimination is preserved at every node of every compiled plan. -/
theorem outputs_normal (p : ScanPlan) : ∀ w ∈ p.outputs, Wire.Normal w := by
  let e : {w : Wire // Wire.Normal w} := ⟨.one, trivial⟩
  let op : {w : Wire // Wire.Normal w} → {w : Wire // Wire.Normal w} →
      {w : Wire // Wire.Normal w} := fun a b => ⟨Wire.times a.1 b.1, Wire.normal_times a.2 b.2⟩
  let ins : p.shape.Data {w : Wire // Wire.Normal w} :=
    p.shape.map (fun i => ⟨Wire.input i, trivial⟩) (p.shape.inputs 0)
  have h := p.runWith_map e op Wire.one Wire.times Subtype.val rfl (fun _ _ => rfl) ins
  simp only [ins, Shape.map_map] at h
  change (p.shape.map Subtype.val (p.runWith e op ins).1, (p.runWith e op ins).2.val) =
    p.circuit p.inputWires at h
  intro w hw
  simp only [outputs, ← h, Shape.flatten_map, List.mem_append, List.mem_map,
    List.mem_singleton] at hw
  rcases hw with ⟨a, _, rfl⟩ | rfl
  · exact a.property
  · exact (p.runWith e op ins).2.property

def sharedCircuit (p : ScanPlan) : SharedCircuit := ⟨p.outputs⟩

def gates (p : ScanPlan) : Finset Wire := p.sharedCircuit.gates
def work (p : ScanPlan) : Nat := p.gates.card

def arrivals (p : ScanPlan) (t : Nat → Nat) : List Nat := p.outputs.map (Wire.arrival t)
def depth (p : ScanPlan) : Nat := (p.arrivals (fun _ => 0)).foldl max 0

def totalArrival (p : ScanPlan) (t : Nat → Nat) : Nat :=
  Wire.arrival t (p.circuit p.inputWires).2

end ScanPlan
end Applications.Parallel
