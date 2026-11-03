import Applications.Parallel.PrefixBounds

/-!
# Topologically indexed binary DAGs

Gate i may reference any earlier gate. Multiple references share that gate;
distinct gates may compute the same expression. Compilation to structural
wires preserves meaning and timing and can only decrease retained gate work.
-/
namespace Applications.Parallel
namespace PrefixDAG

/-- Input wires and identity are free; gate references address earlier nodes. -/
inductive Port (n : Nat) where
  | input (i : Nat)
  | one
  | gate (i : Fin n)
  deriving DecidableEq

namespace Port

def run (inputs : Nat → A) (one : A) (env : Fin n → A) : Port n → A
  | .input i => inputs i
  | .one => one
  | .gate i => env i

def reach (env : Fin n → Finset (Fin n)) : Port n → Finset (Fin n)
  | .input _ => ∅
  | .one => ∅
  | .gate i => env i

theorem run_map (f : A → B) (inputs : Nat → A) (one : A) (env : Fin n → A) (p : Port n) :
    f (p.run inputs one env) = p.run (f ∘ inputs) (f one) (f ∘ env) := by
  cases p <;> rfl

end Port

/-- An arbitrary finite binary concatenation DAG in topological order. -/
inductive Network : Nat → Type where
  | empty : Network 0
  | push {n : Nat} (previous : Network n) (left right : Port n) : Network (n+1)

namespace Network

def run (inputs : Nat → A) (one : A) (op : A → A → A) :
    Network n → Fin n → A
  | .empty => Fin.elim0
  | .push previous a b =>
      Fin.lastCases (op (a.run inputs one (previous.run inputs one op))
        (b.run inputs one (previous.run inputs one op))) (previous.run inputs one op)

def wires (net : Network n) : Fin n → Wire := net.run Wire.input .one .mul

/-- Reachable gate addresses, including the addressed node itself. -/
def reach : Network n → Fin n → Finset (Fin n)
  | .empty => Fin.elim0
  | .push previous a b =>
      Fin.lastCases
        (insert (Fin.last _) (((a.reach previous.reach) ∪ (b.reach previous.reach)).image Fin.castSucc))
        (fun i => (previous.reach i).image Fin.castSucc)

theorem run_map (net : Network n) (f : A → B) (inputs : Nat → A) (one : A)
    (op : A → A → A) (inputs' : Nat → B) (one' : B) (op' : B → B → B)
    (hi : ∀ i, f (inputs i) = inputs' i) (he : f one = one')
    (hop : ∀ a b, f (op a b) = op' (f a) (f b)) :
    ∀ i, f (net.run inputs one op i) = net.run inputs' one' op' i := by
  induction net with
  | empty => intro i; exact Fin.elim0 i
  | @push n previous a b ih =>
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [run, Fin.lastCases_last, hop]
      have hp (p : Port n) : f (p.run inputs one (previous.run inputs one op)) =
          p.run inputs' one' (previous.run inputs' one' op') := by
        cases p <;> simp [Port.run, hi, he, ih]
      exact congrArg₂ op' (hp a) (hp b)
    · simpa only [run, Fin.lastCases_castSucc] using ih j

private theorem port_gates (net : Network n)
    (h : ∀ i, (net.wires i).gates = (net.reach i).image net.wires) (p : Port n) :
    (p.run Wire.input .one net.wires).gates = (p.reach net.reach).image net.wires := by
  cases p with
  | input => simp [Port.run, Port.reach, Wire.gates]
  | one => simp [Port.run, Port.reach, Wire.gates]
  | gate i => exact h i

/-- A structural gate is the image of at least one retained named node. -/
theorem gates_eq_image_reach (net : Network n) :
    ∀ i, (net.wires i).gates = (net.reach i).image net.wires := by
  induction net with
  | empty => intro i; exact Fin.elim0 i
  | @push n previous a b ih =>
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [wires, run, reach, Fin.lastCases_last, Wire.gates,
        Finset.image_insert, Finset.image_image, Finset.image_union]
      change insert _ ((a.run Wire.input Wire.one previous.wires).gates ∪
        (b.run Wire.input Wire.one previous.wires).gates) = _
      rw [port_gates previous ih a, port_gates previous ih b]
      simp only [Function.comp_def, Fin.lastCases_castSucc]
      rfl
    · simp only [wires, run, reach, Fin.lastCases_castSucc, Finset.image_image, Function.comp_def]
      exact ih j

end Network

/-- Output references may omit dead nodes and repeat ports freely. -/
structure Circuit (n : Nat) where
  network : Network n
  outputs : List (Port n)

namespace Circuit

def compile (c : Circuit n) : SharedCircuit :=
  ⟨c.outputs.map (Port.run Wire.input .one c.network.wires)⟩

def retained (c : Circuit n) : Finset (Fin n) :=
  (c.outputs.map (Port.reach c.network.reach)).foldl (· ∪ ·) ∅

def work (c : Circuit n) : Nat := c.retained.card

def eval {M : Type*} [Monoid M] (c : Circuit n) (inputs : Nat → M) : List M :=
  c.outputs.map (Port.run inputs 1 (c.network.run inputs 1 (· * ·)))

def arrivals (c : Circuit n) (inputs : Nat → Nat) : List Nat :=
  c.outputs.map (Port.run inputs 0 (c.network.run inputs 0 (fun a b => max a b + 1)))

def depth (c : Circuit n) : Nat := (c.arrivals (fun _ => 0)).foldl max 0

theorem compile_eval {M : Type*} [Monoid M] (c : Circuit n) (inputs : Nat → M) :
    c.compile.eval inputs = c.eval inputs := by
  simp only [compile, SharedCircuit.eval, List.map_map, eval]
  apply List.map_congr_left
  intro p _
  cases p with
  | input => rfl
  | one => rfl
  | gate i =>
    exact c.network.run_map (Wire.eval inputs) Wire.input Wire.one Wire.mul
      inputs 1 (· * ·) (fun _ => rfl) rfl (fun _ _ => rfl) i

theorem compile_arrivals (c : Circuit n) (inputs : Nat → Nat) :
    c.compile.arrivals inputs = c.arrivals inputs := by
  simp only [compile, SharedCircuit.arrivals, List.map_map, arrivals]
  apply List.map_congr_left
  intro p _
  cases p with
  | input => rfl
  | one => rfl
  | gate i =>
    exact c.network.run_map (Wire.arrival inputs) Wire.input Wire.one Wire.mul
      inputs 0 (fun a b => max a b + 1) (fun _ => rfl) rfl (fun _ _ => rfl) i

@[simp] theorem compile_depth (c : Circuit n) : c.compile.depth = c.depth := by
  simp [SharedCircuit.depth, depth, compile_arrivals]

private theorem image_fold_union (f : A → B) [DecidableEq A] [DecidableEq B]
    (xs : List (Finset A)) (s : Finset A) :
    (xs.foldl (· ∪ ·) s).image f =
      (xs.map (Finset.image f)).foldl (· ∪ ·) (s.image f) := by
  induction xs generalizing s with
  | nil => rfl
  | cons a as ih => simp only [List.foldl_cons, List.map_cons, ih, Finset.image_union]

theorem compile_gates (c : Circuit n) :
    c.compile.gates = c.retained.image c.network.wires := by
  rw [retained, image_fold_union]
  simp only [compile, SharedCircuit.gates, List.map_map, Finset.image_empty]
  congr 1
  apply List.map_congr_left
  intro p _
  exact Network.port_gates c.network c.network.gates_eq_image_reach p

/-- Hash-consing may merge duplicate named nodes but never adds charged work. -/
theorem compile_work_le (c : Circuit n) : c.compile.work ≤ c.work := by
  unfold SharedCircuit.work work
  rw [compile_gates]
  exact Finset.card_image_le

/-- Correctness is tested at independent letters, with only identity constants.
Compilation preserves evaluation for every monoid, not just these test inputs. -/
def ComputesPrefixes (c : Circuit n) (inputs : Nat) : Prop :=
  c.compile.ComputesPrefixes inputs

theorem work_lower {c : Circuit n} {k : Nat} (h : c.ComputesPrefixes k) :
    k-1 ≤ c.work := (SharedCircuit.prefix_work_lower h).trans c.compile_work_le

theorem depth_lower {c : Circuit n} {k : Nat} (h : c.ComputesPrefixes k) :
    k ≤ 2 ^ c.depth := by simpa using SharedCircuit.prefix_depth_lower h

theorem work_depth_lower {c : Circuit n} {k : Nat} (h : c.ComputesPrefixes k) :
    2*k-2 ≤ c.work + c.depth := by
  have hbound := SharedCircuit.prefix_work_depth_lower h
  rw [compile_depth] at hbound
  have hw := c.compile_work_le
  omega

end Circuit
end PrefixDAG
end Applications.Parallel
