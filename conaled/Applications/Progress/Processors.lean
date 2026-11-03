import Applications.Progress.Streams

/-!
# Demand-bounded stream processors

Operations contain no proof fields. Their finite machines consume explicit
input lists. Delivery laws connect those machines to independent stream
semantics. Composition executes the first machine and passes its result to the
second; input demand composes by substitution, and transition bounds add.
-/
namespace Progress
universe u
variable {A B C S : Type u}

abbrev Stream (A : Type u) := Nat → A

def shift (x : Stream A) : Stream A := fun n => x (n + 1)

def prefixOf (x : Stream A) : Nat → List A
  | 0 => []
  | n + 1 => x 0 :: prefixOf (shift x) n

@[simp] theorem prefix_length (x : Stream A) (n : Nat) : (prefixOf x n).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [prefixOf, ih]

theorem prefix_take (x : Stream A) {m n : Nat} (h : m ≤ n) :
    (prefixOf x n).take m = prefixOf x m := by
  induction m generalizing x n with
  | zero => simp [prefixOf]
  | succ m ih =>
    cases n with
    | zero => omega
    | succ n => simpa [prefixOf] using ih (shift x) (by omega : m ≤ n)

structure Processor (A B : Type u) where
  State : Type u
  demand : Nat → Nat
  start : Nat → List A → State
  step : Nat → Machine State (List B)
  meaning : Stream A → Stream B

/-- Uniform finite delivery for all stream inputs. Atomic transition costs only. -/
def DeliversWithin (p : Processor A B) (work : Nat → Nat) : Prop :=
  ∀ x n, ∃ k, k ≤ work n ∧
    Evaluates (p.step n) (p.start n (prefixOf x (p.demand n))) (prefixOf (p.meaning x) n) k

/-- Causality is value dependence on finite input, not an evaluation-time claim. -/
def Causal (p : Processor A B) : Prop :=
  ∀ x y n, prefixOf x (p.demand n) = prefixOf y (p.demand n) →
    prefixOf (p.meaning x) n = prefixOf (p.meaning y) n

theorem delivery_causal {p : Processor A B} {work : Nat → Nat}
    (h : DeliversWithin p work) : Causal p := by
  intro x y n eq
  obtain ⟨k, _, hx⟩ := h x n
  obtain ⟨l, _, hy⟩ := h y n
  rw [← eq] at hy
  exact (hx.unique hy).1

/-- Outputs obtained at different requests are coherent, even if the machines
and demanded input lengths for those requests differ. -/
theorem delivery_coherent {p : Processor A B} {work : Nat → Nat}
    (h : DeliversWithin p work) (x : Stream A) {m n : Nat} (le : m ≤ n)
    {ys zs : List B} {k l : Nat}
    (hy : Evaluates (p.step m) (p.start m (prefixOf x (p.demand m))) ys k)
    (hz : Evaluates (p.step n) (p.start n (prefixOf x (p.demand n))) zs l) :
    zs.take m = ys := by
  obtain ⟨_, _, hm⟩ := h x m
  obtain ⟨_, _, hn⟩ := h x n
  rw [(hy.unique hm).1, (hz.unique hn).1]
  exact prefix_take _ le

def composeProcessor (g : Processor B C) (f : Processor A B) : Processor A C where
  State := Sum f.State g.State
  demand n := f.demand (g.demand n)
  start n xs := .inl (f.start (g.demand n) xs)
  step n := sequential (f.step (g.demand n)) (g.step n) (g.start n)
  meaning := g.meaning ∘ f.meaning

theorem compose_delivery {f : Processor A B} {g : Processor B C}
    {wf wg : Nat → Nat} (hf : DeliversWithin f wf) (hg : DeliversWithin g wg) :
    DeliversWithin (composeProcessor g f) (fun n => wf (g.demand n) + wg n) := by
  intro x n
  obtain ⟨k, hk, h⟩ := hf x (g.demand n)
  obtain ⟨l, hl, j⟩ := hg (f.meaning x) n
  exact ⟨k + l, Nat.add_le_add hk hl, sequential_evaluates h j⟩

/-- Ordinary Mealy operations: one input and one output per transition. -/
abbrev Mealy (S A B : Type u) := S → A → B × S

def runList (op : Mealy S A B) (s : S) : List A → List B
  | [] => []
  | a :: xs => (op s a).1 :: runList op (op s a).2 xs

def runStream (op : Mealy S A B) (s : S) (x : Stream A) : Stream B
  | 0 => (op s (x 0)).1
  | n + 1 => runStream op (op s (x 0)).2 (shift x) n

theorem runStream_prefix (op : Mealy S A B) (s : S) (x : Stream A) (n : Nat) :
    prefixOf (runStream op s x) n = runList op s (prefixOf x n) := by
  induction n generalizing s x with
  | zero => rfl
  | succ n ih =>
    change (op s (x 0)).1 :: prefixOf (runStream op (op s (x 0)).2 (shift x)) n = _
    simp only [prefixOf, runList, ih]

/-- Lists are explicit machine state. Append is atomic in this cost model;
this bound is not a claim about allocation or host runtime. -/
def mealyStep (op : Mealy S A B) : Machine (S × List A × List B) (List B)
  | (_, [], acc) => .inl acc
  | (s, a :: xs, acc) => .inr ((op s a).2, xs, acc ++ [(op s a).1])

theorem mealy_evaluates (op : Mealy S A B) (s : S) (xs : List A) (acc : List B) :
    Evaluates (mealyStep op) (s, xs, acc) (acc ++ runList op s xs) (xs.length + 1) := by
  induction xs generalizing s acc with
  | nil => exact .done (by simp [mealyStep, runList])
  | cons a xs ih =>
    simpa [runList, List.append_assoc] using
      Evaluates.next (step := mealyStep op) (s := (s, a :: xs, acc)) rfl
        (ih (op s a).2 (acc ++ [(op s a).1]))

def mealyProcessor (op : Mealy S A B) (s : S) : Processor A B where
  State := S × List A × List B
  demand := id
  start _ xs := (s, xs, [])
  step _ := mealyStep op
  meaning := runStream op s

theorem mealy_delivery (op : Mealy S A B) (s : S) :
    DeliversWithin (mealyProcessor op s) (fun n => n + 1) := by
  intro x n
  refine ⟨n + 1, le_rfl, ?_⟩
  simpa [mealyProcessor, runStream_prefix] using mealy_evaluates op s (prefixOf x n) []

/-- The same element operation drives a guarded producer when its input is
supplied by a coalgebra. The paired state retains both machines' states. -/
def mealyCoalgebra {T : Type u} (op : Mealy S A B) (input : Coalgebra T A) :
    Coalgebra (S × T) B :=
  fun (s, t) => ((op s (input t).1).1, ((op s (input t).1).2, (input t).2))

theorem unfold_mealy {T : Type u} (op : Mealy S A B) (input : Coalgebra T A)
    (s : S) (t : T) (n : Nat) :
    unfold (mealyCoalgebra op input) (s, t) n = runList op s (unfold input t n) := by
  induction n generalizing s t with
  | zero => rfl
  | succ n ih => simp [unfold, mealyCoalgebra, runList, ih]

/-- Cross the producer/finite-input boundary with actual traces on both sides.
The guarded producer takes n steps; the list machine also checks its empty tail.
Both results are connected to the same independently unfolded input. -/
theorem mealy_realizations {T : Type u} (op : Mealy S A B) (input : Coalgebra T A)
    (s : S) (t : T) (n : Nat) :
    Delivers (guarded (mealyCoalgebra op input)) (s, t)
      (unfold (mealyCoalgebra op input) (s, t) n)
      (advance (mealyCoalgebra op input) (s, t) n) n ∧
    Evaluates (mealyStep op) (s, unfold input t n, [])
      (unfold (mealyCoalgebra op input) (s, t) n) (n + 1) := by
  refine ⟨guarded_delivery _ _ _, ?_⟩
  simpa [unfold_mealy] using mealy_evaluates op s (unfold input t n) []

/-- Maps and scans reuse the same finite delivery proof, without compiler syntax. -/
def mapProcessor (f : A → B) : Processor A B :=
  mealyProcessor (fun (_ : PUnit) a => (f a, PUnit.unit)) PUnit.unit

def scanProcessor (f : B → A → B) (b : B) : Processor A B :=
  mealyProcessor (fun s a => (f s a, f s a)) b

theorem map_delivery (f : A → B) : DeliversWithin (mapProcessor f) (fun n => n + 1) :=
  mealy_delivery _ _

theorem scan_delivery (f : B → A → B) (b : B) :
    DeliversWithin (scanProcessor f b) (fun n => n + 1) := mealy_delivery _ _

/-- Drop a fixed finite prefix. This has a nonidentity demand function. -/
def skipStream : Nat → Stream A → Stream A
  | 0, x => x
  | k + 1, x => skipStream k (shift x)

def dropStep : Machine (Nat × List A) (List A)
  | (0, xs) => .inl xs
  | (_ + 1, []) => .inl []
  | (k + 1, _ :: xs) => .inr (k, xs)

theorem drop_evaluates (k n : Nat) (x : Stream A) :
    Evaluates dropStep (k, prefixOf x (n + k)) (prefixOf (skipStream k x) n) (k + 1) := by
  induction k generalizing x with
  | zero => exact .done rfl
  | succ k ih =>
    exact .next rfl (ih (shift x))

def dropProcessor (k : Nat) : Processor A A where
  State := Nat × List A
  demand n := n + k
  start _ xs := (k, xs)
  step _ := dropStep
  meaning := skipStream k

theorem drop_delivery (k : Nat) :
    DeliversWithin (dropProcessor (A := A) k) (fun _ => k + 1) :=
  fun x n => ⟨k + 1, le_rfl, drop_evaluates k n x⟩

/-- Shared relational squares expose causal transport of finite observations.
The implementation side is actual input/output streams; the relation asks only
for the specified finite observations, not equality of complete streams. -/
def prefixRep (A : Type u) (n : Nat) : Relational.RelRep where
  R := Stream A
  S := List A
  Rel x xs := prefixOf x n = xs

/-- Deliverability establishes that finite evaluation returns this observation.
This adapter packages the corresponding finite observation transformation. -/
def mealySquare (op : Mealy S A B) (s : S) (n : Nat) :
    Relational.RelSquare (prefixRep A n) (prefixRep B n) where
  impl := runStream op s
  spec := runList op s
  preserves := by
    intro x xs h
    change Stream A at x
    change List A at xs
    change prefixOf x n = xs at h
    change prefixOf (runStream op s x) n = runList op s xs
    rw [runStream_prefix, h]

/-- Pasting is inherited from the shared square API, with no new square laws. -/
def composedMealySquare {T : Type u} (f : Mealy S A B) (g : Mealy T B C)
    (s : S) (t : T) (n : Nat) : Relational.RelSquare (prefixRep A n) (prefixRep C n) :=
  Relational.compose (mealySquare g t n) (mealySquare f s n)

end Progress
