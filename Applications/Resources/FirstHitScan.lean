import Applications.Resources.MeasuredLoop

/-! A pre-read first-hit scan. The fixed store is an environment of the local
read primitive; indices and accumulators remain ordinary natural registers. -/
namespace Resources.FirstHitScan
open MeasuredLoop FirstOrderCompiler Iteration

abbrev State := Nat × (Nat × Nat)
abbrev stateTy : Ty := .prod .base (.prod .base .base)
abbrev outputTy : Ty := .prod .base .base

/-- Sum of exactly `k` consecutive contributions, independently of stopping. -/
def sumPrefix (read : Nat → Nat) (i : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => read i + sumPrefix read (i+1) k

def done (n : Nat) (s : State) : Bool := decide (min (n-s.1) (s.2.2-s.2.1) ≤ 0)
def step (read : Nat → Nat) (s : State) : State := (s.1+1, (s.2.1+read s.1,s.2.2))
def rank (n : Nat) (s : State) : Nat := n-s.1

@[simp] theorem done_iff (n : Nat) (s : State) : done n s = true ↔ n ≤ s.1 ∨ s.2.2 ≤ s.2.1 := by
  simp only [done, decide_eq_true_eq]
  omega

theorem continuing (n : Nat) (s : State) (h : done n s = false) : s.1 < n ∧ s.2.1 < s.2.2 := by
  have hn : ¬done n s = true := by simp [h]
  rw [done_iff] at hn
  omega

theorem decreases (n : Nat) (read : Nat → Nat) (s : State) (h : done n s = false) :
    rank n (step read s) < rank n s := by
  have := continuing n s h
  simp only [rank, step]
  omega

/-- Every earlier sumPrefix is below threshold and has an in-bounds next read.
The final sumPrefix reaches the threshold or exhausts the store. -/
def FirstHit (read : Nat → Nat) (n : Nat) (s : State) (k : Nat) (out : Nat × Nat) : Prop :=
  s.1+k ≤ n ∧ out = (s.1+k, s.2.1+sumPrefix read s.1 k) ∧
  (out.1 = n ∨ s.2.2 ≤ out.2) ∧
  ∀ j < k, s.1+j < n ∧ s.2.1+sumPrefix read s.1 j < s.2.2

theorem source_correct {read : Nat → Nat} {n k : Nat} {s y : State}
    (h : Steps (done n) (step read) k s y) (valid : s.1 ≤ n) :
    FirstHit read n s k (y.1,y.2.1) ∧ y.2.2 = s.2.2 := by
  induction h with
  | @stop x hp =>
    have ht := (done_iff n x).mp hp
    refine ⟨⟨by simpa using valid, by simp [sumPrefix], ?_, by simp⟩, rfl⟩
    simp only
    omega
  | @step k x y hp hs ih =>
    have hc := continuing n x hp
    obtain ⟨⟨hb, ho, ht, he⟩, hthreshold⟩ := ih (by simp only [step]; omega)
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hthreshold⟩
    · simp only [step] at hb
      omega
    · simpa [step, sumPrefix, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ho
    · simpa only [step] using ht
    · intro j hj
      cases j with
      | zero => simpa [sumPrefix] using hc
      | succ j =>
        have hj' := he j (by omega)
        simpa [step, sumPrefix, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj'

/-- Total source execution provides the finite derivation used by both routes. -/
theorem source_exists (n : Nat) (read : Nat → Nat) (s : State) :
    ∃ k y, Steps (done n) (step read) k s y := by
  have h := runUntil_spec (done n) (step read) (rank n) (decreases n read) s
  generalize runUntil (done n) (step read) (rank n) (decreases n read) s = y at h
  induction h with
  | stop hp => exact ⟨0, _, .stop hp⟩
  | step hp _ ih =>
    obtain ⟨k, y, hy⟩ := ih
    exact ⟨k+1, y, .step hp hy⟩

inductive Prim : Ty → Ty → Type
  | literal : Nat → Prim .unit .base
  | sub : Prim (.prod .base .base) .base
  | min : Prim (.prod .base .base) .base
  | add : Prim (.prod .base .base) .base
  | succ : Prim .base .base
  | read : Prim .base .base

def meaning (read : Nat → Nat) : {a b : Ty} → Prim a b → Val Nat a → Val Nat b
  | _, _, .literal n, _ => n
  | _, _, .sub, (a,b) => a-b
  | _, _, .min, (a,b) => min a b
  | _, _, .add, (a,b) => a+b
  | _, _, .succ, a => a+1
  | _, _, .read, a => read a

def charge : {a b : Ty} → Prim a b → Nat := fun _ => 1
private def index : Term Prim [stateTy] .base := .fst (.var .here)
private def accum : Term Prim [stateTy] .base := .fst (.snd (.var .here))
private def threshold : Term Prim [stateTy] .base := .snd (.snd (.var .here))

def program (n : Nat) : Program Prim stateTy stateTy outputTy where
  seed := .var .here
  test := ⟨.prim .min (.pair
    (.prim .sub (.pair (.prim (.literal n) .unit) index))
    (.prim .sub (.pair threshold accum))), .prim (.literal 0) .unit⟩
  body := .pair (.prim .succ index)
    (.pair (.prim .add (.pair accum (.prim .read index))) threshold)
  post := .pair index accum

@[simp] theorem program_done (n : Nat) (read : Nat → Nat) (s : State) :
    (program n).done (meaning read) s = done n s := rfl
@[simp] theorem program_step (n : Nat) (read : Nat → Nat) (s : State) :
    (program n).step (meaning read) s = step read s := rfl

def compiled (n : Nat) (read : Nat → Nat) (s : State) : Measured (Nat × Nat) Nat :=
  (program n).execute (meaning read) charge (rank n) (decreases n read) s

/-- The native graph executes both literals, both differences, min and comparison.
It does not short-circuit either component of the stopping condition. -/
def nativeGuard (n : Nat) (s : State) : Measured Bool Nat :=
  bind (n,1) fun size =>
  bind (size-s.1,1) fun remaining =>
  bind (s.2.2-s.2.1,1) fun deficit =>
  bind (min remaining deficit,1) fun m =>
  bind (0,1) fun z => (decide (m ≤ z),1)
def nativeBody (read : Nat → Nat) (s : State) : Measured State Nat :=
  bind (s.1+1,1) fun i =>
  bind (read s.1,1) fun v =>
  bind (s.2.1+v,1) fun a => pure (i,(a,s.2.2))
def native (n : Nat) (read : Nat → Nat) (s : State) : Measured (Nat × Nat) Nat :=
  bind (pure s) fun initial =>
  bind (MeasuredLoop.run (nativeGuard n) (nativeBody read) (rank n) (decreases n read) initial)
    fun final => pure (final.1,final.2.1)

theorem compiled_of_steps {n k : Nat} {read : Nat → Nat} {s y : State}
    (h : Steps (done n) (step read) k s y) :
    compiled n read s = ((y.1,y.2.1),(k+1)*7+k*3) := by
  have hc := Program.execute_of_steps (meaning read) charge (program n) (rank n)
    (decreases n read) s h
  simpa [compiled, Program.finish, program, index, accum, threshold, Test.cost,
    FoldCompiler.bodyCost, charge, FirstOrderCompiler.eval, FirstOrderCompiler.lookup] using hc

theorem native_of_steps {n k : Nat} {read : Nat → Nat} {s y : State}
    (h : Steps (done n) (step read) k s y) :
    native n read s = ((y.1,y.2.1),(k+1)*7+k*3) := by
  have hc := run_of_steps (nativeGuard n) (nativeBody read) (rank n) (decreases n read)
    6 3 (fun _ => rfl) (fun _ => rfl) h
  simp [native, bind, pure, hc]

theorem routes_equal (n : Nat) (read : Nat → Nat) (s : State) : compiled n read s = native n read s := by
  obtain ⟨k,y,h⟩ := source_exists n read s
  rw [compiled_of_steps h, native_of_steps h]

theorem compiled_correct (n : Nat) (read : Nat → Nat) (s : State) (valid : s.1 ≤ n) :
    ∃ k, FirstHit read n s k (compiled n read s).1 ∧
      (compiled n read s).2 = (k+1)*7+k*3 := by
  obtain ⟨k,y,h⟩ := source_exists n read s
  rw [compiled_of_steps h]
  exact ⟨k, (source_correct h valid).1, rfl⟩

/-- Local agreement on legal reads transports the same number of transitions.
No agreement outside the store and no whole-scan equality is assumed. -/
theorem steps_read_transport {n k : Nat} {r q : Nat → Nat} {s y : State}
    (reads : ∀ i < n, q i = r i) (h : Steps (done n) (step r) k s y) :
    Steps (done n) (step q) k s y := by
  induction h with
  | stop hp => exact .stop hp
  | @step k x y hp _ ih =>
    apply Steps.step hp
    simpa only [step, reads x.1 (continuing n x hp).1] using ih

theorem representation_reuse (n : Nat) (r q : Nat → Nat)
    (reads : ∀ i < n, q i = r i) (s : State) : compiled n q s = compiled n r s := by
  obtain ⟨k,y,h⟩ := source_exists n r s
  rw [compiled_of_steps h, compiled_of_steps (steps_read_transport reads h)]

/-- A finite function and a concrete array view, both totalized by zero. -/
def finiteRead {n : Nat} (v : Fin n → Nat) (i : Nat) : Nat := if h : i < n then v ⟨i,h⟩ else 0
def arrayRead (a : Array Nat) (i : Nat) : Nat := a[i]?.getD 0

theorem array_reads (a : Array Nat) (i : Nat) (h : i < a.size) :
    arrayRead a i = finiteRead (fun j : Fin a.size => a[j]) i := by
  simp [arrayRead, finiteRead, h]

theorem array_reuse (a : Array Nat) (s : State) :
    compiled a.size (arrayRead a) s =
      compiled a.size (finiteRead (fun j : Fin a.size => a[j])) s :=
  representation_reuse _ _ _ (array_reads a) s

end Resources.FirstHitScan
