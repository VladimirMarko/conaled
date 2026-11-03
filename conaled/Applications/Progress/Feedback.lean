import Applications.Progress.Processors

/-! Initialized discrete feedback. A tick evaluates one total body; no scheduler
or wall-clock bound is implicit. Operations and solution laws remain separate. -/
namespace Progress.Feedback
universe u
variable {A B C S T X Y : Type u}

structure Initialized (A B S : Type u) where
  step : A × S → B × S
  initial : S

def Initialized.mealy (f : Initialized A B S) : Mealy S A B :=
  fun s a => f.step (a,s)

/-- Independent equations for the state before each tick and output at that tick. -/
def Solution (f : Initialized A B S) (a : Stream A) (s : Stream S) (b : Stream B) : Prop :=
  s 0 = f.initial ∧ (∀ n, s (n+1) = (f.step (a n,s n)).2) ∧
    ∀ n, b n = (f.step (a n,s n)).1

def state (f : Initialized A B S) (a : Stream A) : Stream S
  | 0 => f.initial
  | n+1 => (f.step (a n,state f a n)).2

def output (f : Initialized A B S) (a : Stream A) : Stream B :=
  fun n => (f.step (a n,state f a n)).1

theorem solves (f : Initialized A B S) (a : Stream A) :
    Solution f a (state f a) (output f a) := ⟨rfl,fun _ => rfl,fun _ => rfl⟩

theorem unique {f : Initialized A B S} {a : Stream A} {s : Stream S} {b : Stream B}
    (h : Solution f a s b) : s = state f a ∧ b = output f a := by
  have hs : ∀ n, s n = state f a n := by
    intro n
    induction n with
    | zero => exact h.1
    | succ n ih => simpa [state, ih] using h.2.1 n
  exact ⟨funext hs, funext (fun n => by simpa [output, hs] using h.2.2 n)⟩

/-- Both the state history and output are uniquely determined by initialization. -/
theorem existsUnique_solution (f : Initialized A B S) (a : Stream A) :
    ∃! sb : Stream S × Stream B, Solution f a sb.1 sb.2 := by
  refine ⟨(state f a,output f a),solves f a,?_⟩
  intro sb h
  exact Prod.ext (unique h).1 (unique h).2

theorem state_shift (f : Initialized A B S) (a : Stream A) (n : Nat) :
    state f a (n+1) = state ⟨f.step,(f.step (a 0,f.initial)).2⟩ (shift a) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (f.step (a (n+1),state f a (n+1))).2 = _
    rw [ih]
    rfl

theorem output_mealy (f : Initialized A B S) (a : Stream A) :
    output f a = runStream f.mealy f.initial a := by
  funext n
  induction n generalizing f a with
  | zero => rfl
  | succ n ih =>
    change (f.step (a (n+1),state f a (n+1))).1 =
      runStream f.mealy (f.step (a 0,f.initial)).2 (shift a) n
    rw [state_shift]
    exact ih (⟨f.step,(f.step (a 0,f.initial)).2⟩ : Initialized A B S) (shift a)

theorem output_prefix (f : Initialized A B S) (a : Stream A) (n : Nat) :
    prefixOf (output f a) n = runList f.mealy f.initial (prefixOf a n) := by
  rw [output_mealy]; exact runStream_prefix _ _ _ _

theorem causal (f : Initialized A B S) (a b : Stream A) (n : Nat)
    (h : prefixOf a n = prefixOf b n) :
    prefixOf (output f a) n = prefixOf (output f b) n := by
  rw [output_mealy, output_mealy]
  exact delivery_causal (mealy_delivery f.mealy f.initial) a b n h

/-- Heterogeneous state/output observations; no decoding function is chosen. -/
theorem transport {A' B' T : Type u} (f : Initialized A B S) (g : Initialized A' B' T)
    (I : A → A' → Prop) (R : S → T → Prop) (O : B → B' → Prop)
    (initial : R f.initial g.initial)
    (step : ∀ a a' s t, I a a' → R s t →
      O (f.step (a,s)).1 (g.step (a',t)).1 ∧ R (f.step (a,s)).2 (g.step (a',t)).2)
    (a : Stream A) (a' : Stream A') (inputs : ∀ n, I (a n) (a' n)) :
    (∀ n, R (state f a n) (state g a' n)) ∧ ∀ n, O (output f a n) (output g a' n) := by
  have states : ∀ n, R (state f a n) (state g a' n) := by
    intro n
    induction n with
    | zero => exact initial
    | succ n ih => exact (step _ _ _ _ (inputs n) ih).2
  exact ⟨states,fun n => (step _ _ _ _ (inputs n) (states n)).1⟩

theorem prefix_related {A' : Type u} (R : A → A' → Prop) (a : Stream A) (b : Stream A')
    (h : ∀ n, R (a n) (b n)) (n : Nat) : List.Forall₂ R (prefixOf a n) (prefixOf b n) := by
  induction n generalizing a b with
  | zero => exact .nil
  | succ n ih => exact .cons (h 0) (ih (shift a) (shift b) (fun n => h (n+1)))

def streamRep {A' : Type u} (R : A → A' → Prop) : Relational.RelRep :=
  ⟨Stream A, Stream A', fun a b => ∀ n, R (a n) (b n)⟩

def solutionSquare {A' B' T : Type u} (f : Initialized A B S) (g : Initialized A' B' T)
    (I : A → A' → Prop) (R : S → T → Prop) (O : B → B' → Prop)
    (initial : R f.initial g.initial)
    (step : ∀ a a' s t, I a a' → R s t →
      O (f.step (a,s)).1 (g.step (a',t)).1 ∧ R (f.step (a,s)).2 (g.step (a',t)).2) :
    Relational.RelSquare (streamRep I) (streamRep O) where
  impl := output f
  spec := output g
  preserves h := (transport f g I R O initial step _ _ h).2

/-- Direct finite execution also retains the state needed to continue a chunk. -/
def run (op : Mealy S A B) (s : S) : List A → List B × S
  | [] => ([],s)
  | a::as => let next := op s a; let rest := run op next.2 as; (next.1::rest.1,rest.2)

theorem run_outputs (op : Mealy S A B) (s : S) (as : List A) :
    (run op s as).1 = runList op s as := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => simp [run,runList,ih]

theorem run_append (op : Mealy S A B) (s : S) (as bs : List A) :
    run op s (as ++ bs) =
      let left := run op s as; let right := run op left.2 bs; (left.1 ++ right.1,right.2) := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => simp [run,ih]

/-- A functional state map specializes the relational theorem and the existing
coalgebra law to independently supplied producer input. -/
theorem producer_transport (f : Mealy S A B) (g : Mealy T A C) (h : S → T) (k : B → C)
    (commutes : ∀ s a, g (h s) a = (k (f s a).1,h (f s a).2))
    (input : Coalgebra X A) (s : S) (x : X) (n : Nat) :
    unfold (mealyCoalgebra g input) (h s,x) n =
      (unfold (mealyCoalgebra f input) (s,x) n).map k :=
  unfold_transport _ _ (fun (s,x) => (h s,x)) k
    (fun (s,x) => by simp [mealyCoalgebra,commutes]) (s,x) n

end Progress.Feedback
