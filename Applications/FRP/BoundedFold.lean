import SquareKit.ListFoldCompiler
import Applications.FRP.Indefinite

/-! Capacity-bounded runtime iteration with one retained parity bit. -/
namespace FRPSpec.BoundedFold
open FirstOrderCompiler Applications.Circuits Progress Progress.Feedback

abbrev Batch (capacity : Nat) := {xs : List Bool // xs.length ≤ capacity}

def body : Term Gate [.base, .base] .base :=
  .prim (.xor 0 0) (.pair (.var (.there .here)) (.var .here))

def code : Circuit (context [.base, .base]) .base :=
  FirstOrderCompiler.compile Circuit.target body

/-- Native meaning is ordinary parity; it does not inspect compiled syntax. -/
def parity (s : Bool) (xs : List Bool) : Bool := xs.foldl Bool.xor s

/-- The compiled body is executed on runtime samples. No source evaluator is
called here, and there is no input-dependent compilation. -/
def execute (s : Bool) (xs : List Bool) : Bool :=
  xs.foldl (fun acc x => code.execute (((),acc),x)) s

theorem body_correct (s x : Bool) : code.execute (((),s),x) = Bool.xor s x := by
  rw [Circuit.execute_correct]
  exact FirstOrderCompiler.compile_sound Circuit.target Circuit.sound body (((),s),x)

theorem execute_correct (s : Bool) (xs : List Bool) : execute s xs = parity s xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    change execute (code.execute (((),s),x)) xs = parity (Bool.xor s x) xs
    rw [body_correct, ih]

/-- The existing fold compiler targets runtime lists and compiled circuit bodies. -/
def foldTarget : ListFoldCompiler.Target Gate where
  scalar := Circuit.target
  Hom a b := List (Val Bool a) → Val Bool b
  fold seed step xs := xs.foldl (fun s x => step.execute (((),s),x)) (seed.execute ())
  post finish p xs := finish.execute ((),p xs)

def foldSound : ListFoldCompiler.Sound Bool foldTarget Gate.meaning where
  scalar := {
    denote := Circuit.execute
    ident := fun _ => rfl
    comp := fun _ _ _ => rfl
    terminal := fun _ => rfl
    fst := fun _ => rfl
    snd := fun _ => rfl
    pair := fun _ _ _ => rfl
    primitive := fun _ _ => rfl }
  denote := id
  fold _ _ _ := rfl
  post _ _ _ := rfl

/-- A proof-level seed family connects the resumed loop to the whole fold
compiler. The runtime loop receives the retained bit; it never recompiles it. -/
def sourceFold (seed : Bool) : ListFoldCompiler.Program Gate .base .base :=
  .fold (.prim (.constant seed) .unit) body

theorem whole_fold (s : Bool) (xs : List Bool) :
    ListFoldCompiler.compile foldTarget (sourceFold s) xs = execute s xs := rfl

theorem source_preservation (s : Bool) (xs : List Bool) :
    execute s xs = ListFoldCompiler.eval Gate.meaning (sourceFold s) xs := by
  rw [← whole_fold]
  exact ListFoldCompiler.compile_sound foldTarget foldSound (sourceFold s) xs

/-- Reuses the existing finite iteration semantics, including its visit count. -/
theorem compiled_iteration (s : Bool) (xs : List Bool) :
    execute s xs = ListFoldCompiler.iterate Gate.meaning body s xs := by
  rw [ListFoldCompiler.iterate_eq_foldl, execute_correct]
  rfl

theorem visits (s : Bool) (xs : List Bool) :
    ListFoldCompiler.Executes Gate.meaning body xs s (execute s xs) xs.length := by
  rw [compiled_iteration]
  exact ListFoldCompiler.iterate_executes _ _ _ _

def machine (capacity : Nat) : Initialized (Batch capacity) Bool Bool :=
  ⟨fun (xs,s) => (s,execute s xs.val), false⟩

def native (capacity : Nat) : Initialized (Batch capacity) Bool Bool :=
  ⟨fun (xs,s) => (s,parity s xs.val), false⟩

theorem machine_correct (capacity : Nat) : machine capacity = native capacity := by
  unfold machine native
  congr 1

/-- Both observation and final state are preserved from any current state. -/
theorem run_correct (s : Bool) (xs : List (Batch capacity)) :
    run (machine capacity).mealy s xs = run (native capacity).mealy s xs := by
  rw [machine_correct]

/-- Continuations use the actual retained state, including after nonempty prefixes. -/
theorem continuation (s : Bool) (before after : List (Batch capacity)) :
    run (machine capacity).mealy (run (machine capacity).mealy s before).2 after =
      run (native capacity).mealy (run (native capacity).mealy s before).2 after := by
  rw [machine_correct]

/-- Bounded ingestion inspects at most C+1 constructors. It never traverses a
rejected external tail. External producer storage is outside this ownership. -/
def ingest : (capacity : Nat) → List Bool → Option (Batch capacity)
  | 0, [] => some ⟨[], by simp⟩
  | 0, _ :: _ => none
  | _+1, [] => some ⟨[], by simp⟩
  | n+1, x :: xs => match ingest n xs with
    | none => none
    | some ys => some ⟨x :: ys.val, by simpa using Nat.succ_le_succ ys.property⟩

theorem ingest_value {n : Nat} {xs : List Bool} {b : Batch n}
    (h : ingest n xs = some b) : b.val = xs := by
  induction n generalizing xs with
  | zero =>
    cases xs with
    | nil => have hb := Option.some.inj h; exact congrArg Subtype.val hb.symm
    | cons => simp [ingest] at h
  | succ n ih =>
    cases xs with
    | nil => have hb := Option.some.inj h; exact congrArg Subtype.val hb.symm
    | cons x xs =>
      simp only [ingest] at h
      split at h
      next => contradiction
      next ys he => cases h; simp [ih he]

theorem ingest_success (xs : List Bool) (h : xs.length ≤ n) :
    ∃ b, ingest n xs = some b ∧ b.val = xs := by
  induction n generalizing xs with
  | zero => have : xs = [] := List.eq_nil_of_length_eq_zero (by omega); subst xs; exact ⟨_,rfl,rfl⟩
  | succ n ih =>
    cases xs with
    | nil => exact ⟨_,rfl,rfl⟩
    | cons x xs =>
      obtain ⟨b,hb,hv⟩ := ih xs (by simpa using Nat.le_of_succ_le_succ h)
      simp only [ingest,hb]
      exact ⟨_,rfl,by simp [hv]⟩
/-- Constructor inspections in the same bounded-ingestion recursion. Copying
accepted payload/link cells adds two writes per accepted sample. -/
def ingestionInspections : Nat → List Bool → Nat
  | 0, _ => 1
  | _+1, [] => 1
  | n+1, _::xs => 1 + ingestionInspections n xs

theorem ingestion_bound (n : Nat) (xs : List Bool) : ingestionInspections n xs ≤ n+1 := by
  induction n generalizing xs with
  | zero => simp [ingestionInspections]
  | succ n ih =>
    cases xs with
    | nil => simp [ingestionInspections]
    | cons x xs => have := ih xs; simp only [ingestionInspections]; omega

theorem ingest_rejected (n : Nat) (xs : List Bool) :
    ingest n xs = none ↔ n < xs.length := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨b,hb,_⟩ := ingest_success (n := n) xs (by omega)
    rw [h] at hb
    contradiction
  · intro h
    cases he : ingest n xs with
    | none => rfl
    | some b =>
      have hv := ingest_value he
      have hp := b.property
      rw [hv] at hp
      omega

end FRPSpec.BoundedFold
