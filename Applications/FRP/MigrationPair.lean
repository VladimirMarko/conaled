import Applications.FRP.Indefinite

/-! Concrete conversions for two circuit realizations of Boolean delay.
The finite and infinite continuation laws reuse the shared feedback semantics. -/
namespace FRPSpec.MigrationPair
open FirstOrderCompiler Applications.Circuits Progress Progress.Feedback Indefinite

/-- The second bit retains the complement of the logical delay state. -/
def redundant : Program .base .base (.prod .base .base) where
  initial := (false,true)
  body := .pair (.compose .first .second)
    (.pair .first (.compose Circuit.not .first))

def forward (b : Bool) : Bool × Bool := (b,!b)
def valid (p : Bool × Bool) : Prop := p.2 = !p.1
def validate (p : Bool × Bool) : Bool := p.2 == !p.1
def reverse (p : Bool × Bool) : Option Bool := if validate p then some p.1 else none

def related (x : Bool) (y : Bool × Bool) := y = (x,!x)

theorem validate_iff (p : Bool × Bool) : validate p = true ↔ valid p := by
  simp [validate, valid]

theorem forward_valid (b : Bool) : valid (forward b) := rfl

theorem reverse_forward (b : Bool) : reverse (forward b) = some b := by
  cases b <;> rfl

theorem reverse_valid (p : Bool × Bool) (h : valid p) : reverse p = some p.1 := by
  simp [reverse, (validate_iff p).2 h]

theorem forward_reverse (p : Bool × Bool) (h : valid p) : forward p.1 = p := by
  exact Prod.ext rfl h.symm

theorem related_valid {b : Bool} {p : Bool × Bool} (h : related b p) : valid p := by
  subst p
  rfl

theorem delay_step (x b : Bool) : delay.machine.step (x,b) = (b,x) := rfl

theorem redundant_step (x : Bool) (p : Bool × Bool) :
    redundant.machine.step (x,p) = (p.1,forward x) := rfl

theorem related_step (x u : Bool) (v : Bool × Bool) (h : related u v) :
    (delay.machine.step (x,u)).1 = (redundant.machine.step (x,v)).1 ∧
      related (delay.machine.step (x,u)).2 (redundant.machine.step (x,v)).2 := by
  rcases h with rfl
  exact ⟨rfl,rfl⟩

/-- Both Boolean states are reached after one accepted input. -/
theorem delay_reachable (b : Bool) :
    ∃ xs, (run delay.machine.mealy delay.initial xs).2 = b := ⟨[b],rfl⟩

/-- All finite suffixes, including the empty suffix, preserve both observations. -/
theorem finite_suffix (b : Bool) (p : Bool × Bool) (h : related b p) (xs : List Bool) :
    (run delay.machine.mealy b xs).1 = (run redundant.machine.mealy p xs).1 ∧
    related (run delay.machine.mealy b xs).2 (run redundant.machine.mealy p xs).2 := by
  have hx : List.Forall₂ Eq xs xs := List.forall₂_same.mpr (fun _ _ => rfl)
  have hr := run_related delay.machine.mealy redundant.machine.mealy Eq related Eq
    (by intro x y u v hxy huv; subst y; exact related_step x u v huv) hx h
  exact ⟨by simpa only [List.forall₂_eq_eq_eq] using hr.1,hr.2⟩

theorem redundant_reachable (p : Bool × Bool) :
    (∃ xs, (run redundant.machine.mealy redundant.initial xs).2 = p) ↔ valid p := by
  constructor
  · rintro ⟨xs,rfl⟩
    exact related_valid (finite_suffix false (false,true) rfl xs).2
  · intro h
    refine ⟨[p.1],?_⟩
    exact forward_reverse p h

/-- Reverse conversion exposes the same suffix theorem after validation. -/
theorem reverse_suffix (p : Bool × Bool) (h : valid p) (xs : List Bool) :
    (run redundant.machine.mealy p xs).1 = (run delay.machine.mealy p.1 xs).1 ∧
    related (run delay.machine.mealy p.1 xs).2 (run redundant.machine.mealy p xs).2 := by
  have hr := finite_suffix p.1 p (forward_reverse p h).symm xs
  exact ⟨hr.1.symm,hr.2⟩

/-- Rebase initialization to the live states before applying stream transport. -/
theorem infinite_suffix (b : Bool) (p : Bool × Bool) (h : related b p)
    (input : Stream Bool) :
    (∀ n, related (state ⟨delay.machine.step,b⟩ input n)
      (state ⟨redundant.machine.step,p⟩ input n)) ∧
    ∀ n, output ⟨delay.machine.step,b⟩ input n =
      output ⟨redundant.machine.step,p⟩ input n :=
  Progress.Feedback.transport ⟨delay.machine.step,b⟩ ⟨redundant.machine.step,p⟩
    Eq related Eq h
    (by intro x y u v hxy huv; subst y; exact related_step x u v huv)
    input input (fun _ => rfl)

/-- Convert the retained continuation of an arbitrary processed prefix. -/
theorem prefix_migration (b : Bool) (pre suffix : List Bool) :
    (run delay.machine.mealy b (pre ++ suffix)).1 =
      (run delay.machine.mealy b pre).1 ++
        (run redundant.machine.mealy (forward (run delay.machine.mealy b pre).2) suffix).1 ∧
    related (run delay.machine.mealy b (pre ++ suffix)).2
      (run redundant.machine.mealy (forward (run delay.machine.mealy b pre).2) suffix).2 := by
  rw [run_append]
  have h := finite_suffix (run delay.machine.mealy b pre).2
    (forward (run delay.machine.mealy b pre).2) rfl suffix
  exact ⟨congrArg ((run delay.machine.mealy b pre).1 ++ ·) h.1,h.2⟩

theorem delay_resources : delay.body.work = 3 ∧ delay.body.arena = 13 := ⟨rfl,rfl⟩
theorem redundant_resources : redundant.body.work = 9 ∧ redundant.body.arena = 46 := ⟨rfl,rfl⟩

/-- The preserved previous publication does not identify the continuation. -/
theorem reset_changes_future :
    (run delay.machine.mealy delay.initial [true]).1 = [false] ∧
    (run delay.machine.mealy (run delay.machine.mealy delay.initial [true]).2 [false]).1 = [true] ∧
    (run delay.machine.mealy delay.initial [false]).1 ≠ [true] := by decide

example : reverse (false,false) = none ∧ reverse (true,true) = none := by decide
example : (run redundant.machine.mealy (forward true) [false]).1 = [true] :=
  (finite_suffix true (forward true) rfl [false]).1.symm
example : (run redundant.machine.mealy (forward false) [true,false,true,true,false]).1 =
    [false,true,false,true,true] :=
  (finite_suffix false (forward false) rfl _).1.symm
example : related (run delay.machine.mealy false ([true] ++ [false])).2
    (run redundant.machine.mealy (forward (run delay.machine.mealy false [true]).2) [false]).2 :=
  (prefix_migration false [true] [false]).2

end FRPSpec.MigrationPair
