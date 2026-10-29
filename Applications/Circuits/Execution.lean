import Applications.Circuits.Correctness

/-! Executable circuit evaluation and a finite arena model. A reduction dispatches
one syntax node (including one Boolean gate at gate nodes). Each node reserves one
frame and copies its finite input/output values into a tick-local arena. The arena
is reclaimed between ticks. Work counts dispatches, not elapsed host time; cells
and frames are model units, not bytes allocated by Lean. -/
namespace Applications.Circuits
open FirstOrderCompiler

/-- Boolean cells in a value. Product shape is fixed program data. -/
def cells : Ty → Nat
  | .base => 1
  | .unit => 0
  | .prod a b => cells a + cells b

namespace Circuit
/-- No resource counters or trace are computed by this evaluator. -/
def execute : Circuit a b → Val Bool a → Val Bool b
  | .identity, x => x
  | .compose g f, x => execute g (execute f x)
  | .terminate, _ => ()
  | .first, x => x.1
  | .second, x => x.2
  | .pair f g, x => (execute f x, execute g x)
  | .gate p, x => p.meaning x

theorem execute_correct (c : Circuit a b) (x : Val Bool a) :
    c.execute x = c.digital.value x := by
  induction c with
  | identity => rfl
  | compose g f hg hf => simp only [execute, hf, hg]; rfl
  | terminate => rfl
  | first => rfl
  | second => rfl
  | pair f g hf hg => simp only [execute, hf, hg]; rfl
  | gate p => exact (gate_value p x).symm

/-- Fixed allocation charged at a node: its frame and finite input/output copies.
Keeping every node's allocation to tick end overestimates reuse. -/
def localSpace (a b : Ty) := 1 + cells a + cells b

def work : Circuit a b → Nat
  | .compose g f => work f + work g + 1
  | .pair f g => work f + work g + 1
  | _ => 1

def arena : {a b : Ty} → Circuit a b → Nat
  | a, b, .compose g f => arena f + arena g + localSpace a b
  | a, .prod b c, .pair f g => arena f + arena g + localSpace a (.prod b c)
  | a, b, _ => localSpace a b

/-- Big-step evaluation of the explicit copied-value arena machine. Allocation
includes every entered frame and intermediate, and is never reclaimed mid-tick.
Consequently the allocated total also bounds every intermediate arena prefix. -/
inductive Executes : {a b : Ty} → Circuit a b → Val Bool a → Val Bool b → Nat → Nat → Prop where
  | identity (x : Val Bool a) : Executes .identity x x 1 (localSpace a a)
  | terminate (x : Val Bool a) : Executes .terminate x () 1 (localSpace a .unit)
  | first (x : Val Bool (.prod a b)) : Executes .first x x.1 1 (localSpace (.prod a b) a)
  | second (x : Val Bool (.prod a b)) : Executes .second x x.2 1 (localSpace (.prod a b) b)
  | gate (p : Gate a b) (x : Val Bool a) : Executes (.gate p) x (p.meaning x) 1 (localSpace a b)
  | compose {f : Circuit a b} {g : Circuit b c}
      (hf : Executes f x y wf sf) (hg : Executes g y z wg sg) :
      Executes (.compose g f) x z (wf + wg + 1) (sf + sg + localSpace a c)
  | pair {f : Circuit a b} {g : Circuit a c}
      (hf : Executes f x y wf sf) (hg : Executes g x z wg sg) :
      Executes (.pair f g) x (y,z) (wf + wg + 1) (sf + sg + localSpace a (.prod b c))

theorem executes (c : Circuit a b) (x : Val Bool a) :
    Executes c x (c.execute x) c.work c.arena := by
  induction c with
  | identity => exact .identity x
  | compose g f hg hf => exact .compose (hf x) (hg _)
  | terminate => exact .terminate x
  | first => exact .first x
  | second => exact .second x
  | pair f g hf hg => exact .pair (hf x) (hg x)
  | gate p => exact .gate p x

theorem Executes.result {c : Circuit a b} (h : Executes c x y w s) :
    y = c.execute x ∧ w = c.work ∧ s = c.arena := by
  induction h with
  | identity => exact ⟨rfl,rfl,rfl⟩
  | terminate => exact ⟨rfl,rfl,rfl⟩
  | first => exact ⟨rfl,rfl,rfl⟩
  | second => exact ⟨rfl,rfl,rfl⟩
  | gate => exact ⟨rfl,rfl,rfl⟩
  | compose hf hg ihf ihg => rcases ihf with ⟨rfl,rfl,rfl⟩; rcases ihg with ⟨rfl,rfl,rfl⟩; exact ⟨rfl,rfl,rfl⟩
  | pair hf hg ihf ihg => rcases ihf with ⟨rfl,rfl,rfl⟩; rcases ihg with ⟨rfl,rfl,rfl⟩; exact ⟨rfl,rfl,rfl⟩

/-- Allocation schedule in evaluator order. This is proof data, never retained
by `execute`. Each tick starts with an empty arena. -/
def allocations : {a b : Ty} → Circuit a b → List Nat
  | a, b, .compose g f => [localSpace a b] ++ allocations f ++ allocations g
  | a, .prod b c, .pair f g => [localSpace a (.prod b c)] ++ allocations f ++ allocations g
  | a, b, _ => [localSpace a b]

theorem allocations_sum (c : Circuit a b) : c.allocations.sum = c.arena := by
  induction c <;> simp_all [allocations, arena, Nat.add_comm ]

private theorem take_sum_le (xs : List Nat) (n : Nat) : (xs.take n).sum ≤ xs.sum := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ n => simpa using Nat.add_le_add_left (ih n) x

/-- Every partial allocation schedule, including internal evaluation positions,
has the same bound. This covers temporary storage, not only tick endpoints. -/
theorem arena_prefix (c : Circuit a b) (n : Nat) :
    (c.allocations.take n).sum ≤ c.arena := by
  rw [← allocations_sum]
  exact take_sum_le _ _

end Circuit
end Applications.Circuits
