import Applications.Sequences.Symmetric.Observation

/-! An operation-only FIFO client and relational implementations. The relation
need not be functional; all public observations must respect it. -/
namespace Sequences.AbstractFIFO
universe u

structure Ops (α Q : Type u) where
  empty : Q
  snoc : α → Q → Q
  tail : Q → Q
  head : Q → Option α

inductive Command (α : Type u) where
  | enqueue : α → Command α
  | delete : Command α
  deriving DecidableEq, Repr

variable {α Q R S : Type u}

def step (ops : Ops α Q) : Command α → Q → Q
  | .enqueue x => ops.snoc x
  | .delete => ops.tail

def run (ops : Ops α Q) : List (Command α) → Q → Q
  | [], q => q
  | c :: cs, q => run ops cs (step ops c q)

def client (ops : Ops α Q) (cs : List (Command α)) (q : Q) : Option α :=
  ops.head (run ops cs q)

/-- Behavior evidence is separate from the operations passed to a client. -/
structure Simulation (a : Ops α Q) (b : Ops α R) (rel : Q → R → Prop) : Prop where
  empty : rel a.empty b.empty
  snoc : ∀ x q r, rel q r → rel (a.snoc x q) (b.snoc x r)
  tail : ∀ q r, rel q r → rel (a.tail q) (b.tail r)
  head : ∀ q r, rel q r → a.head q = b.head r

namespace Simulation
variable {a : Ops α Q} {b : Ops α R} {rel : Q → R → Prop}

abbrev representation (rel : Q → R → Prop) : Relational.RelRep := ⟨Q, R, rel⟩

def stepSquare (h : Simulation a b rel) (c : Command α) :
    Relational.RelSquare (representation rel) (representation rel) where
  impl := step a c
  spec := step b c
  preserves := by
    intro q r hr
    cases c with
    | enqueue x => exact h.snoc x q r hr
    | delete => exact h.tail q r hr

def runSquare (h : Simulation a b rel) : List (Command α) →
    Relational.RelSquare (representation rel) (representation rel)
  | [] => Relational.identity _
  | c :: cs => Relational.compose (runSquare h cs) (stepSquare h c)

@[simp] theorem runSquare_impl (h : Simulation a b rel) (cs : List (Command α)) (q : Q) :
    (h.runSquare cs).impl q = run a cs q := by
  induction cs generalizing q with
  | nil => rfl
  | cons c cs ih => exact ih _

@[simp] theorem runSquare_spec (h : Simulation a b rel) (cs : List (Command α)) (r : R) :
    (h.runSquare cs).spec r = run b cs r := by
  induction cs generalizing r with
  | nil => rfl
  | cons c cs ih => exact ih _

theorem run_preserves (h : Simulation a b rel) (cs : List (Command α)) {q r}
    (hr : rel q r) : rel (run a cs q) (run b cs r) := by
  have hp := (h.runSquare cs).preserves hr
  change rel _ _ at hp
  simpa only [runSquare_impl, runSquare_spec] using hp

/-- One client proof, independent of either concrete state representation. -/
theorem client_eq (h : Simulation a b rel) (cs : List (Command α)) {q r}
    (hr : rel q r) : client a cs q = client b cs r :=
  h.head _ _ (h.run_preserves cs hr)

theorem client_empty (h : Simulation a b rel) (cs : List (Command α)) :
    client a cs a.empty = client b cs b.empty := h.client_eq cs h.empty

/-- Route composition retains the intermediate witness in the relation. -/
theorem comp {c : Ops α S} {next : R → S → Prop}
    (h : Simulation a b rel) (k : Simulation b c next) :
    Simulation a c (fun q s => ∃ r, rel q r ∧ next r s) where
  empty := ⟨b.empty, h.empty, k.empty⟩
  snoc x q s hr := by
    obtain ⟨r, hr, hs⟩ := hr
    exact ⟨b.snoc x r, h.snoc x q r hr, k.snoc x r s hs⟩
  tail q s hr := by
    obtain ⟨r, hr, hs⟩ := hr
    exact ⟨b.tail r, h.tail q r hr, k.tail r s hs⟩
  head q s hr := by
    obtain ⟨r, hr, hs⟩ := hr
    exact (h.head q r hr).trans (k.head r s hs)
/-- Reversing a simulation keeps both operation interpretations and reverses
only the representation relation. It supplies no inverse on states. -/
theorem reverse (h : Simulation a b rel) : Simulation b a (fun r q => rel q r) where
  empty := h.empty
  snoc x r q hr := h.snoc x q r hr
  tail r q hr := h.tail q r hr
  head r q hr := (h.head q r hr).symm

/-- All word clients ignore distinctions hidden by the common observation. -/
theorem representation_independent (h : Simulation a b rel) (cs : List (Command α))
    {q q' r} (hq : rel q r) (hq' : rel q' r) : client a cs q = client a cs q' :=
  (h.client_eq cs hq).trans (h.client_eq cs hq').symm
end Simulation

theorem run_append (ops : Ops α Q) (xs ys : List (Command α)) (q : Q) :
    run ops (xs ++ ys) q = run ops ys (run ops xs q) := by
  induction xs generalizing q with
  | nil => rfl
  | cons c cs ih => exact ih _

/-- Executing concatenated clients is horizontal pasting of their contracts. -/
theorem Simulation.runSquare_append {a : Ops α Q} {b : Ops α R} {rel : Q → R → Prop}
    (h : Simulation a b rel) (xs ys : List (Command α)) :
    h.runSquare (xs ++ ys) = Relational.compose (h.runSquare ys) (h.runSquare xs) := by
  apply Relational.RelSquare.ext
  · intro q
    change (h.runSquare (xs ++ ys)).impl q = (h.runSquare ys).impl ((h.runSquare xs).impl q)
    rw [h.runSquare_impl, h.runSquare_impl, h.runSquare_impl, run_append]
  · intro r
    change (h.runSquare (xs ++ ys)).spec r = (h.runSquare ys).spec ((h.runSquare xs).spec r)
    rw [h.runSquare_spec, h.runSquare_spec, h.runSquare_spec, run_append]

/-- Substituting a word for each command agrees with executing those words. -/
theorem run_flatMap (ops : Ops α Q) (replace : Command α → List (Command α))
    (cs : List (Command α)) (q : Q) :
    run ops (cs.flatMap replace) q = cs.foldl (fun s c => run ops (replace c) s) q := by
  induction cs generalizing q with
  | nil => rfl
  | cons c cs ih => simp only [List.flatMap_cons, run_append, List.foldl_cons]; exact ih _

def lists (α : Type u) : Ops α (List α) where
  empty := []
  snoc x xs := xs ++ [x]
  tail := List.tail
  head := List.head?

def symmetric (α : Type u) : Ops α (Symmetric.SymList α) where
  empty := Symmetric.nilSL
  snoc := Symmetric.snocSL
  tail := Symmetric.tailSL
  head := Symmetric.headSL

theorem lists_correct (α : Type u) : Simulation (lists α) (lists α) Eq where
  empty := rfl
  snoc _ _ _ h := congrArg _ h
  tail _ _ h := congrArg _ h
  head _ _ h := congrArg _ h

theorem symmetric_correct (α : Type u) : Simulation (symmetric α) (lists α)
    (Symmetric.representation α).Rel where
  empty := ⟨Symmetric.inv_nilSL, rfl⟩
  snoc x _ _ h := (Symmetric.snocSquare x).preserves h
  tail _ _ h := Symmetric.tailSquare.preserves h
  head _ _ h := Symmetric.headSquare.preserves h

end Sequences.AbstractFIFO
