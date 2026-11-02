import Mathlib.Data.List.Basic

/-!
# A core fragment for the suspension extension

The source boundary is Okasaki's thesis Appendix A over the 1990 Standard ML
core. This syntax retains strict application, ordered patterns, mutable
references, exceptions and finite recursive closures. It is not the complete
Standard ML grammar or elaborator. Ordinary primitive meanings are parameters.

Variables are natural-number names. Environments are finite association lists:
the first occurrence represents the binding, and extension gives the new
bindings precedence. References and suspensions use the same address constructor.
Unit is the empty record, as in the source, rather than an additional atom.
-/
set_option warningAsError true

namespace Suspensions.Core

inductive Atom where
  | boolean (value : Bool)
  | integer (value : Int)
  deriving DecidableEq, Repr

inductive Pattern where
  | wildcard
  | variable (name : Nat)
  | atom (value : Atom)
  | constructor (tag : Nat) (argument : Option Pattern)
  | exception (name : Nat) (argument : Option Pattern)
  | record (fields : List (Nat × Pattern))
  | reference (inner : Pattern)
  | suspended (inner : Pattern)
  | layered (name : Nat) (inner : Pattern)

/-- Runtime core syntax. Recursive bindings are further restricted by
`RecursiveRhs`; their left sides are variable names. Types are a separate layer. -/
inductive Expr (Primitive : Type) where
  | atom (value : Atom)
  | variable (name : Nat)
  | primitive (operation : Primitive)
  | constructor (tag : Nat) (argument : Option (Expr Primitive))
  | record (fields : List (Nat × Expr Primitive))
  | function (clauses : List (Pattern × Expr Primitive))
  | apply (function argument : Expr Primitive)
  | bind (pattern : Pattern) (value body : Expr Primitive)
  | recursive (bindings : List (Nat × Expr Primitive)) (body : Expr Primitive)
  | branch (condition yes no : Expr Primitive)
  | reference (value : Expr Primitive)
  | read (reference : Expr Primitive)
  | assign (reference value : Expr Primitive)
  | delay (body : Expr Primitive)
  | raise (exception : Expr Primitive)
  | handle (body : Expr Primitive) (clauses : List (Pattern × Expr Primitive))
  | newException (name : Nat) (body : Expr Primitive)

/-- Closures retain a finite recursive environment, as in Definition 6.6.
Application unrolls it once with `Env.rec`; no cyclic Lean value or fixed-point
axiom is needed. Cycles through suspension addresses remain possible. -/
inductive Value (Primitive : Type) where
  | atom (value : Atom)
  | constructor (tag : Nat) (argument : Option (Value Primitive))
  | record (fields : List (Nat × Value Primitive))
  | address (location : Nat)
  | closure (clauses : List (Pattern × Expr Primitive))
      (environment recursive : List (Nat × Value Primitive))
  | primitive (operation : Primitive)
  | exception (name : Nat) (argument : Option (Value Primitive))

abbrev Env (Primitive : Type) := List (Nat × Value Primitive)

namespace Env
variable {Primitive : Type}

def lookup : Env Primitive → Nat → Option (Value Primitive)
  | [], _ => none
  | (key, value) :: rest, name =>
      if name = key then some value else lookup rest name

/-- `base + additions` in the source: additions override the old bindings. -/
def extend (base additions : Env Primitive) : Env Primitive := additions ++ base

@[simp] theorem lookup_nil (name : Nat) :
    lookup ([] : Env Primitive) name = none := rfl

@[simp] theorem lookup_cons_eq (name : Nat) (v : Value Primitive) (rest : Env Primitive) :
    lookup ((name, v) :: rest) name = some v := by simp [lookup]

theorem lookup_cons_ne (name key : Nat) (v : Value Primitive) (rest : Env Primitive)
    (different : name ≠ key) :
    lookup ((key, v) :: rest) name = lookup rest name := by simp [lookup, different]

theorem lookup_extend (base additions : Env Primitive) (name : Nat) :
    lookup (extend base additions) name =
      (lookup additions name).orElse (fun _ => lookup base name) := by
  induction additions with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨key, value⟩
    by_cases eq : name = key
    · simp [extend, lookup, eq]
    · simpa [extend, lookup, eq] using ih

/-- One finite unrolling of the source's `Rec` operation. -/
def rec (bindings : Env Primitive) : Env Primitive :=
  bindings.map fun (name, value) => (name, match value with
    | .closure clauses environment _ => .closure clauses environment bindings
    | other => other)

def unrollValue (bindings : Env Primitive) : Value Primitive → Value Primitive
  | .closure clauses environment _ => .closure clauses environment bindings
  | other => other

theorem lookup_rec (bindings : Env Primitive) (name : Nat) :
    lookup (rec bindings) name = (lookup bindings name).map (unrollValue bindings) := by
  suffices general : ∀ (values : Env Primitive),
      lookup (values.map fun (key, value) => (key, unrollValue bindings value)) name =
        (lookup values name).map (unrollValue bindings) by
    simpa [rec, unrollValue] using general bindings
  intro values
  induction values with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨key, value⟩
    by_cases eq : name = key
    · simp [lookup, eq]
    · simpa [lookup, eq] using ih

theorem rec_domain (bindings : Env Primitive) (name : Nat) :
    lookup (rec bindings) name = none ↔ lookup bindings name = none := by
  rw [lookup_rec]
  simp

theorem rec_closure {bindings : Env Primitive} {name clauses environment recursive}
    (found : lookup bindings name = some (.closure clauses environment recursive)) :
    lookup (rec bindings) name = some (.closure clauses environment bindings) := by
  simp [lookup_rec, found, unrollValue]

theorem rec_address {bindings : Env Primitive} {name address}
    (found : lookup bindings name = some (.address address)) :
    lookup (rec bindings) name = some (.address address) := by
  simp [lookup_rec, found, unrollValue]

end Env

/-- The only additional recursive right side is a delayed expression. -/
inductive RecursiveRhs {Primitive : Type} : Expr Primitive → Prop
  | function (clauses) : RecursiveRhs (.function clauses)
  | delay (body) : RecursiveRhs (.delay body)

def recursiveRhs {Primitive : Type} : Expr Primitive → Bool
  | .function _ | .delay _ => true
  | _ => false

theorem recursiveRhs_iff {Primitive : Type} (e : Expr Primitive) :
    recursiveRhs e = true ↔ RecursiveRhs e := by
  constructor
  · intro accepted
    cases e <;> simp only [recursiveRhs, Bool.false_eq_true] at accepted
    · exact .function _
    · exact .delay _
  · intro accepted
    cases accepted <;> rfl

/-- `force` is derived from a suspension pattern, not a second primitive. -/
def force {Primitive : Type} (e : Expr Primitive) : Expr Primitive :=
  .apply (.function [(.suspended (.variable 0), .variable 0)]) e

/-- Ordered matching is inside the new suspension. The caller must choose
`fresh` absent from the free names of `clauses`; the static layer records this
hygiene obligation. Every selected right side has a suspension type. -/
def lazyFunction {Primitive : Type} (fresh : Nat)
    (clauses : List (Pattern × Expr Primitive)) : Expr Primitive :=
  .function [(.variable fresh,
    .delay (force (.apply (.function clauses) (.variable fresh))))]

end Suspensions.Core
