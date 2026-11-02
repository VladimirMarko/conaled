import Applications.Suspensions.Syntax
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Common

/-!
# Conservative name support for derived lazy functions

These finite sets deliberately include bound names as well as free names.
Exception-pattern identifiers are environment lookups and are included. Record
labels and datatype-constructor tags belong to different source namespaces and
are not term-environment identifiers. This is a sufficient freshness test, not
an exact free-variable calculation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Names
open Core

mutual
  def patternNames : Pattern → Finset Nat
    | .wildcard | .atom _ => ∅
    | .variable name => {name}
    | .constructor _ argument => optionalPatternNames argument
    | .exception name argument => {name} ∪ optionalPatternNames argument
    | .record fields => patternFieldNames fields
    | .reference inner | .suspended inner => patternNames inner
    | .layered name inner => {name} ∪ patternNames inner
  termination_by p => sizeOf p
  decreasing_by all_goals simp_wf

  def optionalPatternNames : Option Pattern → Finset Nat
    | none => ∅
    | some p => patternNames p
  termination_by argument => sizeOf argument
  decreasing_by all_goals simp_wf

  def patternFieldNames : List (Nat × Pattern) → Finset Nat
    | [] => ∅
    | (_, p) :: rest => patternNames p ∪ patternFieldNames rest
  termination_by fields => sizeOf fields
  decreasing_by all_goals simp_wf
end

mutual
  def expressionNames {Primitive : Type} : Expr Primitive → Finset Nat
    | .atom _ | .primitive _ => ∅
    | .variable name => {name}
    | .constructor _ argument => optionalExpressionNames argument
    | .record fields => expressionFieldNames fields
    | .function clauses => clauseNames clauses
    | .apply f a | .assign f a => expressionNames f ∪ expressionNames a
    | .bind p value body => patternNames p ∪ expressionNames value ∪ expressionNames body
    | .recursive bindings body => recursiveNames bindings ∪ expressionNames body
    | .branch condition yes no =>
        expressionNames condition ∪ expressionNames yes ∪ expressionNames no
    | .reference e | .read e | .delay e | .raise e => expressionNames e
    | .handle body clauses => expressionNames body ∪ clauseNames clauses
    | .newException name body => {name} ∪ expressionNames body
  termination_by e => sizeOf e
  decreasing_by all_goals simp_wf

  def optionalExpressionNames {Primitive : Type} : Option (Expr Primitive) → Finset Nat
    | none => ∅
    | some e => expressionNames e
  termination_by argument => sizeOf argument
  decreasing_by all_goals simp_wf

  def expressionFieldNames {Primitive : Type} : List (Nat × Expr Primitive) → Finset Nat
    | [] => ∅
    | (_, e) :: rest => expressionNames e ∪ expressionFieldNames rest
  termination_by fields => sizeOf fields
  decreasing_by all_goals simp_wf

  def clauseNames {Primitive : Type} : List (Pattern × Expr Primitive) → Finset Nat
    | [] => ∅
    | (p, e) :: rest => patternNames p ∪ expressionNames e ∪ clauseNames rest
  termination_by clauses => sizeOf clauses
  decreasing_by all_goals simp_wf

  def recursiveNames {Primitive : Type} : List (Nat × Expr Primitive) → Finset Nat
    | [] => ∅
    | (name, e) :: rest => {name} ∪ expressionNames e ∪ recursiveNames rest
  termination_by bindings => sizeOf bindings
  decreasing_by all_goals simp_wf
end

/-- One choice fresh for every conservative clause name and any supplied
context-name set. The latter can include all variable and exception bindings. -/
def fresh {Primitive : Type} (contextNames : Finset Nat)
    (clauses : List (Pattern × Expr Primitive)) : Nat :=
  (contextNames ∪ clauseNames clauses).sup id + 1

theorem fresh_not_mem {Primitive : Type} (contextNames : Finset Nat)
    (clauses : List (Pattern × Expr Primitive)) :
    fresh contextNames clauses ∉ contextNames ∪ clauseNames clauses := by
  intro member
  have bounded := Finset.le_sup (f := id) member
  change (contextNames ∪ clauseNames clauses).sup id + 1 ≤
    (contextNames ∪ clauseNames clauses).sup id at bounded
  omega

theorem fresh_context {Primitive : Type} (contextNames : Finset Nat)
    (clauses : List (Pattern × Expr Primitive)) :
    fresh contextNames clauses ∉ contextNames := by
  intro member
  exact fresh_not_mem contextNames clauses (Finset.mem_union_left _ member)

theorem fresh_clauses {Primitive : Type} (contextNames : Finset Nat)
    (clauses : List (Pattern × Expr Primitive)) :
    fresh contextNames clauses ∉ clauseNames clauses := by
  intro member
  exact fresh_not_mem contextNames clauses (Finset.mem_union_right _ member)


/-- Every recursive binder is included, even if its right side never uses it. -/
theorem recursive_binders_subset {Primitive : Type}
    (bindings : List (Nat × Expr Primitive)) :
    (bindings.map Prod.fst).toFinset ⊆ recursiveNames bindings := by
  induction bindings with
  | nil => simp
  | cons pair rest ih =>
    rcases pair with ⟨name, e⟩
    intro key member
    simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert] at member
    rcases member with same | tail
    · subst key
      simp [recursiveNames]
    · rw [recursiveNames]
      exact Finset.mem_union_right _ (ih tail)

end Suspensions.Names
