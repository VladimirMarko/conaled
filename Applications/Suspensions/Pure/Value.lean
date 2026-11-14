import Applications.Suspensions.Pure.Syntax

/-!
# Finite values for an unshared suspension interpretation

A recursive group stores source right-hand sides and the earlier environment.
It never stores its newly created members. Each member instead carries the
same finite group descriptor. Unrolling constructs the same members over the
same capture on every use, including mutual function/suspension dependencies.

There is no heap, address, cache or evaluation judgment here. These value
constructors retain source code; the separate effect predicates restrict that
code when interpreting pure programs. The RHS wrapper records only the two
forms permitted by the source recursive-binding rule. Distinctness, nonempty
matches, identifier classification and typing remain separate obligations.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure

/-- The two permitted RHS shapes, with their original source payloads. -/
inductive Rhs (Primitive : Type) where
  | function (clauses : List (Core.Pattern × Core.Expr Primitive))
  | delay (body : Core.Expr Primitive)

namespace Rhs
variable {Primitive : Type}

def toExpr : Rhs Primitive → Core.Expr Primitive
  | .function clauses => .function clauses
  | .delay body => .delay body

def ofExpr : Core.Expr Primitive → Option (Rhs Primitive)
  | .function clauses => some (.function clauses)
  | .delay body => some (.delay body)
  | _ => none

@[simp] theorem ofExpr_toExpr (rhs : Rhs Primitive) : ofExpr rhs.toExpr = some rhs := by
  cases rhs <;> rfl

theorem toExpr_ofExpr {expression : Core.Expr Primitive} {rhs : Rhs Primitive}
    (decoded : ofExpr expression = some rhs) : rhs.toExpr = expression := by
  cases expression <;> simp_all [ofExpr, toExpr]
  all_goals exact congrArg toExpr decoded.symm

theorem toExpr_permitted (rhs : Rhs Primitive) : Core.RecursiveRhs rhs.toExpr := by
  cases rhs with
  | function clauses => exact .function clauses
  | delay body => exact .delay body

theorem ofExpr_success_iff (expression : Core.Expr Primitive) :
    (∃ rhs, ofExpr expression = some rhs) ↔ Core.RecursiveRhs expression := by
  constructor
  · rintro ⟨rhs, decoded⟩
    rw [← toExpr_ofExpr decoded]
    exact toExpr_permitted rhs
  · intro permitted
    cases permitted with
    | function clauses => exact ⟨.function clauses, rfl⟩
    | delay body => exact ⟨.delay body, rfl⟩

def toBindings (bindings : List (Nat × Rhs Primitive)) : List (Nat × Core.Expr Primitive) :=
  bindings.map fun (name, rhs) => (name, rhs.toExpr)

/-- Preserve source order and report the first unsupported right-hand side. -/
def ofBindings : List (Nat × Core.Expr Primitive) → Except Nat (List (Nat × Rhs Primitive))
  | [] => .ok []
  | (name, expression) :: rest => match ofExpr expression with
    | none => .error name
    | some rhs => (ofBindings rest).map fun decoded => (name, rhs) :: decoded

@[simp] theorem ofBindings_toBindings (bindings : List (Nat × Rhs Primitive)) :
    ofBindings (toBindings bindings) = .ok bindings := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨name, rhs⟩
      change ofBindings ((name, rhs.toExpr) :: toBindings rest) = .ok ((name, rhs) :: rest)
      rw [ofBindings, ofExpr_toExpr, ih]
      rfl

theorem toBindings_ofBindings {bindings : List (Nat × Core.Expr Primitive)}
    {decoded : List (Nat × Rhs Primitive)}
    (success : ofBindings bindings = .ok decoded) : toBindings decoded = bindings := by
  induction bindings generalizing decoded with
  | nil =>
      cases success
      rfl
  | cons binding rest ih =>
      rcases binding with ⟨name, expression⟩
      cases first : ofExpr expression with
      | none => simp [ofBindings, first] at success
      | some rhs =>
          cases following : ofBindings rest with
          | error invalid => simp [ofBindings, first, following, Except.map] at success
          | ok tail =>
              have decodedEq : (name, rhs) :: tail = decoded := by
                simpa [ofBindings, first, following, Except.map] using success
              subst decoded
              change (name, rhs.toExpr) :: toBindings tail = (name, expression) :: rest
              rw [toExpr_ofExpr first, ih following]

theorem toBindings_permitted (bindings : List (Nat × Rhs Primitive)) :
    List.Forall (fun binding => Core.RecursiveRhs binding.2) (toBindings bindings) := by
  induction bindings with
  | nil => trivial
  | cons binding rest ih =>
      rcases binding with ⟨name, rhs⟩
      change List.Forall (fun entry => Core.RecursiveRhs entry.2)
        ((name, rhs.toExpr) :: toBindings rest)
      exact (List.forall_cons _ _ _).mpr ⟨toExpr_permitted rhs, ih⟩

@[simp] theorem toBindings_names (bindings : List (Nat × Rhs Primitive)) :
    (toBindings bindings).map Prod.fst = bindings.map Prod.fst := by
  simp [toBindings, List.map_map]

end Rhs

mutual
  /-- Unshared values have explicit suspensions rather than heap addresses. -/
  inductive Value (Primitive : Type) where
    | atom (value : Core.Atom)
    | constructor (tag : Nat) (argument : Option (Value Primitive))
    | record (fields : List (Nat × Value Primitive))
    | closure (clauses : List (Core.Pattern × Core.Expr Primitive))
        (captured : List (Nat × Value Primitive)) (recursive : Option (Group Primitive))
    | suspension (body : Core.Expr Primitive)
        (captured : List (Nat × Value Primitive)) (recursive : Option (Group Primitive))
    | primitive (operation : Primitive)
    | exception (name : Nat) (argument : Option (Value Primitive))

  /-- No newly created member appears inside its descriptor. -/
  inductive Group (Primitive : Type) where
    | mk (bindings : List (Nat × Rhs Primitive)) (outer : List (Nat × Value Primitive))
end

abbrev Env (Primitive : Type) := List (Nat × Value Primitive)

namespace Env
variable {α β : Type}

/-- First binding wins, as in `Core.Env.lookup`. The element type is arbitrary
so the same operation also looks up source RHS wrappers. -/
def lookup : List (Nat × α) → Nat → Option α
  | [], _ => none
  | (key, value) :: rest, name => if name = key then some value else lookup rest name

def extend (base additions : List (Nat × α)) : List (Nat × α) := additions ++ base

@[simp] theorem lookup_nil (name : Nat) : lookup ([] : List (Nat × α)) name = none := rfl

@[simp] theorem lookup_cons_eq (name : Nat) (value : α) (rest : List (Nat × α)) :
    lookup ((name, value) :: rest) name = some value := by simp [lookup]

theorem lookup_cons_ne (name key : Nat) (value : α) (rest : List (Nat × α))
    (different : name ≠ key) : lookup ((key, value) :: rest) name = lookup rest name := by
  simp [lookup, different]

theorem lookup_extend (base additions : List (Nat × α)) (name : Nat) :
    lookup (extend base additions) name =
      (lookup additions name).orElse (fun _ => lookup base name) := by
  induction additions with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      by_cases same : name = key
      · simp [extend, lookup, same]
      · simpa [extend, lookup, same] using ih

theorem lookup_map (bindings : List (Nat × α)) (f : α → β) (name : Nat) :
    lookup (bindings.map fun (key, value) => (key, f value)) name =
      (lookup bindings name).map f := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      by_cases same : name = key
      · simp [lookup, same]
      · simpa [lookup, same] using ih

theorem lookup_eq_core {Primitive : Type} (environment : Core.Env Primitive) (name : Nat) :
    lookup environment name = Core.Env.lookup environment name := by
  induction environment with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      by_cases same : name = key
      · simp [lookup, Core.Env.lookup, same]
      · simpa [lookup, Core.Env.lookup, same] using ih

end Env

namespace Group
variable {Primitive : Type}

def bindings : Group Primitive → List (Nat × Rhs Primitive)
  | .mk definitions _ => definitions

def outer : Group Primitive → Env Primitive
  | .mk _ environment => environment

end Group

namespace Rhs
variable {Primitive : Type}

/-- A member retains the earlier capture and the same descriptor. It does not
recursively expand the other members while constructing this value. -/
def instantiate (group : Group Primitive) : Rhs Primitive → Value Primitive
  | .function clauses => .closure clauses group.outer (some group)
  | .delay body => .suspension body group.outer (some group)

@[simp] theorem instantiate_function (group : Group Primitive)
    (clauses : List (Core.Pattern × Core.Expr Primitive)) :
    instantiate group (.function clauses) = .closure clauses group.outer (some group) := rfl

@[simp] theorem instantiate_delay (group : Group Primitive) (body : Core.Expr Primitive) :
    instantiate group (.delay body) = .suspension body group.outer (some group) := rfl

end Rhs

namespace Group
variable {Primitive : Type}

/-- Creation prepends each binding, so the final member list reverses source
order. Source-valid groups have distinct names; raw lookup order is explicit. -/
def members (group : Group Primitive) : Env Primitive :=
  group.bindings.reverse.map fun (name, rhs) => (name, rhs.instantiate group)

theorem lookup_members (group : Group Primitive) (name : Nat) :
    Env.lookup group.members name =
      (Env.lookup group.bindings.reverse name).map (Rhs.instantiate group) :=
  Env.lookup_map group.bindings.reverse (Rhs.instantiate group) name

theorem lookup_function {group : Group Primitive} {name : Nat}
    {clauses : List (Core.Pattern × Core.Expr Primitive)}
    (found : Env.lookup group.bindings.reverse name = some (.function clauses)) :
    Env.lookup group.members name = some (.closure clauses group.outer (some group)) := by
  rw [lookup_members, found]
  rfl

theorem lookup_delay {group : Group Primitive} {name : Nat} {body : Core.Expr Primitive}
    (found : Env.lookup group.bindings.reverse name = some (.delay body)) :
    Env.lookup group.members name = some (.suspension body group.outer (some group)) := by
  rw [lookup_members, found]
  rfl

@[simp] theorem members_names (group : Group Primitive) :
    group.members.map Prod.fst = (group.bindings.map Prod.fst).reverse := by
  simp [members, List.map_map]

end Group

variable {Primitive : Type}

/-- Recursive members override the capture, exactly once on each use. The
descriptor and capture themselves remain unchanged. -/
def bodyEnvironment (captured : Env Primitive) : Option (Group Primitive) → Env Primitive
  | none => captured
  | some group => Env.extend captured group.members

@[simp] theorem bodyEnvironment_none (captured : Env Primitive) :
    bodyEnvironment captured none = captured := rfl

theorem bodyEnvironment_some (captured : Env Primitive) (group : Group Primitive) :
    bodyEnvironment captured (some group) = group.members ++ captured := rfl

theorem bodyEnvironment_lookup {captured : Env Primitive} {group : Group Primitive}
    {name : Nat} {value : Value Primitive}
    (found : Env.lookup group.members name = some value) :
    Env.lookup (bodyEnvironment captured (some group)) name = some value := by
  rw [bodyEnvironment, Env.lookup_extend, found]
  rfl

theorem bodyEnvironment_outer {captured : Env Primitive} {group : Group Primitive}
    {name : Nat} (absent : Env.lookup group.members name = none) :
    Env.lookup (bodyEnvironment captured (some group)) name = Env.lookup captured name := by
  rw [bodyEnvironment, Env.lookup_extend, absent]
  rfl

end Suspensions.Pure
