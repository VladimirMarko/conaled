import Applications.Suspensions.Syntax
import Mathlib.Data.Finmap
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Common

/-!
# The 1990 static attributes and the suspension extension

This is a typed core fragment, not a complete Standard ML elaborator. Its base
is the 1990 Definition, §§4.4, 4.7–4.8 and the core typing rules, extended by
Okasaki's thesis Appendix A. In particular, expansive bindings still generalize
fresh *applicative* variables. Suspension expressions are non-expansive even
when their bodies allocate references; no stronger value restriction is inserted.

Primitive and datatype-constructor signatures are explicit parameters. Unit is
the empty record. The two type-variable attributes are independent, and every
closed type is imperative, including a closed function type.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Static
open Core

/-- Equality and imperative status belong to a type variable, independently. -/
structure TyVar where
  name : Nat
  equality : Bool
  imperative : Bool
  deriving DecidableEq, Repr

inductive Ty where
  | variable (name : TyVar)
  | boolean
  | integer
  | exception
  | arrow (domain codomain : Ty)
  | reference (payload : Ty)
  | suspension (payload : Ty)
  | record (fields : List (Nat × Ty))
  | named (constructor : Nat) (arguments : List Ty)

namespace Ty

def unit : Ty := .record []

mutual
  def vars : Ty → Finset TyVar
    | .variable a => {a}
    | .boolean | .integer | .exception => ∅
    | .arrow a b => vars a ∪ vars b
    | .reference a | .suspension a => vars a
    | .record fields => fieldVars fields
    | .named _ arguments => argumentVars arguments
  termination_by t => sizeOf t
  decreasing_by all_goals simp_wf; omega

  def fieldVars : List (Nat × Ty) → Finset TyVar
    | [] => ∅
    | (_, t) :: rest => vars t ∪ fieldVars rest
  termination_by fields => sizeOf fields
  decreasing_by all_goals simp_wf; omega

  def argumentVars : List Ty → Finset TyVar
    | [] => ∅
    | t :: rest => vars t ∪ argumentVars rest
  termination_by arguments => sizeOf arguments
  decreasing_by all_goals simp_wf; omega
end

/-- Source imperative types may contain only imperative free variables. -/
def Imperative (t : Ty) : Prop := ∀ a ∈ vars t, a.imperative = true

/-- Source equality: references admit equality regardless of their payload.
Suspensions and functions have no equality constructor in this relation. -/
inductive AdmitsEquality (nameAdmits : Nat → Bool) : Ty → Prop
  | variable {a : TyVar} (allowed : a.equality = true) :
      AdmitsEquality nameAdmits (.variable a)
  | boolean : AdmitsEquality nameAdmits .boolean
  | integer : AdmitsEquality nameAdmits .integer
  | reference (payload : Ty) : AdmitsEquality nameAdmits (.reference payload)
  | record {fields : List (Nat × Ty)}
      (allowed : ∀ label t, (label, t) ∈ fields → AdmitsEquality nameAdmits t) :
      AdmitsEquality nameAdmits (.record fields)
  | named {name : Nat} {arguments : List Ty}
      (allowedName : nameAdmits name = true)
      (allowedArguments : ∀ t ∈ arguments, AdmitsEquality nameAdmits t) :
      AdmitsEquality nameAdmits (.named name arguments)

@[simp] theorem not_suspension_equality (names : Nat → Bool) (t : Ty) :
    ¬ AdmitsEquality names (.suspension t) := by
  intro impossible
  cases impossible

@[simp] theorem not_arrow_equality (names : Nat → Bool) (a b : Ty) :
    ¬ AdmitsEquality names (.arrow a b) := by
  intro impossible
  cases impossible

@[simp] theorem not_exception_equality (names : Nat → Bool) :
    ¬ AdmitsEquality names .exception := by
  intro impossible
  cases impossible

theorem closed_imperative {t : Ty} (closed : vars t = ∅) : Imperative t := by
  simp [Imperative, closed]

@[simp] theorem imperative_variable (a : TyVar) :
    Imperative (.variable a) ↔ a.imperative = true := by
  simp [Imperative, vars]

@[simp] theorem imperative_arrow (a b : Ty) :
    Imperative (.arrow a b) ↔ Imperative a ∧ Imperative b := by
  simp [Imperative, vars, or_imp, forall_and]

@[simp] theorem imperative_boolean : Imperative .boolean := by
  simp [Imperative, vars]

@[simp] theorem imperative_integer : Imperative .integer := by
  simp [Imperative, vars]

mutual
  /-- Simultaneous substitution; there are no type binders inside a monotype. -/
  def substitute (replacement : TyVar → Ty) : Ty → Ty
    | .variable a => replacement a
    | .boolean => .boolean
    | .integer => .integer
    | .exception => .exception
    | .arrow a b => .arrow (substitute replacement a) (substitute replacement b)
    | .reference a => .reference (substitute replacement a)
    | .suspension a => .suspension (substitute replacement a)
    | .record fields => .record (substituteFields replacement fields)
    | .named name arguments => .named name (substituteArguments replacement arguments)
  termination_by _ t => sizeOf t
  decreasing_by all_goals simp_wf; omega

  def substituteFields (replacement : TyVar → Ty) : List (Nat × Ty) → List (Nat × Ty)
    | [] => []
    | (label, t) :: rest =>
        (label, substitute replacement t) :: substituteFields replacement rest
  termination_by _ fields => sizeOf fields
  decreasing_by all_goals simp_wf; omega

  def substituteArguments (replacement : TyVar → Ty) : List Ty → List Ty
    | [] => []
    | t :: rest => substitute replacement t :: substituteArguments replacement rest
  termination_by _ arguments => sizeOf arguments
  decreasing_by all_goals simp_wf; omega
end

mutual
  @[simp] theorem substitute_identity (t : Ty) : substitute .variable t = t := by
    cases t with
    | variable a => rfl
    | boolean => rfl
    | integer => rfl
    | exception => rfl
    | arrow a b => simp only [substitute, substitute_identity a, substitute_identity b]
    | reference a => simp only [substitute, substitute_identity a]
    | suspension a => simp only [substitute, substitute_identity a]
    | record fields => simp only [substitute, substituteFields_identity fields]
    | named name arguments => simp only [substitute, substituteArguments_identity arguments]
  termination_by sizeOf t
  decreasing_by all_goals simp_wf; omega

  theorem substituteFields_identity (fields : List (Nat × Ty)) :
      substituteFields .variable fields = fields := by
    cases fields with
    | nil => rfl
    | cons pair rest =>
      rcases pair with ⟨label, t⟩
      simp only [substituteFields, substitute_identity t, substituteFields_identity rest]
  termination_by sizeOf fields
  decreasing_by all_goals simp_wf; omega

  theorem substituteArguments_identity (arguments : List Ty) :
      substituteArguments .variable arguments = arguments := by
    cases arguments with
    | nil => rfl
    | cons t rest =>
      simp only [substituteArguments, substitute_identity t, substituteArguments_identity rest]
  termination_by sizeOf arguments
  decreasing_by all_goals simp_wf; omega
end

end Ty

structure Scheme where
  quantified : Finset TyVar
  body : Ty

namespace Scheme

def mono (t : Ty) : Scheme := ⟨∅, t⟩

def freeVars (s : Scheme) : Finset TyVar := s.body.vars \ s.quantified

/-- Instantiation preserves each quantified variable's source attributes and
fixes every unquantified variable. Substitution is simultaneous. -/
def Instantiates (names : Nat → Bool) (s : Scheme) (result : Ty) : Prop :=
  ∃ replacement : TyVar → Ty,
    (∀ a, a ∉ s.quantified → replacement a = .variable a) ∧
    (∀ a ∈ s.quantified,
      (a.equality = true → Ty.AdmitsEquality names (replacement a)) ∧
      (a.imperative = true → Ty.Imperative (replacement a))) ∧
    Ty.substitute replacement s.body = result

@[simp] theorem freeVars_mono (t : Ty) : freeVars (mono t) = t.vars := by
  simp [freeVars, mono]

theorem mono_instantiates (names : Nat → Bool) (t : Ty) :
    Instantiates names (mono t) t := by
  refine ⟨.variable, ?_, ?_, Ty.substitute_identity t⟩
  · intro a _
    rfl
  · simp [mono]

end Scheme

/-- The 1990 classification, restricted to the core's source embeddings.
Boolean atoms embed datatype constructors; primitive symbols embed basis
variables. An applied constructor is an application, not a bare constructor. -/
def nonExpansive {Primitive : Type} : Expr Primitive → Bool
  | .variable _ | .primitive _ | .constructor _ none | .function _ | .delay _ => true
  | .atom (.boolean _) => true
  | _ => false

/-- Exact value-binding `Clos`: expansive expressions exclude imperative
variables, but still quantify fresh applicative variables. -/
def generalize {Primitive : Type} (contextVars : Finset TyVar)
    (expression : Expr Primitive) (t : Ty) : Scheme :=
  ⟨t.vars.filter (fun a => a ∉ contextVars ∧
      (nonExpansive expression = true ∨ a.imperative = false)), t⟩

theorem mem_generalize {Primitive : Type} (contextVars : Finset TyVar)
    (e : Expr Primitive) (t : Ty) (a : TyVar) :
    a ∈ (generalize contextVars e t).quantified ↔
      a ∈ t.vars ∧ a ∉ contextVars ∧
        (nonExpansive e = true ∨ a.imperative = false) := by
  simp [generalize]

theorem generalize_delay {Primitive : Type} (contextVars : Finset TyVar)
    (e : Expr Primitive) (t : Ty) :
    (generalize contextVars (.delay e) t).quantified = t.vars \ contextVars := by
  ext a
  simp [generalize, nonExpansive]

/-- Exception constructors remain monomorphic; the identifier's status is part
of the same finite environment as ordinary variables, matching runtime lookup. -/
inductive Binding where
  | variable (scheme : Scheme)
  | exception (argument : Option Ty)

namespace Binding

def freeVars : Binding → Finset TyVar
  | .variable scheme => scheme.freeVars
  | .exception none => ∅
  | .exception (some t) => t.vars

end Binding

abbrev Bindings := Finmap (fun _ : Nat => Binding)

namespace Bindings

def freeVars (bindings : Bindings) : Finset TyVar :=
  (⟨bindings.entries, bindings.nodup_entries⟩ : Finset (Sigma (fun _ : Nat => Binding))).biUnion
    (fun entry => entry.2.freeVars)

theorem mem_freeVars (bindings : Bindings) (a : TyVar) :
    a ∈ bindings.freeVars ↔ ∃ name binding,
      bindings.lookup name = some binding ∧ a ∈ binding.freeVars := by
  simp only [freeVars, Finset.mem_biUnion, Finset.mem_mk]
  constructor
  · rintro ⟨⟨name, binding⟩, entry, member⟩
    exact ⟨name, binding, Finmap.lookup_eq_some_iff.mpr entry, member⟩
  · rintro ⟨name, binding, entry, member⟩
    exact ⟨⟨name, binding⟩, Finmap.lookup_eq_some_iff.mp entry, member⟩

@[simp] theorem freeVars_empty : freeVars ∅ = ∅ := by
  ext a
  simp [mem_freeVars]

/-- Map values without changing keys, using Mathlib's finite-map equivalence. -/
def map (f : Binding → Binding) (bindings : Bindings) : Bindings :=
  Finmap.keysLookupEquiv.symm
    ⟨(bindings.keys, fun name => (bindings.lookup name).map f), by
      intro name
      simp [Finmap.lookup_isSome, Finmap.mem_keys]⟩

@[simp] theorem lookup_map (f : Binding → Binding) (bindings : Bindings) (name : Nat) :
    (bindings.map f).lookup name = (bindings.lookup name).map f := by
  simp [map]

@[simp] theorem map_empty (f : Binding → Binding) : map f ∅ = ∅ := by
  apply Finmap.ext_lookup
  intro name
  simp

end Bindings

structure Context where
  ambient : Finset TyVar := ∅
  values : Bindings := ∅

namespace Context

def empty : Context := ⟨∅, ∅⟩

def freeVars (context : Context) : Finset TyVar :=
  context.ambient ∪ context.values.freeVars

def extend (context : Context) (bindings : Bindings) : Context :=
  { context with values := bindings ∪ context.values }

def variable (context : Context) (name : Nat) (t : Ty) : Context :=
  context.extend (Finmap.singleton name (.variable (.mono t)))

def exception (context : Context) (name : Nat) (argument : Option Ty) : Context :=
  context.extend (Finmap.singleton name (.exception argument))

@[simp] theorem freeVars_empty : freeVars empty = ∅ := by
  simp [freeVars, empty]

@[simp] theorem extend_empty (context : Context) : context.extend ∅ = context := by
  simp [extend]

@[simp] theorem variable_lookup (context : Context) (name : Nat) (t : Ty) :
    (context.variable name t).values.lookup name = some (.variable (.mono t)) := by
  simp [variable, extend]

end Context

/-- Closure is applied only to variable bindings. Pattern typing below produces
monotypes; exception environments are never generalized by value binding. -/
def closeBindings {Primitive : Type} (context : Context) (e : Expr Primitive)
    (bindings : Bindings) : Bindings :=
  bindings.map fun binding => match binding with
    | .variable s => .variable (generalize context.freeVars e s.body)
    | .exception argument => .exception argument

@[simp] theorem closeBindings_empty {Primitive : Type} (context : Context) (e : Expr Primitive) :
    closeBindings context e ∅ = ∅ := by simp [closeBindings]

/-- Datatype and basis operation signatures are the bounded fragment's explicit
parameters. Clients must supply the relevant source signatures. -/
structure Signature (Primitive : Type) where
  equalityNames : Nat → Bool
  primitives : Primitive → Scheme
  constructors : Nat → Option Scheme

end Suspensions.Static
