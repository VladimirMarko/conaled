import Applications.Suspensions.Syntax
import Applications.Suspensions.Names
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
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def fieldVars : List (Nat × Ty) → Finset TyVar
    | [] => ∅
    | (_, t) :: rest => vars t ∪ fieldVars rest
  termination_by fields => sizeOf fields
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def argumentVars : List Ty → Finset TyVar
    | [] => ∅
    | t :: rest => vars t ∪ argumentVars rest
  termination_by arguments => sizeOf arguments
  decreasing_by
    all_goals simp_wf
    all_goals omega
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
  termination_by t => sizeOf t
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def substituteFields (replacement : TyVar → Ty) : List (Nat × Ty) → List (Nat × Ty)
    | [] => []
    | (label, t) :: rest =>
        (label, substitute replacement t) :: substituteFields replacement rest
  termination_by fields => sizeOf fields
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def substituteArguments (replacement : TyVar → Ty) : List Ty → List Ty
    | [] => []
    | t :: rest => substitute replacement t :: substituteArguments replacement rest
  termination_by arguments => sizeOf arguments
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  @[simp] theorem substitute_identity (t : Ty) : substitute .variable t = t := by
    cases t with
    | «variable» a => simp only [substitute]
    | boolean => simp only [substitute]
    | integer => simp only [substitute]
    | exception => simp only [substitute]
    | arrow a b => simp only [substitute, substitute_identity a, substitute_identity b]
    | reference a => simp only [substitute, substitute_identity a]
    | suspension a => simp only [substitute, substitute_identity a]
    | record fields => simp only [substitute, substituteFields_identity fields]
    | named name arguments => simp only [substitute, substituteArguments_identity arguments]
  termination_by sizeOf t
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem substituteFields_identity (fields : List (Nat × Ty)) :
      substituteFields .variable fields = fields := by
    cases fields with
    | nil => simp only [substituteFields]
    | cons pair rest =>
      rcases pair with ⟨label, t⟩
      simp only [substituteFields, substitute_identity t, substituteFields_identity rest]
  termination_by sizeOf fields
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem substituteArguments_identity (arguments : List Ty) :
      substituteArguments .variable arguments = arguments := by
    cases arguments with
    | nil => simp only [substituteArguments]
    | cons t rest =>
      simp only [substituteArguments, substitute_identity t, substituteArguments_identity rest]
  termination_by sizeOf arguments
  decreasing_by
    all_goals simp_wf
    all_goals omega
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

def bindVariable (context : Context) (name : Nat) (t : Ty) : Context :=
  context.extend (Finmap.singleton name (.variable (.mono t)))

def exception (context : Context) (name : Nat) (argument : Option Ty) : Context :=
  context.extend (Finmap.singleton name (.exception argument))

@[simp] theorem freeVars_empty : freeVars empty = ∅ := by
  simp [freeVars, empty]

@[simp] theorem extend_empty (context : Context) : context.extend ∅ = context := by
  simp [extend]

@[simp] theorem variable_lookup (context : Context) (name : Nat) (t : Ty) :
    (context.bindVariable name t).values.lookup name = some (.variable (.mono t)) := by
  simp [bindVariable, extend]

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

namespace Signature

/-- Supplied basis/datatype schemes contribute their free variables to the
persistent ambient scope. This is required when relating the bounded fragment's
Clos calculation to the source context, whose basis includes those schemes. -/
def ScopedIn {Primitive : Type} (signature : Signature Primitive) (context : Context) : Prop :=
  (∀ operation, (signature.primitives operation).freeVars ⊆ context.ambient) ∧
  (∀ tag scheme, signature.constructors tag = some scheme → scheme.freeVars ⊆ context.ambient)

theorem ScopedIn.extend {Primitive : Type} {signature : Signature Primitive}
    {context : Context} (support : signature.ScopedIn context) (bindings : Bindings) :
    signature.ScopedIn (context.extend bindings) := support

theorem ScopedIn.bindVariable {Primitive : Type} {signature : Signature Primitive}
    {context : Context} (support : signature.ScopedIn context) (name : Nat) (t : Ty) :
    signature.ScopedIn (context.bindVariable name t) := support

end Signature

namespace Scheme

/-- A useful specialization of simultaneous, attribute-preserving instantiation. -/
theorem instantiate_single (names : Nat → Bool) (a : TyVar) (body replacement : Ty)
    (equality : a.equality = true → Ty.AdmitsEquality names replacement)
    (imperative : a.imperative = true → Ty.Imperative replacement) :
    Instantiates names ⟨{a}, body⟩
      (Ty.substitute (fun b => if b = a then replacement else .variable b) body) := by
  refine ⟨(fun b => if b = a then replacement else .variable b), ?_, ?_, rfl⟩
  · intro b outside
    have different : b ≠ a := by simpa using outside
    simp [different]
  · intro b member
    have same : b = a := by simpa using member
    subst b
    simpa using And.intro equality imperative

end Scheme

namespace Bindings

theorem lookup_singleton (name key : Nat) (binding : Binding) :
    (Finmap.singleton key binding : Bindings).lookup name =
      if name = key then some binding else none := by
  by_cases same : name = key
  · subst name
    simp
  · rw [ite_eq_right same]
    apply Finmap.lookup_eq_none.mpr
    simpa using same

@[simp] theorem keys_map (f : Binding → Binding) (bindings : Bindings) :
    (bindings.map f).keys = bindings.keys := by
  simp [map]

@[simp] theorem map_singleton (f : Binding → Binding) (name : Nat) (binding : Binding) :
    Bindings.map f (Finmap.singleton name binding) = Finmap.singleton name (f binding) := by
  apply Finmap.ext_lookup
  intro key
  by_cases same : key = name <;> simp [lookup_singleton, same]

@[simp] theorem freeVars_singleton (name : Nat) (binding : Binding) :
    Bindings.freeVars (Finmap.singleton name binding) = binding.freeVars := by
  ext a
  rw [mem_freeVars]
  constructor
  · rintro ⟨key, value, found, member⟩
    have same : key = name := by
      have present := Finmap.mem_of_lookup_eq_some found
      simpa using present
    subst key
    have value_eq : value = binding := by simpa using found.symm
    subst value
    exact member
  · intro member
    exact ⟨name, binding, Finmap.lookup_singleton_eq, member⟩

end Bindings

namespace Context

/-- The 1990 lexical classification forbids a value pattern from binding an
identifier currently classified as an exception constructor (§2.4). -/
def VariableAllowed (context : Context) (name : Nat) : Prop :=
  ∀ argument, context.values.lookup name ≠ some (.exception argument)

@[simp] theorem variableAllowed_empty (name : Nat) : empty.VariableAllowed name := by
  simp [VariableAllowed, empty]

theorem variableAllowed_of_fresh (context : Context) (name : Nat)
    (fresh : name ∉ context.values.keys) : context.VariableAllowed name := by
  have missing : context.values.lookup name = none :=
    Finmap.lookup_eq_none.mpr (by simpa only [Finmap.mem_keys] using fresh)
  simp [VariableAllowed, missing]

@[simp] theorem variableAllowed_bound (context : Context) (name : Nat) (t : Ty) :
    (context.bindVariable name t).VariableAllowed name := by
  simp [VariableAllowed]

end Context

@[simp] theorem closeBindings_keys {Primitive : Type} (context : Context) (e : Expr Primitive)
    (bindings : Bindings) : (closeBindings context e bindings).keys = bindings.keys := by
  simp [closeBindings]

@[simp] theorem closeBindings_singleton {Primitive : Type} (context : Context)
    (e : Expr Primitive) (name : Nat) (t : Ty) :
    closeBindings context e (Finmap.singleton name (.variable (.mono t))) =
      Finmap.singleton name (.variable (generalize context.freeVars e t)) := by
  simp [closeBindings, Scheme.mono]

def atomType : Atom → Ty
  | .boolean _ => .boolean
  | .integer _ => .integer

/-! The judgments below use monotypes for pattern bindings. They omit modules,
type declarations, open rows and explicit type annotations. Value bindings are
the source U=∅ fragment; persistent scoped variables are retained in `ambient`.
Record type lists fix a representation of the corresponding finite row; no
claim of a complete row-equivalence elaborator is made. -/

mutual
  inductive PatternHasType {Primitive : Type} (signature : Signature Primitive) :
      Context → Pattern → Ty → Bindings → Prop
    | wildcard {context : Context} {t : Ty} :
        PatternHasType signature context .wildcard t ∅
    | variable {context : Context} {name : Nat} {t : Ty}
        (allowed : context.VariableAllowed name) :
        PatternHasType signature context (.variable name) t
          (Finmap.singleton name (.variable (.mono t)))
    | atom {context : Context} (value : Atom) :
        PatternHasType signature context (.atom value) (atomType value) ∅
    | constructor {context : Context} {tag name : Nat} {arguments : List Ty} {scheme : Scheme}
        (found : signature.constructors tag = some scheme)
        (instanceType : scheme.Instantiates signature.equalityNames (.named name arguments)) :
        PatternHasType signature context (.constructor tag none) (.named name arguments) ∅
    | constructor_argument {context : Context} {tag : Nat} {p : Pattern} {input output : Ty}
        {scheme : Scheme} {bindings : Bindings}
        (found : signature.constructors tag = some scheme)
        (instanceType : scheme.Instantiates signature.equalityNames (.arrow input output))
        (argument : PatternHasType signature context p input bindings) :
        PatternHasType signature context (.constructor tag (some p)) output bindings
    | exception {context : Context} {name : Nat}
        (found : context.values.lookup name = some (.exception none)) :
        PatternHasType signature context (.exception name none) .exception ∅
    | exception_argument {context : Context} {name : Nat} {p : Pattern} {t : Ty}
        {bindings : Bindings}
        (found : context.values.lookup name = some (.exception (some t)))
        (imperative : t.Imperative)
        (argument : PatternHasType signature context p t bindings) :
        PatternHasType signature context (.exception name (some p)) .exception bindings
    | record {context : Context} {fields : List (Nat × Pattern)}
        {types : List (Nat × Ty)} {bindings : Bindings}
        (labels : (fields.map Prod.fst).Nodup)
        (typed : PatternFieldsHaveType signature context fields types bindings) :
        PatternHasType signature context (.record fields) (.record types) bindings
    | reference {context : Context} {p : Pattern} {t : Ty} {bindings : Bindings}
        (imperative : t.Imperative)
        (inner : PatternHasType signature context p t bindings) :
        PatternHasType signature context (.reference p) (.reference t) bindings
    | suspended {context : Context} {p : Pattern} {t : Ty} {bindings : Bindings}
        (inner : PatternHasType signature context p t bindings) :
        PatternHasType signature context (.suspended p) (.suspension t) bindings
    | layered {context : Context} {name : Nat} {p : Pattern} {t : Ty} {bindings : Bindings}
        (allowed : context.VariableAllowed name)
        (fresh : name ∉ bindings.keys)
        (inner : PatternHasType signature context p t bindings) :
        PatternHasType signature context (.layered name p) t
          (Finmap.singleton name (.variable (.mono t)) ∪ bindings)

  inductive PatternFieldsHaveType {Primitive : Type} (signature : Signature Primitive) :
      Context → List (Nat × Pattern) → List (Nat × Ty) → Bindings → Prop
    | nil {context : Context} : PatternFieldsHaveType signature context [] [] ∅
    | cons {context : Context} {name : Nat} {p : Pattern} {rest : List (Nat × Pattern)}
        {t : Ty} {types : List (Nat × Ty)} {bindings restBindings : Bindings}
        (head : PatternHasType signature context p t bindings)
        (tail : PatternFieldsHaveType signature context rest types restBindings)
        (disjoint : Finmap.Disjoint bindings restBindings) :
        PatternFieldsHaveType signature context ((name, p) :: rest) ((name, t) :: types)
          (bindings ∪ restBindings)
end

mutual
  inductive HasType {Primitive : Type} (signature : Signature Primitive) :
      Context → Expr Primitive → Ty → Prop
    | atom {context : Context} (value : Atom) :
        HasType signature context (.atom value) (atomType value)
    | variable {context : Context} {name : Nat} {scheme : Scheme} {t : Ty}
        (found : context.values.lookup name = some (.variable scheme))
        (instanceType : scheme.Instantiates signature.equalityNames t) :
        HasType signature context (.variable name) t
    | exception {context : Context} {name : Nat}
        (found : context.values.lookup name = some (.exception none)) :
        HasType signature context (.variable name) .exception
    | exception_function {context : Context} {name : Nat} {t : Ty}
        (found : context.values.lookup name = some (.exception (some t)))
        (imperative : t.Imperative) :
        HasType signature context (.variable name) (.arrow t .exception)
    | primitive {context : Context} {operation : Primitive} {t : Ty}
        (instanceType : (signature.primitives operation).Instantiates signature.equalityNames t) :
        HasType signature context (.primitive operation) t
    | constructor {context : Context} {tag : Nat} {scheme : Scheme} {t : Ty}
        (found : signature.constructors tag = some scheme)
        (instanceType : scheme.Instantiates signature.equalityNames t) :
        HasType signature context (.constructor tag none) t
    | constructor_argument {context : Context} {tag : Nat} {e : Expr Primitive}
        {scheme : Scheme} {input output : Ty}
        (found : signature.constructors tag = some scheme)
        (instanceType : scheme.Instantiates signature.equalityNames (.arrow input output))
        (argument : HasType signature context e input) :
        HasType signature context (.constructor tag (some e)) output
    | record {context : Context} {fields : List (Nat × Expr Primitive)} {types : List (Nat × Ty)}
        (labels : (fields.map Prod.fst).Nodup)
        (typed : FieldsHaveType signature context fields types) :
        HasType signature context (.record fields) (.record types)
    | function {context : Context} {clauses : List (Pattern × Expr Primitive)} {input output : Ty}
        (nonempty : clauses ≠ [])
        (typed : ClausesHaveType signature context clauses input output) :
        HasType signature context (.function clauses) (.arrow input output)
    | apply {context : Context} {function argument : Expr Primitive} {input output : Ty}
        (operator : HasType signature context function (.arrow input output))
        (operand : HasType signature context argument input) :
        HasType signature context (.apply function argument) output
    | bind {context : Context} {p : Pattern} {value body : Expr Primitive}
        {input output : Ty} {bindings : Bindings}
        (right : HasType signature context value input)
        (pattern : PatternHasType signature context p input bindings)
        (continuation : HasType signature (context.extend (closeBindings context value bindings))
          body output) :
        HasType signature context (.bind p value body) output
    | recursive {context : Context} {bindings : List (Nat × Expr Primitive)}
        {body : Expr Primitive} {monotypes closed : Bindings} {output : Ty}
        (distinct : (bindings.map Prod.fst).Nodup)
        (domain : monotypes.keys = (bindings.map Prod.fst).toFinset)
        (definitions : RecursiveBindingsHaveType signature context monotypes bindings closed)
        (continuation : HasType signature (context.extend closed) body output) :
        HasType signature context (.recursive bindings body) output
    | branch {context : Context} {condition yes no : Expr Primitive} {t : Ty}
        (test : HasType signature context condition .boolean)
        (positive : HasType signature context yes t)
        (negative : HasType signature context no t) :
        HasType signature context (.branch condition yes no) t
    | reference {context : Context} {e : Expr Primitive} {t : Ty}
        (imperative : t.Imperative)
        (value : HasType signature context e t) :
        HasType signature context (.reference e) (.reference t)
    | read {context : Context} {e : Expr Primitive} {t : Ty}
        (reference : HasType signature context e (.reference t)) :
        HasType signature context (.read e) t
    | assign {context : Context} {reference value : Expr Primitive} {t : Ty}
        (target : HasType signature context reference (.reference t))
        (replacement : HasType signature context value t) :
        HasType signature context (.assign reference value) .unit
    | delay {context : Context} {e : Expr Primitive} {t : Ty}
        (body : HasType signature context e t) :
        HasType signature context (.delay e) (.suspension t)
    | raise {context : Context} {e : Expr Primitive} {t : Ty}
        (packet : HasType signature context e .exception) :
        HasType signature context (.raise e) t
    | handle {context : Context} {e : Expr Primitive} {clauses : List (Pattern × Expr Primitive)}
        {t : Ty} (body : HasType signature context e t)
        (nonempty : clauses ≠ [])
        (handlers : ClausesHaveType signature context clauses .exception t) :
        HasType signature context (.handle e clauses) t
    | newException {context : Context} {name : Nat} {e : Expr Primitive} {t : Ty}
        (body : HasType signature (context.exception name none) e t) :
        HasType signature context (.newException name e) t

  inductive ClausesHaveType {Primitive : Type} (signature : Signature Primitive) :
      Context → List (Pattern × Expr Primitive) → Ty → Ty → Prop
    | nil {context : Context} {input output : Ty} :
        ClausesHaveType signature context [] input output
    | cons {context : Context} {p : Pattern} {e : Expr Primitive}
        {rest : List (Pattern × Expr Primitive)} {input output : Ty} {bindings : Bindings}
        (pattern : PatternHasType signature context p input bindings)
        (body : HasType signature (context.extend bindings) e output)
        (tail : ClausesHaveType signature context rest input output) :
        ClausesHaveType signature context ((p, e) :: rest) input output

  inductive FieldsHaveType {Primitive : Type} (signature : Signature Primitive) :
      Context → List (Nat × Expr Primitive) → List (Nat × Ty) → Prop
    | nil {context : Context} : FieldsHaveType signature context [] []
    | cons {context : Context} {label : Nat} {e : Expr Primitive}
        {rest : List (Nat × Expr Primitive)} {t : Ty} {types : List (Nat × Ty)}
        (head : HasType signature context e t)
        (tail : FieldsHaveType signature context rest types) :
        FieldsHaveType signature context ((label, e) :: rest) ((label, t) :: types)

  inductive RecursiveBindingsHaveType {Primitive : Type} (signature : Signature Primitive) :
      Context → Bindings → List (Nat × Expr Primitive) → Bindings → Prop
    | nil {context : Context} {monotypes : Bindings} :
        RecursiveBindingsHaveType signature context monotypes [] ∅
    | cons {context : Context} {monotypes : Bindings} {name : Nat} {e : Expr Primitive}
        {rest : List (Nat × Expr Primitive)} {t : Ty} {closed : Bindings}
        (allowed : context.VariableAllowed name)
        (found : monotypes.lookup name = some (.variable (.mono t)))
        (permitted : RecursiveRhs e)
        (right : HasType signature (context.extend monotypes) e t)
        (tail : RecursiveBindingsHaveType signature context monotypes rest closed) :
        RecursiveBindingsHaveType signature context monotypes ((name, e) :: rest)
          (Finmap.insert name (.variable (generalize context.freeVars e t)) closed)
end

/-- Every representable payload has the derived force function's expected type.
The name condition is automatic in the checked even-variable/odd-exception
source embedding: generated name0 is a variable, never an exception identifier. -/
theorem force_function_type {Primitive : Type} (signature : Signature Primitive)
    (context : Context) (t : Ty) (allowed : context.VariableAllowed 0) :
    HasType signature context
      (.function [(.suspended (.variable 0), .variable 0)]) (.arrow (.suspension t) t) := by
  apply HasType.function (by simp)
  apply ClausesHaveType.cons (bindings := Finmap.singleton 0 (.variable (.mono t)))
  · exact .suspended (.variable allowed)
  · apply HasType.variable
    · exact context.variable_lookup 0 t
    · exact Scheme.mono_instantiates _ _
  · exact .nil

theorem force_type {Primitive : Type} (signature : Signature Primitive)
    {context : Context} {e : Expr Primitive} {t : Ty}
    (allowed : context.VariableAllowed 0) (typed : HasType signature context e (.suspension t)) :
    HasType signature context (force e) t := by
  exact .apply (force_function_type signature context t allowed) typed


namespace Context

theorem lookup_bindVariable_ne (context : Context) (bound key : Nat) (t : Ty)
    (different : key ≠ bound) :
    (context.bindVariable bound t).values.lookup key = context.values.lookup key := by
  apply Finmap.lookup_union_right
  simpa only [Finmap.mem_singleton] using different

theorem variableAllowed_bindVariable (context : Context) (bound key : Nat) (t : Ty)
    (allowed : context.VariableAllowed key) :
    (context.bindVariable bound t).VariableAllowed key := by
  intro argument found
  by_cases same : key = bound
  · subst key
    rw [variable_lookup] at found
    cases found
  · rw [lookup_bindVariable_ne context bound key t same] at found
    exact allowed argument found

theorem extend_fresh (context : Context) (bindings : Bindings) (name : Nat)
    (old : name ∉ context.values.keys) (added : name ∉ bindings.keys) :
    name ∉ (context.extend bindings).values.keys := by
  change name ∉ (bindings ∪ context.values).keys
  rw [Finmap.keys_union]
  exact Finset.notMem_union.mpr ⟨added, old⟩

theorem bindVariable_extend (context : Context) (bindings : Bindings) (name : Nat) (t : Ty)
    (fresh : name ∉ bindings.keys) :
    (context.extend bindings).bindVariable name t =
      (context.bindVariable name t).extend bindings := by
  have disjoint : Finmap.Disjoint (Finmap.singleton name (.variable (.mono t))) bindings := by
    intro key present
    have same : key = name := by simpa only [Finmap.mem_singleton] using present
    subst key
    simpa only [Finmap.mem_keys] using fresh
  have commute := Finmap.union_comm_of_disjoint disjoint
  cases context with
  | mk ambient values =>
    change Context.mk ambient
      (Finmap.singleton name (.variable (.mono t)) ∪ (bindings ∪ values)) =
      Context.mk ambient (bindings ∪ (Finmap.singleton name (.variable (.mono t)) ∪ values))
    rw [← Finmap.union_assoc, commute, Finmap.union_assoc]

/-- An added monotype contributes no new context variables when its variables
are already in the persistent ambient scope. Freshness prevents removal of an
old binding's free variables. -/
theorem freeVars_bindVariable (context : Context) (name : Nat) (t : Ty)
    (fresh : name ∉ context.values.keys) (contained : t.vars ⊆ context.ambient) :
    (context.bindVariable name t).freeVars = context.freeVars := by
  ext a
  constructor
  · intro member
    rcases Finset.mem_union.mp member with ambient | stored
    · exact Finset.mem_union_left _ ambient
    · obtain ⟨key, binding, found, used⟩ :=
        (Bindings.mem_freeVars (context.bindVariable name t).values a).mp stored
      by_cases same : key = name
      · subst key
        rw [variable_lookup] at found
        have equal : binding = .variable (.mono t) := Option.some.inj found.symm
        subst binding
        have inType : a ∈ t.vars := by
          simpa only [Binding.freeVars, Scheme.freeVars_mono] using used
        exact Finset.mem_union_left _ (contained inType)
      · rw [lookup_bindVariable_ne context name key t same] at found
        exact Finset.mem_union_right _ ((Bindings.mem_freeVars context.values a).mpr
          ⟨key, binding, found, used⟩)
  · intro member
    rcases Finset.mem_union.mp member with ambient | stored
    · exact Finset.mem_union_left _ ambient
    · obtain ⟨key, binding, found, used⟩ := (Bindings.mem_freeVars context.values a).mp stored
      have different : key ≠ name := by
        intro same
        subst key
        exact fresh (Finmap.mem_keys.mpr (Finmap.mem_of_lookup_eq_some found))
      exact Finset.mem_union_right _ ((Bindings.mem_freeVars
        (context.bindVariable name t).values a).mpr
          ⟨key, binding, (lookup_bindVariable_ne context name key t different).trans found, used⟩)

end Context

mutual
  theorem PatternHasType.bound_names {Primitive : Type} {signature : Signature Primitive}
      {context : Context} {p : Pattern} {t : Ty} {bindings : Bindings}
      (typed : PatternHasType signature context p t bindings) :
      bindings.keys ⊆ Names.patternNames p := by
    cases typed with
    | wildcard => simp
    | «variable» => simp [Names.patternNames]
    | atom => simp
    | constructor => simp
    | constructor_argument _ _ inner =>
      simpa only [Names.patternNames, Names.optionalPatternNames] using inner.bound_names
    | exception => simp
    | exception_argument _ _ inner =>
      rw [Names.patternNames, Names.optionalPatternNames]
      exact Finset.Subset.trans inner.bound_names Finset.subset_union_right
    | record _ fields => simpa only [Names.patternNames] using fields.bound_names
    | reference _ inner => simpa only [Names.patternNames] using inner.bound_names
    | suspended inner => simpa only [Names.patternNames] using inner.bound_names
    | @layered name p t bindings _ _ inner =>
      rw [Names.patternNames, Finmap.keys_union, Finmap.keys_singleton]
      exact Finset.union_subset_union (Finset.Subset.refl _) inner.bound_names
  termination_by sizeOf p
  decreasing_by
    all_goals simp_wf
    all_goals omega

  theorem PatternFieldsHaveType.bound_names {Primitive : Type} {signature : Signature Primitive}
      {context : Context} {fields : List (Nat × Pattern)} {types : List (Nat × Ty)}
      {bindings : Bindings} (typed : PatternFieldsHaveType signature context fields types bindings) :
      bindings.keys ⊆ Names.patternFieldNames fields := by
    cases typed with
    | nil => simp
    | cons head tail _ =>
      rw [Names.patternFieldNames, Finmap.keys_union]
      exact Finset.union_subset_union head.bound_names tail.bound_names
  termination_by sizeOf fields
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  theorem PatternHasType.weaken {Primitive : Type} {signature : Signature Primitive}
      {context : Context} {p : Pattern} {t : Ty} {bindings : Bindings}
      (typed : PatternHasType signature context p t bindings)
      (fresh : Nat) (addedType : Ty) (avoids : fresh ∉ Names.patternNames p) :
      PatternHasType signature (context.bindVariable fresh addedType) p t bindings := by
    generalize syntaxEq : p = whole at typed avoids ⊢
    cases typed with
    | wildcard => exact .wildcard
    | @«variable» name t allowed =>
      exact .variable (context.variableAllowed_bindVariable fresh name addedType allowed)
    | atom value => exact .atom value
    | constructor found instanceType => exact .constructor found instanceType
    | constructor_argument found instanceType inner =>
      exact .constructor_argument found instanceType (inner.weaken fresh addedType
        (by simpa only [Names.patternNames, Names.optionalPatternNames] using avoids))
    | @exception name found =>
      have different : name ≠ fresh := by
        simpa [Names.patternNames, Names.optionalPatternNames, eq_comm] using avoids
      exact .exception ((context.lookup_bindVariable_ne fresh name addedType different).trans found)
    | @exception_argument name p t bindings found imperative inner =>
      have parts : fresh ≠ name ∧ fresh ∉ Names.patternNames p := by
        simpa [Names.patternNames, Names.optionalPatternNames] using avoids
      exact .exception_argument
        ((context.lookup_bindVariable_ne fresh name addedType parts.1.symm).trans found)
        imperative (inner.weaken fresh addedType parts.2)
    | record labels fields => exact .record labels (fields.weaken fresh addedType
        (by simpa only [Names.patternNames] using avoids))
    | reference imperative inner => exact .reference imperative (inner.weaken fresh addedType
        (by simpa only [Names.patternNames] using avoids))
    | suspended inner => exact .suspended (inner.weaken fresh addedType
        (by simpa only [Names.patternNames] using avoids))
    | @layered name p t bindings allowed distinct inner =>
      rw [Names.patternNames] at avoids
      have innerAvoids : fresh ∉ Names.patternNames p :=
        (Finset.notMem_union.mp avoids).2
      exact .layered (context.variableAllowed_bindVariable fresh name addedType allowed)
        distinct (inner.weaken fresh addedType innerAvoids)
  termination_by sizeOf p
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

  theorem PatternFieldsHaveType.weaken {Primitive : Type} {signature : Signature Primitive}
      {context : Context} {fields : List (Nat × Pattern)} {types : List (Nat × Ty)}
      {bindings : Bindings} (typed : PatternFieldsHaveType signature context fields types bindings)
      (fresh : Nat) (addedType : Ty) (avoids : fresh ∉ Names.patternFieldNames fields) :
      PatternFieldsHaveType signature (context.bindVariable fresh addedType) fields types bindings := by
    generalize syntaxEq : fields = whole at typed avoids ⊢
    cases typed with
    | nil => exact .nil
    | cons head tail disjoint =>
      rw [Names.patternFieldNames] at avoids
      have parts := Finset.notMem_union.mp avoids
      exact .cons (head.weaken fresh addedType parts.1) (tail.weaken fresh addedType parts.2) disjoint
  termination_by sizeOf fields
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega
end

theorem RecursiveBindingsHaveType.domain {Primitive : Type} {signature : Signature Primitive}
    {context : Context} {monotypes : Bindings} {bindings : List (Nat × Expr Primitive)}
    {closed : Bindings}
    (typed : RecursiveBindingsHaveType signature context monotypes bindings closed) :
    closed.keys = (bindings.map Prod.fst).toFinset := by
  induction bindings generalizing closed with
  | nil =>
    cases typed
    rfl
  | cons pair rest ih =>
    cases typed with
    | cons _ _ _ _ tail =>
      ext name
      simp only [Finmap.mem_keys, Finmap.mem_insert, List.map_cons, List.toFinset_cons,
        Finset.mem_insert]
      rw [← Finmap.mem_keys, ih tail]

mutual
  /-- Source-sensitive weakening. A fresh term binder alone is insufficient:
  its free type variables must already belong to the persistent ambient scope. -/
  theorem HasType.weaken {Primitive : Type} {signature : Signature Primitive}
      {context : Context} {e : Expr Primitive} {t : Ty}
      (typed : HasType signature context e t) (fresh : Nat) (addedType : Ty)
      (freshContext : fresh ∉ context.values.keys)
      (support : addedType.vars ⊆ context.ambient)
      (avoids : fresh ∉ Names.expressionNames e) :
      HasType signature (context.bindVariable fresh addedType) e t := by
    generalize syntaxEq : e = whole at typed avoids ⊢
    cases typed with
    | atom value => exact .atom value
    | @«variable» context name scheme t found instanceType =>
      have different : name ≠ fresh := by
        simpa only [Names.expressionNames, Finset.mem_singleton, ne_eq, eq_comm] using avoids
      exact .variable
        ((context.lookup_bindVariable_ne fresh name addedType different).trans found) instanceType
    | @exception context name found =>
      have different : name ≠ fresh := by
        simpa only [Names.expressionNames, Finset.mem_singleton, ne_eq, eq_comm] using avoids
      exact .exception ((context.lookup_bindVariable_ne fresh name addedType different).trans found)
    | @exception_function context name t found imperative =>
      have different : name ≠ fresh := by
        simpa only [Names.expressionNames, Finset.mem_singleton, ne_eq, eq_comm] using avoids
      exact .exception_function
        ((context.lookup_bindVariable_ne fresh name addedType different).trans found) imperative
    | primitive instanceType => exact .primitive instanceType
    | constructor found instanceType => exact .constructor found instanceType
    | constructor_argument found instanceType argument =>
      exact .constructor_argument found instanceType
        (argument.weaken fresh addedType freshContext support
          (by simpa only [Names.expressionNames, Names.optionalExpressionNames] using avoids))
    | record labels fields =>
      exact .record labels (fields.weaken fresh addedType freshContext support
        (by simpa only [Names.expressionNames] using avoids))
    | function nonempty clauses =>
      exact .function nonempty (clauses.weaken fresh addedType freshContext support
        (by simpa only [Names.expressionNames] using avoids))
    | apply operator operand =>
      rw [Names.expressionNames] at avoids
      have parts := Finset.notMem_union.mp avoids
      exact .apply (operator.weaken fresh addedType freshContext support parts.1)
        (operand.weaken fresh addedType freshContext support parts.2)
    | @bind context p value body input output bindings right pattern continuation =>
      rw [Names.expressionNames] at avoids
      have parts := Finset.notMem_union.mp avoids
      have firstParts := Finset.notMem_union.mp parts.1
      have freshBindings : fresh ∉ bindings.keys := fun member =>
        firstParts.1 (pattern.bound_names member)
      have freshClosed : fresh ∉ (closeBindings context value bindings).keys := by
        simpa only [closeBindings_keys] using freshBindings
      have closeSame : closeBindings (context.bindVariable fresh addedType) value bindings =
          closeBindings context value bindings := by
        unfold closeBindings
        rw [context.freeVars_bindVariable fresh addedType freshContext support]
      refine .bind (right.weaken fresh addedType freshContext support firstParts.2)
        (pattern.weaken fresh addedType firstParts.1) ?_
      rw [closeSame, ← context.bindVariable_extend (closeBindings context value bindings)
        fresh addedType freshClosed]
      exact continuation.weaken fresh addedType
        (context.extend_fresh _ fresh freshContext freshClosed) support parts.2
    | @recursive context bindings body monotypes closed output distinct domain definitions continuation =>
      rw [Names.expressionNames] at avoids
      have parts := Finset.notMem_union.mp avoids
      have freshMonotypes : fresh ∉ monotypes.keys := by
        intro member
        apply parts.1
        apply Names.recursive_binders_subset bindings
        rwa [← domain]
      have freshClosed : fresh ∉ closed.keys := by
        intro member
        apply parts.1
        apply Names.recursive_binders_subset bindings
        rwa [← definitions.domain]
      refine .recursive distinct domain
        (definitions.weaken fresh addedType freshContext freshMonotypes support parts.1) ?_
      rw [← context.bindVariable_extend closed fresh addedType freshClosed]
      exact continuation.weaken fresh addedType
        (context.extend_fresh closed fresh freshContext freshClosed) support parts.2
    | branch test positive negative =>
      rw [Names.expressionNames] at avoids
      have parts := Finset.notMem_union.mp avoids
      have firstParts := Finset.notMem_union.mp parts.1
      exact .branch (test.weaken fresh addedType freshContext support firstParts.1)
        (positive.weaken fresh addedType freshContext support firstParts.2)
        (negative.weaken fresh addedType freshContext support parts.2)
    | reference imperative value =>
      exact .reference imperative (value.weaken fresh addedType freshContext support
        (by simpa only [Names.expressionNames] using avoids))
    | read reference => exact .read (reference.weaken fresh addedType freshContext support
        (by simpa only [Names.expressionNames] using avoids))
    | assign target replacement =>
      rw [Names.expressionNames] at avoids
      have parts := Finset.notMem_union.mp avoids
      exact .assign (target.weaken fresh addedType freshContext support parts.1)
        (replacement.weaken fresh addedType freshContext support parts.2)
    | delay body => exact .delay (body.weaken fresh addedType freshContext support
        (by simpa only [Names.expressionNames] using avoids))
    | raise packet => exact .raise (packet.weaken fresh addedType freshContext support
        (by simpa only [Names.expressionNames] using avoids))
    | handle body nonempty handlers =>
      rw [Names.expressionNames] at avoids
      have parts := Finset.notMem_union.mp avoids
      exact .handle (body.weaken fresh addedType freshContext support parts.1) nonempty
        (handlers.weaken fresh addedType freshContext support parts.2)
    | @newException context name e t body =>
      have parts : fresh ≠ name ∧ fresh ∉ Names.expressionNames e := by
        simpa only [Names.expressionNames, Finset.notMem_union, Finset.mem_singleton] using avoids
      have freshBinding : fresh ∉
          (Finmap.singleton name (.exception none) : Bindings).keys := by
        simpa only [Finmap.keys_singleton, Finset.mem_singleton] using parts.1
      apply HasType.newException
      change HasType signature ((context.bindVariable fresh addedType).extend
        (Finmap.singleton name (.exception none))) e t
      rw [← context.bindVariable_extend _ fresh addedType freshBinding]
      exact body.weaken fresh addedType
        (context.extend_fresh _ fresh freshContext freshBinding) support parts.2
  termination_by sizeOf e
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

  theorem ClausesHaveType.weaken {Primitive : Type} {signature : Signature Primitive}
      {context : Context} {clauses : List (Pattern × Expr Primitive)} {input output : Ty}
      (typed : ClausesHaveType signature context clauses input output)
      (fresh : Nat) (addedType : Ty) (freshContext : fresh ∉ context.values.keys)
      (support : addedType.vars ⊆ context.ambient)
      (avoids : fresh ∉ Names.clauseNames clauses) :
      ClausesHaveType signature (context.bindVariable fresh addedType) clauses input output := by
    generalize syntaxEq : clauses = whole at typed avoids ⊢
    cases typed with
    | nil => exact .nil
    | @cons context p e rest input output bindings pattern body tail =>
      rw [Names.clauseNames] at avoids
      have parts := Finset.notMem_union.mp avoids
      have firstParts := Finset.notMem_union.mp parts.1
      have freshBindings : fresh ∉ bindings.keys := fun member =>
        firstParts.1 (pattern.bound_names member)
      refine .cons (pattern.weaken fresh addedType firstParts.1) ?_
        (tail.weaken fresh addedType freshContext support parts.2)
      rw [← context.bindVariable_extend bindings fresh addedType freshBindings]
      exact body.weaken fresh addedType
        (context.extend_fresh bindings fresh freshContext freshBindings) support firstParts.2
  termination_by sizeOf clauses
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

  theorem FieldsHaveType.weaken {Primitive : Type} {signature : Signature Primitive}
      {context : Context} {fields : List (Nat × Expr Primitive)} {types : List (Nat × Ty)}
      (typed : FieldsHaveType signature context fields types)
      (fresh : Nat) (addedType : Ty) (freshContext : fresh ∉ context.values.keys)
      (support : addedType.vars ⊆ context.ambient)
      (avoids : fresh ∉ Names.expressionFieldNames fields) :
      FieldsHaveType signature (context.bindVariable fresh addedType) fields types := by
    generalize syntaxEq : fields = whole at typed avoids ⊢
    cases typed with
    | nil => exact .nil
    | cons head tail =>
      rw [Names.expressionFieldNames] at avoids
      have parts := Finset.notMem_union.mp avoids
      exact .cons (head.weaken fresh addedType freshContext support parts.1)
        (tail.weaken fresh addedType freshContext support parts.2)
  termination_by sizeOf fields
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

  theorem RecursiveBindingsHaveType.weaken {Primitive : Type} {signature : Signature Primitive}
      {context : Context} {monotypes : Bindings} {bindings : List (Nat × Expr Primitive)}
      {closed : Bindings}
      (typed : RecursiveBindingsHaveType signature context monotypes bindings closed)
      (fresh : Nat) (addedType : Ty) (freshContext : fresh ∉ context.values.keys)
      (freshMonotypes : fresh ∉ monotypes.keys)
      (support : addedType.vars ⊆ context.ambient)
      (avoids : fresh ∉ Names.recursiveNames bindings) :
      RecursiveBindingsHaveType signature (context.bindVariable fresh addedType)
        monotypes bindings closed := by
    generalize syntaxEq : bindings = whole at typed avoids ⊢
    cases typed with
    | nil => exact .nil
    | @cons context monotypes name e rest t closed allowed found permitted right tail =>
      rw [Names.recursiveNames] at avoids
      have parts := Finset.notMem_union.mp avoids
      have firstParts := Finset.notMem_union.mp parts.1
      have generalizeSame : generalize (context.bindVariable fresh addedType).freeVars e t =
          generalize context.freeVars e t := by
        rw [context.freeVars_bindVariable fresh addedType freshContext support]
      rw [← generalizeSame]
      refine .cons (context.variableAllowed_bindVariable fresh name addedType allowed)
        found permitted ?_
        (tail.weaken fresh addedType freshContext freshMonotypes support parts.2)
      rw [← context.bindVariable_extend monotypes fresh addedType freshMonotypes]
      exact right.weaken fresh addedType
        (context.extend_fresh monotypes fresh freshContext freshMonotypes) support firstParts.2
  termination_by sizeOf bindings
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega
end

/-- Book lazy-function sugar preserves the clause type and places its ordered
matching inside the newly delayed body. Its operational formation contract is
proved separately for the source machine. -/
theorem lazyFunction_type {Primitive : Type} (signature : Signature Primitive)
    {context : Context} {clauses : List (Pattern × Expr Primitive)} {input result : Ty}
    (typed : ClausesHaveType signature context clauses input (.suspension result))
    (nonempty : clauses ≠ []) (fresh : Nat)
    (freshContext : fresh ∉ context.values.keys)
    (freshClauses : fresh ∉ Names.clauseNames clauses)
    (support : input.vars ⊆ context.ambient)
    (forceName : context.VariableAllowed 0) :
    HasType signature context (lazyFunction fresh clauses) (.arrow input (.suspension result)) := by
  apply HasType.function (by simp)
  apply ClausesHaveType.cons (bindings := Finmap.singleton fresh (.variable (.mono input)))
  · exact .variable (context.variableAllowed_of_fresh fresh freshContext)
  · apply HasType.delay
    apply force_type signature
      (context.variableAllowed_bindVariable fresh 0 input forceName)
    apply HasType.apply
    · exact .function nonempty (typed.weaken fresh input freshContext support freshClauses)
    · exact .variable (context.variable_lookup fresh input) (Scheme.mono_instantiates _ _)
  · exact .nil

theorem lazyFunction_fresh_type {Primitive : Type} (signature : Signature Primitive)
    {context : Context} {clauses : List (Pattern × Expr Primitive)} {input result : Ty}
    (typed : ClausesHaveType signature context clauses input (.suspension result))
    (nonempty : clauses ≠ []) (support : input.vars ⊆ context.ambient)
    (forceName : context.VariableAllowed 0) :
    HasType signature context
      (lazyFunction (Names.fresh context.values.keys clauses) clauses)
      (.arrow input (.suspension result)) :=
  lazyFunction_type signature typed nonempty _
    (Names.fresh_context _ _) (Names.fresh_clauses _ _) support forceName

end Suspensions.Static
