import Applications.Suspensions.Syntax

/-!
# Distinct variable and exception namespaces

The 1990 Definition classifies identifier occurrences into disjoint variable
and exception-constructor classes. The concrete core uses natural-number keys;
this adapter realizes the distinction by disjoint injections. Values here are
already core values: this is an environment lookup/update adapter, not a claim
to translate arbitrary unencoded closure bodies or all Standard ML syntax.
-/
set_option warningAsError true

namespace Suspensions.Core.Namespaces
variable {Primitive : Type}

def variableId (name : Nat) : Nat := 2 * name
def exceptionId (name : Nat) : Nat := 2 * name + 1

theorem variableId_injective : Function.Injective variableId := by
  intro a b equal
  simp only [variableId] at equal
  omega

theorem exceptionId_injective : Function.Injective exceptionId := by
  intro a b equal
  simp only [exceptionId] at equal
  omega

theorem distinct (variable exception : Nat) : variableId variable ≠ exceptionId exception := by
  simp only [variableId, exceptionId]
  omega

def mapKeys (rename : Nat → Nat) (bindings : Env Primitive) : Env Primitive :=
  bindings.map fun (name, value) => (rename name, value)

theorem lookup_mapKeys (rename : Nat → Nat) (injective : Function.Injective rename)
    (bindings : Env Primitive) (name : Nat) :
    Env.lookup (mapKeys rename bindings) (rename name) = Env.lookup bindings name := by
  induction bindings with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨key, value⟩
    by_cases same : name = key
    · subst key
      simp [mapKeys, Env.lookup]
    · have different : rename name ≠ rename key := fun equal => same (injective equal)
      simpa [mapKeys, Env.lookup, same, different] using ih

theorem lookup_mapKeys_absent (rename : Nat → Nat) (bindings : Env Primitive) (name : Nat)
    (outside : ∀ key, name ≠ rename key) :
    Env.lookup (mapKeys rename bindings) name = none := by
  induction bindings with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨key, value⟩
    simpa [mapKeys, Env.lookup, outside key] using ih

def encode (variables exceptions : Env Primitive) : Env Primitive :=
  Env.extend (mapKeys exceptionId exceptions) (mapKeys variableId variables)

theorem lookup_variable (variables exceptions : Env Primitive) (name : Nat) :
    Env.lookup (encode variables exceptions) (variableId name) = Env.lookup variables name := by
  rw [encode, Env.lookup_extend, lookup_mapKeys variableId variableId_injective,
    lookup_mapKeys_absent exceptionId exceptions (variableId name) (distinct name)]
  cases Env.lookup variables name <;> rfl

theorem lookup_exception (variables exceptions : Env Primitive) (name : Nat) :
    Env.lookup (encode variables exceptions) (exceptionId name) = Env.lookup exceptions name := by
  rw [encode, Env.lookup_extend,
    lookup_mapKeys_absent variableId variables (exceptionId name)
      (fun key => Ne.symm (distinct key name))]
  exact lookup_mapKeys exceptionId exceptionId_injective exceptions name

theorem extend_variables (variables exceptions additions : Env Primitive) :
    Env.extend (encode variables exceptions) (mapKeys variableId additions) =
      encode (Env.extend variables additions) exceptions := by
  simp [encode, Env.extend, mapKeys, List.map_append, List.append_assoc]

theorem exceptions_after_variable_extension (variables exceptions additions : Env Primitive)
    (name : Nat) :
    Env.lookup (Env.extend (encode variables exceptions) (mapKeys variableId additions))
      (exceptionId name) = Env.lookup exceptions name := by
  rw [extend_variables, lookup_exception]

theorem variables_after_exception_extension (variables exceptions additions : Env Primitive)
    (name : Nat) :
    Env.lookup (Env.extend (encode variables exceptions) (mapKeys exceptionId additions))
      (variableId name) = Env.lookup variables name := by
  rw [Env.lookup_extend,
    lookup_mapKeys_absent exceptionId additions (variableId name) (distinct name)]
  exact lookup_variable variables exceptions name

end Suspensions.Core.Namespaces
