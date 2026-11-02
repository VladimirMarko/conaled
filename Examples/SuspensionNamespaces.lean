import Applications.Suspensions.Namespace

/-! The two source identifier classes may use the same underlying index without
colliding in the core. An ordinary variable update preserves exception lookup. -/
set_option warningAsError true

namespace Examples.SuspensionNamespaces
open Suspensions.Core Suspensions.Core.Namespaces

def varBindings : Env Unit := [(3, .atom (.integer 7))]
def exceptions : Env Unit := [(3, .exception 19 none)]

theorem separate_lookup :
    Env.lookup (encode varBindings exceptions) (variableId 3) = some (.atom (.integer 7)) ∧
      Env.lookup (encode varBindings exceptions) (exceptionId 3) = some (.exception 19 none) := by
  exact ⟨lookup_variable varBindings exceptions 3, lookup_exception varBindings exceptions 3⟩

theorem variable_update_keeps_exception :
    Env.lookup
      (Env.extend (encode varBindings exceptions) (mapKeys variableId [(3, .atom (.integer 8))]))
      (exceptionId 3) = some (.exception 19 none) :=
  exceptions_after_variable_extension varBindings exceptions [(3, .atom (.integer 8))] 3

end Examples.SuspensionNamespaces
