import Applications.Suspensions.Namespace

/-! The two source identifier classes may use the same underlying index without
colliding in the core. An ordinary variable update preserves exception lookup. -/
set_option warningAsError true

namespace Examples.SuspensionNamespaces
open Suspensions.Core Suspensions.Core.Namespaces

def variables : Env Unit := [(3, .atom (.integer 7))]
def exceptions : Env Unit := [(3, .exception 19 none)]

theorem separate_lookup :
    Env.lookup (encode variables exceptions) (variableId 3) = some (.atom (.integer 7)) ∧
      Env.lookup (encode variables exceptions) (exceptionId 3) = some (.exception 19 none) := by
  exact ⟨lookup_variable variables exceptions 3, lookup_exception variables exceptions 3⟩

theorem variable_update_keeps_exception :
    Env.lookup
      (Env.extend (encode variables exceptions) (mapKeys variableId [(3, .atom (.integer 8))]))
      (exceptionId 3) = some (.exception 19 none) :=
  exceptions_after_variable_extension variables exceptions [(3, .atom (.integer 8))] 3

end Examples.SuspensionNamespaces
