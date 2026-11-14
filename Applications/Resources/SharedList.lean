import Applications.Sequences.SharedList.Suffixes
import Applications.Resources.Growth

/-! Standard asymptotic interfaces for the exact structural visit and shared
result-cell counts proved in `Sequences.SharedList.suffixesRun_correct`.
The graph interpretation additionally uses `suffixesRun_reachable` and
`nonnull_nodup`; these counts do not describe a machine allocator. -/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.SharedList

theorem visits_linear :
    Asymptotics.IsBigO Filter.atTop (fun n : Nat => ((n + 1 : Nat) : ℝ))
      (fun n : Nat => (n : ℝ)) :=
  Resources.isBigO_of_nat_bound (fun n => n + 1) id 2 1 (by
    intro n hn
    change n + 1 ≤ 2 * n
    omega)

theorem space_linear :
    Asymptotics.IsBigO Filter.atTop (fun n : Nat => ((2 * n + 1 : Nat) : ℝ))
      (fun n : Nat => (n : ℝ)) :=
  Resources.isBigO_of_nat_bound (fun n => 2 * n + 1) id 3 1 (by
    intro n hn
    change 2 * n + 1 ≤ 3 * n
    omega)

end Resources.SharedList
