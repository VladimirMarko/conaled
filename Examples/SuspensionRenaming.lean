import Applications.Suspensions.Renaming
import Applications.Suspensions.AddressRange

/-!
# Old identities, new allocation identities and recursive captures

The small algebraic cases here precede the full execution transport. They
distinguish old address0 from shifted allocation1, include addresses inside
closures, and check that shadowed address entries are not SRec targets.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionRenaming
open Suspensions Suspensions.Core Suspensions.Core.Machine Suspensions.Core.Renaming

theorem old_and_new_addresses : shift 1 0 = 0 ∧ shift 1 1 = 2 ∧ shift 1 2 = 3 := by
  exact ⟨shift_old (by decide), shift_new (by decide), shift_new (by decide)⟩

def capturedClosure : Value Unit :=
  .closure [(.wildcard, .variable 7)] [(7, .address 0)] [(8, .address 1)]

theorem closure_contents_are_renamed :
    value (shift 1) capturedClosure =
      .closure [(.wildcard, .variable 7)] [(7, .address 0)] [(8, .address 2)] := by
  simp [capturedClosure, shift]

def shadowed : Env Unit := [(4, .atom (.integer 9)), (4, .address 0), (5, .address 1)]

theorem effective_recursive_addresses : addressRange shadowed = {1} := by
  ext address
  rw [mem_addressRange]
  constructor
  · rintro ⟨name, found⟩
    by_cases first : name = 4
    · subst name
      simp [shadowed] at found
    · by_cases second : name = 5
      · subst name
        simp [shadowed, Env.lookup] at found
        subst address
        simp
      · simp [shadowed, Env.lookup, first, second] at found
  · intro present
    have same : address = 1 := Finset.mem_singleton.mp present
    subst address
    exact ⟨5, rfl⟩

theorem recursive_unrolling_preserves_targets :
    addressRange (Env.rec shadowed) = {1} := by
  rw [addressRange_rec, effective_recursive_addresses]

end Examples.SuspensionRenaming
