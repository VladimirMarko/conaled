import Applications.Collections.Map
import Mathlib.Data.List.AList

/-!
# The existing AList operations realize the Map contract

The standard carrier already contains unique-key evidence. Its insertion
prepends a binding after erasing the old one; it is not the ordered-list
insertion algorithm from FDSA. The concrete key decision does not impose value
equality, default values, ordered keys or a finite abstract model.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Collections.Maps

universe u v

/-- A thin adapter, retaining the actual standard association-list operations. -/
def alistOps (α : Type u) (β : Type v) [DecidableEq α] :
    Ops α β (AList (fun _ : α => β)) where
  empty := ∅
  update := AList.insert
  delete := AList.erase
  lookup m a := AList.lookup a m

/-- Key uniqueness is intrinsic to AList; no additional external invariant is
needed for its actual lookup, insertion and erasure operations. -/
theorem alist_laws (α : Type u) (β : Type v) [DecidableEq α] :
    Laws (alistOps α β) (fun _ => True) where
  empty_lookup := by
    funext a
    exact AList.lookup_empty a
  empty_valid := True.intro
  update_lookup _ _ m _ :=
    ⟨AList.lookup_insert m, fun _ hk => AList.lookup_insert_ne hk⟩
  update_valid _ _ _ _ := True.intro
  delete_lookup a m _ :=
    ⟨AList.lookup_erase a m, fun _ hk => AList.lookup_erase_ne hk⟩
  delete_valid _ _ _ := True.intro

end Collections.Maps
