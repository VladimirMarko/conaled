import Applications.Collections.Map

/-!
# The Map interface with a single modifying operation

FDSA Exercise 6.2 replaces update and delete with a callback on the selected
optional value. These translations use only interface operations. Their laws
are about values and validity, not callback evaluation counts or state identity.
Source provenance and the retained Isabelle notice are in
`Applications.Collections.Map`.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Collections.Maps.Modify

universe u v w

/-- The replacement interface retains the original empty and lookup fields. -/
structure Ops (α : Type u) (β : Type v) (M : Type w) where
  empty : M
  modify : α → (Option β → Option β) → M → M
  lookup : M → α → Option β

variable {α : Type u} {β : Type v} {M : Type w}

/-- The four modified laws allow callbacks that create a value from `none`. -/
structure Laws (ops : Ops α β M) (Valid : M → Prop) : Prop where
  empty_lookup : ops.lookup ops.empty = fun _ => none
  empty_valid : Valid ops.empty
  modify_lookup : ∀ a f m, Valid m →
    ops.lookup (ops.modify a f m) a = f (ops.lookup m a) ∧
      ∀ k, k ≠ a → ops.lookup (ops.modify a f m) k = ops.lookup m k
  modify_valid : ∀ a f m, Valid m → Valid (ops.modify a f m)

/-- Constant callbacks implement the original two mutations. -/
def toMap (ops : Ops α β M) : Collections.Maps.Ops α β M where
  empty := ops.empty
  update a x := ops.modify a (fun _ => some x)
  delete a := ops.modify a (fun _ => none)
  lookup := ops.lookup

/-- The selected new optional value determines which original mutation runs.
There is no inspection of the state representation. -/
def ofMap (ops : Collections.Maps.Ops α β M) : Ops α β M where
  empty := ops.empty
  modify a f m :=
    match f (ops.lookup m a) with
    | none => ops.delete a m
    | some x => ops.update a x m
  lookup := ops.lookup

namespace Laws

variable {ops : Ops α β M} {Valid : M → Prop}

/-- Grouped pointwise semantics agrees with the exact exercise equation. -/
theorem lookup_modify_eq (h : Laws ops Valid) [DecidableEq α]
    (a : α) (f : Option β → Option β) {m : M} (hm : Valid m) :
    ops.lookup (ops.modify a f m) =
      Function.update (ops.lookup m) a (f (ops.lookup m a)) :=
  Function.eq_update_iff.2 (h.modify_lookup a f m hm)

/-- Every original Map law follows from the four modified laws. -/
theorem toMap (h : Laws ops Valid) : Collections.Maps.Laws (Modify.toMap ops) Valid where
  empty_lookup := h.empty_lookup
  empty_valid := h.empty_valid
  update_lookup a x m hm := h.modify_lookup a (fun _ => some x) m hm
  update_valid a x m hm := h.modify_valid a (fun _ => some x) m hm
  delete_lookup a m hm := h.modify_lookup a (fun _ => none) m hm
  delete_valid a m hm := h.modify_valid a (fun _ => none) m hm

end Laws

/-- Both cases use the semantic and invariant law of the selected actual
mutation. Empty and lookup are retained unchanged. -/
theorem ofMap_laws {ops : Collections.Maps.Ops α β M} {Valid : M → Prop}
    (h : Collections.Maps.Laws ops Valid) : Laws (ofMap ops) Valid where
  empty_lookup := h.empty_lookup
  empty_valid := h.empty_valid
  modify_lookup a f m hm := by
    cases hresult : f (ops.lookup m a) with
    | none => simpa only [ofMap, hresult] using h.delete_lookup a m hm
    | some x => simpa only [ofMap, hresult] using h.update_lookup a x m hm
  modify_valid a f m hm := by
    cases hresult : f (ops.lookup m a) with
    | none => simpa only [ofMap, hresult] using h.delete_valid a m hm
    | some x => simpa only [ofMap, hresult] using h.update_valid a x m hm

/-- The constant callbacks select their branches by reduction, so this round
trip recovers all original operations even on invalid raw states. -/
theorem toMap_ofMap (ops : Collections.Maps.Ops α β M) : toMap (ofMap ops) = ops := by
  cases ops
  rfl

namespace Laws

variable {ops : Ops α β M} {Valid : M → Prop}

/-- Reconstructing a lawful modifying operation preserves output validity. -/
theorem roundTrip_valid (h : Laws ops Valid)
    (a : α) (f : Option β → Option β) {m : M} (hm : Valid m) :
    Valid ((ofMap (Modify.toMap ops)).modify a f m) :=
  (ofMap_laws h.toMap).modify_valid a f m hm

/-- The reverse round trip preserves every lookup on valid input. It does not
assert equality of the resulting concrete states. -/
theorem roundTrip_lookup (h : Laws ops Valid)
    (a : α) (f : Option β → Option β) {m : M} (hm : Valid m) :
    ops.lookup ((ofMap (Modify.toMap ops)).modify a f m) =
      ops.lookup (ops.modify a f m) := by
  classical
  calc
    ops.lookup ((ofMap (Modify.toMap ops)).modify a f m) =
        Function.update (ops.lookup m) a (f (ops.lookup m a)) :=
      (ofMap_laws h.toMap).lookup_modify_eq a f hm
    _ = ops.lookup (ops.modify a f m) := (h.lookup_modify_eq a f hm).symm

end Laws
end Collections.Maps.Modify
