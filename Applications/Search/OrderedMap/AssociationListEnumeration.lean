import Applications.Search.OrderedMap.AssociationList
import Mathlib.Logic.Equiv.Defs

/-!
# Unique-key pair lists and the existing association-list map

The final VFA ADT exercise stores a list of ordinary key/value pairs with a
proof that its projected keys have no repetitions. Its elements operation is
the identity projection; it imposes no ordering on keys or payloads.

The executable update below uses the existing first-match `List.eraseP`.
The constant-family Sigma/product equivalence connects it exactly to Mathlib's
`AList.insert`. These conversions justify the proofs; the pair-list update does
not execute a conversion of the entire list. Resource accounting belongs to
the separate measured erasure realization.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedMap.AssociationListEnumeration

universe u v
variable {κ : Type u} {ν : Type v}

def toSigmaList (bindings : List (κ × ν)) : List (Sigma fun _ : κ => ν) :=
  bindings.map (Equiv.sigmaEquivProd κ ν).symm

def toPairList (bindings : List (Sigma fun _ : κ => ν)) : List (κ × ν) :=
  bindings.map (Equiv.sigmaEquivProd κ ν)

@[simp] theorem toPairList_toSigmaList (bindings : List (κ × ν)) :
    toPairList (toSigmaList bindings) = bindings := by
  simp [toPairList, toSigmaList, List.map_map, Function.comp_def]

@[simp] theorem toSigmaList_toPairList (bindings : List (Sigma fun _ : κ => ν)) :
    toSigmaList (toPairList bindings) = bindings := by
  simp [toPairList, toSigmaList, List.map_map, Function.comp_def]

@[simp] theorem keys_toSigmaList (bindings : List (κ × ν)) :
    (toSigmaList bindings).keys = bindings.map Prod.fst := by
  simp [toSigmaList, List.keys, List.map_map, Function.comp_def, Equiv.sigmaEquivProd]

@[simp] theorem keys_toPairList (bindings : List (Sigma fun _ : κ => ν)) :
    (toPairList bindings).map Prod.fst = bindings.keys := by
  simp [toPairList, List.keys, List.map_map, Function.comp_def, Equiv.sigmaEquivProd]

theorem toSigmaList_nodup_iff (bindings : List (κ × ν)) :
    (toSigmaList bindings).NodupKeys ↔ (bindings.map Prod.fst).Nodup := by
  unfold List.NodupKeys
  rw [keys_toSigmaList]

theorem mem_toSigmaList_iff (bindings : List (κ × ν)) (key : κ) (value : ν) :
    Sigma.mk key value ∈ toSigmaList bindings ↔ (key, value) ∈ bindings := by
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨binding, member, same⟩
    have pair := congrArg (Equiv.sigmaEquivProd κ ν) same
    change binding = (key, value) at pair
    exact pair ▸ member
  · intro member
    exact List.mem_map.mpr ⟨(key, value), member, rfl⟩

/-- Uniqueness is on keys, not on complete key/value pairs. -/
abbrev UniqueList (κ : Type u) (ν : Type v) :=
  {bindings : List (κ × ν) // (bindings.map Prod.fst).Nodup}

def toAList (bindings : UniqueList κ ν) : AList (fun _ : κ => ν) :=
  ⟨toSigmaList bindings.1, (toSigmaList_nodup_iff bindings.1).mpr bindings.2⟩

def ofAList (bindings : AList (fun _ : κ => ν)) : UniqueList κ ν :=
  ⟨toPairList bindings.entries, by
    simpa only [keys_toPairList, List.NodupKeys] using bindings.nodupKeys⟩

@[simp] theorem ofAList_toAList (bindings : UniqueList κ ν) :
    ofAList (toAList bindings) = bindings := by
  apply Subtype.ext
  exact toPairList_toSigmaList bindings.1

@[simp] theorem toAList_ofAList (bindings : AList (fun _ : κ => ν)) :
    toAList (ofAList bindings) = bindings := by
  apply AList.ext
  exact toSigmaList_toPairList bindings.entries

/-- The two existing presentations have the same entries and key invariant. -/
def aListEquiv : UniqueList κ ν ≃ AList (fun _ : κ => ν) where
  toFun := toAList
  invFun := ofAList
  left_inv := ofAList_toAList
  right_inv := toAList_ofAList

@[simp] theorem toAList_keys (bindings : UniqueList κ ν) :
    (toAList bindings).keys = bindings.1.map Prod.fst :=
  keys_toSigmaList bindings.1

def empty : UniqueList κ ν := ⟨[], by simp⟩

@[simp] theorem empty_entries : (empty : UniqueList κ ν).1 = [] := rfl

@[simp] theorem toAList_empty : toAList (empty : UniqueList κ ν) = ∅ := rfl

section DecidableKeys
variable [DecidableEq κ]

/-- This traverses only to the first old occurrence and prepends the new pair. -/
def pairSet (key : κ) (value : ν) (bindings : List (κ × ν)) : List (κ × ν) :=
  (key, value) :: bindings.eraseP (fun binding => decide (key = binding.1))

theorem pairSet_replaces_front (key : κ) (old value : ν) (rest : List (κ × ν)) :
    pairSet key value ((key, old) :: rest) = (key, value) :: rest := by
  simp [pairSet]

theorem toSigmaList_eraseP (key : κ) (bindings : List (κ × ν)) :
    toSigmaList (bindings.eraseP (fun binding => decide (key = binding.1))) =
      (toSigmaList bindings).kerase key := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
      by_cases same : key = binding.1
      · simp [toSigmaList, List.kerase, Equiv.sigmaEquivProd, same]
      · simpa [toSigmaList, List.kerase, Equiv.sigmaEquivProd, same] using
          congrArg (fun tail => (Equiv.sigmaEquivProd κ ν).symm binding :: tail) ih

theorem toSigmaList_pairSet (key : κ) (value : ν) (bindings : List (κ × ν)) :
    toSigmaList (pairSet key value bindings) =
      List.kinsert key value (toSigmaList bindings) := by
  change Sigma.mk key value ::
      toSigmaList (bindings.eraseP (fun binding => decide (key = binding.1))) = _
  rw [toSigmaList_eraseP]
  rfl

theorem pairSet_nodup (key : κ) (value : ν) {bindings : List (κ × ν)}
    (unique : (bindings.map Prod.fst).Nodup) :
    ((pairSet key value bindings).map Prod.fst).Nodup := by
  apply (toSigmaList_nodup_iff _).mp
  rw [toSigmaList_pairSet]
  exact List.kinsert_nodupKeys key value ((toSigmaList_nodup_iff _).mpr unique)

def set (key : κ) (value : ν) (bindings : UniqueList κ ν) : UniqueList κ ν :=
  ⟨pairSet key value bindings.1, pairSet_nodup key value bindings.2⟩

theorem set_entries (key : κ) (value : ν) (bindings : UniqueList κ ν) :
    (set key value bindings).1 = pairSet key value bindings.1 := rfl

theorem toAList_set (key : κ) (value : ν) (bindings : UniqueList κ ν) :
    toAList (set key value bindings) = AList.insert key value (toAList bindings) := by
  apply AList.ext
  exact toSigmaList_pairSet key value bindings.1

theorem set_keys (key : κ) (value : ν) (bindings : UniqueList κ ν) :
    ((set key value bindings).1.map Prod.fst) =
      key :: (bindings.1.map Prod.fst).erase key := by
  rw [← toAList_keys, toAList_set, AList.keys_insert, toAList_keys]

/-- This literal state equation also observes replacement of an existing head. -/
theorem set_shadow (key : κ) (first last : ν) (bindings : UniqueList κ ν) :
    set key last (set key first bindings) = set key last bindings := by
  apply Subtype.ext
  exact pairSet_replaces_front key first last _

theorem dlookup_toSigmaList (query : κ) (bindings : List (κ × ν)) :
    (toSigmaList bindings).dlookup query = listLookup query bindings := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      by_cases same : query = key
      · subst query
        simp [toSigmaList, Equiv.sigmaEquivProd, listLookup]
      · simpa [toSigmaList, Equiv.sigmaEquivProd, listLookup, same] using ih

theorem lookup_toAList (query : κ) (bindings : UniqueList κ ν) :
    AList.lookup query (toAList bindings) = listLookup query bindings.1 :=
  dlookup_toSigmaList query bindings.1

/-- The map equation holds even on duplicate raw input; only the carrier proof
needs key uniqueness. Other shadowed bindings remain behind the first erasure. -/
theorem listObserve_pairSet (key : κ) (value : ν) (bindings : List (κ × ν)) :
    listObserve (pairSet key value bindings) = write key value (listObserve bindings) := by
  funext query
  change listLookup query (pairSet key value bindings) = _
  rw [← dlookup_toSigmaList, toSigmaList_pairSet]
  by_cases same : query = key
  · subst query
    simp [write]
  · rw [List.dlookup_kinsert_ne same, dlookup_toSigmaList]
    simp [write, same, listObserve]

def partialOps : Ops κ ν (UniqueList κ ν) where
  empty := empty
  bind := set
  lookup query bindings := listLookup query bindings.1

theorem partial_laws : Laws (partialOps : Ops κ ν (UniqueList κ ν))
    (fun bindings => listObserve bindings.1) where
  empty := rfl
  bind key value bindings := listObserve_pairSet key value bindings.1
  lookup _ _ := rfl

theorem lookup_eq_some_iff_mem (bindings : UniqueList κ ν) (key : κ) (value : ν) :
    listLookup key bindings.1 = some value ↔ (key, value) ∈ bindings.1 := by
  rw [← lookup_toAList]
  change value ∈ AList.lookup key (toAList bindings) ↔ _
  exact AList.mem_lookup_iff.trans (mem_toSigmaList_iff bindings.1 key value)

omit [DecidableEq κ] in
/-- Enumeration is the original unsorted list, with no reordering conversion. -/
theorem ofAList_entries (bindings : AList (fun _ : κ => ν)) :
    (ofAList bindings).1 = toPairList bindings.entries := rfl

end DecidableKeys
end Search.OrderedMap.AssociationListEnumeration
