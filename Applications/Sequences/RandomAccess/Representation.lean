import Applications.Sequences.RandomAccess.TreeBuild
import Squares

/-! The canonical valid carrier realizes List operations through existing squares. -/
set_option autoImplicit false
set_option warningAsError true

namespace RandomAccess
universe u
variable {α : Type u}

abbrev Carrier (α : Type u) := {ds : RAList α // Inv ds}

def encode (xs : List α) : Carrier α := ⟨toRA xs, inv_toRA xs⟩

def representation (α : Type u) : Squares.Rep.{u} :=
  ⟨Carrier α, List α, fun ds => fromRA ds.val⟩

theorem decode_encode (xs : List α) : (representation α).decode (encode xs) = xs :=
  fromRA_toRA xs

theorem encode_decode (ds : Carrier α) : encode ((representation α).decode ds) = ds :=
  Subtype.ext (toRA_fromRA ds.property)

def encodeSquare : Squares.Square ⟨List α, List α, id⟩ (representation α) where
  impl := encode
  spec := id
  commutes := decode_encode

def updateSquare (k : Nat) (x : α) : Squares.Square (representation α) (representation α) where
  impl ds := ⟨updateRA k x ds.val, valid_updateRA ds.property k x⟩
  spec xs := xs.set k x
  commutes ds := updateRA_refinement ds.property k x

theorem updateSquare_encode (xs : List α) (k : Nat) (x : α) :
    (updateSquare k x).impl (encode xs) = encode (xs.set k x) := by
  apply Subtype.ext
  apply valid_abstraction_injective (valid_updateRA (inv_toRA xs) k x) (inv_toRA _)
  exact (updateRA_toRA k x xs).trans (fromRA_toRA _).symm

def lookupSquare (k : Nat) : Squares.Square (representation α) ⟨Option α, Option α, id⟩ where
  impl ds := fetchRA k ds.val
  spec := fun (xs : List α) => xs[k]?
  commutes ds := fetchRA_refinement ds.property k

/-- The actual update is followed by the actual cached-size lookup. -/
def updateQuery (k : Nat) (x : α) (query : Nat) :=
  Squares.compose (lookupSquare query) (updateSquare k x)

theorem updateQuery_refinement (ds : Carrier α) (k : Nat) (x : α) (query : Nat) :
    (updateQuery k x query).impl ds = ((fromRA ds.val).set k x)[query]? :=
  (updateQuery k x query).commutes ds

theorem updateQuery_same (ds : Carrier α) (k : Nat) (x : α)
    (hk : k < (fromRA ds.val).length) : (updateQuery k x k).impl ds = some x := by
  rw [updateQuery_refinement, List.getElem?_set_self hk]

theorem updateQuery_other (ds : Carrier α) (k : Nat) (x : α) (query : Nat)
    (hk : k ≠ query) : (updateQuery k x query).impl ds = (lookupSquare query).impl ds := by
  rw [updateQuery_refinement, List.getElem?_set_ne hk]
  exact (fetchRA_refinement ds.property query).symm

def consSquare (x : α) : Squares.Square (representation α) (representation α) where
  impl ds := ⟨consRA x ds.val, inv_consRA x ds.property⟩
  spec xs := x :: xs
  commutes ds := fromRA_consRA x ds.val

/-- Refine the result with its preserved invariant; no decoding is used to pop. -/
def unconsCarrier (ds : Carrier α) : Option (α × Carrier α) :=
  match he : unconsRA ds.val with
  | none => none
  | some (x, ys) => some (x, ⟨ys, unconsRA_valid ds.property he⟩)

def unconsRepresentation (α : Type u) : Squares.Rep.{u} :=
  ⟨Option (α × Carrier α), Option (α × List α),
    fun result => result.map (fun p => (p.1, fromRA p.2.val))⟩

def unconsSquare : Squares.Square (representation α) (unconsRepresentation α) where
  impl := unconsCarrier
  spec := unconsList
  commutes ds := by
    change (unconsCarrier ds).map (fun p => (p.1, fromRA p.2.val)) =
      unconsList (fromRA ds.val)
    have h := unconsRA_refinement ds.property
    unfold unconsCarrier
    split <;> simp_all

/-- Binary carrying followed by borrowing, composed through the common carrier. -/
def pushPop (x : α) := Squares.compose unconsSquare (consSquare x)

theorem pushPop_refinement (ds : Carrier α) (x : α) :
    (unconsRepresentation α).decode ((pushPop x).impl ds) = some (x, fromRA ds.val) :=
  (pushPop x).commutes ds

theorem pushPop_exact (ds : Carrier α) (x : α) :
    (pushPop x).impl ds = some (x, ds) := by
  change unconsCarrier ⟨consRA x ds.val, inv_consRA x ds.property⟩ = some (x, ds)
  have h := unconsRA_consRA x ds.property
  unfold unconsCarrier
  split <;> simp_all

end RandomAccess
