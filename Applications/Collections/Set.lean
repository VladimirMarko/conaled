import SquareKit.ValidGraphs
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Set.Basic

/-! Operation-only sets and their separate invariant-restricted laws.
The seven contracts follow the pinned Isabelle `Set_Specs` interface; source
identity and the applicable BSD-3-Clause notice are recorded in
`docs/research/fdsa-adt-refinement.md`. No membership decision for arbitrary
mathematical sets is supplied by this interface. -/

set_option autoImplicit false
set_option warningAsError true

namespace Collections.Sets
universe u v w

/-- The operations passed to a client, without semantic evidence. -/
structure Ops (α : Type u) (S : Type v) where
  empty : S
  insert : α → S → S
  delete : α → S → S
  isin : S → α → Bool

variable {α : Type u} {S : Type v}

/-- The seven Set laws, relative to a separate observation and invariant. -/
structure Laws (ops : Ops α S) (decode : S → Set α) (Valid : S → Prop) : Prop where
  empty_decode : decode ops.empty = ∅
  empty_valid : Valid ops.empty
  insert_decode : ∀ a s, Valid s → decode (ops.insert a s) = decode s ∪ {a}
  insert_valid : ∀ a s, Valid s → Valid (ops.insert a s)
  delete_decode : ∀ a s, Valid s → decode (ops.delete a s) = decode s \ {a}
  delete_valid : ∀ a s, Valid s → Valid (ops.delete a s)
  isin_iff : ∀ s a, Valid s → (ops.isin s a = true ↔ a ∈ decode s)

/-- Insert two supplied elements, then delete the first. -/
def client (ops : Ops α S) (a b : α) (s : S) : S :=
  ops.delete a (ops.insert b (ops.insert a s))

namespace Laws
open SquareKit.ValidGraphs

variable {ops : Ops α S} {decode : S → Set α} {Valid : S → Prop}

/-- Initialization is related to the empty mathematical set unconditionally. -/
theorem empty_related (h : Laws ops decode Valid) :
    validGraph Valid decode ops.empty ∅ :=
  ⟨h.empty_valid, h.empty_decode⟩

/-- The insertion schema uses equality on the ordinary supplied element. -/
theorem insert_preserves (h : Laws ops decode Valid) (a : α) :
    Relator.LiftFun (validGraph Valid decode) (validGraph Valid decode)
      (ops.insert a) (fun s => s ∪ {a}) := by
  apply (liftFun_iff Valid decode Valid decode
    (ops.insert a) (fun s => s ∪ {a})).mpr
  intro s hs
  exact ⟨h.insert_valid a s hs, h.insert_decode a s hs⟩

/-- Deletion preserves both validity and singleton subtraction. -/
theorem delete_preserves (h : Laws ops decode Valid) (a : α) :
    Relator.LiftFun (validGraph Valid decode) (validGraph Valid decode)
      (ops.delete a) (fun s => s \ {a}) := by
  apply (liftFun_iff Valid decode Valid decode
    (ops.delete a) (fun s => s \ {a})).mpr
  intro s hs
  exact ⟨h.delete_valid a s hs, h.delete_decode a s hs⟩

/-- Membership is an ordinary observation with trivial output validity;
its Bool result is decoded to a proposition by reflection. -/
theorem isin_preserves (h : Laws ops decode Valid) (a : α) :
    Relator.LiftFun (validGraph Valid decode)
      (validGraph (fun _ : Bool => True) (fun b : Bool => b = true))
      (fun s => ops.isin s a) (fun s => a ∈ s) := by
  apply (liftFun_iff Valid decode
    (fun _ : Bool => True) (fun b : Bool => b = true)
    (fun s => ops.isin s a) (fun s => a ∈ s)).mpr
  intro s hs
  exact ⟨True.intro, propext (h.isin_iff s a hs)⟩

/-- Both inserted states are valid before the final deletion law is applied. -/
theorem client_valid (h : Laws ops decode Valid) (a b : α) (s : S)
    (hs : Valid s) : Valid (client ops a b s) := by
  have hfirst := h.insert_valid a s hs
  have hsecond := h.insert_valid b (ops.insert a s) hfirst
  exact h.delete_valid a (ops.insert b (ops.insert a s)) hsecond

/-- The client observes exactly its three actual set operations. -/
theorem client_decode (h : Laws ops decode Valid) (a b : α) (s : S)
    (hs : Valid s) :
    decode (client ops a b s) = ((decode s ∪ {a}) ∪ {b}) \ {a} := by
  have hfirst := h.insert_valid a s hs
  have hsecond := h.insert_valid b (ops.insert a s) hfirst
  change decode (ops.delete a (ops.insert b (ops.insert a s))) = _
  rw [h.delete_decode a (ops.insert b (ops.insert a s)) hsecond,
    h.insert_decode b (ops.insert a s) hfirst, h.insert_decode a s hs]

/-- Reflection of every query after the client, on arbitrary valid input. -/
theorem client_isin_iff (h : Laws ops decode Valid) (a b : α) (s : S)
    (hs : Valid s) (q : α) :
    ops.isin (client ops a b s) q = true ↔
      ((q ∈ decode s ∨ q = a) ∨ q = b) ∧ q ≠ a := by
  have hquery := h.isin_iff (client ops a b s) q (h.client_valid a b s hs)
  rw [h.client_decode a b s hs] at hquery
  exact hquery

/-- The deleted key is absent, regardless of its original membership. -/
theorem client_isin_first (h : Laws ops decode Valid) (a b : α) (s : S)
    (hs : Valid s) : ops.isin (client ops a b s) a = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hquery
  exact ((h.client_isin_iff a b s hs a).mp hquery).2 rfl

/-- A distinct second key remains present after deletion of the first. -/
theorem client_isin_second (h : Laws ops decode Valid) (a b : α) (s : S)
    (hs : Valid s) (hba : b ≠ a) :
    ops.isin (client ops a b s) b = true :=
  (h.client_isin_iff a b s hs b).mpr ⟨Or.inr rfl, hba⟩

/-- Reusing the same key does not make the final deletion ineffective. -/
theorem client_isin_same (h : Laws ops decode Valid) (a : α) (s : S)
    (hs : Valid s) : ops.isin (client ops a a s) a = false :=
  h.client_isin_first a a s hs

/-- An unrelated query retains its original Boolean observation. -/
theorem client_isin_other (h : Laws ops decode Valid) (a b : α) (s : S)
    (hs : Valid s) (q : α) (hqa : q ≠ a) (hqb : q ≠ b) :
    ops.isin (client ops a b s) q = ops.isin s q := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hquery
    have hmem := ((h.client_isin_iff a b s hs q).mp hquery).1
    apply (h.isin_iff s q hs).mpr
    rcases hmem with (hmem | heq) | heq
    · exact hmem
    · exact (hqa heq).elim
    · exact (hqb heq).elim
  · intro hquery
    exact (h.client_isin_iff a b s hs q).mpr
      ⟨Or.inl (Or.inl ((h.isin_iff s q hs).mp hquery)), hqa⟩

/-- Equal set observations suffice for equal queries; states need not agree. -/
theorem isin_eq_of_decode_eq {T : Type w}
    {ops' : Ops α T} {decode' : T → Set α} {Valid' : T → Prop}
    (h : Laws ops decode Valid) (k : Laws ops' decode' Valid')
    (s : S) (t : T) (hs : Valid s) (ht : Valid' t)
    (hdecode : decode s = decode' t) (q : α) :
    ops.isin s q = ops'.isin t q := by
  apply Bool.eq_iff_iff.mpr
  calc
    ops.isin s q = true ↔ q ∈ decode s := h.isin_iff s q hs
    _ ↔ q ∈ decode' t := by rw [hdecode]
    _ ↔ ops'.isin t q = true := (k.isin_iff t q ht).symm

/-- The same operation-only client agrees observationally across lawful
implementations starting from corresponding valid states. -/
theorem client_isin_eq {T : Type w}
    {ops' : Ops α T} {decode' : T → Set α} {Valid' : T → Prop}
    (h : Laws ops decode Valid) (k : Laws ops' decode' Valid')
    (a b : α) (s : S) (t : T) (hs : Valid s) (ht : Valid' t)
    (hdecode : decode s = decode' t) (q : α) :
    ops.isin (client ops a b s) q = ops'.isin (client ops' a b t) q := by
  apply h.isin_eq_of_decode_eq k (client ops a b s) (client ops' a b t)
    (h.client_valid a b s hs) (k.client_valid a b t ht) ?_ q
  rw [h.client_decode a b s hs, k.client_decode a b t ht, hdecode]

end Laws
end Collections.Sets
