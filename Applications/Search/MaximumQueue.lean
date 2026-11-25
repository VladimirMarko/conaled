import Applications.Search.ExactPriority
import Applications.Sequences.Multiplicity
import Mathlib.Order.OrderDual
import Mathlib.Data.Multiset.AddSub

/-!
The Nat maximum-queue contract from VFA's Priqueue chapter. Its four operations,
validity predicate, relational abstraction and eleven laws remain separate.
The later observation adapter uses the existing exact occurrence queue interface.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.MaximumQueue

universe u
variable {Q : Type u}

/-- The source operations, including its native merge. -/
structure Operations (Q : Type u) where
  empty : Q
  insert : Nat → Q → Q
  deleteMax : Q → Option (Nat × Q)
  merge : Q → Q → Q

/-- The eleven source laws. An abstraction witness need not be closed under
permutation, and the laws constrain valid states only. -/
structure Laws (ops : Operations Q) (Valid : Q → Prop)
    (Abs : Q → List Nat → Prop) : Prop where
  can_relate : ∀ p, Valid p → ∃ al, Abs p al
  abs_perm : ∀ p al bl, Valid p → Abs p al → Abs p bl → al.Perm bl
  empty_valid : Valid ops.empty
  empty_relate : Abs ops.empty []
  insert_valid : ∀ k p, Valid p → Valid (ops.insert k p)
  insert_relate : ∀ p al k, Valid p → Abs p al → Abs (ops.insert k p) (k :: al)
  deleteMax_none : ∀ p, Valid p → (Abs p [] ↔ ops.deleteMax p = none)
  deleteMax_valid : ∀ p q k, Valid p → ops.deleteMax p = some (k, q) → Valid q
  deleteMax_relate : ∀ p q k pl ql, Valid p → Abs p pl →
    ops.deleteMax p = some (k, q) → Abs q ql →
    pl.Perm (k :: ql) ∧ ∀ x ∈ ql, x ≤ k
  merge_valid : ∀ p q, Valid p → Valid q → Valid (ops.merge p q)
  merge_relate : ∀ p q pl ql al, Valid p → Valid q → Abs p pl → Abs q ql →
    Abs (ops.merge p q) al → al.Perm (pl ++ ql)

/-- Maximum priorities become minimum priorities without changing the Nat value. -/
def encode (key : Nat) : Unit × OrderDual Nat := ((), OrderDual.toDual key)

/-- The Unit payload carries no additional information to discard. -/
def decode (entry : Unit × OrderDual Nat) : Nat := OrderDual.ofDual entry.2

@[simp] theorem decode_encode (key : Nat) : decode (encode key) = key := rfl

@[simp] theorem encode_decode (entry : Unit × OrderDual Nat) :
    encode (decode entry) = entry := by
  rcases entry with ⟨⟨⟩, key⟩
  rfl

@[simp] theorem encode_priority_le (a b : Nat) :
    (encode a).2 ≤ (encode b).2 ↔ b ≤ a := Iff.rfl

/-- This changes the interface, not the carrier or the recursive source calls.
Batch insertion directly folds the supplied entries, with no preprocessing map. -/
def encodedOperations (ops : Operations Q) :
    PriorityInterface.Operations.{0,0,u} Unit (OrderDual Nat) where
  Carrier := Q
  empty := ops.empty
  add := fun entries q => entries.foldr (fun entry rest => ops.insert (decode entry) rest) q
  remove := fun q => (ops.deleteMax q).map (fun (key, rest) => (encode key, rest))

@[simp] theorem encodedOperations_empty (ops : Operations Q) :
    (encodedOperations ops).empty = ops.empty := rfl

@[simp] theorem encodedOperations_add_singleton (ops : Operations Q)
    (key : Nat) (q : Q) :
    (encodedOperations ops).add [encode key] q = ops.insert key q := rfl

@[simp] theorem encodedOperations_remove (ops : Operations Q) (q : Q) :
    (encodedOperations ops).remove q =
      (ops.deleteMax q).map (fun (key, rest) => (encode key, rest)) := rfl

section Consequences
variable {Q : Type u} {ops : Operations Q} {Valid : Q → Prop}
  {Abs : Q → List Nat → Prop}

namespace Laws
variable (laws : Laws ops Valid Abs)
include laws

/-- Different abstraction witnesses agree as multisets, without requiring that
every permutation is itself an abstraction witness. -/
theorem abs_multiset (p : Q) (al bl : List Nat) (hp : Valid p)
    (hal : Abs p al) (hbl : Abs p bl) : (al : Multiset Nat) = bl :=
  Multiset.coe_eq_coe.mpr (laws.abs_perm p al bl hp hal hbl)

theorem abs_contents (p : Q) (al bl : List Nat) (hp : Valid p)
    (hal : Abs p al) (hbl : Abs p bl) :
    Sequences.Multiplicity.contents al = Sequences.Multiplicity.contents bl :=
  Sequences.Multiplicity.perm_contents (laws.abs_perm p al bl hp hal hbl)

/-- Any chosen empty-state witness must be the empty list. This identifies an
observation, not the raw queue state. -/
theorem empty_abstract (al : List Nat) (hal : Abs ops.empty al) : al = [] :=
  List.perm_nil.mp (laws.abs_perm ops.empty al [] laws.empty_valid hal laws.empty_relate)

theorem insert_contents (p : Q) (pl al : List Nat) (key : Nat)
    (hp : Valid p) (hpl : Abs p pl) (hal : Abs (ops.insert key p) al) :
    Sequences.Multiplicity.contents al =
      Sequences.Multiplicity.union (Sequences.Multiplicity.singleton key)
        (Sequences.Multiplicity.contents pl) :=
  (laws.abs_contents (ops.insert key p) al (key :: pl) (laws.insert_valid key p hp)
    hal (laws.insert_relate p pl key hp hpl)).trans
      (Sequences.Multiplicity.contents_cons_union key pl)

theorem insert_count (p : Q) (pl al : List Nat) (key query : Nat)
    (hp : Valid p) (hpl : Abs p pl) (hal : Abs (ops.insert key p) al) :
    al.count query = pl.count query + if query = key then 1 else 0 := by
  simpa [Sequences.Multiplicity.contents, Sequences.Multiplicity.union,
    Sequences.Multiplicity.singleton, Nat.add_comm] using
    congrFun (laws.insert_contents p pl al key hp hpl hal) query

/-- The source None law applies to any supplied witness, using uniqueness up to
permutation to recover equality with the empty list. -/
theorem deleteMax_none_iff (p : Q) (pl : List Nat) (hp : Valid p) (hpl : Abs p pl) :
    ops.deleteMax p = none ↔ pl = [] := by
  constructor
  · intro h
    exact List.perm_nil.mp
      (laws.abs_perm p pl [] hp hpl ((laws.deleteMax_none p hp).mpr h))
  · rintro rfl
    exact (laws.deleteMax_none p hp).mp hpl

/-- Successful deletion has a valid residual and an actual abstraction witness;
the residual-sensitive law therefore cannot be used vacuously. -/
theorem deleteMax_exists (p q : Q) (key : Nat) (pl : List Nat)
    (hp : Valid p) (hpl : Abs p pl) (hd : ops.deleteMax p = some (key, q)) :
    Valid q ∧ ∃ ql, Abs q ql ∧ pl.Perm (key :: ql) ∧ ∀ x ∈ ql, x ≤ key := by
  have hq := laws.deleteMax_valid p q key hp hd
  obtain ⟨ql, hql⟩ := laws.can_relate q hq
  exact ⟨hq, ql, hql, laws.deleteMax_relate p q key pl ql hp hpl hd hql⟩

theorem deleteMax_mem (p q : Q) (key : Nat) (pl : List Nat)
    (hp : Valid p) (hpl : Abs p pl) (hd : ops.deleteMax p = some (key, q)) :
    key ∈ pl := by
  obtain ⟨_, ql, _, hperm, _⟩ := laws.deleteMax_exists p q key pl hp hpl hd
  exact hperm.mem_iff.mpr List.mem_cons_self

/-- The selected key is a maximum of the original observation, not merely of
the residual observation named in the source field. -/
theorem deleteMax_maximum (p q : Q) (key : Nat) (pl : List Nat)
    (hp : Valid p) (hpl : Abs p pl) (hd : ops.deleteMax p = some (key, q)) :
    ∀ x ∈ pl, x ≤ key := by
  obtain ⟨_, _, _, hperm, hmax⟩ := laws.deleteMax_exists p q key pl hp hpl hd
  intro x hx
  rcases List.mem_cons.mp (hperm.mem_iff.mp hx) with rfl | hx
  · exact Nat.le_refl _
  · exact hmax x hx

theorem deleteMax_length (p q : Q) (key : Nat) (pl ql : List Nat)
    (hp : Valid p) (hpl : Abs p pl) (hd : ops.deleteMax p = some (key, q))
    (hql : Abs q ql) : ql.length + 1 = pl.length := by
  simpa using (laws.deleteMax_relate p q key pl ql hp hpl hd hql).1.length_eq.symm

theorem deleteMax_contents (p q : Q) (key : Nat) (pl ql : List Nat)
    (hp : Valid p) (hpl : Abs p pl) (hd : ops.deleteMax p = some (key, q))
    (hql : Abs q ql) :
    Sequences.Multiplicity.contents pl =
      Sequences.Multiplicity.union (Sequences.Multiplicity.singleton key)
        (Sequences.Multiplicity.contents ql) :=
  (Sequences.Multiplicity.perm_contents
    (laws.deleteMax_relate p q key pl ql hp hpl hd hql).1).trans
      (Sequences.Multiplicity.contents_cons_union key ql)

theorem deleteMax_count (p q : Q) (key query : Nat) (pl ql : List Nat)
    (hp : Valid p) (hpl : Abs p pl) (hd : ops.deleteMax p = some (key, q))
    (hql : Abs q ql) :
    pl.count query = ql.count query + if query = key then 1 else 0 := by
  simpa [Sequences.Multiplicity.contents, Sequences.Multiplicity.union,
    Sequences.Multiplicity.singleton, Nat.add_comm] using
    congrFun (laws.deleteMax_contents p q key pl ql hp hpl hd hql) query

/-- Merge produces a valid state and a witness of additive occurrence union. -/
theorem merge_exists (p q : Q) (pl ql : List Nat)
    (hp : Valid p) (hq : Valid q) (hpl : Abs p pl) (hql : Abs q ql) :
    Valid (ops.merge p q) ∧ ∃ al, Abs (ops.merge p q) al ∧ al.Perm (pl ++ ql) := by
  have hm := laws.merge_valid p q hp hq
  obtain ⟨al, hal⟩ := laws.can_relate (ops.merge p q) hm
  exact ⟨hm, al, hal, laws.merge_relate p q pl ql al hp hq hpl hql hal⟩

theorem merge_contents (p q : Q) (pl ql al : List Nat)
    (hp : Valid p) (hq : Valid q) (hpl : Abs p pl) (hql : Abs q ql)
    (hal : Abs (ops.merge p q) al) :
    Sequences.Multiplicity.contents al = Sequences.Multiplicity.union
      (Sequences.Multiplicity.contents pl) (Sequences.Multiplicity.contents ql) :=
  (Sequences.Multiplicity.perm_contents
    (laws.merge_relate p q pl ql al hp hq hpl hql hal)).trans
      (Sequences.Multiplicity.contents_append pl ql)

theorem merge_count (p q : Q) (pl ql al : List Nat) (query : Nat)
    (hp : Valid p) (hq : Valid q) (hpl : Abs p pl) (hql : Abs q ql)
    (hal : Abs (ops.merge p q) al) : al.count query = pl.count query + ql.count query :=
  congrFun (laws.merge_contents p q pl ql al hp hq hpl hql hal) query

theorem merge_length (p q : Q) (pl ql al : List Nat)
    (hp : Valid p) (hq : Valid q) (hpl : Abs p pl) (hql : Abs q ql)
    (hal : Abs (ops.merge p q) al) : al.length = pl.length + ql.length := by
  simpa using (laws.merge_relate p q pl ql al hp hq hpl hql hal).length_eq

theorem merge_multiset (p q : Q) (pl ql al : List Nat)
    (hp : Valid p) (hq : Valid q) (hpl : Abs p pl) (hql : Abs q ql)
    (hal : Abs (ops.merge p q) al) : (al : Multiset Nat) = (pl : Multiset Nat) + ql := by
  rw [Multiset.coe_add]
  exact Multiset.coe_eq_coe.mpr (laws.merge_relate p q pl ql al hp hq hpl hql hal)

end Laws
end Consequences

section Observation
variable {Q : Type u} {ops : Operations Q} {Valid : Q → Prop}
  {Abs : Q → List Nat → Prop}

theorem encodedOperations_add_valid (laws : Laws ops Valid Abs)
    (entries : List (Unit × OrderDual Nat)) (q : Q) (hq : Valid q) :
    Valid ((encodedOperations ops).add entries q) := by
  induction entries with
  | nil => exact hq
  | cons entry entries ih => exact laws.insert_valid (decode entry) _ ih

theorem encodedOperations_add_relate (laws : Laws ops Valid Abs)
    (entries : List (Unit × OrderDual Nat)) (q : Q) (ql : List Nat)
    (hq : Valid q) (hql : Abs q ql) :
    Abs ((encodedOperations ops).add entries q) (entries.map decode ++ ql) := by
  induction entries with
  | nil => exact hql
  | cons entry entries ih =>
    exact laws.insert_relate _ _ (decode entry)
      (encodedOperations_add_valid laws entries q hq) ih

@[simp] theorem encodedOperations_remove_none (ops : Operations Q) (q : Q) :
    (encodedOperations ops).remove q = none ↔ ops.deleteMax q = none := by
  cases h : ops.deleteMax q with
  | none => simp [encodedOperations, h]
  | some result => simp [encodedOperations, h]

theorem encodedOperations_remove_some (ops : Operations Q) (q rest : Q)
    (entry : Unit × OrderDual Nat) :
    (encodedOperations ops).remove q = some (entry, rest) ↔
      ops.deleteMax q = some (decode entry, rest) := by
  cases h : ops.deleteMax q with
  | none => simp [encodedOperations, h]
  | some result =>
    rcases result with ⟨key, residual⟩
    simp only [encodedOperations, h, Option.map_some, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨he, hr⟩
      exact ⟨by rw [← he]; rfl, hr⟩
    · rintro ⟨he, hr⟩
      exact ⟨by rw [he, encode_decode], hr⟩

/-- When every raw state is valid, the existing ExactQueue can retain the raw
carrier. Its observation is supplied explicitly with an abstraction witness. -/
def exactQueueOfAllValid (ops : Operations Q) {Valid : Q → Prop}
    {Abs : Q → List Nat → Prop} (laws : Laws ops Valid Abs)
    (observe : Q → List Nat) (observe_spec : ∀ q, Valid q → Abs q (observe q))
    (all_valid : ∀ q, Valid q) : PriorityInterface.ExactQueue.{0,0,u} Unit (OrderDual Nat) where
  toOperations := encodedOperations ops
  entries := fun q => (observe q).map encode
  Valid := Valid
  lawful := {
    empty_entries := by
      change (observe ops.empty).map encode = []
      rw [laws.empty_abstract (observe ops.empty) (observe_spec _ laws.empty_valid)]
      rfl
    empty_valid := laws.empty_valid
    add_valid := encodedOperations_add_valid laws
    add_exact := fun entries q => by
      have hmap : (entries.map decode).map encode = entries := by
        induction entries with
        | nil => rfl
        | cons entry entries ih => simp only [List.map_cons, encode_decode, ih]
      have hv := encodedOperations_add_valid laws entries q (all_valid q)
      have hp := laws.abs_perm ((encodedOperations ops).add entries q) _ _ hv
        (observe_spec _ hv)
        (encodedOperations_add_relate laws entries q (observe q) (all_valid q)
          (observe_spec q (all_valid q)))
      simpa only [List.map_append, hmap] using hp.map encode
    remove_none := fun q => by
      exact (encodedOperations_remove_none ops q).trans
        ((laws.deleteMax_none_iff q (observe q) (all_valid q)
          (observe_spec q (all_valid q))).trans List.map_eq_nil_iff.symm)
    remove_spec := fun q entry rest hq hr => by
      have hd := (encodedOperations_remove_some ops q rest entry).mp hr
      have hv := laws.deleteMax_valid q rest (decode entry) hq hd
      refine ⟨hv, ?_, ?_⟩
      · have hp := (laws.deleteMax_relate q rest (decode entry) (observe q) (observe rest)
          hq (observe_spec q hq) hd (observe_spec rest hv)).1
        simpa only [List.map_cons, encode_decode] using hp.map encode
      · intro other hother
        obtain ⟨key, hkey, rfl⟩ := List.mem_map.mp hother
        change key ≤ decode entry
        exact laws.deleteMax_maximum q rest (decode entry) (observe q)
          hq (observe_spec q hq) hd key hkey
  }

@[simp] theorem exactQueueOfAllValid_entries (ops : Operations Q)
    (laws : Laws ops Valid Abs) (observe : Q → List Nat)
    (observe_spec : ∀ q, Valid q → Abs q (observe q)) (all_valid : ∀ q, Valid q) (q : Q) :
    (exactQueueOfAllValid ops laws observe observe_spec all_valid).entries q =
      (observe q).map encode := rfl

/-- Native merge remains outside the minimum-queue operations record. Its exact
observation nevertheless uses the same occurrence contract as batch insertion. -/
theorem encoded_merge_entries (laws : Laws ops Valid Abs) (observe : Q → List Nat)
    (observe_spec : ∀ q, Valid q → Abs q (observe q))
    (p q : Q) (hp : Valid p) (hq : Valid q) :
    ((observe (ops.merge p q)).map encode).Perm
      ((observe p).map encode ++ (observe q).map encode) := by
  have hm := laws.merge_valid p q hp hq
  simpa only [List.map_append] using
    (laws.merge_relate p q (observe p) (observe q) (observe (ops.merge p q))
      hp hq (observe_spec p hp) (observe_spec q hq) (observe_spec _ hm)).map encode

end Observation

section ValidStates
variable {Q : Type u} {Valid : Q → Prop} {Abs : Q → List Nat → Prop}

/-- Restrict source execution to its valid states. Residual proofs come from the
actual deletion result; no representative or abstraction witness is chosen. -/
def validOperations (ops : Operations Q) (laws : Laws ops Valid Abs) :
    Operations {q : Q // Valid q} where
  empty := ⟨ops.empty, laws.empty_valid⟩
  insert := fun key q => ⟨ops.insert key q.val, laws.insert_valid key q.val q.property⟩
  deleteMax := fun q => match h : ops.deleteMax q.val with
    | none => none
    | some (key, rest) => some (key, ⟨rest, laws.deleteMax_valid q.val rest key q.property h⟩)
  merge := fun p q => ⟨ops.merge p.val q.val, laws.merge_valid p.val q.val p.property q.property⟩

@[simp] theorem validOperations_empty_val (ops : Operations Q) (laws : Laws ops Valid Abs) :
    (validOperations ops laws).empty.val = ops.empty := rfl

@[simp] theorem validOperations_insert_val (ops : Operations Q) (laws : Laws ops Valid Abs)
    (key : Nat) (q : {q : Q // Valid q}) :
    ((validOperations ops laws).insert key q).val = ops.insert key q.val := rfl

@[simp] theorem validOperations_merge_val (ops : Operations Q) (laws : Laws ops Valid Abs)
    (p q : {q : Q // Valid q}) :
    ((validOperations ops laws).merge p q).val = ops.merge p.val q.val := rfl

theorem validOperations_deleteMax_val (ops : Operations Q) (laws : Laws ops Valid Abs)
    (q : {q : Q // Valid q}) :
    ((validOperations ops laws).deleteMax q).map (fun (key, rest) => (key, rest.val)) =
      ops.deleteMax q.val := by
  dsimp only [validOperations]
  split <;> simp_all

@[simp] theorem validOperations_deleteMax_none (ops : Operations Q)
    (laws : Laws ops Valid Abs) (q : {q : Q // Valid q}) :
    (validOperations ops laws).deleteMax q = none ↔ ops.deleteMax q.val = none := by
  dsimp only [validOperations]
  split <;> simp_all

theorem validOperations_deleteMax_some (ops : Operations Q) (laws : Laws ops Valid Abs)
    (p q : {q : Q // Valid q}) (key : Nat) :
    (validOperations ops laws).deleteMax p = some (key, q) ↔
      ops.deleteMax p.val = some (key, q.val) := by
  dsimp only [validOperations]
  split <;> simp_all [Subtype.ext_iff]

/-- The guarded relational contract becomes an all-valid contract on the subtype,
with exactly the same abstraction relation on underlying states. -/
theorem valid_laws (ops : Operations Q) (laws : Laws ops Valid Abs) :
    Laws (validOperations ops laws) (fun _ => True) (fun q al => Abs q.val al) where
  can_relate := fun p _ => laws.can_relate p.val p.property
  abs_perm := fun p al bl _ hal hbl => laws.abs_perm p.val al bl p.property hal hbl
  empty_valid := trivial
  empty_relate := laws.empty_relate
  insert_valid := fun _ _ _ => trivial
  insert_relate := fun p al key _ hal => laws.insert_relate p.val al key p.property hal
  deleteMax_none := fun p _ => (laws.deleteMax_none p.val p.property).trans
    (validOperations_deleteMax_none ops laws p).symm
  deleteMax_valid := fun _ _ _ _ _ => trivial
  deleteMax_relate := fun p q key pl ql _ hpl hd hql =>
    laws.deleteMax_relate p.val q.val key pl ql p.property hpl
      ((validOperations_deleteMax_some ops laws p q key).mp hd) hql
  merge_valid := fun _ _ _ _ => trivial
  merge_relate := fun p q pl ql al _ _ hpl hql hal =>
    laws.merge_relate p.val q.val pl ql al p.property q.property hpl hql hal

/-- A general guarded source implementation enters the existing exact minimum
queue interface on valid states. The supplied observation remains explicit. -/
def exactQueueOnValid (ops : Operations Q) (laws : Laws ops Valid Abs)
    (observe : Q → List Nat) (observe_spec : ∀ q, Valid q → Abs q (observe q)) :
    PriorityInterface.ExactQueue.{0,0,u} Unit (OrderDual Nat) :=
  exactQueueOfAllValid (validOperations ops laws) (valid_laws ops laws)
    (fun q => observe q.val) (fun q _ => observe_spec q.val q.property) (fun _ => trivial)

@[simp] theorem exactQueueOnValid_entries (ops : Operations Q) (laws : Laws ops Valid Abs)
    (observe : Q → List Nat) (observe_spec : ∀ q, Valid q → Abs q (observe q))
    (q : {q : Q // Valid q}) :
    (exactQueueOnValid ops laws observe observe_spec).entries q =
      (observe q.val).map encode := rfl

theorem exactQueueOnValid_remove_some (ops : Operations Q) (laws : Laws ops Valid Abs)
    (observe : Q → List Nat) (observe_spec : ∀ q, Valid q → Abs q (observe q))
    (p q : {q : Q // Valid q}) (entry : Unit × OrderDual Nat) :
    (exactQueueOnValid ops laws observe observe_spec).remove p = some (entry, q) ↔
      ops.deleteMax p.val = some (decode entry, q.val) :=
  (encodedOperations_remove_some (validOperations ops laws) p q entry).trans
    (validOperations_deleteMax_some ops laws p q (decode entry))

end ValidStates

end Search.MaximumQueue
