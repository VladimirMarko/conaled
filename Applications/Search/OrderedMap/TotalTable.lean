import Applications.Search.OrderedMap.Invariant
import Applications.Search.OrderedMap.Observations

/-!
# Total tables with validity-restricted laws

The weaker VFA table contract needs only total lookup, not a partial map or
presence observation. This recovers the total-table part of the preserved
`TableObservations.lean` draft (SHA-256
`0233781d210056e9a61ae9a355120429e55007e72713434d25a5338aa6489b57`).
Partial maps specialize it by forgetting absence through a supplied default.
The converse does not recover presence. All claims concern observations;
execution costs, raw-state equality and finite support are separate contracts.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.TotalTable
universe u v w z

structure Ops (κ : Type u) (ν : Type v) (T : Type w) where
  empty : T
  get : κ → T → ν
  set : κ → ν → T → T

variable {κ : Type u} {ν : Type v} {T : Type w} {U : Type z}

/-- Pointwise laws impose no equality decision on keys or values. -/
structure Laws (ops : Ops κ ν T) (default : ν) (Valid : T → Prop) : Prop where
  empty_valid : Valid ops.empty
  set_valid : ∀ k v t, Valid t → Valid (ops.set k v t)
  get_empty : ∀ k, ops.get k ops.empty = default
  get_set_same : ∀ k v t, Valid t → ops.get k (ops.set k v t) = v
  get_set_other : ∀ k q v t, k ≠ q → Valid t →
    ops.get q (ops.set k v t) = ops.get q t

def observe (ops : Ops κ ν T) (t : T) : κ → ν := fun q => ops.get q t

/-- Later writes win. Execution uses only the supplied operations. -/
def setAll (ops : Ops κ ν T) : List (κ × ν) → T → T
  | [], t => t
  | (k, v) :: rest, t => setAll ops rest (ops.set k v t)

theorem Laws.observe_set [DecidableEq κ] {ops : Ops κ ν T} {d : ν}
    {Valid : T → Prop} (h : Laws ops d Valid) (k : κ) (v : ν)
    {t : T} (ht : Valid t) :
    observe ops (ops.set k v t) = Function.update (observe ops t) k v := by
  funext q
  by_cases hq : q = k
  · subst q
    simpa only [Function.update_self, observe] using h.get_set_same k v t ht
  · simpa only [Function.update_of_ne hq, observe] using
      h.get_set_other k q v t (Ne.symm hq) ht

theorem Laws.setAll_valid {ops : Ops κ ν T} {d : ν} {Valid : T → Prop}
    (h : Laws ops d Valid) (writes : List (κ × ν)) {t : T} (ht : Valid t) :
    Valid (setAll ops writes t) := by
  induction writes generalizing t with
  | nil => exact ht
  | cons kv rest ih => exact ih (h.set_valid kv.1 kv.2 t ht)

theorem Laws.observe_setAll [DecidableEq κ] {ops : Ops κ ν T} {d : ν}
    {Valid : T → Prop} (h : Laws ops d Valid) (writes : List (κ × ν))
    {t : T} (ht : Valid t) :
    observe ops (setAll ops writes t) =
      writes.foldl (fun f kv => Function.update f kv.1 kv.2) (observe ops t) := by
  induction writes generalizing t with
  | nil => rfl
  | cons kv rest ih =>
      simp only [setAll, List.foldl]
      rw [ih (h.set_valid kv.1 kv.2 t ht), h.observe_set kv.1 kv.2 ht]

/-- Corresponding arbitrary initial states suffice; their raw carriers and
validity predicates may differ. No equality decision is needed for this law. -/
theorem Laws.setAll_agrees {a : Ops κ ν T} {b : Ops κ ν U} {d e : ν}
    {P : T → Prop} {Q : U → Prop} (ha : Laws a d P) (hb : Laws b e Q)
    (writes : List (κ × ν)) {t : T} {s : U} (ht : P t) (hs : Q s)
    (same : observe a t = observe b s) :
    observe a (setAll a writes t) = observe b (setAll b writes s) := by
  induction writes generalizing t s with
  | nil => exact same
  | cons kv rest ih =>
      apply ih (ha.set_valid kv.1 kv.2 t ht) (hb.set_valid kv.1 kv.2 s hs)
      funext q
      by_cases hq : kv.1 = q
      · subst q
        exact (ha.get_set_same kv.1 kv.2 t ht).trans
          (hb.get_set_same kv.1 kv.2 s hs).symm
      · exact (ha.get_set_other kv.1 q kv.2 t hq ht).trans
          ((congrFun same q).trans (hb.get_set_other kv.1 q kv.2 s hq hs).symm)

def functions [DecidableEq κ] (d : ν) : Ops κ ν (κ → ν) where
  empty := fun _ => d
  get q t := t q
  set k v t := Function.update t k v

theorem functions_laws [DecidableEq κ] (d : ν) :
    Laws (functions (κ := κ) d) d (fun _ => True) where
  empty_valid := trivial
  set_valid _ _ _ _ := trivial
  get_empty _ := rfl
  get_set_same _ _ _ _ := by simp [functions]
  get_set_other _ _ _ _ h _ := by simp [functions, Ne.symm h]

/-- Retain the existing partial operations and forget absence only at lookup. -/
def ofPartial (ops : OrderedMap.Ops κ ν T) (d : ν) : Ops κ ν T where
  empty := ops.empty
  get k t := (ops.lookup k t).getD d
  set := ops.bind

/-- The adapter executes exactly the existing chronological binding client. -/
theorem setAll_ofPartial (ops : OrderedMap.Ops κ ν T) (d : ν)
    (writes : List (κ × ν)) (t : T) :
    setAll (ofPartial ops d) writes t = OrderedMap.bindAll ops writes t := by
  induction writes generalizing t with
  | nil => rfl
  | cons kv rest ih => exact ih (ops.bind kv.1 kv.2 t)

/-- Raw validity and semantic equations are separate. No law is asserted on
an invalid raw state. This also accepts current valid-subtype realizations. -/
theorem ofPartial_laws [DecidableEq κ] (ops : OrderedMap.Ops κ ν T)
    (meaning : T → OrderedMap.Meaning κ ν) (Valid : T → Prop) (d : ν)
    (he : Valid ops.empty)
    (hb : ∀ k v t, Valid t → Valid (ops.bind k v t))
    (law : OrderedMap.Laws (ops.restrict Valid he hb) (fun t => meaning t.1)) :
    Laws (ofPartial ops d) d Valid := by
  rcases (OrderedMap.Laws.restrict_iff ops Valid meaning he hb).mp law with
    ⟨empty, bind, lookup⟩
  refine ⟨he, hb, ?_, ?_, ?_⟩
  · intro k
    change (ops.lookup k ops.empty).getD d = d
    rw [lookup k ops.empty he, empty]
    rfl
  · intro k v t ht
    change (ops.lookup k (ops.bind k v t)).getD d = v
    rw [lookup k _ (hb k v t ht), bind k v t ht]
    simp [OrderedMap.write]
  · intro k q v t hne ht
    change (ops.lookup q (ops.bind k v t)).getD d = (ops.lookup q t).getD d
    rw [lookup q _ (hb k v t ht), bind k v t ht, lookup q t ht]
    simp [OrderedMap.write, Ne.symm hne]

theorem ofPartial_unrestricted [DecidableEq κ] {ops : OrderedMap.Ops κ ν T}
    {meaning : T → OrderedMap.Meaning κ ν} (h : OrderedMap.Laws ops meaning) (d : ν) :
    Laws (ofPartial ops d) d (fun _ => True) :=
  ofPartial_laws ops meaning (fun _ => True) d trivial (fun _ _ _ _ => trivial)
    (OrderedMap.Laws.ofValid trivial (fun _ _ _ _ => trivial) h.empty
      (fun k v t _ => h.bind k v t) (fun k t _ => h.lookup k t))

/-- The complete client agrees with the previously integrated weakening of
partial-map meaning. No reverse reconstruction is asserted. -/
theorem observe_partial_setAll [DecidableEq κ] {ops : OrderedMap.Ops κ ν T}
    {meaning : T → OrderedMap.Meaning κ ν} (h : OrderedMap.Laws ops meaning)
    (d : ν) (writes : List (κ × ν)) (t : T) :
    observe (ofPartial ops d) (setAll (ofPartial ops d) writes t) =
      OrderedMap.withDefault d (OrderedMap.writeAll writes (meaning t)) := by
  rw [setAll_ofPartial]
  funext q
  change (ops.lookup q (OrderedMap.bindAll ops writes t)).getD d = _
  rw [h.lookup_bindAll]
  rfl

end Search.TotalTable
