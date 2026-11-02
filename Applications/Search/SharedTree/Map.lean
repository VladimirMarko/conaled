import Applications.Search.SharedTree.Path
import Applications.Search.SharedTree.Observation
import Applications.Search.OrderedMap.Basic

/-!
# Finite maps through immutable cell references

Only keys are compared. Binding copies its ancestor path and writes the target
cell even when the key was already present. The exact measures are element
comparisons, structural visits and fresh cells. All are model operations.

`Rebuilds` records unchanged ancestor labels and unselected child addresses.
`WrittenAt` additionally records the replacement cell's unchanged children;
those children lie beyond the endpoint of the ancestor path.

Raw traversals are not validators of arbitrary heap roots. Their source-level
contracts require `Represents`; the frontier then supplies sufficient fuel.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.SharedTree.Map

variable {α : Type}

/-- The endpoint is newly written, preserving the two children of a previous
endpoint cell, or using two empty children when extending an empty root. -/
def WrittenAt (before after : Durability.Heap (Cell α))
    (oldRoot newRoot : Root) (path : List Branch) (value : α) : Prop :=
  ∃ oldFocus newFocus l r,
    follow before path oldRoot = some oldFocus ∧
    follow after path newRoot = some newFocus ∧
    ((oldFocus = none ∧ l = none ∧ r = none) ∨
      ∃ oldValue, oldFocus.bind before = some ((oldValue, l), r)) ∧
    newFocus.bind after = some ((value, l), r)

private theorem read_mono {before after : Durability.Heap (Cell α)}
    (extension : Durability.Extends before after) {root : Root} {cell : Cell α}
    (lookup : root.bind before = some cell) : root.bind after = some cell := by
  cases root with
  | none => cases lookup
  | some a => exact extension a cell lookup

theorem WrittenAt.mono {before after later : Durability.Heap (Cell α)}
    {oldRoot newRoot : Root} {path : List Branch} {value : α}
    (h : WrittenAt before after oldRoot newRoot path value)
    (extension : Durability.Extends after later) :
    WrittenAt before later oldRoot newRoot path value := by
  obtain ⟨oldFocus, newFocus, l, r, oldPath, newPath, oldCell, newCell⟩ := h
  exact ⟨oldFocus, newFocus, l, r, oldPath, follow_mono extension newPath,
    oldCell, read_mono extension newCell⟩

theorem WrittenAt.prefix {before after : Durability.Heap (Cell α)}
    {a b : Nat} {oldCell newCell : Cell α} {path : List Branch} {value : α}
    (direction : Branch) (oldLookup : before a = some oldCell)
    (newLookup : after b = some newCell)
    (h : WrittenAt before after (child direction oldCell) (child direction newCell) path value) :
    WrittenAt before after (some a) (some b) (direction :: path) value := by
  obtain ⟨oldFocus, newFocus, l, r, oldPath, newPath, oldNode, newNode⟩ := h
  exact ⟨oldFocus, newFocus, l, r,
    by simpa only [follow_step oldLookup] using oldPath,
    by simpa only [follow_step newLookup] using newPath, oldNode, newNode⟩

/-- When the replaced endpoint is the root, its two child addresses are
preserved even though the payload at that root changes. -/
theorem WrittenAt.nil_children {before after : Durability.Heap (Cell α)}
    {oldRoot newRoot l r : Root} {oldValue newValue : α}
    (h : WrittenAt before after oldRoot newRoot [] newValue)
    (oldLookup : oldRoot.bind before = some ((oldValue, l), r)) :
    newRoot.bind after = some ((newValue, l), r) := by
  obtain ⟨oldFocus, newFocus, l', r', oldPath, newPath, oldNode, newNode⟩ := h
  simp only [follow, Option.some.injEq] at oldPath newPath
  subst oldFocus newFocus
  rcases oldNode with ⟨empty, _, _⟩ | ⟨value, lookup⟩
  · rw [empty] at oldLookup
    cases oldLookup
  · have cells : ((value, l'), r') = ((oldValue, l), r) :=
      Option.some.inj (lookup.symm.trans oldLookup)
    have left : l' = l := congrArg (fun cell : Cell α => cell.1.2) cells
    have right : r' = r := congrArg (fun cell : Cell α => cell.2) cells
    simpa only [left, right] using newNode

variable {κ ν : Type} [LinearOrder κ]

/-- The independent key-tree comparison count and source search-path length.
Each visited node, including the new or replaced endpoint, is copied by bind. -/
def profile (query : κ) (t : BinaryTree (κ × ν)) : Nat × Nat × Nat :=
  ((OrderedTree.memberRun query (t.map Prod.fst)).2,
    (searchPathBy Prod.fst query t).length + 1,
    (searchPathBy Prod.fst query t).length + 1)

private theorem profile_left {query : κ} {binding : κ × ν}
    (l r : BinaryTree (κ × ν)) (h : query < binding.1) :
    profile query (.node binding l r) =
      ((profile query l).1 + 1, (profile query l).2.1 + 1, (profile query l).2.2 + 1) := by
  simp [profile, searchPathBy, BinaryTree.map, OrderedTree.memberRun, h]

private theorem profile_right {query : κ} {binding : κ × ν}
    (l r : BinaryTree (κ × ν)) (hl : ¬query < binding.1) (hr : binding.1 < query) :
    profile query (.node binding l r) =
      ((profile query r).1 + 2, (profile query r).2.1 + 1, (profile query r).2.2 + 1) := by
  simp [profile, searchPathBy, BinaryTree.map, OrderedTree.memberRun, hl, hr]

private theorem map_height (t : BinaryTree (κ × ν)) :
    (t.map Prod.fst).height = t.height := by
  induction t with
  | nil => rfl
  | node binding l r hl hr => simp [BinaryTree.map, BinaryTree.height, hl, hr]

theorem profile_bounds (query : κ) (t : BinaryTree (κ × ν)) :
    (profile query t).1 ≤ 2 * t.height ∧
    (profile query t).2.1 ≤ t.height + 1 ∧ (profile query t).2.2 ≤ t.height + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [profile, map_height] using OrderedTree.memberRun_bound query (t.map Prod.fst)
  · exact Nat.add_le_add_right (searchPathBy_length_le Prod.fst query t) 1
  · exact Nat.add_le_add_right (searchPathBy_length_le Prod.fst query t) 1

def lookupRunFuel : Nat → Store (κ × ν) → Root → κ →
    Resources.Measured (Option ν) (Nat × Nat)
  | _, _, none, _ => (none, (0, 1))
  | 0, _, some _, _ => (none, (0, 0))
  | fuel + 1, s, some a, query =>
      match s.heap a with
      | none => (none, (0, 1))
      | some ((binding, l), r) =>
          if query < binding.1 then
            let rest := lookupRunFuel fuel s l query
            (rest.1, (rest.2.1 + 1, rest.2.2 + 1))
          else if binding.1 < query then
            let rest := lookupRunFuel fuel s r query
            (rest.1, (rest.2.1 + 2, rest.2.2 + 1))
          else (some binding.2, (2, 1))

theorem lookupRunFuel_correct {s : Store (κ × ν)} {root : Root}
    {t : BinaryTree (κ × ν)} (h : Represents s.heap root t)
    {fuel : Nat} (enough : t.height ≤ fuel) (query : κ) :
    lookupRunFuel fuel s root query =
      (OrderedMap.lookup query t, ((profile query t).1, (profile query t).2.1)) := by
  induction h generalizing fuel with
  | nil => rfl
  | @node a binding l r lt rt lookup leftBelow rightBelow hl hr ihl ihr =>
      cases fuel with
      | zero => simp [BinaryTree.height] at enough
      | succ fuel =>
          have leftEnough : lt.height ≤ fuel := by
            have le := Nat.le_max_left lt.height rt.height
            simp only [BinaryTree.height] at enough
            omega
          have rightEnough : rt.height ≤ fuel := by
            have le := Nat.le_max_right lt.height rt.height
            simp only [BinaryTree.height] at enough
            omega
          by_cases ql : query < binding.1
          · rw [profile_left lt rt ql]
            simp [lookupRunFuel, lookup, ql, ihl leftEnough, OrderedMap.lookup]
          · by_cases qr : binding.1 < query
            · rw [profile_right lt rt ql qr]
              simp [lookupRunFuel, lookup, ql, qr, ihr rightEnough, OrderedMap.lookup]
            · simp [lookupRunFuel, lookup, ql, qr, OrderedMap.lookup, profile,
                searchPathBy, BinaryTree.map, OrderedTree.memberRun]

def lookupRun (s : Store (κ × ν)) (root : Root) (query : κ) :
    Resources.Measured (Option ν) (Nat × Nat) := lookupRunFuel s.next s root query

theorem lookupRun_correct {s : Store (κ × ν)} {root : Root} {t : BinaryTree (κ × ν)}
    (h : Represents s.heap root t) (query : κ) :
    lookupRun s root query =
      (OrderedMap.lookup query t, ((profile query t).1, (profile query t).2.1)) :=
  lookupRunFuel_correct h h.height_le_next query

theorem lookupRun_observes {s : Store (κ × ν)} {root : Root} {t : BinaryTree (κ × ν)}
    (h : Represents s.heap root t) (ordered : OrderedTree.OrderedBy Prod.fst t) (query : κ) :
    (lookupRun s root query).1 = OrderedMap.observe t query :=
  (congrArg Prod.fst (lookupRun_correct h query)).trans (OrderedMap.lookup_correct ordered query)

def bindRunFuel : Nat → Store (κ × ν) → Root → κ → ν →
    Resources.Measured (Option (Store (κ × ν) × Root)) (Nat × Nat × Nat)
  | _, s, none, key, value => (some (allocate s (key, value) none none), (0, 1, 1))
  | 0, _, some _, _, _ => (none, (0, 0, 0))
  | fuel + 1, s, some a, key, value =>
      match s.heap a with
      | none => (none, (0, 1, 0))
      | some ((binding, l), r) =>
          if key < binding.1 then
            let rest := bindRunFuel fuel s l key value
            match rest.1 with
            | none => (none, (rest.2.1 + 1, rest.2.2.1 + 1, rest.2.2.2))
            | some out => (some (allocate out.1 binding out.2 r),
                (rest.2.1 + 1, rest.2.2.1 + 1, rest.2.2.2 + 1))
          else if binding.1 < key then
            let rest := bindRunFuel fuel s r key value
            match rest.1 with
            | none => (none, (rest.2.1 + 2, rest.2.2.1 + 1, rest.2.2.2))
            | some out => (some (allocate out.1 binding l out.2),
                (rest.2.1 + 2, rest.2.2.1 + 1, rest.2.2.2 + 1))
          else (some (allocate s (key, value) l r), (2, 1, 1))

theorem bindRunFuel_correct {s : Store (κ × ν)} {root : Root}
    {t : BinaryTree (κ × ν)} (h : Represents s.heap root t)
    {fuel : Nat} (enough : t.height ≤ fuel) (key : κ) (value : ν) :
    ∃ out, bindRunFuel fuel s root key value = (some out, profile key t) ∧
      Durability.Extends s.heap out.1.heap ∧
      Represents out.1.heap out.2 (OrderedMap.bind key value t) ∧
      out.1.next = s.next + (profile key t).2.2 ∧
      Rebuilds s.heap out.1.heap root out.2 (searchPathBy Prod.fst key t) ∧
      WrittenAt s.heap out.1.heap root out.2 (searchPathBy Prod.fst key t) (key, value) := by
  induction h generalizing fuel with
  | nil =>
      refine ⟨allocate s (key, value) none none, rfl, allocate_extends _ _ _ _,
        allocate_represents .nil .nil (key, value), rfl, .here _ _, ?_⟩
      exact ⟨none, some s.next, none, none, rfl, rfl, Or.inl ⟨rfl, rfl, rfl⟩,
        allocate_lookup _ _ _ _⟩
  | @node a binding l r lt rt lookup leftBelow rightBelow hl hr ihl ihr =>
      cases fuel with
      | zero => simp [BinaryTree.height] at enough
      | succ fuel =>
          have leftEnough : lt.height ≤ fuel := by
            have le := Nat.le_max_left lt.height rt.height
            simp only [BinaryTree.height] at enough
            omega
          have rightEnough : rt.height ≤ fuel := by
            have le := Nat.le_max_right lt.height rt.height
            simp only [BinaryTree.height] at enough
            omega
          by_cases kl : key < binding.1
          · obtain ⟨out, run, extension, rep, count, rebuilt, written⟩ := ihl leftEnough
            have grown := allocate_extends out.1 binding out.2 r
            refine ⟨allocate out.1 binding out.2 r, ?_, extension.trans grown, ?_, ?_, ?_, ?_⟩
            · rw [profile_left lt rt kl]
              simp [bindRunFuel, lookup, kl, run]
            · simpa only [OrderedMap.bind, ite_eq_left kl] using
                allocate_represents rep (hr.mono extension) binding
            · rw [allocate_next, count, profile_left lt rt kl]
              simp only [Prod.snd, Prod.fst]
              omega
            · simpa only [searchPathBy, ite_eq_left kl] using
                Rebuilds.left lookup (allocate_lookup out.1 binding out.2 r) (rebuilt.mono grown)
            · simpa only [searchPathBy, ite_eq_left kl] using
                WrittenAt.prefix .left lookup (allocate_lookup out.1 binding out.2 r)
                  (written.mono grown)
          · by_cases kr : binding.1 < key
            · obtain ⟨out, run, extension, rep, count, rebuilt, written⟩ := ihr rightEnough
              have grown := allocate_extends out.1 binding l out.2
              refine ⟨allocate out.1 binding l out.2, ?_, extension.trans grown, ?_, ?_, ?_, ?_⟩
              · rw [profile_right lt rt kl kr]
                simp [bindRunFuel, lookup, kl, kr, run]
              · simpa only [OrderedMap.bind, ite_eq_right kl, ite_eq_left kr] using
                  allocate_represents (hl.mono extension) rep binding
              · rw [allocate_next, count, profile_right lt rt kl kr]
                simp only [Prod.snd, Prod.fst]
                omega
              · simpa only [searchPathBy, ite_eq_right kl, ite_eq_left kr] using
                  Rebuilds.right lookup (allocate_lookup out.1 binding l out.2) (rebuilt.mono grown)
              · simpa only [searchPathBy, ite_eq_right kl, ite_eq_left kr] using
                  WrittenAt.prefix .right lookup (allocate_lookup out.1 binding l out.2)
                    (written.mono grown)
            · refine ⟨allocate s (key, value) l r, ?_, allocate_extends _ _ _ _, ?_, ?_, ?_, ?_⟩
              · simp [bindRunFuel, lookup, kl, kr, profile, searchPathBy,
                  BinaryTree.map, OrderedTree.memberRun]
              · simpa only [OrderedMap.bind, ite_eq_right kl, ite_eq_right kr] using
                  allocate_represents hl hr (key, value)
              · simp [profile, searchPathBy, kl, kr]
              · simpa only [searchPathBy, ite_eq_right kl, ite_eq_right kr] using
                  (Rebuilds.here (before := s.heap) (after := (allocate s (key, value) l r).1.heap)
                    (some a) (some s.next))
              · refine ⟨some a, some s.next, l, r, ?_, ?_, Or.inr ⟨binding, lookup⟩,
                  allocate_lookup _ _ _ _⟩ <;>
                  simp [searchPathBy, kl, kr, follow]

def bindRun (s : Store (κ × ν)) (root : Root) (key : κ) (value : ν) :
    Resources.Measured (Option (Store (κ × ν) × Root)) (Nat × Nat × Nat) :=
  bindRunFuel s.next s root key value

theorem bindRun_correct {s : Store (κ × ν)} {root : Root} {t : BinaryTree (κ × ν)}
    (h : Represents s.heap root t) (key : κ) (value : ν) :
    ∃ out, bindRun s root key value = (some out, profile key t) ∧
      Durability.Extends s.heap out.1.heap ∧
      Represents out.1.heap out.2 (OrderedMap.bind key value t) ∧
      out.1.next = s.next + (profile key t).2.2 ∧
      Rebuilds s.heap out.1.heap root out.2 (searchPathBy Prod.fst key t) ∧
      WrittenAt s.heap out.1.heap root out.2 (searchPathBy Prod.fst key t) (key, value) :=
  bindRunFuel_correct h h.height_le_next key value

theorem bindRun_retention {s : Store (κ × ν)} {root old : Root}
    {t previous : BinaryTree (κ × ν)}
    (h : Represents s.heap root t) (kept : Represents s.heap old previous)
    (key : κ) (value : ν) :
    ∃ out, bindRun s root key value = (some out, profile key t) ∧
      Represents out.1.heap out.2 (OrderedMap.bind key value t) ∧
      Represents out.1.heap old previous ∧
      (∀ probe, Diverges (searchPathBy Prod.fst key t) probe →
        follow out.1.heap probe out.2 = follow out.1.heap probe root) ∧
      WrittenAt s.heap out.1.heap root out.2 (searchPathBy Prod.fst key t) (key, value) := by
  obtain ⟨out, run, extension, rep, _, rebuilt, written⟩ := bindRun_correct h key value
  exact ⟨out, run, rep, kept.mono extension, rebuilt.off_path extension, written⟩

/-- Actual shared execution satisfies the same all-key update law as the
abstract finite map, while preserving the previous heap for other roots. -/
theorem bind_lookup {s : Store (κ × ν)} {root : Root} {t : BinaryTree (κ × ν)}
    (h : Represents s.heap root t) (key : κ) (value : ν) :
    ∃ out, bindRun s root key value = (some out, profile key t) ∧
      Durability.Extends s.heap out.1.heap ∧
      (∀ query, (lookupRun out.1 out.2 query).1 =
        if query = key then some value else (lookupRun s root query).1) := by
  obtain ⟨out, run, extension, rep, _⟩ := bindRun_correct h key value
  refine ⟨out, run, extension, fun query => ?_⟩
  rw [lookupRun_correct rep, lookupRun_correct h]
  exact OrderedMap.lookup_bind key value query t

def bindSquare (key : κ) (value : ν) :
    Relational.RelSquare (representation (κ × ν)) (optionalRepresentation (κ × ν)) where
  impl state := (bindRun state.1 state.2 key value).1
  spec tree := some (OrderedMap.bind key value tree)
  preserves := by
    intro state tree h
    obtain ⟨out, run, _, rep, _⟩ := bindRun_correct h key value
    change (optionalRepresentation (κ × ν)).Rel _ _
    rw [run]
    exact rep

def lookupSquare (query : κ) :
    Relational.RelSquare (representation (κ × ν)) ⟨Option ν, Option ν, Eq⟩ where
  impl state := (lookupRun state.1 state.2 query).1
  spec := OrderedMap.lookup query
  preserves := by
    intro state tree h
    exact congrArg Prod.fst (lookupRun_correct h query)

end Search.SharedTree.Map
