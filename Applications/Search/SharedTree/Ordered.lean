import Applications.Search.SharedTree.Path
import Applications.Search.OrderedTree.Basic

/-!
# Ordered insertion through immutable cell references

The executable traversal reads the heap and copies only the selected ancestor
path on return. The specification uses the independent tree-value algorithm.
Its three measures count element comparisons, structural visits, and fresh
cells, in that order. All are model operations, not Lean runtime allocations.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.SharedTree
variable {α : Type} [LinearOrder α]

/-- The search ends at either an empty root or the first equal label. -/
def searchPath (x : α) (t : BinaryTree α) : List Branch := searchPathBy id x t

/-- Independent expected counts: one copied cell per ancestor, plus the new
leaf precisely when the directed search does not find an equal label. -/
def insertProfile (x : α) (t : BinaryTree α) : Nat × Nat × Nat :=
  ((OrderedTree.memberRun x t).2, (searchPath x t).length + 1,
    (searchPath x t).length + if OrderedTree.member x t then 0 else 1)

private theorem insertProfile_left {x y : α} (l r : BinaryTree α) (xy : x < y) :
    insertProfile x (.node y l r) =
      ((insertProfile x l).1 + 1, (insertProfile x l).2.1 + 1,
        (insertProfile x l).2.2 + 1) := by
  cases h : (OrderedTree.memberRun x l).1 <;>
    simp [insertProfile, searchPath, searchPathBy, OrderedTree.member,
      OrderedTree.memberRun, xy, h]

private theorem insertProfile_right {x y : α} (l r : BinaryTree α)
    (xy : ¬ x < y) (yx : y < x) :
    insertProfile x (.node y l r) =
      ((insertProfile x r).1 + 2, (insertProfile x r).2.1 + 1,
        (insertProfile x r).2.2 + 1) := by
  cases h : (OrderedTree.memberRun x r).1 <;>
    simp [insertProfile, searchPath, searchPathBy, OrderedTree.member,
      OrderedTree.memberRun, xy, yx, h]

theorem searchPath_length_le (x : α) (t : BinaryTree α) :
    (searchPath x t).length ≤ t.height := searchPathBy_length_le id x t

theorem insertProfile_bounds (x : α) (t : BinaryTree α) :
    (insertProfile x t).1 ≤ 2 * t.height ∧
    (insertProfile x t).2.1 ≤ t.height + 1 ∧
    (insertProfile x t).2.2 ≤ t.height + 1 := by
  refine ⟨OrderedTree.memberRun_bound x t, ?_, ?_⟩
  · exact Nat.add_le_add_right (searchPath_length_le x t) 1
  · have bound := searchPath_length_le x t
    change (searchPath x t).length + (if OrderedTree.member x t then 0 else 1) ≤
      t.height + 1
    split <;> omega

def insertRunFuel : Nat → Store α → Root → α →
    Resources.Measured (Option (Store α × Root)) (Nat × Nat × Nat)
  | _, s, none, x => (some (allocate s x none none), (0, 1, 1))
  | 0, _, some _, _ => (none, (0, 0, 0))
  | fuel + 1, s, some a, x =>
      match s.heap a with
      | none => (none, (0, 1, 0))
      | some ((y, l), r) =>
          if x < y then
            let rest := insertRunFuel fuel s l x
            match rest.1 with
            | none => (none, (rest.2.1 + 1, rest.2.2.1 + 1, rest.2.2.2))
            | some out => (some (allocate out.1 y out.2 r),
                (rest.2.1 + 1, rest.2.2.1 + 1, rest.2.2.2 + 1))
          else if y < x then
            let rest := insertRunFuel fuel s r x
            match rest.1 with
            | none => (none, (rest.2.1 + 2, rest.2.2.1 + 1, rest.2.2.2))
            | some out => (some (allocate out.1 y l out.2),
                (rest.2.1 + 2, rest.2.2.1 + 1, rest.2.2.2 + 1))
          else (some (s, some a), (2, 1, 0))

theorem insertRunFuel_correct {s : Store α} {root : Root} {t : BinaryTree α}
    (h : Represents s.heap root t) {fuel : Nat} (enough : t.height ≤ fuel) (x : α) :
    ∃ out, insertRunFuel fuel s root x = (some out, insertProfile x t) ∧
      Durability.Extends s.heap out.1.heap ∧
      Represents out.1.heap out.2 (OrderedTree.insert x t) ∧
      out.1.next = s.next + (insertProfile x t).2.2 ∧
      Rebuilds s.heap out.1.heap root out.2 (searchPath x t) := by
  induction h generalizing fuel with
  | nil =>
      refine ⟨allocate s x none none, ?_, allocate_extends _ _ _ _,
        allocate_represents .nil .nil x, rfl, .here _ _⟩
      simp [insertRunFuel, insertProfile, searchPath, searchPathBy, OrderedTree.member,
        OrderedTree.memberRun]
  | @node a y l r lt rt lookup leftBelow rightBelow hl hr ihl ihr =>
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
          by_cases xy : x < y
          · obtain ⟨out, run, extension, rep, count, rebuilt⟩ := ihl leftEnough
            have grown := allocate_extends out.1 y out.2 r
            refine ⟨allocate out.1 y out.2 r, ?_, extension.trans grown, ?_, ?_, ?_⟩
            · rw [insertProfile_left lt rt xy]
              simp [insertRunFuel, lookup, xy, run]
            · simpa only [OrderedTree.insert, ite_eq_left xy] using
                allocate_represents rep (hr.mono extension) y
            · rw [allocate_next, count, insertProfile_left lt rt xy]
              change s.next + (insertProfile x lt).2.2 + 1 =
                s.next + ((insertProfile x lt).2.2 + 1)
              exact Nat.add_assoc _ _ _
            · simpa only [searchPath, searchPathBy, id_eq, ite_eq_left xy, allocate_root] using
                Rebuilds.left lookup (allocate_lookup out.1 y out.2 r) (rebuilt.mono grown)
          · by_cases yx : y < x
            · obtain ⟨out, run, extension, rep, count, rebuilt⟩ := ihr rightEnough
              have grown := allocate_extends out.1 y l out.2
              refine ⟨allocate out.1 y l out.2, ?_, extension.trans grown, ?_, ?_, ?_⟩
              · rw [insertProfile_right lt rt xy yx]
                simp [insertRunFuel, lookup, xy, yx, run]
              · simpa only [OrderedTree.insert, ite_eq_right xy, ite_eq_left yx] using
                  allocate_represents (hl.mono extension) rep y
              · rw [allocate_next, count, insertProfile_right lt rt xy yx]
                change s.next + (insertProfile x rt).2.2 + 1 =
                  s.next + ((insertProfile x rt).2.2 + 1)
                exact Nat.add_assoc _ _ _
              · simpa only [searchPath, searchPathBy, id_eq, ite_eq_right xy, ite_eq_left yx,
                  allocate_root] using
                  Rebuilds.right lookup (allocate_lookup out.1 y l out.2) (rebuilt.mono grown)
            · refine ⟨(s, some a), ?_, Durability.Extends.refl _, ?_, ?_, ?_⟩
              · simp [insertRunFuel, lookup, xy, yx, insertProfile, searchPath, searchPathBy,
                  OrderedTree.member, OrderedTree.memberRun]
              · simpa only [OrderedTree.insert, ite_eq_right xy, ite_eq_right yx] using
                  Represents.node lookup leftBelow rightBelow hl hr
              · simp [insertProfile, searchPath, searchPathBy, xy, yx, OrderedTree.member,
                  OrderedTree.memberRun]
              · simpa only [searchPath, searchPathBy, id_eq, ite_eq_right xy, ite_eq_right yx] using
                  (Rebuilds.here (before := s.heap) (after := s.heap) (some a) (some a))

/-- Backwards references make the frontier a sufficient bound for any root. -/
def insertRun (s : Store α) (root : Root) (x : α) :
    Resources.Measured (Option (Store α × Root)) (Nat × Nat × Nat) :=
  insertRunFuel s.next s root x

theorem insertRun_correct {s : Store α} {root : Root} {t : BinaryTree α}
    (h : Represents s.heap root t) (x : α) :
    ∃ out, insertRun s root x = (some out, insertProfile x t) ∧
      Durability.Extends s.heap out.1.heap ∧
      Represents out.1.heap out.2 (OrderedTree.insert x t) ∧
      out.1.next = s.next + (insertProfile x t).2.2 ∧
      Rebuilds s.heap out.1.heap root out.2 (searchPath x t) :=
  insertRunFuel_correct h h.height_le_next x

/-- The public execution theorem preserves every unrelated old tree and every
off-path root, including branches of a retained version not otherwise observed. -/
theorem insertRun_retention {s : Store α} {root old : Root} {t previous : BinaryTree α}
    (h : Represents s.heap root t) (kept : Represents s.heap old previous) (x : α) :
    ∃ out, insertRun s root x = (some out, insertProfile x t) ∧
      Represents out.1.heap out.2 (OrderedTree.insert x t) ∧
      Represents out.1.heap old previous ∧
      (∀ probe, Diverges (searchPath x t) probe →
        follow out.1.heap probe out.2 = follow out.1.heap probe root) := by
  obtain ⟨out, run, extension, rep, _, rebuilt⟩ := insertRun_correct h x
  exact ⟨out, run, rep, kept.mono extension, rebuilt.off_path extension⟩

end Search.SharedTree
