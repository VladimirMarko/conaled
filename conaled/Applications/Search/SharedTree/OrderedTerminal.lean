import Applications.Search.SharedTree.Ordered
import Applications.Search.SharedTree.PathEndpoint

/-!
# Baseline duplicate insertion retains the matched subtree root

`Rebuilds` constrains copied ancestors and their unselected children; its focus
constructor deliberately permits an arbitrary replacement. Baseline insertion
has a stronger duplicate contract: the search endpoint is the identical old
nonempty root. Consequently every path continuing below that endpoint observes
the same roots in the final heap, including branches below a matched node.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.SharedTree
variable {α : Type} [LinearOrder α]

/-- Directed membership suffices for this execution fact. Orderedness is needed
only when deriving that premise from independent whole-tree membership. -/
theorem insertRunFuel_duplicate_endpoint {s : Store α} {root : Root}
    {t : BinaryTree α} (h : Represents s.heap root t) {fuel : Nat}
    (enough : t.height ≤ fuel) (x : α) (present : OrderedTree.member x t = true)
    {out : Store α × Root} (run : (insertRunFuel fuel s root x).1 = some out) :
    ∃ address,
      follow s.heap (searchPath x t) root = some (some address) ∧
      follow out.1.heap (searchPath x t) out.2 = some (some address) := by
  induction h generalizing fuel out with
  | nil => simp [OrderedTree.member, OrderedTree.memberRun] at present
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
          · have found : OrderedTree.member x lt = true := by
              simpa only [OrderedTree.member, OrderedTree.memberRun, ite_eq_left xy]
                using present
            obtain ⟨childOut, childRun, _, _, _, _⟩ := insertRunFuel_correct hl leftEnough x
            have result : allocate childOut.1 y childOut.2 r = out := by
              simpa [insertRunFuel, lookup, xy, childRun] using run
            obtain ⟨address, oldEndpoint, newEndpoint⟩ :=
              ihl leftEnough found (congrArg Prod.fst childRun)
            subst out
            have route : searchPath x (.node y lt rt) = .left :: searchPath x lt := by
              simp [searchPath, searchPathBy, xy]
            refine ⟨address, ?_, ?_⟩
            · rw [route, follow_step lookup]
              exact oldEndpoint
            · rw [route, allocate_root,
                follow_step (allocate_lookup childOut.1 y childOut.2 r)]
              exact follow_mono (allocate_extends childOut.1 y childOut.2 r) newEndpoint
          · by_cases yx : y < x
            · have found : OrderedTree.member x rt = true := by
                simpa only [OrderedTree.member, OrderedTree.memberRun,
                  ite_eq_right xy, ite_eq_left yx] using present
              obtain ⟨childOut, childRun, _, _, _, _⟩ := insertRunFuel_correct hr rightEnough x
              have result : allocate childOut.1 y l childOut.2 = out := by
                simpa [insertRunFuel, lookup, xy, yx, childRun] using run
              obtain ⟨address, oldEndpoint, newEndpoint⟩ :=
                ihr rightEnough found (congrArg Prod.fst childRun)
              subst out
              have route : searchPath x (.node y lt rt) = .right :: searchPath x rt := by
                simp [searchPath, searchPathBy, xy, yx]
              refine ⟨address, ?_, ?_⟩
              · rw [route, follow_step lookup]
                exact oldEndpoint
              · rw [route, allocate_root,
                  follow_step (allocate_lookup childOut.1 y l childOut.2)]
                exact follow_mono (allocate_extends childOut.1 y l childOut.2) newEndpoint
            · have result : (s, some a) = out := by
                simpa [insertRunFuel, lookup, xy, yx] using run
              subst out
              exact ⟨a, by simp [searchPath, searchPathBy, xy, yx, follow],
                by simp [searchPath, searchPathBy, xy, yx, follow]⟩

/-- On a duplicate, only strict ancestors are copied. The exact matched root
and all its descendant path observations are retained, as is the old version.
Both versions in the descendant equality are read in the same final heap. -/
theorem insertRun_duplicate_subtree {s : Store α} {root : Root} {t : BinaryTree α}
    (h : Represents s.heap root t) (ordered : OrderedTree.Ordered t) {x : α}
    (present : OrderedTree.Contains x t) :
    ∃ out address,
      insertRun s root x = (some out, insertProfile x t) ∧
      Durability.Extends s.heap out.1.heap ∧
      out.1.next = s.next + (searchPath x t).length ∧
      follow s.heap (searchPath x t) root = some (some address) ∧
      follow out.1.heap (searchPath x t) out.2 = some (some address) ∧
      Represents out.1.heap root t ∧
      (∀ suffix, follow out.1.heap (searchPath x t ++ suffix) out.2 =
        follow out.1.heap (searchPath x t ++ suffix) root) := by
  have found := (OrderedTree.member_correct ordered x).mpr present
  obtain ⟨out, run, extension, _, count, _⟩ := insertRun_correct h x
  obtain ⟨address, oldEndpoint, newEndpoint⟩ :=
    insertRunFuel_duplicate_endpoint h h.height_le_next x found (congrArg Prod.fst run)
  refine ⟨out, address, run, extension, ?_, oldEndpoint, newEndpoint,
    h.mono extension, ?_⟩
  · simpa only [insertProfile, found, Bool.true_eq, ite_true, Nat.add_zero] using count
  · exact follow_descendants (newEndpoint.trans (follow_mono extension oldEndpoint).symm)

end Search.SharedTree
