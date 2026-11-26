import Applications.Sequences.SharedList.Observation
import Applications.Sequences.SharedList.Suffixes

/-! PFDS persistence cases through public allocation, traversal, resource and
composition theorems. Counts describe the explicit cell model only. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SharedList
open Sequences.SharedList

def three : Store Nat × Root := allocate empty 3 none

theorem three_represents : Represents three.1.heap three.2 [3] :=
  allocate_represents (.nil : Represents (empty : Store Nat).heap none []) 3

def twoThree : Store Nat × Root := allocate three.1 2 three.2

theorem old_version_retained : Represents twoThree.1.heap three.2 [3] :=
  allocate_retains three.1 2 three.2 three.2 [3] three_represents

theorem new_version_correct : Represents twoThree.1.heap twoThree.2 [2, 3] :=
  allocate_represents three_represents 2

theorem both_heads : head twoThree.1 three.2 = some 3 ∧
    head twoThree.1 twoThree.2 = some 2 :=
  ⟨head_correct old_version_retained, head_correct new_version_correct⟩

theorem empty_tail_fails : tail (empty : Store Nat) none = none := tail_empty _

theorem singleton_tail_succeeds : tail three.1 three.2 = some none := by
  obtain ⟨q, run, rep⟩ := tail_cons three_represents
  cases rep
  exact run

def right : Store Nat × Root := load [3, 4]
def left : Store Nat × Root := prepend [1, 2] right.1 none

theorem left_represents : Represents left.1.heap left.2 [1, 2] := by
  simpa [left] using (prepend_correct [1, 2] (s := right.1) .nil).2.1

theorem right_retained : Represents left.1.heap right.2 [3, 4] :=
  (load_represents [3, 4]).mono (prepend_correct [1, 2] (s := right.1) .nil).1

/-- Six total cells: four original cells plus two copied left cells.
The result still reaches the exact original right root. -/
theorem append_shares : ∃ out,
    appendRun left.1 left.2 right.2 = (some out, 3) ∧
    Represents out.1.heap out.2 [1, 2, 3, 4] ∧
    Represents out.1.heap left.2 [1, 2] ∧
    Represents out.1.heap right.2 [3, 4] ∧
    out.1.next = 6 ∧ advance 2 out.1 out.2 = some right.2 := by
  obtain ⟨out, run, ext, rep, count, shared⟩ :=
    appendRun_correct left_represents right_retained
  exact ⟨out, run, rep, left_represents.mono ext, right_retained.mono ext, count, shared⟩

theorem append_client :
    ((appendRun left.1 left.2 right.2).1.bind fun state => head state.1 state.2) = some 1 :=
  appendRun_head_correct left_represents right_retained

def initial : Store Nat × Root := load [1, 2, 3]

theorem update_shares : ∃ out,
    updateRun initial.1 initial.2 1 9 = (some out, 2) ∧
    Represents out.1.heap out.2 [1, 9, 3] ∧
    Represents out.1.heap initial.2 [1, 2, 3] ∧
    out.1.next = 5 ∧ advance 2 out.1 out.2 = advance 2 initial.1 initial.2 := by
  obtain ⟨out, run, ext, rep, count, shared⟩ :=
    updateRun_success (load_represents [1, 2, 3]) (i := 1) (by decide) 9
  exact ⟨out, run, rep, (load_represents [1, 2, 3]).mono ext, count, shared⟩

theorem update_past_end : updateRun initial.1 initial.2 3 9 = (none, 4) :=
  updateRun_failure (load_represents [1, 2, 3]) (i := 3) (by decide) 9

/-- The separately composed client preserves the specified failure. -/
theorem update_client_failure :
    ((updateRun initial.1 initial.2 3 9).1.bind fun state => head state.1 state.2) = none :=
  updateRun_head_correct (load_represents [1, 2, 3]) 3 9

theorem suffixes_share : ∃ roots,
    suffixesRun initial.1 initial.2 = (some roots, 4) ∧
    List.Forall₂ (Represents initial.1.heap) roots [[1, 2, 3], [2, 3], [3], []] ∧
    roots.length = 4 ∧ (roots.filterMap id).length = 3 ∧
    roots.Nodup ∧ sharedSpace roots = 7 :=
  suffixesRun_correct (load_represents [1, 2, 3])

/-- The space count is tied to a duplicate-free enumeration of the actual
reachable graph, not just to a list of equal-valued suffix observations. -/
theorem suffixes_storage : ∃ roots,
    suffixesRun initial.1 initial.2 = (some roots, 4) ∧
    (∀ a, ReachableFrom initial.1.heap roots a ↔ a ∈ roots.filterMap id) ∧
    (roots.filterMap id).Nodup ∧ sharedSpace roots = 7 := by
  obtain ⟨roots, run, _, _, _, distinct, space⟩ := suffixes_share
  exact ⟨roots, run, suffixesRun_reachable (congrArg Prod.fst run),
    nonnull_nodup distinct, space⟩

def baseTwo : Store Nat × Root := allocate empty 2 none
def oneTwo : Store Nat × Root := allocate baseTwo.1 1 baseTwo.2
def extraTwo : Store Nat × Root := allocate oneTwo.1 2 none
def unsharedRoots : List Root := [oneTwo.2, extraTwo.2, none]

/-- Distinct roots and correct suffix values alone do not establish sharing. -/
theorem equal_suffix_values :
    List.Forall₂ (Represents extraTwo.1.heap) unsharedRoots [[1, 2], [2], []] ∧
    unsharedRoots.Nodup ∧ sharedSpace unsharedRoots = 5 := by
  have base : Represents baseTwo.1.heap baseTwo.2 [2] :=
    allocate_represents (.nil : Represents (empty : Store Nat).heap none []) 2
  have first : Represents oneTwo.1.heap oneTwo.2 [1, 2] := allocate_represents base 1
  have kept : Represents extraTwo.1.heap oneTwo.2 [1, 2] :=
    first.mono (allocate_extends oneTwo.1 2 none)
  have second : Represents extraTwo.1.heap extraTwo.2 [2] :=
    allocate_represents (.nil : Represents oneTwo.1.heap none []) 2
  exact ⟨.cons kept (.cons second (.cons .nil .nil)), by decide, rfl⟩

theorem an_unlisted_cell_is_reachable :
    ReachableFrom extraTwo.1.heap unsharedRoots 0 ∧
    0 ∉ unsharedRoots.filterMap id := by
  refine ⟨⟨oneTwo.2, by decide, ?_⟩, by decide⟩
  exact .next (x := 1) (r := some 0) (by rfl) (.here 0)

theorem equal_suffix_values_are_not_closed : ¬ ClosedRoots extraTwo.1.heap unsharedRoots := by
  intro closed
  exact an_unlisted_cell_is_reachable.2
    ((closed.reachable_iff 0).mp an_unlisted_cell_is_reachable.1)

theorem no_fuel_is_not_empty :
    appendRunFuel 0 three.1 three.2 none = (none, 0) := rfl

end Examples.SharedList
