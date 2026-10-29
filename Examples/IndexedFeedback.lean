import Applications.Progress.OccurrenceCursor

namespace Examples.IndexedFeedback
open Progress Progress.Feedback Progress.Feedback.Occurrence
open DependentSquares

def seed : List Nat := [7,7]
def first : Cursor seed := ⟨0,by decide⟩
def reverseFirst : Cursor seed := ⟨1,by decide⟩
def second : Cursor seed := ⟨1,by decide⟩
def reverseSecond : Cursor seed := ⟨0,by decide⟩
def inputs : Stream Nat := fun n => n+3

theorem initialRelated : Repr seed seed := rfl
theorem firstRelated : CursorRel seed seed initialRelated first reverseFirst := rfl
theorem secondRelated : CursorRel seed seed initialRelated second reverseSecond := rfl

example : state (forward seed) inputs 2 = [7,7,3,4] := rfl
example : state (backward seed) inputs 2 = [4,3,7,7] := rfl
example : (forwardCursor seed first inputs 2).val = 0 := rfl
example : (backwardCursor seed reverseFirst inputs 2).val = 3 := rfl
example : (forwardCursor seed second inputs 2).val = 1 := rfl
example : (backwardCursor seed reverseSecond inputs 2).val = 2 := rfl

example (a : Stream Nat) : forwardCursor seed first a 0 = first :=
  Dependent.certificate_zero _ _ _ _ _
example (a : Stream Nat) (n : Nat) : forwardCursor seed first a (n+1) =
    keep (a n) (state (forward seed) a n) (forwardCursor seed first a n) :=
  Dependent.certificate_step _ _ _ _ _ _
example (a : Stream Nat) (n : Nat) : backwardCursor seed reverseFirst a (n+1) =
    move (a n) (state (backward seed) a n) (backwardCursor seed reverseFirst a n) :=
  Dependent.certificate_step _ _ _ _ _ _

/-- Arbitrary inputs and prefixes consume the generic lifted-state transport. -/
example (a : Stream Nat) (n : Nat) :
    ∃ h : Repr (state (forward seed) a n) (state (backward seed) a n),
      CursorRel _ _ h (forwardCursor seed first a n) (backwardCursor seed reverseFirst a n) :=
  cursors_related seed seed initialRelated first reverseFirst firstRelated a n
example (a : Stream Nat) (n : Nat) :
    (state (forward seed) a n)[(forwardCursor seed first a n).val] =
      (state (backward seed) a n)[(backwardCursor seed reverseFirst a n).val] :=
  cursor_lookup seed seed initialRelated first reverseFirst firstRelated a n
example (a : Stream Nat) (n : Nat) :
    (state (forward seed) a n)[(forwardCursor seed first a n).val] = 7 :=
  selected_value seed first a n
example (a : Stream Nat) (n : Nat) :
    (state (backward seed) a n)[(backwardCursor seed reverseFirst a n).val] = 7 :=
  (cursor_lookup seed seed initialRelated first reverseFirst firstRelated a n).symm.trans
    (selected_value seed first a n)
example : encode (seed++[3]) (3::seed) (repr_step 3 seed seed initialRelated) (keep 3 seed first) =
    move 3 seed (encode seed seed initialRelated first) :=
  encode_advance 3 seed seed initialRelated first

/-- Actual related sections are reindexed, not replaced by pointwise existence. -/
theorem laterRelated : SubRelated (Eq : Parameters Nat → Parameters Nat → Prop) Eq later later := by
  intro p q h; cases h; rfl
example : TermRelated Eq (reindexedRel (sectionRel seed seed initialRelated) laterRelated)
    (tmSub (forwardSection seed first) later) (tmSub (backwardSection seed reverseFirst) later) :=
  term_sub_related (sections_related seed seed initialRelated first reverseFirst firstRelated) laterRelated
example : tmSub (forwardSection seed first) idSub = forwardSection seed first := tmSub_id _
example : tmSub (tmSub (forwardSection seed first) later) later =
    tmSub (forwardSection seed first) (compSub later later) := tmSub_comp _ _ _
example : tmSub (tmSub (backwardSection seed reverseFirst) later) later =
    tmSub (backwardSection seed reverseFirst) (compSub later later) := tmSub_comp _ _ _
example : (compSub later later (inputs,0)).2 = 2 := rfl
example : (tmSub (tmSub (backwardSection seed reverseFirst) later) later (inputs,0)).val = 3 := rfl

/-- The terminal family really depends on the evolving history length. -/
def delayed : Temporal.Until (fun _ => PUnit) (fun n => forwardFamily seed (inputs,n)) 0 :=
  .wait PUnit.unit (.wait PUnit.unit (.now (forwardCursor seed first inputs 2)))

def reversed := mapUntil seed seed initialRelated inputs delayed
example : delayed.horizon = 2 := rfl
example : reversed.horizon = delayed.horizon := Temporal.Until.horizon_map _ _ _
example : reversed.window.2.2.val = 3 := rfl
example : (state (backward seed) inputs (0+reversed.horizon))[reversed.window.2.2.val] = 7 := rfl
example : Temporal.Until.Rel (fun _ => Eq)
    (fun n => CursorRel _ _ (history_related seed seed initialRelated inputs n)) delayed reversed :=
  until_related seed seed initialRelated inputs delayed
example : reversed.map (fun _ => id) (fun _ i => i.val) =
    delayed.map (fun _ => id)
      (fun n i => (encode _ _ (history_related seed seed initialRelated inputs n) i).val) :=
  Temporal.Until.map_comp _ _ _ _ _

/-- Equal payloads cannot reconstruct which occurrence was selected. -/
example : first ≠ second ∧ seed[first.val] = seed[second.val] := by decide
example : ¬ ∃ decode : Nat → Fin 2, ∀ i : Fin 2, decode (seed[i.val]) = i := by
  rintro ⟨decode,h⟩
  have h₀ := congrArg Fin.val (h ⟨0,by decide⟩)
  have h₁ := congrArg Fin.val (h ⟨1,by decide⟩)
  change (decode 7).val = 0 at h₀
  change (decode 7).val = 1 at h₁
  omega
example : ¬ Nonempty (Cursor ([] : List Nat)) := by
  rintro ⟨i⟩; exact Nat.not_lt_zero i.val i.isLt

/-- A fixed reverse index breaks occurrence coherence; index0 also exposes wrong lookup. -/
def wrong (a : Nat) (s : List Nat) (i : Cursor s) : Cursor (a::s) :=
  ⟨i.val,by have := i.isLt; simp only [List.length_cons]; omega⟩
example : encode (seed++[3]) (3::seed) (repr_step 3 seed seed initialRelated) (keep 3 seed second) ≠
    wrong 3 seed reverseSecond := by decide
example : (3::seed)[(wrong 3 seed reverseSecond).val] = 3 ∧
    (3::seed)[(move 3 seed reverseSecond).val] = 7 := by decide

#eval ((forwardCursor seed first inputs 2).val,(backwardCursor seed reverseFirst inputs 2).val)
end Examples.IndexedFeedback
