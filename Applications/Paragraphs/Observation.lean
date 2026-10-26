import Applications.Paragraphs.Helper
import Applications.Optimization.Relations

/-! Layout and line-count observations preserve the same justified input problem. -/
set_option autoImplicit false
set_option warningAsError true
namespace Paragraphs

/-- Word-fit evidence is the actual realization premise, weaker than SourceInput. -/
abbrev Problem := {i : Nat × Text // AllWordsFit i.1 i.2}

def feasible (i : Problem) : Set Para := {p | FitPartition i.val.1 i.val.2 p}

theorem minimumLex_iff_minimizer (i : Problem) (p : Para) :
    MinimumLex i.val.1 i.val.2 p ↔ p ∈ Optimization.minimizers (feasible i) lexCost := by
  constructor
  · intro h
    exact ⟨h.1, fun q hq => (costLE_iff_lex p q).mp (h.2 q hq)⟩
  · intro h
    exact ⟨h.1, fun q hq => (costLE_iff_lex p q).mpr (h.2 hq)⟩

def witnessSquare : Relational.RelSquare (Optimization.inputRep Problem)
    (Optimization.membershipRep (I := Problem) (id : Para → Para)) :=
  Optimization.selectionSquare feasible (fun _ => lexCost) id
    (fun i => greedy i.val.1 i.val.2)
    (fun i => (minimumLex_iff_minimizer i _).mp
      (greedy_minimumLex i.val.1 i.val.2 i.property))

def lineCountSquare : Relational.RelSquare (Optimization.inputRep Problem)
    (Optimization.membershipRep (I := Problem) (id : Nat → Nat)) :=
  Relational.compose (Optimization.observationSquare cost1) witnessSquare

theorem selected_layout_optimal (i : Problem) :
    MinimumLex i.val.1 i.val.2 (greedy i.val.1 i.val.2) :=
  (minimumLex_iff_minimizer i _).mpr
    (witnessSquare.preserves (r := i) (s := i) rfl).2

theorem selected_lineCount_attained (i : Problem) :
    ∃ p, MinimumLex i.val.1 i.val.2 p ∧ cost1 p = (lineCountSquare.impl i).2 := by
  obtain ⟨p, hp, he⟩ := (lineCountSquare.preserves (r := i) (s := i) rfl).2
  exact ⟨p, (minimumLex_iff_minimizer i p).mpr hp, he⟩

theorem selected_lineCount_le (i : Problem) (q : Para) (hq : FitPartition i.val.1 i.val.2 q) :
    (lineCountSquare.impl i).2 ≤ cost1 q := by
  obtain ⟨p, hp, he⟩ := selected_lineCount_attained i
  rw [← he]
  exact costLE_count p q (hp.2 q hq)

theorem selected_lineCount_eq (i : Problem) (q : Para)
    (hq : MinimumLines i.val.1 i.val.2 q) : (lineCountSquare.impl i).2 = cost1 q := by
  obtain ⟨p, hp, he⟩ := selected_lineCount_attained i
  rw [← he]
  exact Nat.le_antisymm (costLE_count p q (hp.2 q hq.1)) (hq.2 p hp.1)

end Paragraphs
