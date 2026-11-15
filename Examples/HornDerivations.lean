import SquareKit.HornDerivations
import Examples.HornSupport

/-! Selected traces, shortest-proof reselection, and a changed Horn rule. -/
namespace Examples.HornDerivations
open SquareKit.HornSupport SquareKit.HornSupport.LabelledRule
open Examples.HornSupport
open Atom

inductive Label where
  | a | b | c | d | bprime | e
  deriving DecidableEq
open Label

abbrev table : Label → LabelledRule Atom
  | a => ⟨[], by simp, p⟩
  | b => ⟨[p], by simp, q⟩
  | c => ⟨[q], by simp, r⟩
  | d => ⟨[], by simp, q⟩
  | bprime => ⟨[p, r], by decide, q⟩
  | e => ⟨[p], by simp, r⟩

def L1 : Finset Label := {a, b}
def L2 : Finset Label := {a, b, c}
def L3 : Finset Label := {a, b, c, d}
def Lminus : Finset Label := {a, bprime}
def Lrepair : Finset Label := {a, bprime, e}

theorem inclusion12 : L1 ⊆ L2 := by decide
theorem inclusion23 : L2 ⊆ L3 := by decide

theorem L1_erasure : base table L1 = B1 := by decide
theorem L2_erasure : base table L2 = B2 := by decide

def tp : Tree table L1 p := .rule (R := rules table L1) ⟨a, by decide⟩ (fun i => Fin.elim0 i)
def tq : Tree table L1 q := .rule (R := rules table L1) ⟨b, by decide⟩ (Fin.cases tp (fun i => Fin.elim0 i))
def tr : Tree table L2 r := .rule (R := rules table L2) ⟨c, by decide⟩ (Fin.cases (map inclusion12 tq) (fun i => Fin.elim0 i))
def shortQ : Tree table L3 q := .rule (R := rules table L3) ⟨d, by decide⟩ (fun i => Fin.elim0 i)

theorem tq_trace : trace tq = [a, b] := rfl
theorem tr_trace : trace tr = [a, b, c] := rfl
theorem short_trace : trace shortQ = [d] := rfl
theorem copied_trace : trace (map inclusion23 (map inclusion12 tq)) = [a, b] := by
  simp [tq_trace]

theorem short_minimum : Shortest shortQ := by
  intro s
  have h := size_pos s
  change 1 ≤ size s
  omega

/-- Before the shortcut is added, every q tree must end in the unary b rule. -/
theorem old_minimum : Shortest (map inclusion12 tq) := by
  have lower {x : Atom} (s : Tree table L2 x) (hx : x = q) : 2 ≤ size s := by
    cases s with
    | hyp h => exact nomatch h
    | rule l ds =>
      rcases l with ⟨l, hl⟩
      have hm : l = a ∨ l = b ∨ l = c := by simpa [L2] using hl
      rcases hm with rfl | rfl | rfl
      · cases hx
      · simpa [size, trace, rules, table, List.ofFn_succ] using
          Nat.succ_le_succ (size_pos (ds 0))
      · cases hx
  intro s
  exact lower s rfl

/-- A valid minimum-node reselection changes the observed trace. -/
theorem reselection_changes :
    trace (map inclusion23 (map inclusion12 tq)) ≠ trace shortQ := by
  rw [copied_trace, short_trace]
  decide

/-- Ties cannot repair the trace mismatch: every minimum at L3 uses d. -/
theorem minimum_trace (s : Tree table L3 q) (h : Shortest s) : trace s = [d] := by
  have small {x : Atom} (t : Tree table L3 x) (hx : x = q)
      (bound : size t ≤ 1) : trace t = [d] := by
    cases t with
    | hyp h => exact nomatch h
    | rule l ds =>
      rcases l with ⟨l, hl⟩
      have hm : l = a ∨ l = b ∨ l = c ∨ l = d := by simpa [L3] using hl
      rcases hm with rfl | rfl | rfl | rfl
      · cases hx
      · have positive := size_pos (ds 0)
        have zero : trace (ds 0) = [] := by
          simpa [size, trace, List.ofFn_succ] using bound
        simp only [size] at positive
        rw [zero] at positive
        exact False.elim (Nat.not_lt_zero _ positive)
      · cases hx
      · rfl
  exact small s rfl (h shortQ)

theorem every_shortest_changes (s : Tree table L3 q) (h : Shortest s) :
    trace (map inclusion23 (map inclusion12 tq)) ≠ trace s := by
  rw [minimum_trace s h]
  exact reselection_changes

theorem fixed_base_no_recovery :
    ¬ ∃ recover : Derivable (base table L3) q → List Label,
      ∀ t : Tree table L3 q, recover (eraseTree t) = trace t :=
  no_trace_recovery _ _ reselection_changes

theorem minus_p : Derivable (base table Lminus) p :=
  .rule (table a).erase (by decide) (by simp [erase])

theorem minus_only_p {x : Atom} (h : Derivable (base table Lminus) x) : x = p := by
  apply h.invariant (fun x => x = p)
  intro rule hr children
  have hm : rule = (table a).erase ∨ rule = (table bprime).erase := by
    simpa [base, Lminus] using hr
  rcases hm with rfl | rfl
  · rfl
  · have impossible := children r (by simp [erase])
    cases impossible

theorem minus_not_q : ¬ Derivable (base table Lminus) q := by
  intro h
  cases minus_only_p h

theorem minus_not_pq :
    ¬ Support allBases (base table Lminus) (.imp (.atom p) (.atom q)) :=
  fun h => minus_not_q (application (Set.mem_univ _) h minus_p)

/-- Each old b use gets an additional r proof built from the same translated p
child. The recursion translates all old trees, not only the displayed q tree. -/
def repairMap : SquareKit.DependentTheoryMaps.TheoryMap
    (rules table L1) (rules table Lrepair) id where
  certificate l := by
    rcases l with ⟨l, hl⟩
    cases l
    · exact .rule (R := rules table Lrepair) ⟨a, by decide⟩ (fun i => Fin.elim0 i)
    · apply SquareKit.DependentTheoryMaps.Derivation.rule
        (R := rules table Lrepair) ⟨bprime, by decide⟩
      intro i
      refine Fin.cases ?_ ?_ i
      · exact .hyp ⟨0, rfl⟩
      · intro j
        refine Fin.cases ?_ (fun k => Fin.elim0 k) j
        exact .rule (R := rules table Lrepair) ⟨e, by decide⟩
          (Fin.cases (.hyp ⟨0, rfl⟩) (fun k => Fin.elim0 k))
    all_goals exact False.elim (by simp [L1] at hl)

def repair {x : Atom} (t : Tree table L1 x) : Tree table Lrepair x :=
  repairMap.transport (fun _ h => nomatch h) t

theorem repair_trace : trace (repair tq) = [a, a, e, bprime] := rfl
theorem repair_size : size (repair tq) = 4 := rfl
theorem repair_changes_trace : trace (repair tq) ≠ trace tq := by
  rw [repair_trace, tq_trace]
  decide

theorem repair_support :
    Support allBases (base table Lrepair) (.imp (.atom p) (.atom q)) := by
  intro D _ hD hp
  have hr : Derivable D r := .rule (table e).erase (hD (by decide)) (by
    simpa [table, erase, Support] using hp)
  apply Derivable.rule (table bprime).erase (hD (by decide))
  intro x hx
  simp [erase] at hx
  rcases hx with rfl | rfl
  · exact hp
  · exact hr
end Examples.HornDerivations
