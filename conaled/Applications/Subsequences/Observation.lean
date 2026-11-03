import Applications.Subsequences.Selection
import Applications.Optimization.Relations

/-! Witness and length observations of the same independent feasible problem. -/
set_option autoImplicit false
set_option warningAsError true
namespace Subsequences

def feasible (xs : List Int) : Set (List Int) := {p | p.Sublist xs ∧ Increasing p}

def objective (_ : List Int) (p : List Int) : OrderDual Nat := OrderDual.toDual p.length

theorem lusOptimal_iff_minimizer (xs p : List Int) :
    LusOptimal xs p ↔ p ∈ Optimization.minimizers (feasible xs) (objective xs) := by
  constructor
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, fun _ hp => h.2.2 _ hp.1 hp.2⟩
  · intro h
    exact ⟨h.1.1, h.1.2, fun _ hp hi => h.2 ⟨hp, hi⟩⟩

def witnessSquare : Relational.RelSquare (Optimization.inputRep (List Int))
    (Optimization.membershipRep (I := List Int) (id : List Int → List Int)) :=
  Optimization.selectionSquare feasible objective id lus
    (fun xs => (lusOptimal_iff_minimizer xs _).mp (lus_optimal xs))

def lengthSquare : Relational.RelSquare (Optimization.inputRep (List Int))
    (Optimization.membershipRep (I := List Int) (id : Nat → Nat)) :=
  Relational.compose (Optimization.observationSquare List.length) witnessSquare

theorem selected_witness_optimal (xs : List Int) : LusOptimal xs (lus xs) :=
  (lusOptimal_iff_minimizer xs _).mpr
    (witnessSquare.preserves (r := xs) (s := xs) rfl).2

theorem selected_length_attained (xs : List Int) :
    ∃ p, LusOptimal xs p ∧ p.length = (lengthSquare.impl xs).2 := by
  obtain ⟨p, hp, he⟩ := (lengthSquare.preserves (r := xs) (s := xs) rfl).2
  exact ⟨p, (lusOptimal_iff_minimizer xs p).mpr hp, he⟩

theorem selected_length_eq (xs p : List Int) (hp : LusOptimal xs p) :
    (lengthSquare.impl xs).2 = p.length := by
  obtain ⟨q, hq, he⟩ := selected_length_attained xs
  exact he.symm.trans (lusOptimal_length_eq xs q p hq hp)

end Subsequences
