import Applications.ClassicalControl.Adequacy
import Applications.ClassicalControl.Frames
import Applications.ClassicalControl.LastPolicy

/-! Experimental bounded classical-control construction (#380). Logical
adequacy and search correctness are deliberately exercised as separate contracts. -/
namespace ClassicalControl.Examples

open Source

def frameSearch (L : List Nat) : Target.Term 0 :=
  .app .cc (.lam (.walk (.var 0) L 0 []))

theorem search_related (L : List Nat) :
    Representation.StateRel (.run (search L) (.out L)) (.run (frameSearch L) (.out L)) :=
  .run (.app .cc (.lam (.walk .var))) .out

theorem frame_search_complete (L : List Nat) :
    Target.Runs (.run (frameSearch L) (.out L)) (.deliver L (direct L)) ∧ First L (direct L) :=
  ⟨(Representation.observations (search_related L) L (direct L)).mp (search_runs_direct L), direct_first L⟩

theorem multiple_witnesses :
    Runs (.run (search [1,2,4]) (.out [1,2,4])) (.deliver [1,2,4] (.found 1 2 1 [0])) ∧
    First [1,2,4] (.found 1 2 1 [0]) := by
  simpa [direct, prependOdd] using
    (show Runs (.run (search L₀) (.out L₀)) (.deliver L₀ (direct L₀)) ∧ First L₀ (direct L₀) from
      ⟨search_runs_direct L₀, direct_first L₀⟩)

theorem all_odd :
    Target.Runs (.run (frameSearch [1,3,5]) (.out [1,3,5])) (.deliver [1,3,5] (.none [0,1,2])) ∧
    First [1,3,5] (.none [0,1,2]) := by
  simpa [direct, prependOdd] using frame_search_complete [1,3,5]

theorem empty_input :
    Target.Runs (.run (frameSearch []) (.out [])) (.deliver [] (.none [])) ∧ First [] (.none []) :=
  frame_search_complete []

theorem position_zero :
    Target.Runs (.run (frameSearch [0,2]) (.out [0,2])) (.deliver [0,2] (.found 0 0 0 [])) ∧
    First [0,2] (.found 0 0 0 []) := by
  simpa [direct] using frame_search_complete [0,2]

/-- This is the mixed initializer case omitted by a pure-core substitution lemma. -/
theorem initializer_substitution (L : List Nat) :
    Representation.TermRel
      ((Term.walk (.var 0) L 0 []).subst (single (n := 0) (.saved (.out L))))
      ((Target.Term.walk (.var 0) L 0 []).subst (Target.single (n := 0) (.saved (.out L)))) :=
  Representation.beta_subst (.walk .var) (.saved .out)

theorem open_test_substitution (L : List Nat) (j : Nat) (O : List Nat) :
    Representation.TermRel
      ((Term.test (.var 0) L j O).subst (single (n := 0) (.saved (.out L))))
      ((Target.Term.test (.var 0) L j O).subst (Target.single (n := 0) (.saved (.out L)))) :=
  Representation.beta_subst (.test .var) (.saved .out)

/-- The relation keeps the unvisited suffix position and every oddness witness. -/
theorem pending_suffix (L : List Nat) (j : Nat) (O : List Nat) :
    Representation.StackRel
      (.cb (callback (.saved (.out L)) L j O) (.out L))
      (.next (.saved (.out L)) L j O (.out L)) :=
  .callback (.saved .out) .out (fun _ => rfl)

/-- Restoring the saved output stack discards the whole pending callback tail. -/
theorem discard_suffix (L : List Nat) (j n h : Nat) (O : List Nat) (ρ : Stack) :
    Step (.run (.saved (.out L))
      (.arg (.ret (.found j n h O)) (.cb (callback (.saved (.out L)) L j O) ρ)))
      (.run (.ret (.found j n h O)) (.out L)) := .restore

theorem no_prefix_for_later_even (O : List Nat) : ¬ First L₀ (.found 2 4 2 O) := by
  intro h
  have he := first_eq_direct h
  simp [direct, prependOdd] at he

example : Pgood.holds (.run (search L₀) (.out L₀)) := search_good
example : Pgood.holds (.run (.last L₀ 0 none []) (.out L₀)) := changed_policy_good
example : ¬ First L₀ (.found 2 4 2 []) := later_even_not_first
example : ¬ Pgood.holds (.deliver L₀ (.found 0 1 0 [])) := invalid_terminal
example : universalPole.holds (.deliver L₀ (.found 0 1 0 [])) := universal_accepts_invalid

/-- The same pole interprets Peirce independently of the search theorem. -/
example (atoms : Nat → Set Stack) (A B : Formula) :
    Realizes Pgood atoms (.imp (.imp (.imp A B) A) A) .cc := peirce Pgood atoms A B

example (P : Pole) (atoms : Nat → Set Stack) (A : Formula) :
    Realizes P atoms (.imp A A) (.lam (.var 0)) := by
  have ht : HasType (fun i : Fin 0 => Fin.elim0 i) (.lam (.var 0)) (.imp A A) := .lam .var
  simpa using adequacy P atoms ht Term.var (fun i => Fin.elim0 i)

example (t : Term 0) : ¬ HasType (fun i : Fin 0 => Fin.elim0 i) t .bottom :=
  no_closed_bottom t _

example : decode [1,2,4] (.found 1 2 1 [0]) = some (.found 1 2 1 [0]) :=
  (decode_correct _ _).mpr multiple_witnesses.2

example : decode [1,2,4] (.found 2 4 2 []) = none := by decide
example : decode [1,3,5] (.none [0,1,2]) = some (.none [0,1,2]) :=
  (decode_correct _ _).mpr all_odd.2
example : decode [1] (.odd 0) = none := rfl

example (L : List Nat) : Acc (fun t s => Step s t) (.run (search L) (.out L)) :=
  search_normalizes L

example (L : List Nat) :
    Acc (fun t s => Target.Step s t) (.run (frameSearch L) (.out L)) :=
  Representation.target_normalizes (search_normalizes L) (search_related L)

end ClassicalControl.Examples
