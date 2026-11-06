import SquareKit.Internal.Cubical.Judgments.IntervalsTheory

/-! Source double reversal retains an arbitrary represented interval section,
including the generic variable rather than only its two endpoints. -/
namespace Examples.CubicalSourceIntervals
set_option backward.isDefEq.respectTransparency false
open CategoryTheory SquareKit SquareKit.Cubical Source
open GuardedTheory Intervals Presheaf

noncomputable def doubleNegSource : Derivation theory
    (List.ofFn (conversionRule (.neg (.neg (.var (0 : Fin 1)))) (.var 0)).premise)
    (conversionRule (.neg (.neg (.var (0 : Fin 1)))) (.var 0)).conclusion := by
  have d := Derivation.rule (T := theory) (.inr (.conversion (Expr.Conv.neg_neg (.var (0 : Fin 1)))))
    GuardedTheory.Term.var (fun i => .hypothesis (List.mem_ofFn.mpr ⟨i,rfl⟩))
  simpa only [theory,Theory.extend,Intervals.rule,Atom.subst_id] using d

theorem source_double_neg (Γ : Context) (r : Presheaf.Term (Presheaf.interval Γ)) :
    intervalDimension (.neg (.neg (.var (0 : Fin 1)))) (fun _ => r) = r := by
  have h := interpret doubleNegSource (Matrix.vecCons (.context Γ) (fun _ : Fin 1 => .term Γ (Presheaf.interval Γ) r)) (by
    intro p hp
    rcases List.mem_ofFn.mp hp with ⟨i,rfl⟩
    fin_cases i
    · exact ⟨Γ,rfl⟩
    · exact ⟨Γ,Presheaf.interval Γ,r,rfl,rfl,rfl⟩)
  change extraOperation (.dimension (.neg (.neg (.var (0 : Fin 1)))))
      (Matrix.vecCons (.context Γ) (fun i => .term Γ (Presheaf.interval Γ) ((fun _ => r) i))) =
    extraOperation (.dimension (.var (0 : Fin 1)))
      (Matrix.vecCons (.context Γ) (fun i => .term Γ (Presheaf.interval Γ) ((fun _ => r) i))) at h
  rw [extra_dimension,extra_dimension,intervalDimension_var] at h
  exact eq_of_heq (Value.term.inj h).2.2

abbrev line : Context := total (Presheaf.interval terminal)
def coordinate : Presheaf.Term (Presheaf.interval line) := Presheaf.generic (Presheaf.interval terminal)

theorem source_double_neg_at_variable :
    (intervalDimension (.neg (.neg (.var (0 : Fin 1)))) (fun _ => coordinate)).val
      (line.elementsMk (Opposite.op ⟨1⟩) ⟨PUnit.unit,⟨Cube.identity ⟨1⟩⟩⟩) =
      ULift.up (Cube.identity ⟨1⟩) := by
  rw [source_double_neg]
  rfl

end Examples.CubicalSourceIntervals
