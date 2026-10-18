import SquareKit.TypeFamilyCoherence
import Examples.SheafFamilies

/-! Experimental coherence consumers: a restricted dependent sheaf family and
an ordinary value-dependent Fin family, using the public comparison laws. -/
noncomputable section
namespace Examples.FamilyCoherence
open CategoryTheory Limits Opposite SquareKit.Family
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange
open Examples.SheafFunctions Examples.SheafFamilies

abbrev restricted := reindex reversedDisplay truePoint
abbrev tripleTerm := termSub (reindex (reindex restricted base) negation) negation
  (termSub (reindex restricted base) negation (termSub restricted base trueTerm))

/-- Both nonidentity-negation routes are equal as actual maps. -/
theorem sheaf_routes : innerRoute restricted base negation negation =
    outerRoute restricted base negation negation := associativity _ _ _ _

theorem sheaf_term_inner : tripleTerm.val ≫ innerRoute restricted base negation negation =
    (termSub restricted (negation ≫ (negation ≫ base)) trueTerm).val :=
  triple_term_inner _ _ _ _ _

theorem sheaf_term_outer : tripleTerm.val ≫ outerRoute restricted base negation negation =
    (termSub restricted (negation ≫ (negation ≫ base)) trueTerm).val :=
  triple_term_outer _ _ _ _ _

/-- The coherent transported term still lies over true, not the empty false fiber. -/
theorem transported_value :
    (tripleTerm.val ≫ innerRoute restricted base negation negation) ≫
      comparison restricted (negation ≫ (negation ≫ base)) ≫
        comparison reversedDisplay truePoint ≫ reversedDisplay =
          (negation ≫ (negation ≫ base)) ≫ truePoint := by
  rw [sheaf_term_inner]
  simp only [Category.assoc, termSub_comparison_assoc]
  rw [← Category.assoc trueTerm.val, trueTerm_value, trueLift_display]

theorem transported_at_X (b : Bool) :
    reversedDisplay.hom.app (op X)
      ((comparison reversedDisplay truePoint).hom.app (op X)
        ((comparison restricted (negation ≫ (negation ≫ base))).hom.app (op X)
          ((tripleTerm.val ≫ innerRoute restricted base negation negation).hom.app (op X) b))) = true :=
  congrArg (fun f : D ⟶ D => f.hom.app (op X) b) transported_value

/-- Both unit routes recover this restricted term's ordinary substitution. -/
theorem sheaf_right_unit :
    (termSub (reindex restricted base) (𝟙 D) (termSub restricted base trueTerm)).val ≫
      (compositionIso restricted base (𝟙 D)).hom ≫ (baseIso restricted (Category.id_comp base)).hom =
        (termSub restricted base trueTerm).val := right_unit_term _ _ _

theorem sheaf_left_unit :
    (termSub (reindex restricted (𝟙 _)) base (termSub restricted (𝟙 _) trueTerm)).val ≫
      (compositionIso restricted (𝟙 _) base).hom ≫ (baseIso restricted (Category.comp_id base)).hom =
        (termSub restricted base trueTerm).val := left_unit_term _ _ _

open SquareKit.TypeFamily

/-- Native dependent values with fibers of increasing finite size. -/
def finiteFamily (n : Nat) := Fin (n + 1)
def zeroTerm : DependentSquares.Tm finiteFamily := fun _ => ⟨0, Nat.zero_lt_succ _⟩

/-- Two successor substitutions use the actual split/categorical comparison square. -/
theorem finite_comparison :
    (pullbackIso (DependentSquares.tySub finiteFamily Nat.succ) Nat.succ).hom ≫
      SquareKit.Family.map (display (DependentSquares.tySub finiteFamily Nat.succ))
        (reindex (display finiteFamily) (↾Nat.succ)) (↾Nat.succ)
        (pullbackIso finiteFamily Nat.succ).hom (pullbackIso_display finiteFamily Nat.succ) ≫
          (compositionIso (display finiteFamily) (↾Nat.succ) (↾Nat.succ)).hom =
      (splitComposition finiteFamily Nat.succ Nat.succ).hom ≫
        (pullbackIso finiteFamily (DependentSquares.compSub Nat.succ Nat.succ)).hom :=
  composition_comparison _ _ _

/-- Term comparison uses the public split substitution theorem, then native zero. -/
theorem finite_term :
    (asSection (DependentSquares.tySub (DependentSquares.tySub finiteFamily Nat.succ) Nat.succ)
      (DependentSquares.tmSub (DependentSquares.tmSub zeroTerm Nat.succ) Nat.succ)).val ≫
      (splitComposition finiteFamily Nat.succ Nat.succ).hom ≫
        (pullbackIso finiteFamily (DependentSquares.compSub Nat.succ Nat.succ)).hom =
          (termSub (display finiteFamily) (↾(DependentSquares.compSub Nat.succ Nat.succ))
            (asSection finiteFamily zeroTerm)).val :=
  split_composition_term _ _ _ _

theorem finite_value (n : Nat) :
    ((comparison (display finiteFamily) (↾(DependentSquares.compSub Nat.succ Nat.succ)))
      ((termSub (display finiteFamily) (↾(DependentSquares.compSub Nat.succ Nat.succ))
        (asSection finiteFamily zeroTerm)).val n)).2.val = 0 := by
  have h := termSub_comparison (display finiteFamily)
    (↾(DependentSquares.compSub Nat.succ Nat.succ)) (asSection finiteFamily zeroTerm)
  have hn := congrArg (fun f : Nat ⟶ DependentSquares.Ext Nat finiteFamily => f n) h
  exact congrArg (fun z : DependentSquares.Ext Nat finiteFamily => z.2.val) hn
/-- The iterated split route also computes zero, by its public comparison. -/
theorem finite_route_value (n : Nat) :
    ((comparison (display finiteFamily) (↾(DependentSquares.compSub Nat.succ Nat.succ)))
      (((asSection (DependentSquares.tySub (DependentSquares.tySub finiteFamily Nat.succ) Nat.succ)
        (DependentSquares.tmSub (DependentSquares.tmSub zeroTerm Nat.succ) Nat.succ)).val ≫
        (splitComposition finiteFamily Nat.succ Nat.succ).hom ≫
          (pullbackIso finiteFamily (DependentSquares.compSub Nat.succ Nat.succ)).hom) n)).2.val = 0 := by
  rw [finite_term]
  exact finite_value n
end Examples.FamilyCoherence
