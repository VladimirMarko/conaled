import Examples.DependentPairTypedClient

/-! Independent meanings for the selected declaration fragment. These relations
cover the client's selected terms, not an interpretation of every raw expression. -/
namespace SquareKit.DependentPairSelectedMeaning
open DependentTheoryMaps DependentPairPresentations DependentPairTheoryTransport

/-- The eliminator presentation has its own quotation of the declaration fragment. -/
def eliminationExpression : IndexTerm V → EExpr V
  | .var v => .var v
  | .successor e => DependentPairDeclarations.Elimination.s (eliminationExpression e)
  | .double e => DependentPairDeclarations.Elimination.d (eliminationExpression e)

theorem translated_index (e : IndexTerm V) : G.act e.expression = eliminationExpression e := by
  induction e with
  | var v => exact G.on_var v
  | successor e ih =>
    change G.act (DependentPairDeclarations.Terms.s DependentPairDeclarations.projection e.expression) = _
    rw [DependentPairDeclarations.G_s, ih]
    rfl
  | double e ih =>
    change G.act (DependentPairDeclarations.Terms.d DependentPairDeclarations.projection e.expression) = _
    rw [DependentPairDeclarations.G_d, ih]
    rfl

/-- The full selected dependent tuple, including its index and both witnesses. -/
def selectedValue (ρ : V → Nat) (e : IndexTerm V) : DependentPairTheoryModels.ClientContext :=
  ⟨DependentPairTheoryModels.s (e.meaning ρ), DependentPairTheoryModels.t (e.meaning ρ), selectedMeaning ρ e⟩

inductive ProjectionMeaning (ρ : V → Nat) : PExpr V → DependentPairTheoryModels.ClientContext → Prop where
  | selected (e : IndexTerm V) : ProjectionMeaning ρ (DependentPairDeclarations.Projection.u e.expression) (selectedValue ρ e)

inductive EliminationMeaning (ρ : V → Nat) : EExpr V → DependentPairTheoryModels.ClientContext → Prop where
  | selected (e : IndexTerm V) :
      EliminationMeaning ρ (DependentPairDeclarations.Elimination.u (eliminationExpression e)) (selectedValue ρ e)

/-- The relation retains the whole selected tuple, rather than its inhabitation. -/
theorem meaning_preserved {ρ : V → Nat} {e : PExpr V} {value : DependentPairTheoryModels.ClientContext}
    (h : ProjectionMeaning ρ e value) : EliminationMeaning ρ (G.act e) value := by
  cases h with
  | selected e =>
    change EliminationMeaning ρ (G.act (DependentPairDeclarations.Terms.u DependentPairDeclarations.projection e.expression)) _
    rw [DependentPairDeclarations.G_u, translated_index]
    exact .selected e

def finalValue : DependentPairTheoryModels.ClientContext := ⟨5, ⟨5, by decide⟩, ⟨6, by decide⟩⟩

/-- This is the exact expression indexed by the closed `selectedTwice` derivation. -/
theorem source_selected : ProjectionMeaning (fun _ : SingleV => 2)
    (u (d (.var m))) finalValue := .selected finalIndex

theorem target_selected : EliminationMeaning (fun _ : SingleV => 2)
    (G.act (u (d (.var m)))) finalValue := meaning_preserved source_selected

theorem same_fixture : finalValue = DependentPairTheoryModels.sigma (DependentPairTheoryModels.tau 2) := rfl

theorem selected_six : finalValue.2.2 = (⟨6, by decide⟩ : Fin 7) := rfl

theorem selected_not_zero : finalValue.2.2 ≠ (⟨0, by decide⟩ : Fin 7) := by
  intro h
  have hval := congrArg Fin.val h
  change (6 : Nat) = 0 at hval
  omega

end SquareKit.DependentPairSelectedMeaning
