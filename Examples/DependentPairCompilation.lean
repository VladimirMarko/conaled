import Examples.DependentPairSelectedMeaning
import SquareKit.DependentPairTheoryMap
import SquareKit.DependentProjectionBoundaries
import SquareKit.DependentEliminationBoundaries

/-! The selected dependent client uses both translations and both substitutions. -/
namespace SquareKit.DependentPairCompilation
open DependentTheoryMaps DependentPairPresentations DependentPairJudgments
open DependentPairTheoryTransport DependentPairTypedClient
open Judgment

/-- Compile the original selected-variable derivation. -/
def original : Derivation eliminationPresentation (fun _ => Empty)
    (map G (term Γ selectedRaw clientType)) := compile selectedClient

/-- Compile after the first nonidentity typed substitution. -/
def afterSigma : Derivation eliminationPresentation (fun _ => Empty)
    (map G (term Γn (u (.var m)) (Expr.subst sigmaRaw clientType))) := compile selectedSigma

/-- Compile after both substitutions without replacing the selected term. -/
def afterBoth : Derivation eliminationPresentation (fun _ => Empty)
    (map G (term Γn (u (d (.var m))) (Expr.subst tauRaw (Expr.subst sigmaRaw clientType)))) :=
  compile selectedTwice

/-- The staged and assembled routes retain exactly the same ordinary proof tree. -/
theorem staged_afterBoth : pairPipeline.run selectedTwice = afterBoth :=
  pipeline_compiles selectedTwice

/-- Compression to one certificate map also retains the selected proof tree. -/
theorem compressed_afterBoth :
    fullFG.transportClosed (TypedSubstitution.fullEliminationLocal _) selectedTwice = afterBoth :=
  compressed_compiles selectedTwice

/-- The target expression is the independently declared target section at d(k). -/
theorem target_expression : G.act (u (d (.var m))) =
    DependentPairDeclarations.Elimination.u (DependentPairDeclarations.Elimination.d (.var m)) := by
  change G.act (DependentPairDeclarations.Terms.u DependentPairDeclarations.projection
    (DependentPairDeclarations.Terms.d DependentPairDeclarations.projection (.var m))) = _
  rw [DependentPairDeclarations.G_u, DependentPairDeclarations.G_d, G.on_var]

def sourceBoundary := projectionPresuppositions false selectedTwice
def targetBoundary := eliminationPresuppositions afterBoth

/-- Both the checked derivation and the independently defined selected meaning
refer to the same compiled expression. -/
structure SelectedCompilation where
  derivation : Derivation eliminationPresentation (fun _ => Empty)
    (map G (term Γn (u (d (.var m))) (Expr.subst tauRaw (Expr.subst sigmaRaw clientType))))
  meaning : DependentPairSelectedMeaning.EliminationMeaning (fun _ : SingleV => 2)
    (G.act (u (d (.var m)))) DependentPairSelectedMeaning.finalValue

def selected : SelectedCompilation := ⟨afterBoth, DependentPairSelectedMeaning.target_selected⟩

/-- The selected witness is six, not an arbitrary member of the same fiber. -/
theorem selected_value : DependentPairSelectedMeaning.finalValue.2.2 = (⟨6, by decide⟩ : Fin 7) :=
  DependentPairSelectedMeaning.selected_six

end SquareKit.DependentPairCompilation
