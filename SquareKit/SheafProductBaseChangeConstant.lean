import SquareKit.SheafProductBaseChange

/-! Experimental compatibility of canonical dependent-product base change with
constant families and their previously constructed exponential comparison. -/
noncomputable section
namespace SquareKit.SheafProductBaseChange
open CategoryTheory Limits SheafRelation
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (A Γ B : Sheaf J (Type (max u v)))

/-- The old constant-family product, pulled back to the parameter sheaf. -/
abbrev constantSource := (Over.pullback (SheafTerminalProduct.terminalMap Γ)).obj
  ((SheafTerminalProduct.pi A).obj (Over.mk (snd B A)))

/-- Base change of the old section/exponential comparison in value coordinates. -/
def oldConstantValue : (constantSource A Γ B).left ⟶ SheafFunction.exponential A B :=
  pullback.fst ((SheafTerminalProduct.pi A).obj (Over.mk (snd B A))).hom
    (SheafTerminalProduct.terminalMap Γ) ≫ (SheafTerminalProduct.sectionsIso (snd B A)).hom ≫
      (SheafSections.constantIso A B).hom

/-- Original terminal-product evaluation through its section comparison. -/
theorem old_evaluation :
    SheafFunction.parameterMap A
      (pullback.fst ((SheafTerminalProduct.pi A).obj (Over.mk (snd B A))).hom
        (SheafTerminalProduct.terminalMap Γ)) ≫
      (SheafSections.parameterComparison A (SheafTerminalProduct.object (snd B A))).hom ≫
        ((TerminalProduct.pullbackComparison A).inv.app
          ((SheafTerminalProduct.pi A).obj (Over.mk (snd B A)))).left ≫
            ((SheafTerminalProduct.adjunction A).counit.app (Over.mk (snd B A))).left ≫ fst B A =
    SheafFunction.parameterMap A (oldConstantValue A Γ B) ≫ SheafFunction.evaluation A B := by
  have hc := congrArg (fun k => k ≫ fst B A)
    (SheafTerminalProduct.counit_comparison (snd B A))
  simp only [Category.assoc] at hc
  erw [hc, ← SheafSections.constantIso_evaluation (Γ := A) (B := B)]
  ext U x
  rfl

/-- The input-family pullback comparison preserves the evaluated value. -/
theorem input_evaluation :
    ((Over.pullback (fst A Γ)).map
      ((SheafTerminalProduct.adjunction A).counit.app (Over.mk (snd B A)))).left ≫
        (inputIso A Γ B).hom.left ≫ fst B (product A Γ) =
    pullback.fst (pullback.snd ((SheafTerminalProduct.pi A).obj (Over.mk (snd B A))).hom
      (SheafTerminalProduct.terminalMap A)) (fst A Γ) ≫
        ((SheafTerminalProduct.adjunction A).counit.app (Over.mk (snd B A))).left ≫ fst B A := by
  change _ ≫ (SheafFamily.constantIso B (fst A Γ)).hom ≫ _ = _
  rw [SheafFamily.constantIso_comparison]
  simp only [Over.pullback_map_left, Family.comparison]
  erw [pullback.lift_fst_assoc]
  rfl

/-- Base-changed old evaluation through both explicit pullback comparisons. -/
theorem constant_body_evaluation :
    (SheafProjectionProduct.parameterIso A Γ (constantSource A Γ B)).inv ≫
      ((DependentBaseChange.pullbackComparison (square A Γ)).app
        ((SheafTerminalProduct.pi A).obj (Over.mk (snd B A)))).left ≫
      ((Over.pullback (fst A Γ)).map
        ((SheafTerminalProduct.adjunction A).counit.app (Over.mk (snd B A)))).left ≫
      (inputIso A Γ B).hom.left ≫ fst B (product A Γ) =
    SheafFunction.parameterMap A (oldConstantValue A Γ B) ≫ SheafFunction.evaluation A B := by
  have hi := congrArg (fun k =>
    (SheafProjectionProduct.parameterIso A Γ (constantSource A Γ B)).inv ≫
      ((DependentBaseChange.pullbackComparison (square A Γ)).app
        ((SheafTerminalProduct.pi A).obj (Over.mk (snd B A)))).left ≫ k)
      (input_evaluation A Γ B)
  have hp := congrArg (fun k => k ≫
    ((SheafTerminalProduct.adjunction A).counit.app (Over.mk (snd B A))).left ≫ fst B A)
    (parameter_comparison A Γ ((SheafTerminalProduct.pi A).obj (Over.mk (snd B A))))
  simp only [Category.assoc] at hp
  exact hi.trans (hp.trans (old_evaluation A Γ B))

/-- Evaluation of the canonical mate, with explicit parameter and value comparisons. -/
abbrev constant_evaluation := DependentBaseChange.WithAdjunction.evaluation_of (square A Γ)
  (SheafTerminalProduct.adjunction A) (SheafProjectionProduct.adjunction A Γ) (Over.mk (snd B A))
  (SheafProjectionProduct.parameterIso A Γ (constantSource A Γ B)).inv
  ((inputIso A Γ B).hom.left ≫ fst B (product A Γ))
  (SheafFunction.parameterMap A (oldConstantValue A Γ B) ≫ SheafFunction.evaluation A B)
  (constant_body_evaluation A Γ B)

/-- Evaluate the old family after the two pullbacks and identify the input family. -/
def constantBody : (Over.pullback (snd A Γ)).obj (constantSource A Γ B) ⟶
    Over.mk (snd B (product A Γ)) :=
  (DependentBaseChange.pullbackComparison (square A Γ)).app
    ((SheafTerminalProduct.pi A).obj (Over.mk (snd B A))) ≫
      (Over.pullback (fst A Γ)).map
        ((SheafTerminalProduct.adjunction A).counit.app (Over.mk (snd B A))) ≫ (inputIso A Γ B).hom

/-- Transposing that evaluation is transport through the canonical mate. -/
def constantTransport : constantSource A Γ B ⟶
    (SheafProjectionProduct.pi A Γ).obj (Over.mk (snd B (product A Γ))) :=
  (SheafProjectionProduct.adjunction A Γ).homEquiv (constantSource A Γ B)
    (Over.mk (snd B (product A Γ))) (constantBody A Γ B)

/-- The transported map is exactly mate followed by the input-family comparison. -/
abbrev constantTransport_eq_mate := DependentBaseChange.WithAdjunction.transpose_map (square A Γ)
  (SheafTerminalProduct.adjunction A) (SheafProjectionProduct.adjunction A Γ) (Over.mk (snd B A))
  (Over.mk (snd B (product A Γ))) (inputIso A Γ B).hom

/-- Uncurrying the transported family map recovers exponential evaluation. -/
theorem constantTransport_evaluation :
    (SheafProjectionProduct.parameterIso A Γ (constantSource A Γ B)).inv ≫
      (((SheafProjectionProduct.adjunction A Γ).homEquiv (constantSource A Γ B)
        (Over.mk (snd B (product A Γ)))).symm (constantTransport A Γ B)).left ≫
          fst B (product A Γ) =
    SheafFunction.parameterMap A (oldConstantValue A Γ B) ≫ SheafFunction.evaluation A B := by
  rw [constantTransport, Equiv.symm_apply_apply]
  exact constant_body_evaluation A Γ B

/-- The canonical mate commutes with both existing constant-family comparisons. -/
theorem constant_comparison :
    constantTransport A Γ B ≫ (SheafProjectionProduct.constantIso A Γ B).hom =
      (SheafProjectionProduct.constantMaps (constantSource A Γ B)
        (SheafFunction.exponential A B)).symm (oldConstantValue A Γ B) := by
  have hn := SheafProjectionProduct.constantHomEquiv_natural
    (𝟙 ((SheafProjectionProduct.pi A Γ).obj (Over.mk (snd B (product A Γ)))))
    (constantTransport A Γ B)
  change _ ≫ SheafProjectionProduct.constantHomEquiv A Γ B _ (𝟙 _) = _
  rw [← hn, Category.comp_id]
  apply (SheafProjectionProduct.constantMaps (constantSource A Γ B)
    (SheafFunction.exponential A B)).injective
  change SheafFunction.curry ((SheafProjectionProduct.parameterIso A Γ (constantSource A Γ B)).inv ≫
    (((SheafProjectionProduct.adjunction A Γ).homEquiv (constantSource A Γ B)
      (Over.mk (snd B (product A Γ)))).symm (constantTransport A Γ B)).left ≫
        fst B (product A Γ)) = oldConstantValue A Γ B
  rw [constantTransport_evaluation, ← SheafFunction.uncurry_evaluation]
  exact SheafFunction.eta _

end SquareKit.SheafProductBaseChange
