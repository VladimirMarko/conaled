import SquareKit.Internal.DependentSheafComparison
import Examples.SheafFamilies

/-! Experimental finite interpretation of the same derived structural source
proof in two sheaf models. Source typing forbids a closed true-fiber inhabitant. -/
noncomputable section
namespace Examples.DependentSource
open CategoryTheory Limits Opposite SquareKit
open Internal.DependentStructural Internal.DependentStructural.SheafSem
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange
open Examples.SheafFamilies Examples.SheafFunctions

abbrev Γ : Ctx 1 := .base .nil
abbrev b : Base 1 := .var 0
abbrev Δ : Ctx 1 := .family Γ (.neg b)
abbrev Ξ : Ctx 1 := .family Δ .zero

def σ : Sub Δ Γ where
  base _ := .neg b
  dep | .base v => nomatch v
  typed | .base v => nomatch v
abbrev τ : Sub Ξ Δ := Sub.p Δ .zero
def argument : Tm Δ (.family (b.sub σ.base)) := ⟨.var .top, rfl⟩

/-- A source derivation over an extended dependent telescope, before selecting
any model. The substitution negates the base and uses the dependent variable. -/
theorem source_equation : SubEq (Sub.comp (Sub.pair σ b argument) τ)
    (Sub.pair (Sub.comp σ τ) b (substitutedArgument σ τ b argument)) :=
  pairing_naturality σ τ b argument

abbrev chosenUnit := ⊤_ (Sheaf topology Type)
def unitIso : chosenUnit ≅ SheafImage.terminal :=
  (Limits.terminalIsTerminal).uniqueUpToIso SheafImage.terminalIsTerminal

def falseModel : Model topology where
  B := D
  A := SplitSheaf.ofDisplay falsePoint
  zero := unitIso.hom ≫ falsePoint
  neg := negation
  point := unitIso.hom ≫ (SplitSheaf.displayIso falsePoint).inv
  point_type := by
    rw [Category.assoc, ← SplitSheaf.displayIso_projection, Iso.inv_hom_id_assoc]

/-- The rule-restricted source proof becomes an equality of actual sheaf maps. -/
theorem false_interpretation :
    substitution falseModel (Sub.comp (Sub.pair σ b argument) τ) =
      substitution falseModel (Sub.pair (Sub.comp σ τ) b (substitutedArgument σ τ b argument)) :=
  sound falseModel source_equation

abbrev false_ordinary := derived_ordinary falseModel σ τ b argument

/-- The nonidentity source operation really denotes Boolean negation. -/
theorem negation_value (U : Diamondᵒᵖ) (x : (context falseModel Δ).carrier.obj.obj U) :
    ((context falseModel Γ).base 0).hom.app U ((substitution falseModel σ).hom.app U x) =
      !((context falseModel Δ).base 0).hom.app U x :=
  congrArg (fun f => f.hom.app U x) (substitution_base falseModel σ 0)

/-- The open dependent context used by the source proof is inhabited in the
finite model: its base is true and its dependent value lies over its negation. -/
def trueBase : chosenUnit ⟶ (context falseModel Γ).carrier :=
  basePair falseModel (𝟙 chosenUnit) (unitIso.hom ≫ truePoint)

theorem trueBase_negation :
    trueBase ≫ evalBase falseModel (context falseModel Γ).base (.neg b) = falseModel.zero := by
  change trueBase ≫ (baseValue falseModel chosenUnit ≫ negation) = _
  have h := basePair_value falseModel (𝟙 chosenUnit) (unitIso.hom ≫ truePoint)
  exact (congrArg (fun k => k ≫ negation) h).trans rfl

def inhabitedContext : chosenUnit ⟶ (context falseModel Δ).carrier :=
  SplitSheaf.pair (type falseModel Γ (.family (.neg b))) trueBase
    (SplitSheaf.readTerm falseModel.A falseModel.point
      (falseModel.point_type.trans trueBase_negation.symm))

theorem inhabited_base : inhabitedContext ≫ (context falseModel Δ).base 0 = unitIso.hom ≫ truePoint := by
  change (inhabitedContext ≫ SplitSheaf.p (type falseModel Γ (.family (.neg b)))) ≫
    baseValue falseModel chosenUnit = _
  exact basePair_value falseModel (𝟙 chosenUnit) (unitIso.hom ≫ truePoint)

theorem inhabited_variable : inhabitedContext ≫ (context falseModel Δ).dep .top = falseModel.point :=
  SplitSheaf.pair_read falseModel.A falseModel.point (falseModel.point_type.trans trueBase_negation.symm)

/-- Any well-typed closed source inhabitant would interpret to an impossible
section of the actual empty true fiber. No semantic equality is a source rule. -/
theorem no_closed_true : ¬ Nonempty (Tm Ctx.nil (.family (.neg .zero))) := by
  rintro ⟨t⟩
  have h := (evalDep_type falseModel (context falseModel Ctx.nil) t.val).trans
    (congrArg (evalBase falseModel (context falseModel Ctx.nil).base) t.property)
  let x : chosenUnit.obj.obj (op X) := unitIso.inv.hom.app (op X) ()
  have hh := congrArg (fun f => f.hom.app (op X) x) h
  change ((SplitSheaf.p (SplitSheaf.ofDisplay falsePoint)).hom.app (op X)
    ((evalDep falseModel (context falseModel Ctx.nil) t.val).hom.app (op X) x)) = true at hh
  have hf (z : (SplitSheaf.Ext (SplitSheaf.ofDisplay falsePoint)).obj.obj (op X)) :
      (SplitSheaf.p (SplitSheaf.ofDisplay falsePoint)).hom.app (op X) z = false := z.2.property.symm
  exact Bool.noConfusion ((hf _).symm.trans hh)

abbrev endomorphisms := SheafFunction.exponential E E
def identityName : chosenUnit ⟶ endomorphisms := SheafFunction.curry (SheafRelation.fst E chosenUnit)

/-- An E-based interpretation of the primitive family, with the natural
identity section as the named primitive. No global E section is assumed. -/
def varyingModel : Model topology where
  B := D
  A := SplitSheaf.ofDisplay (SheafRelation.snd endomorphisms D)
  zero := unitIso.hom ≫ falsePoint
  neg := negation
  point := SheafRelation.lift identityName (unitIso.hom ≫ falsePoint) ≫
    (SplitSheaf.displayIso (SheafRelation.snd endomorphisms D)).inv
  point_type := by
    rw [Category.assoc, ← SplitSheaf.displayIso_projection, Iso.inv_hom_id_assoc]
    rfl

/-- Exactly the same source derivation is reused for the E-based model. -/
theorem varying_interpretation :
    substitution varyingModel (Sub.comp (Sub.pair σ b argument) τ) =
      substitution varyingModel (Sub.pair (Sub.comp σ τ) b (substitutedArgument σ τ b argument)) :=
  sound varyingModel source_equation

abbrev varying_ordinary := derived_ordinary varyingModel σ τ b argument

theorem identity_evaluation (U : Diamondᵒᵖ) (a : E.obj.obj U) (x : chosenUnit.obj.obj U) :
    (SheafFunction.evaluation E E).hom.app U (a, identityName.hom.app U x) = a :=
  SheafFunction.evaluation_curry_apply (SheafRelation.fst E chosenUnit) U a x

/-- The E-based application retains its nonconstant overlap restrictions. -/
theorem identity_wu (x : chosenUnit.obj.obj (op W)) :
    (SheafFunction.evaluation E E).hom.app (op W)
      (E.obj.map (show W ⟶ U from Arrow.wu).op (), identityName.hom.app (op W) x) = false :=
  identity_evaluation (op W) _ x

theorem identity_wv (x : chosenUnit.obj.obj (op W)) :
    (SheafFunction.evaluation E E).hom.app (op W)
      (E.obj.map (show W ⟶ V from Arrow.wv).op (), identityName.hom.app (op W) x) = true :=
  identity_evaluation (op W) _ x

end Examples.DependentSource
