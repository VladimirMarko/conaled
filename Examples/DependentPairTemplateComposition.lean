import SquareKit.DependentTemplateComposition
import SquareKit.DependentPairTemplates
import Examples.DependentPairCompilation

/-! The concrete expanding projection template participates in generic finite
composition before its interpretation as a syntax map. -/
namespace SquareKit.DependentPairPresentations.Templates
open DependentTheoryMaps

/-- Identity followed by the actual G expansion is constructed as finite
closed templates and interpreted through the generic composition theorem. -/
def FGtemplate : TemplateMap projectionSignature eliminationSignature :=
  TemplateMap.comp (TemplateMap.identity projectionSignature) Gtemplate

theorem FGtemplate_act (e : PExpr V) :
    (TemplateMap.toSyntax FGtemplate).act e = G.act e := by
  rw [FGtemplate, TemplateMap.identity_comp_act, Gtemplate_act]

/-- The selected expression after both substitutions uses that same composed
finite-template action, rather than an unrelated raw translation. -/
theorem selected_template_action :
    (TemplateMap.toSyntax FGtemplate).act
      (DependentPairTheoryTransport.u (DependentPairTheoryTransport.d
        (.var DependentPairTheoryTransport.m))) =
      DependentPairDeclarations.Elimination.u (DependentPairDeclarations.Elimination.d
        (.var DependentPairTheoryTransport.m)) := by
  rw [FGtemplate_act]
  exact DependentPairCompilation.target_expression

end SquareKit.DependentPairPresentations.Templates
