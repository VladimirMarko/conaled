import Examples.TwoFamilyFrozenOrdinaryAction
namespace Examples.TwoFamilyFrozenOrdinaryAction
open CategoryTheory SquareKit.Internal.PathTransport HigherInterpretation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 3000
theorem pathType_subsingleton (γ : (show Context from paths.context)) :
 Subsingleton (pathType.data.obj γ) := by
 change Subsingleton (LocallyDiscrete (SingleObj (Multiplicative ℤ)))
 exact ⟨fun a b => by cases a; cases b; congr 1⟩
end Examples.TwoFamilyFrozenOrdinaryAction
