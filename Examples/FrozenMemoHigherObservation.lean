import Examples.FrozenMemoStages
import SquareKit.Internal.PathTransport.TwoFamilyModelVariable
noncomputable section
namespace Examples.FrozenMemoStages
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport HigherInterpretation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u})
local notation "M" => structuralModel C D
variable (A : Family Context.empty) (B : Family A.total)
abbrev higherInputContext : Context := inputContext M A B

def selectedHomotopy_payload (z : higherInputContext C D A B) :=
  variable_two_weaken C D (parallel M A B).identity (qFamily M A B) (uFamily M A B) z
end Examples.FrozenMemoStages
