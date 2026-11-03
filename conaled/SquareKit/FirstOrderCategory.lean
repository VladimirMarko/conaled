import SquareKit.Category
import FirstOrder

/-! Compatibility operations for the existing first-order target. The adapter
requires no closure, function interpretation, or extra primitives. -/
namespace SquareKit.FirstOrderCategory
open FirstOrderCompiler
variable {Prim : Ty → Ty → Type} (K : Target Prim)

def ops : CategoryOps Ty where
  Hom := K.Hom
  ident := K.ident
  comp := K.comp

def terminal : TerminalOps (ops K) where
  unit := .unit
  terminal := K.terminal

def products : ProductOps (ops K) where
  prod := .prod
  fst := K.fst
  snd := K.snd
  pair := K.pair
end SquareKit.FirstOrderCategory
