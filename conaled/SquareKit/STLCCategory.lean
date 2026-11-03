import SquareKit.Category
import Compiler
import SquareKit.Optional

/-! Compatibility operations for the existing full-source target. The adapter
keeps all optional capabilities separate from category and product operations. -/
namespace SquareKit.STLCCategory
open CategoricalCompiler
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
def coproducts : CoproductOps (ops K) where
  sum := .sum
  inl := K.inl
  inr := K.inr
  copair := K.copair

def distribution : DistributionOps (ops K) (products K) (coproducts K) where
  distribute := K.dist

def closed : ClosedOps (ops K) (products K) where
  exp := .arr
  evaluation := K.apply
  curry := K.curry
end SquareKit.STLCCategory
