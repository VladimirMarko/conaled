import SquareKit.Optional
import SquareKit.FunctionCategory

namespace SquareKit.FunctionCategory
universe u

def coproducts : CoproductOps ops.{u} where
  sum := Sum
  inl := Sum.inl
  inr := Sum.inr
  copair := Sum.elim

def distribution : DistributionOps ops.{u} products coproducts where
  distribute p := match p.2 with
    | .inl a => .inl (p.1, a)
    | .inr b => .inr (p.1, b)

def closed : ClosedOps ops.{u} products where
  exp a b := a → b
  evaluation p := p.1 p.2
  curry f x a := f (x, a)

theorem coproductCongr : CoproductCongr ops.{u} (equality _) coproducts where
  copair := by intros; subst_vars; rfl

theorem closedCongr : ClosedCongr (equality ops.{u}) products closed where
  curry := by intros; subst_vars; rfl
end SquareKit.FunctionCategory
