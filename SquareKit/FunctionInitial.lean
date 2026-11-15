import SquareKit.Initial
import SquareKit.FunctionCategory

namespace SquareKit.FunctionCategory
universe u

def initial : InitialOps ops.{u} where
  zero := PEmpty
  initial := PEmpty.elim

theorem initialLaws : InitialLaws (equality ops.{u}) initial :=
  ⟨fun _ => funext fun x => PEmpty.elim x⟩
end SquareKit.FunctionCategory
