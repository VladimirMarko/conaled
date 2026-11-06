import SquareKit.Internal.Cubical.CocycleFilling
import SquareKit.Internal.Cubical.CocycleSecondIdentity
import SquareKit.Internal.Cubical.ContextualModel

/-! A dependent rooted-path family in the same constructed cubical model. -/
noncomputable section
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf

abbrev cocycleBase : LawfulFamily terminal.{0} := lawfulCocycleFamily terminal

/-- Its endpoint is the generic cocycle, not a constant point. -/
def cocycleRootedFamily : LawfulFamily (total cocycleBase.family) :=
  (cocycleBase.reindex (projection cocycleBase.family)).identity
    ((zeroTerm terminal).reindex (projection cocycleBase.family)) (generic cocycleBase.family)

def cocycleModel := Contextual.model cocycleBase cocycleRootedFamily

end SquareKit.Cubical.CategoryCocycles
