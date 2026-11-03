import SquareKit.Internal.RelativeSheafClassifier
import SquareKit.Internal.ClassifierBaseChange
import SquareKit.Internal.MixedClassifierModel
import SquareKit.Internal.GenericModelPullback
import SquareKit.Internal.ClassifierTransformation
import SquareKit.Internal.SheafPseudopullback
import SquareKit.Internal.GeometricMixedChange
import SquareKit.Internal.PartitionCoherence
import SquareKit.Internal.FiniteClassifierComparison
import SquareKit.Internal.PresheafClassifierComparison

/-! Arbitrary-source classification of the finite complementary-predicate theory.

`GeometricMorphism.relativeSheafClassifier` is the relative theorem over E/X
for represented sheaf toposes. `finiteClassifier` states the structural
categorical version. Both are equivalences of categories of genuine geometric
lifts and predicate-preserving models. `finiteClassifierPullbackIso` identifies
their interpretation functor with actual pullback of the generic model.

`sheafPseudopullback` retains varying base legs and arbitrary compatible
transformations. Source unit, composition and transformation diagrams appear
in `ClassifierPseudonaturality` and `ClassifierTransformation`; parameter and
context interchange use `PartitionCoherence` and `GeometricMixedChange`.
The old finite and presheaf model categories compare through explicit formed
object coproduct isomorphisms, preserving their original section maps.
-/
