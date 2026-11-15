import SquareKit.Internal.PathTransport.CechMatchingConstant
import SquareKit.SmoothQuotientGeneratedMatchingFibers
import SquareKit.Internal.PathTransport.CechMatchingSetFamily
import Mathlib.CategoryTheory.SingleObj

/-! Relative matching does not discard automorphisms in its fibers. -/
noncomputable section
namespace Examples.GeneratedMatchingFibers
open CategoryTheory SquareKit.Internal.PathTransport

abbrev Loops := SingleObj (Multiplicative ℤ)

/-- For the identity projection, a fiber object still has its selected base arrow. -/
example (x : Loops) (g : x ⟶ x) :
    (((GroupoidFiberDecomposition.family (𝟭 Loops)).map g).obj
      (CostructuredArrow.mk (𝟙 x))).left = x := rfl

/-- The total decomposition keeps every original arrow, with no discreteness hypothesis. -/
example : (GroupoidFiberDecomposition.forget (𝟭 Loops)).Full := inferInstance

/-- A constant set family with identity comparisons accepts every local value
on an identity display. -/
example (C : Grpd.{0,0}) (d : CechMatching.Datum (CechMatching.constant C))
    (x : ℕ) :
    ∃ y : CechMatching.SetFamily.Fiber ((Functor.const C).obj ℕ)
      ((Functor.const C).obj ℕ) (𝟙 _) (𝟙 _) d, y.val = x := by
  exact ⟨⟨x, rfl⟩, rfl⟩

end Examples.GeneratedMatchingFibers
