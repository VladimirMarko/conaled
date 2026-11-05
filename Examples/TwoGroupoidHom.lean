import SquareKit.Internal.PathTransport.TwoGroupoidHom
import SquareKit.Internal.PathTransport.TwoGroupoidPath
import SquareKit.Internal.PathTransport.StrictTwoTransformation

/-! The general hom construction must retain nontrivial fiber 2-cells as well
as the nontrivial base components of the original path-family discriminator. -/
namespace Examples.TwoGroupoidHom
open CategoryTheory SquareKit
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev A := DoubleDelooping.Space (Multiplicative ℤ)
abbrev x : A := DoubleDelooping.point (Multiplicative ℤ)
abbrev f : x ⟶ x := DoubleDelooping.arrow (Multiplicative ℤ)

def E : Discrete Unit ⥤ A := (Functor.const _).obj x

def a : TwoGroupoidHom.Total E x := TwoGroupoidHom.arrow E x ⟨()⟩ f

/-- The base component is reflexivity, but the fiber cell is the supplied integer. -/
def fiberLoop (n : ℤ) : a ⟶ a :=
  TwoGroupoidHom.cell (𝟙 (Discrete.mk ())) (Multiplicative.ofAdd n)

theorem fiberLoop_detect (n : ℤ) :
    Multiplicative.toAdd (TwoGroupoidHom.fiberCell (fiberLoop n)) = n := rfl

/-- A locally discrete replacement of the fiber would erase this distinction. -/
theorem fiber_one_ne_zero : fiberLoop 1 ≠ fiberLoop 0 := by
  intro h
  have := congrArg (fun p : a ⟶ a =>
    Multiplicative.toAdd (TwoGroupoidHom.fiberCell p)) h
  change (1 : ℤ) = 0 at this
  omega

/-- Evaluation of a base 2-cell in the original path fiber. -/
def pathEvaluation : TwoGroupoidPath.Fiber ⥤ LocallyDiscrete TwoGroupoidPath.Fiber where
  obj c := ⟨c⟩
  map m := ⟨m⟩

def pathTarget : LocallyDiscrete TwoGroupoidPath.Fiber :=
  ⟨SingleObj.star (Multiplicative ℤ)⟩

def pathArrow (n : ℤ) : TwoGroupoidHom.Total pathEvaluation pathTarget :=
  TwoGroupoidHom.arrow pathEvaluation pathTarget (SingleObj.star (Multiplicative ℤ))
    (Discrete.mk (Multiplicative.ofAdd n))

/-- The old concrete cell is admitted by the general hom construction. -/
def pathCell {m n : ℤ} (p : TwoGroupoidPath.Cell m n) : pathArrow m ⟶ pathArrow n :=
  TwoGroupoidHom.cell (Multiplicative.ofAdd p.base)
    (eqToHom (Discrete.ext p.boundary))

/-- Conversely every cell of this specialization retains the original boundary. -/
def pathCellDecode {m n : ℤ} (p : pathArrow m ⟶ pathArrow n) : TwoGroupoidPath.Cell m n where
  base := Multiplicative.toAdd p.base
  boundary := congrArg (fun d : Discrete (Multiplicative ℤ) => Multiplicative.toAdd d.as)
    (LocallyDiscrete.eq_of_hom p.fiber)

theorem pathCellDecode_encode {m n : ℤ} (p : TwoGroupoidPath.Cell m n) :
    pathCellDecode (pathCell p) = p := rfl

theorem pathCell_encode_decode {m n : ℤ} (p : pathArrow m ⟶ pathArrow n) :
    pathCell (pathCellDecode p) = p := by
  apply Pseudofunctor.CoGrothendieck.Hom.ext (pathCell (pathCellDecode p)) p
    (show (pathCell (pathCellDecode p)).base = p.base from rfl)
  exact congrArg Discrete.Hom.mk rfl

/-- The general construction cannot discard the required base component. -/
theorem path_comparison_one :
    Multiplicative.toAdd (pathCell (TwoGroupoidPath.comparison 1 0)).base = 1 := rfl

/-- The integer action also inhabits the strict higher transformation interface. -/
def integerTrans (m : ℤ) : StrictTwoTransformation.Trans
    (StrictPseudofunctor.id (LocallyDiscrete TwoGroupoidPath.Fiber))
    (StrictPseudofunctor.id (LocallyDiscrete TwoGroupoidPath.Fiber)) where
  app _ := Discrete.mk (Multiplicative.ofAdd m)
  naturality f := by
    apply Discrete.ext
    change Multiplicative.ofAdd m * (show Multiplicative ℤ from f.as) =
      (show Multiplicative ℤ from f.as) * Multiplicative.ofAdd m
    exact mul_comm _ _
  naturality₂ _ := congrArg Discrete.Hom.mk rfl

theorem integerTrans_component (m : ℤ) :
    Multiplicative.toAdd ((integerTrans m).toStrong.app pathTarget).as = m := rfl

theorem double_reindex_preserves_fiber (n : ℤ) :
    ((TwoGroupoidHom.reindex (𝟭 (Discrete Unit)) E x) ⋙
      TwoGroupoidHom.reindex (𝟭 (Discrete Unit)) E x).map (fiberLoop n) = fiberLoop n := by
  rw [TwoGroupoidHom.reindex_id]
  rfl

theorem fiber_inverse_cancel (n : ℤ) :
    TwoGroupoidHom.inverse (fiberLoop n) ≫ fiberLoop n = 𝟙 a :=
  TwoGroupoidHom.inverse_comp _

end Examples.TwoGroupoidHom
