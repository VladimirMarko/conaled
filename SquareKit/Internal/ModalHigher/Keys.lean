import SquareKit.Internal.ModalHigher.Total
import SquareKit.Internal.PathTransport.TwoFamilyHigherReindexLaws

/-! Keys, admissible substitutions and their full higher total lifts. -/
namespace SquareKit.Internal.ModalHigher
open CategoryTheory Bicategory
open SquareKit.Internal.PathTransport
universe u v w
variable {G : Type u} {H : Type v} {J : Type w}
variable [AddCommGroup G] [AddCommGroup H] [AddCommGroup J]

theorem multiplier_comp (d c : ℤ) :
    (multiplier (G := G) d).comp (multiplier c) = multiplier (d * c) := by
  ext g
  exact (mul_zsmul g d c).symm

theorem key_comp (d c : ℤ) :
    (key (G := G) c).comp (key d) = key (d * c) := by
  rw [baseMap_comp, multiplier_comp]

theorem key_id : key (G := G) 1 = StrictPseudofunctor.id (Base G) := by
  have h : multiplier (G := G) 1 = AddMonoidHom.id G := by ext g; exact one_zsmul g
  change baseMap _ = _
  rw [h, baseMap_id]

/-- Every admitted group homomorphism commutes with every multiplication key. -/
theorem key_naturality (f : G →+ H) (d : ℤ) :
    (key d).comp (baseMap f) = (baseMap f).comp (key d) := by
  rw [baseMap_comp, baseMap_comp]
  congr 1
  ext g
  exact f.map_zsmul d g

/-- Two base changes retain the final target fiber BJ. -/
theorem pullback_comp (f : G →+ H) (j : H →+ J) :
    TwoFamily.reindex (baseMap f) (pulled j) = pulled (j.comp f) := by
  rw [TwoFamily.reindex_comp, baseMap_comp]

/-- Composition is equality of the whole strict functor after the family cast.
This imports the existing all-cell proof, not only its object-level shadow. -/
theorem lift_comp (f : G →+ H) (j : H →+ J) :
    (TwoFamily.familyCast (TwoFamily.reindex_comp (family J) (baseMap j)
      (baseMap f)).symm).comp
      ((TwoFamily.reindexHigher (pulled j) (baseMap f)).comp (lift j)) =
        TwoFamily.reindexHigher (family J) ((baseMap f).comp (baseMap j)) :=
  TwoFamily.reindexHigher_comp_cast _ _ _

/-- The direct key lift keeps a fiber arrow and rescales its base cell. -/
def boundaryLift (f : G →+ H) (k : H →+ J) {a b : J}
    (p : BoundaryCell (k.comp f) a b) : BoundaryCell k a b :=
  ⟨f p.label, p.boundary⟩

theorem boundaryLift_vertical (f : G →+ H) (k : H →+ J) {a b c : J}
    (p : BoundaryCell (k.comp f) a b) (q : BoundaryCell (k.comp f) b c) :
    boundaryLift f k (p.vertical q) =
      (boundaryLift f k p).vertical (boundaryLift f k q) := by
  apply BoundaryCell.ext
  exact f.map_add _ _

theorem boundaryLift_horizontal (f : G →+ H) (k : H →+ J) {a b a' b' : J}
    (p : BoundaryCell (k.comp f) a b) (q : BoundaryCell (k.comp f) a' b') :
    boundaryLift f k (p.horizontal q) =
      (boundaryLift f k p).horizontal (boundaryLift f k q) := by
  apply BoundaryCell.ext
  exact f.map_add _ _

abbrev nestedPoint (f : G →+ H) (k : H →+ J) :
    TwoFamily.Total (TwoFamily.reindex (baseMap f) (pulled k)) := ⟨point G, fiberPoint J⟩
def nestedArrow (f : G →+ H) (k : H →+ J) (a : J) :
    nestedPoint f k ⟶ nestedPoint f k :=
  TwoGroupoidHom.arrow _ _ (SingleObj.star _) (Discrete.mk (Multiplicative.ofAdd a))
def nestedCell (f : G →+ H) (k : H →+ J) {a b : J}
    (p : BoundaryCell (k.comp f) a b) : nestedArrow f k a ⟶ nestedArrow f k b :=
  TwoGroupoidHom.cell (Multiplicative.ofAdd p.label)
    (eqToHom (Discrete.ext (congrArg Multiplicative.ofAdd p.boundary)))

/-- The actual TwoFamily lift is the direct boundary lift, not just the same label. -/
theorem nested_lift_cell (f : G →+ H) (k : H →+ J) {a b : J}
    (p : BoundaryCell (k.comp f) a b) :
    (TwoFamily.reindexHigher (pulled k) (baseMap f)).map₂ (nestedCell f k p) =
      encode (boundaryLift f k p) := rfl

theorem nested_lift_arrow (f : G →+ H) (k : H →+ J) (a : J) :
    (TwoFamily.reindexHigher (pulled k) (baseMap f)).map (nestedArrow f k a) =
      totalArrow k a := rfl

theorem nested_lift_object (f : G →+ H) (k : H →+ J) :
    (TwoFamily.reindexHigher (pulled k) (baseMap f)).obj (nestedPoint f k) =
      totalPoint k := rfl

/-- Open endpoint comparisons are preserved uniformly, not just at a selected loop. -/
theorem open_square (f : G →+ H) {h h' a b : G} (e : h' + a = b + h) :
    f h' + f a = f b + f h := by
  simpa only [map_add] using congrArg f e

/-- Changing the fiber input commutes with the family action. -/
theorem input_naturality (f : G →+ H) (g : G) (r : H) :
    r + f g = f g + r := add_comm _ _

end SquareKit.Internal.ModalHigher
