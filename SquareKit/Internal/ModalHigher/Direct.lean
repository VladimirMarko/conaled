import SquareKit.Internal.ModalHigher.Total

/-! Direct algebraic total-cell laws and checked comparison with TwoFamily. -/
namespace SquareKit.Internal.ModalHigher
open CategoryTheory Bicategory
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
variable {G : Type u} {H : Type v} [AddCommGroup G] [AddCommGroup H]
namespace BoundaryCell
variable {f : G →+ H} {a b c d a' b' c' : H}
theorem identity_vertical (p : BoundaryCell f a b) : (identity a).vertical p = p :=
  ext (zero_add _)
theorem vertical_identity (p : BoundaryCell f a b) : p.vertical (identity b) = p :=
  ext (add_zero _)
theorem vertical_assoc (p : BoundaryCell f a b) (q : BoundaryCell f b c)
    (r : BoundaryCell f c d) : (p.vertical q).vertical r = p.vertical (q.vertical r) :=
  ext (add_assoc _ _ _)
theorem inverse_vertical (p : BoundaryCell f a b) : p.inverse.vertical p = identity b :=
  ext (neg_add_cancel _)
theorem vertical_inverse (p : BoundaryCell f a b) : p.vertical p.inverse = identity a :=
  ext (add_neg_cancel _)

theorem interchange (p : BoundaryCell f a b) (q : BoundaryCell f b c)
    (r : BoundaryCell f a' b') (s : BoundaryCell f b' c') :
    (p.horizontal r).vertical (q.horizontal s) =
      (p.vertical q).horizontal (r.vertical s) := by
  apply ext
  change (p.label + r.label) + (q.label + s.label) = _
  change _ = (p.label + q.label) + (r.label + s.label)
  abel
end BoundaryCell

/-- Arrow composition in the reused total is the direct additive composition. -/
theorem totalArrow_comp (f : G →+ H) (a b : H) :
    totalArrow f a ≫ totalArrow f b = totalArrow f (a + b) := by
  apply Pseudofunctor.CoGrothendieck.ext
  · rfl
  change HEq ((show fiberPoint H ⟶ fiberPoint H from 𝟙 _) ≫
    Discrete.mk (Multiplicative.ofAdd a) ≫ Discrete.mk (Multiplicative.ofAdd b))
    (Discrete.mk (Multiplicative.ofAdd (a + b)))
  simp only [Category.id_comp, heq_eq_eq]
  apply Discrete.ext
  exact congrArg Multiplicative.ofAdd (add_comm b a)

/-- Encoding the direct vertical composition gives the categorical composition. -/
theorem encode_vertical {f : G →+ H} {a b c : H}
    (p : BoundaryCell f a b) (q : BoundaryCell f b c) :
    encode (p.vertical q) = encode p ≫ encode q := by
  apply Pseudofunctor.CoGrothendieck.Hom.ext _ _
    (show Multiplicative.ofAdd (p.label + q.label) =
      Multiplicative.ofAdd (q.label + p.label) from
      congrArg Multiplicative.ofAdd (add_comm _ _))
  exact congrArg Discrete.Hom.mk rfl

/-- Both whiskerings keep the selected base second cell. -/
theorem left_whisker_label {f : G →+ H} {a b : H}
    (p : BoundaryCell f a b) (r : H) :
    Multiplicative.toAdd (TwoFamily.whiskerLeft (pulled f)
      (totalArrow f r) (encode p)).base = p.label := rfl

theorem right_whisker_label {f : G →+ H} {a b : H}
    (p : BoundaryCell f a b) (r : H) :
    Multiplicative.toAdd (TwoFamily.whiskerRight (pulled f)
      (encode p) (totalArrow f r)).base = p.label := rfl

end SquareKit.Internal.ModalHigher
