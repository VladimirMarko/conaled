import SquareKit.Internal.ModalHigher.Family
import Mathlib.Tactic.Abel
import SquareKit.Internal.PathTransport.TwoFamilyHigherReindex

/-! Explicit boundary presentation and its connection to the reused total context. -/
namespace SquareKit.Internal.ModalHigher
open CategoryTheory Bicategory
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
variable {G : Type u} {H : Type v} [AddCommGroup G] [AddCommGroup H]

abbrev lift (f : G →+ H) := TwoFamily.reindexHigher (family H) (baseMap f)

theorem projection (f : G →+ H) :
    (lift f).comp (TwoFamily.projectionHigher (family H)) =
      (TwoFamily.projectionHigher (pulled f)).comp (baseMap f) :=
  TwoFamily.reindexHigher_projection _ _

/-- Direct presentation: arrows lie in H, while second cells lie in G. -/
structure BoundaryCell (f : G →+ H) (a b : H) where
  label : G
  boundary : a = b + f label

namespace BoundaryCell
variable {f : G →+ H} {a b c a' b' : H}
@[ext] theorem ext {p q : BoundaryCell f a b} (h : p.label = q.label) : p = q := by
  cases p; cases q; cases h; rfl

def identity (a : H) : BoundaryCell f a a := ⟨0, by simp⟩
def vertical (p : BoundaryCell f a b) (q : BoundaryCell f b c) : BoundaryCell f a c := by
  rcases p with ⟨p, hp⟩
  rcases q with ⟨q, hq⟩
  refine ⟨p + q, ?_⟩
  rw [map_add, hp, hq]
  abel
def horizontal (p : BoundaryCell f a b) (q : BoundaryCell f a' b') :
    BoundaryCell f (a + a') (b + b') := by
  rcases p with ⟨p, hp⟩
  rcases q with ⟨q, hq⟩
  refine ⟨p + q, ?_⟩
  rw [map_add, hp, hq]
  abel
def inverse (p : BoundaryCell f a b) : BoundaryCell f b a := by
  rcases p with ⟨p, hp⟩
  refine ⟨-p, ?_⟩
  rw [map_neg, hp]
  abel
end BoundaryCell

abbrev totalPoint (f : G →+ H) : TwoFamily.Total (pulled f) := ⟨point G, fiberPoint H⟩
def totalArrow (f : G →+ H) (a : H) : totalPoint f ⟶ totalPoint f :=
  TwoGroupoidHom.arrow _ _ (SingleObj.star _) (Discrete.mk (Multiplicative.ofAdd a))

/-- Every direct boundary supplies the actual fiber second cell in TwoFamily. -/
def encode {f : G →+ H} {a b : H} (p : BoundaryCell f a b) :
    totalArrow f a ⟶ totalArrow f b :=
  TwoGroupoidHom.cell (Multiplicative.ofAdd p.label)
    (eqToHom (Discrete.ext (congrArg Multiplicative.ofAdd p.boundary)))

/-- Conversely the typed total cell enforces the advertised boundary equation. -/
def decode {f : G →+ H} {a b : H} (p : totalArrow f a ⟶ totalArrow f b) :
    BoundaryCell f a b where
  label := Multiplicative.toAdd p.base
  boundary := congrArg (fun d : Discrete (Multiplicative H) => Multiplicative.toAdd d.as)
    (LocallyDiscrete.eq_of_hom p.fiber)

theorem decode_encode {f : G →+ H} {a b : H} (p : BoundaryCell f a b) :
    decode (encode p) = p := rfl

theorem encode_decode {f : G →+ H} {a b : H} (p : totalArrow f a ⟶ totalArrow f b) :
    encode (decode p) = p := by
  apply Pseudofunctor.CoGrothendieck.Hom.ext (encode (decode p)) p
    (show (encode (decode p)).base = p.base from rfl)
  exact congrArg Discrete.Hom.mk rfl

/-- A base substitution retains the supplied fiber arrow, in H. -/
theorem lift_arrow (f : G →+ H) (a : H) :
    ((lift f).map (totalArrow f a)).fiber = Discrete.mk (Multiplicative.ofAdd a) := rfl

theorem lift_cell (f : G →+ H) {a b : H} (p : BoundaryCell f a b) :
    Multiplicative.toAdd ((lift f).map₂ (encode p)).base = f p.label := rfl

end SquareKit.Internal.ModalHigher
