import SquareKit.CommaPullback
import SquareKit.CommaExactLawful
import Examples.CommaSquares

/-! Checked clients for the comma universal property: noninvertible connectors,
nonidentity transformations, reindexing, strict pullback uniqueness and recovery
of an existing exact-square computation. -/

namespace Examples.CommaUniversal

open CategoryTheory CategoryTheory.Functor
open SquareKit.Comma.Universal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Keep a Boolean tag alongside every value. -/
def tagged : Type ⥤ Type where
  obj X := X × Bool
  map f := TypeCat.ofHom fun p => (f p.1, p.2)

/-- A natural comparison between nonconstant functors. -/
def tagFalse : 𝟭 (Type) ⟶ tagged where
  app _ := TypeCat.ofHom fun x => (x, false)

def tagCone : Cone (𝟭 (Type)) (𝟭 (Type)) (Type) :=
  ⟨𝟭 _, tagged, tagFalse⟩

/-- Resetting the tag is a nonidentity map of cones compatible with insertion. -/
def reset : tagCone ⟶ tagCone where
  left := 𝟙 _
  right := { app := fun _ => TypeCat.ofHom fun p => (p.1, false) }
  w := rfl

def taggedArrows : Type ⥤ Arrow (Type) :=
  (fromCones (𝟭 (Type)) (𝟭 (Type))).obj tagCone

example : (taggedArrows.map (TypeCat.ofHom (fun n : Nat => n + 1))).right (3, true) = (4, true) := rfl

/-- The connector is not an isomorphism: the true tag is not in its image. -/
example : ¬ Function.Surjective (taggedArrows.obj Nat).hom := by
  intro h
  obtain ⟨n, hn⟩ := h (0, true)
  have bad : false = true := congrArg Prod.snd hn
  cases bad

example : (((fromCones (𝟭 (Type)) (𝟭 (Type))).map reset).app Nat).right (3, true) =
    (3, false) := rfl

/-- Transformation composition is supplied by the shared lifting functor. -/
example : (fromCones (𝟭 (Type)) (𝟭 (Type))).map (reset ≫ reset) =
    (fromCones (𝟭 (Type)) (𝟭 (Type))).map reset ≫
      (fromCones (𝟭 (Type)) (𝟭 (Type))).map reset :=
  (fromCones _ _).map_comp _ _

/-- Two nonidentity parameter changes compose through the public law. -/
example : precompose (𝟭 (Type)) (𝟭 (Type)) (tagged ⋙ tagged) =
    precompose (𝟭 (Type)) (𝟭 (Type)) tagged ⋙ precompose _ _ tagged :=
  precompose_comp _ _ _ _

/-- A nonidentity transformation between nonconstant test functors survives whiskering. -/
example : precomposeNat (𝟭 (Type)) (𝟭 (Type)) (whiskerLeft tagged tagFalse) =
    whiskerRight (precomposeNat _ _ tagFalse) (precompose _ _ tagged) :=
  precomposeNat_whiskerLeft _ _ _ _

example : whiskerRight ((whiskeringLeft (Type) (Type) (Arrow (Type))).map tagFalse)
      (toCones (𝟭 (Type)) (𝟭 (Type))) =
    whiskerLeft (toCones _ _) (precomposeNat _ _ tagFalse) :=
  toCones_precomposeNat _ _ _

/-- The strict pullback accepts the same noninvertible connectors. -/
example : pullbackLift (𝟭 (Type)) (𝟭 (Type))
      (taggedArrows ⋙ projections _ _) (taggedArrows ⋙ connector _ _) rfl = taggedArrows := by
  symm
  exact pullbackLift_unique _ _ _ _ _ _ rfl rfl

open Examples.CommaSquares

/-- Recover the existing increment/double square through a universal lift. -/
def exactArrows : Arrow (Type) ⥤ Arrow (Type) :=
  lift (𝟭 _) (𝟭 _) Arrow.leftFunc Arrow.rightFunc Arrow.leftToRight

example :
    (SquareKit.Comma.Exact.toSquare
      (SquareKit.Comma.Exact.homFromArrow
        (exactArrows.map
          (SquareKit.Comma.Exact.homToArrow
            (SquareKit.Comma.Exact.ofSquare (Squares.compose double increment)))))).impl (3 : Nat) = (9 : Nat) := by
  change (Squares.compose double increment).impl (3 : Nat) = (9 : Nat)
  rfl

end Examples.CommaUniversal
