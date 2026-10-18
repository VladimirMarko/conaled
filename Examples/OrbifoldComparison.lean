import Applications.Orbifolds.QuarterTurn

/-! Checked consumers of the conventional action-groupoid and smooth quotient comparison. -/
noncomputable section
open Orbifolds Orbifolds.QuarterTurn CategoryTheory Diffeology MulAction
open scoped Manifold ContDiff
namespace Examples.OrbifoldComparison

/-- The apex stays fixed, but its quarter-turn derivative is nonidentity. -/
example : ((quarterTurn • diskEllipse origin : Ellipse) : ℂ) = 0 ∧
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun w : Ellipse => quarterTurn • w)
      (diskEllipse origin) Complex.I = (-2 : ℂ) := by
  constructor
  · rw [ellipse_quarterTurn_coordinates]
    change ellipseQuarterTurn (stretch 0) = 0
    apply Complex.ext <;> norm_num [ellipseQuarterTurn]
  · rw [ellipse_quarterTurn_tangent]
    apply Complex.ext <;> norm_num [ellipseQuarterTurn]

/-- Away from the apex, the base point moves and both tangent coordinates scale. -/
example : ((quarterTurn • diskEllipse half : Ellipse) : ℂ) = Complex.I / 2 ∧
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun w : Ellipse => quarterTurn • w)
      (diskEllipse half) (1 + Complex.I : ℂ) = (-2 + Complex.I / 2 : ℂ) := by
  constructor
  · rw [ellipse_quarterTurn_coordinates]
    change ellipseQuarterTurn (stretch (1 / 2)) = Complex.I / 2
    apply Complex.ext <;> norm_num [ellipseQuarterTurn]
  · rw [ellipse_quarterTurn_tangent]
    apply Complex.ext <;> norm_num [ellipseQuarterTurn]

/-- The disk-to-ellipse adapter maps arrows, preserving their C4 labels. -/
theorem arrow_label {x y : ActionCategory C4 Disk} (a : x ⟶ y) :
    (coordinateChange.functor.map a).hom = a.hom := rfl

/-- The nonidentity coordinate change and its inverse compose as lawful SquareKit maps. -/
theorem roundtrip_map_laws : SquareKit.MapLaws
    (coordinateChange.rawMap.comp coordinateChange.symm.rawMap)
    (SquareKit.equality _) (SquareKit.equality _) :=
  SquareKit.RawMap.comp_laws coordinateChange.rawMap_laws coordinateChange.symm.rawMap_laws

/-- Pasting the two quotient projection squares recovers the identity square. -/
theorem roundtrip_square :
    Squares.compose
      (orbitSquare (MulEquiv.refl C4).symm.toMonoidHom coordinateChange.symm.toEquiv
        coordinateChange.symm.equivariant)
      (orbitSquare (MulEquiv.refl C4).toMonoidHom coordinateChange.toEquiv
        coordinateChange.equivariant) =
    Squares.identity ⟨Disk, Quotient (orbitRel C4 Disk), Quotient.mk _⟩ := by
  apply Squares.Square.ext
  · intro x; exact coordinateChange.toEquiv.symm_apply_apply x
  · intro q; exact coordinateChange.quotientEquiv.symm_apply_apply q

/-- The quotient comparison is smooth even at the orbit with full isotropy. -/
example :
    let _ := IsManifold.toDiffeology 𝓘(ℝ, ℂ) Disk
    let _ := IsManifold.toDiffeology 𝓘(ℝ, ℂ) Ellipse
    DSmooth quotientComparison.toEquiv := by
  let _ := IsManifold.toDiffeology 𝓘(ℝ, ℂ) Disk
  let _ := IsManifold.toDiffeology 𝓘(ℝ, ℂ) Ellipse
  exact quotientComparison.smooth

/-- Both directions use the smoothness bridge for open manifolds. -/
example :
    let _ := IsManifold.toDiffeology 𝓘(ℝ, ℂ) Disk
    let _ := IsManifold.toDiffeology 𝓘(ℝ, ℂ) Ellipse
    DSmooth quotientComparison.toEquiv.symm := by
  let _ := IsManifold.toDiffeology 𝓘(ℝ, ℂ) Disk
  let _ := IsManifold.toDiffeology 𝓘(ℝ, ℂ) Ellipse
  exact quotientComparison.smooth_symm

/-- The singular orbit keeps its full stabilizer after changing coordinates. -/
example : stabilizer C4 origin ≃* stabilizer C4 (diskEllipse origin) :=
  coordinateChange.stabilizerEquiv origin

section TrivialGroup
local instance : MulAction Unit ℝ where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def trivialGroupChange : CoordinateChange (MulEquiv.refl Unit) ℝ ℝ :=
  manifoldCoordinateChange (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞) (fun _ _ => rfl)

example : ActionCategory Unit ℝ ≌ ActionCategory Unit ℝ :=
  trivialGroupChange.groupoidEquivalence

/-- A real manifold with the trivial group has its usual smooth quotient. -/
def trivialGroupQuotient : SmoothEquiv (Quotient (orbitRel Unit ℝ)) ℝ :=
  trivialActionQuotient (fun _ _ => rfl)

example (x : ℝ) : stabilizer Unit x = ⊤ := trivialAction_stabilizer (fun _ _ => rfl) x
end TrivialGroup

section Ineffective
local instance : MulAction C4 ℝ where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def ineffectiveChange : CoordinateChange (MulEquiv.refl C4) ℝ ℝ :=
  manifoldCoordinateChange (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞) (fun _ _ => rfl)

example : ActionCategory C4 ℝ ≌ ActionCategory C4 ℝ :=
  ineffectiveChange.groupoidEquivalence

/-- A nontrivial finite ineffective group has the same smooth quotient as the manifold. -/
def ineffectiveQuotient : SmoothEquiv (Quotient (orbitRel C4 ℝ)) ℝ :=
  trivialActionQuotient (fun _ _ => rfl)

theorem ineffective_isotropy (x : ℝ) : stabilizer C4 x = ⊤ :=
  trivialAction_stabilizer (fun _ _ => rfl) x

/-- The quotient has forgotten isotropy that the action category retains. -/
example (x : ℝ) : Nat.card (stabilizer C4 x) = 4 := by
  rw [ineffective_isotropy]
  exact (Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup C4) ≃* C4).toEquiv).trans card_C4
end Ineffective
end Examples.OrbifoldComparison
