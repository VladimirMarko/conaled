import SquareKit.Internal.Cubical.IntervalExtension

/-! Uniform filling for constant coefficients, constructed from interval rigidity.
This is a discrete instance, not fibrancy of arbitrary dependent presheaves. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

structure DiscreteBox (Γ : Context.{u}) (S : Type u) (φ : Cofibration Γ) where
  tube : PartialSection (constantFamily (total (interval Γ)) S) (φ.reindex (projection (interval Γ)))
  base : Term (constantFamily Γ S)
  boundary : ∀ x h, tube.val (extendObj (interval Γ) x ((endpoint Γ false).val x)) h = base.val x

def DiscreteBox.fill {Γ : Context.{u}} {S : Type u} {φ : Cofibration Γ} (b : DiscreteBox Γ S φ) :
    Term (constantFamily (total (interval Γ)) S) := b.base.reindex (projection (interval Γ))

theorem DiscreteBox.fill_zero {Γ : Context.{u}} {S : Type u} {φ : Cofibration Γ} (b : DiscreteBox Γ S φ) :
    b.fill.reindex (endpointSub Γ false) = b.base := rfl

theorem DiscreteBox.fill_tube {Γ : Context.{u}} {S : Type u} {φ : Cofibration Γ} (b : DiscreteBox Γ S φ)
    (x : (total (interval Γ)).Elements) (h : (φ.reindex (projection (interval Γ))).full x) :
    b.fill.val x = b.tube.val x h := by
  rcases x with @⟨I,⟨γ,r⟩⟩
  let y := Γ.elementsMk I γ
  exact ((constant_partial_interval b.tube y h r ((endpoint Γ false).val y)).trans (b.boundary y h)).symm

/-- Homogeneous composition is the far endpoint of this actual filler. -/
def DiscreteBox.hcomp {Γ : Context.{u}} {S : Type u} {φ : Cofibration Γ} (b : DiscreteBox Γ S φ) :
    Term (constantFamily Γ S) := b.fill.reindex (endpointSub Γ true)

theorem DiscreteBox.hcomp_on_face {Γ : Context.{u}} {S : Type u} {φ : Cofibration Γ}
    (b : DiscreteBox Γ S φ) (x : Γ.Elements) (h : φ.full x) :
    b.hcomp.val x = b.tube.val (extendObj (interval Γ) x ((endpoint Γ true).val x)) h :=
  b.fill_tube (extendObj (interval Γ) x ((endpoint Γ true).val x)) h

def DiscreteBox.reindex {Γ Δ : Context.{u}} {S : Type u} {φ : Cofibration Γ}
    (b : DiscreteBox Γ S φ) (σ : Δ ⟶ Γ) : DiscreteBox Δ S (φ.reindex σ) where
  tube := b.tube.reindex (liftSub (interval Γ) σ)
  base := b.base.reindex σ
  boundary x h := b.boundary (σ.mapElements.obj x) h

theorem DiscreteBox.fill_reindex {Γ Δ : Context.{u}} {S : Type u} {φ : Cofibration Γ}
    (b : DiscreteBox Γ S φ) (σ : Δ ⟶ Γ) :
    (b.reindex σ).fill = b.fill.reindex (liftSub (interval Γ) σ) := rfl

theorem DiscreteBox.hcomp_reindex {Γ Δ : Context.{u}} {S : Type u} {φ : Cofibration Γ}
    (b : DiscreteBox Γ S φ) (σ : Δ ⟶ Γ) : (b.reindex σ).hcomp = b.hcomp.reindex σ := rfl

theorem DiscreteBox.fill_unique {Γ : Context.{u}} {S : Type u} {φ : Cofibration Γ}
    (b : DiscreteBox Γ S φ) (a : Term (constantFamily (total (interval Γ)) S))
    (h : a.reindex (endpointSub Γ false) = b.base) : a = b.fill := by
  apply Term.ext
  intro x
  rcases x with @⟨I,⟨γ,r⟩⟩
  let y := Γ.elementsMk I γ
  exact (constant_section_interval a y r ((endpoint Γ false).val y)).trans
    (congrArg (fun t => t.val y) h)

end SquareKit.Cubical.Presheaf
