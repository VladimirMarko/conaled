import SquareKit.Internal.Cubical.DiscreteFamilies

/-! Open boxes in families that may vary along the filling dimension. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

structure OpenBox {Γ : Context.{u}} (A : Family (total (interval Γ))) (φ : Cofibration Γ) where
  tube : PartialSection A (φ.reindex (projection (interval Γ)))
  base : Term (reindex A (endpointSub Γ false))
  boundary : ∀ x h, tube.val (extendObj (interval Γ) x ((endpoint Γ false).val x)) h = base.val x

def OpenBox.empty {Γ : Context.{u}} (A : Family (total (interval Γ)))
    (a : Term (reindex A (endpointSub Γ false))) : OpenBox A (Cofibration.bot Γ) where
  tube := {
    val := fun _ h => (Bool.false_ne_true h).elim
    property := fun _ h => (Bool.false_ne_true h).elim }
  base := a
  boundary _ h := (Bool.false_ne_true h).elim

@[ext] theorem OpenBox.ext {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {φ : Cofibration Γ} {b c : OpenBox A φ} (ht : b.tube = c.tube) (hb : b.base = c.base) : b = c := by
  cases b
  cases c
  cases ht
  cases hb
  rfl

def OpenBox.reindex {Γ Δ : Context.{u}} {A : Family (total (interval Γ))} {φ : Cofibration Γ}
    (b : OpenBox A φ) (σ : Δ ⟶ Γ) :
    OpenBox (Presheaf.reindex A (liftSub (interval Γ) σ)) (φ.reindex σ) where
  tube := b.tube.reindex (liftSub (interval Γ) σ)
  base := b.base.reindex σ
  boundary x h := b.boundary (σ.mapElements.obj x) h

/-- Correctness of an actual filler, kept separate from its section data. -/
def OpenBox.Fills {Γ : Context.{u}} {A : Family (total (interval Γ))} {φ : Cofibration Γ}
    (b : OpenBox A φ) (a : Term A) : Prop :=
  a.reindex (endpointSub Γ false) = b.base ∧
    ∀ x h, a.val x = b.tube.val x h

theorem OpenBox.Fills.reindex {Γ Δ : Context.{u}} {A : Family (total (interval Γ))}
    {φ : Cofibration Γ} {b : OpenBox A φ} {a : Term A} (h : b.Fills a) (σ : Δ ⟶ Γ) :
    (b.reindex σ).Fills (a.reindex (liftSub (interval Γ) σ)) := by
  constructor
  · exact congrArg (fun t => t.reindex σ) h.1
  · intro x p
    exact h.2 ((liftSub (interval Γ) σ).mapElements.obj x) p

/-- A discrete index is constant along each generalized interval, even when
presented as a section over the whole interval extension. -/
theorem discreteIndex_zero {Γ : Context.{u}} {T : Type u}
    (q : Term (constantFamily (total (interval Γ)) T))
    (x : (total (interval Γ)).Elements) :
    q.val ((endpointSub Γ false).mapElements.obj ((projection (interval Γ)).mapElements.obj x)) =
      q.val x := by
  rcases x with @⟨I,⟨γ,r⟩⟩
  exact constant_section_interval q (Γ.elementsMk I γ) ((endpoint Γ false).val _) r

def OpenBox.discreteFill {Γ : Context.{u}} {T : Type u}
    {q : Term (constantFamily (total (interval Γ)) T)} {S : T → Type u}
    {φ : Cofibration Γ} (b : OpenBox (discreteFamily q S) φ) : Term (discreteFamily q S) where
  val x := cast (congrArg S (discreteIndex_zero q x))
    (b.base.val ((projection (interval Γ)).mapElements.obj x))
  property {x y} f := by
    apply eq_of_heq
    apply (cast_heq _ _).trans
    apply (cast_heq _ _).trans
    have h := b.base.property ((projection (interval Γ)).mapElements.map f)
    exact ((cast_heq _ _).symm.trans (heq_of_eq h)).trans (cast_heq _ _).symm

theorem OpenBox.discreteFill_fills {Γ : Context.{u}} {T : Type u}
    {q : Term (constantFamily (total (interval Γ)) T)} {S : T → Type u}
    {φ : Cofibration Γ} (b : OpenBox (discreteFamily q S) φ) : b.Fills b.discreteFill := by
  constructor
  · apply Term.ext
    intro x
    rfl
  · intro x h
    rcases x with @⟨I,⟨γ,r⟩⟩
    let y := Γ.elementsMk I γ
    have ht := constant_partial_interval (PartialSection.totalize b.tube) y h
      ((endpoint Γ false).val y) r
    apply eq_of_heq
    exact (cast_heq _ _).trans ((heq_of_eq (b.boundary y h)).symm.trans (Sigma.mk.inj ht).2)

theorem OpenBox.discreteFill_reindex {Γ Δ : Context.{u}} {T : Type u}
    {q : Term (constantFamily (total (interval Γ)) T)} {S : T → Type u}
    {φ : Cofibration Γ} (b : OpenBox (discreteFamily q S) φ) (σ : Δ ⟶ Γ) :
    OpenBox.discreteFill (q := q.reindex (liftSub (interval Γ) σ)) (S := S) (b.reindex σ) = b.discreteFill.reindex (liftSub (interval Γ) σ) := rfl

end SquareKit.Cubical.Presheaf
