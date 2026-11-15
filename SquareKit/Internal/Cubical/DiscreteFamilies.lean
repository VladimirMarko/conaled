import SquareKit.Internal.Cubical.DiscreteFilling

/-! Constructed discrete families retain a varying fiber selected by a natural
index. They supply a dependent filling instance, not general cubical fibrancy. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def discreteFamily {Γ : Context.{u}} {T : Type u} (q : Term (constantFamily Γ T)) (S : T → Type u) : Family Γ where
  obj x := S (q.val x)
  map f := TypeCat.ofHom (cast (congrArg S (q.property f)))
  map_id _ := rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (cast_cast _ _ a).symm

@[simp] theorem discreteFamily_reindex {Γ Δ : Context.{u}} {T : Type u}
    (q : Term (constantFamily Γ T)) (S : T → Type u) (σ : Δ ⟶ Γ) :
    reindex (discreteFamily q S) σ = discreteFamily (q.reindex σ) S := rfl

def PartialSection.totalize {Γ : Context.{u}} {T : Type u} {q : Term (constantFamily Γ T)}
    {S : T → Type u} {φ : Cofibration Γ} (a : PartialSection (discreteFamily q S) φ) :
    PartialSection (constantFamily Γ (Σ t, S t)) φ where
  val x h := ⟨q.val x,a.val x h⟩
  property {x y} f h := by
    apply Sigma.ext (q.property f)
    have ha := a.property f h
    exact (cast_heq (congrArg S (q.property f)) (a.val x h)).symm.trans (heq_of_eq ha)

theorem discrete_partial_interval {Γ : Context.{u}} {T : Type u} {q : Term (constantFamily Γ T)}
    {S : T → Type u} {φ : Cofibration Γ}
    (a : PartialSection (reindex (discreteFamily q S) (projection (interval Γ)))
      (φ.reindex (projection (interval Γ))))
    (x : Γ.Elements) (h : φ.full x) (r s : (interval Γ).obj x) :
    a.val (extendObj (interval Γ) x r) h = a.val (extendObj (interval Γ) x s) h := by
  have he := constant_partial_interval (PartialSection.totalize (q := q.reindex (projection (interval Γ))) (S := S) a) x h r s
  exact eq_of_heq (Sigma.mk.inj he).2

structure DiscreteDependentBox {Γ : Context.{u}} {T : Type u}
    (q : Term (constantFamily Γ T)) (S : T → Type u) (φ : Cofibration Γ) where
  tube : PartialSection (reindex (discreteFamily q S) (projection (interval Γ)))
    (φ.reindex (projection (interval Γ)))
  base : Term (discreteFamily q S)
  boundary : ∀ x h, tube.val (extendObj (interval Γ) x ((endpoint Γ false).val x)) h = base.val x

def DiscreteDependentBox.fill {Γ : Context.{u}} {T : Type u} {q : Term (constantFamily Γ T)}
    {S : T → Type u} {φ : Cofibration Γ} (b : DiscreteDependentBox q S φ) :
    Term (reindex (discreteFamily q S) (projection (interval Γ))) := b.base.reindex (projection (interval Γ))

theorem DiscreteDependentBox.fill_zero {Γ : Context.{u}} {T : Type u} {q : Term (constantFamily Γ T)}
    {S : T → Type u} {φ : Cofibration Γ} (b : DiscreteDependentBox q S φ) :
    b.fill.reindex (endpointSub Γ false) = b.base := rfl

theorem DiscreteDependentBox.fill_tube {Γ : Context.{u}} {T : Type u} {q : Term (constantFamily Γ T)}
    {S : T → Type u} {φ : Cofibration Γ} (b : DiscreteDependentBox q S φ)
    (x : (total (interval Γ)).Elements) (h : (φ.reindex (projection (interval Γ))).full x) :
    b.fill.val x = b.tube.val x h := by
  rcases x with @⟨I,⟨γ,r⟩⟩
  let y := Γ.elementsMk I γ
  exact ((discrete_partial_interval b.tube y h r ((endpoint Γ false).val y)).trans (b.boundary y h)).symm

def DiscreteDependentBox.reindex {Γ Δ : Context.{u}} {T : Type u} {q : Term (constantFamily Γ T)}
    {S : T → Type u} {φ : Cofibration Γ} (b : DiscreteDependentBox q S φ) (σ : Δ ⟶ Γ) :
    DiscreteDependentBox (q.reindex σ) S (φ.reindex σ) where
  tube := b.tube.reindex (liftSub (interval Γ) σ)
  base := b.base.reindex σ
  boundary x h := b.boundary (σ.mapElements.obj x) h

theorem DiscreteDependentBox.fill_reindex {Γ Δ : Context.{u}} {T : Type u} {q : Term (constantFamily Γ T)}
    {S : T → Type u} {φ : Cofibration Γ} (b : DiscreteDependentBox q S φ) (σ : Δ ⟶ Γ) :
    (b.reindex σ).fill = b.fill.reindex (liftSub (interval Γ) σ) := rfl

def DiscreteDependentBox.hcomp {Γ : Context.{u}} {T : Type u} {q : Term (constantFamily Γ T)}
    {S : T → Type u} {φ : Cofibration Γ} (b : DiscreteDependentBox q S φ) :
    Term (discreteFamily q S) := b.fill.reindex (endpointSub Γ true)

theorem DiscreteDependentBox.hcomp_on_face {Γ : Context.{u}} {T : Type u} {q : Term (constantFamily Γ T)}
    {S : T → Type u} {φ : Cofibration Γ} (b : DiscreteDependentBox q S φ) (x : Γ.Elements) (h : φ.full x) :
    b.hcomp.val x = b.tube.val (extendObj (interval Γ) x ((endpoint Γ true).val x)) h :=
  b.fill_tube (extendObj (interval Γ) x ((endpoint Γ true).val x)) h

theorem DiscreteDependentBox.hcomp_reindex {Γ Δ : Context.{u}} {T : Type u} {q : Term (constantFamily Γ T)}
    {S : T → Type u} {φ : Cofibration Γ} (b : DiscreteDependentBox q S φ) (σ : Δ ⟶ Γ) :
    (b.reindex σ).hcomp = b.hcomp.reindex σ := rfl

end SquareKit.Cubical.Presheaf
