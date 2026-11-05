import SquareKit.Internal.Cubical.FaceEndpoints

/-! Compatible partial sections glue on a union of constructed faces. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

structure PartialSection {Γ : Context.{u}} (A : Family Γ) (φ : Cofibration Γ) where
  val : ∀ x : Γ.Elements, φ.full x → A.obj x
  property : ∀ {x y : Γ.Elements} (f : x ⟶ y) (h : φ.full x),
    A.map f (val x h) = val y (φ.full_natural f h)

@[ext] theorem PartialSection.ext {Γ : Context.{u}} {A : Family Γ} {φ : Cofibration Γ}
    {a b : PartialSection A φ} (h : ∀ x p, a.val x p = b.val x p) : a = b := by
  cases a
  cases b
  simp_all only [mk.injEq]
  exact funext (fun x => funext (h x))

def PartialSection.ofTerm {Γ : Context.{u}} {A : Family Γ} (φ : Cofibration Γ) (a : Term A) :
    PartialSection A φ where
  val x _ := a.val x
  property f _ := a.property f

def PartialSection.reindex {Γ Δ : Context.{u}} {A : Family Γ} {φ : Cofibration Γ}
    (a : PartialSection A φ) (σ : Δ ⟶ Γ) : PartialSection (Presheaf.reindex A σ) (φ.reindex σ) where
  val x p := a.val (σ.mapElements.obj x) p
  property f p := a.property (σ.mapElements.map f) p

/-- A partial section is an actual section over the restricted context. -/
def PartialSection.toRestricted {Γ : Context.{u}} {A : Family Γ} {φ : Cofibration Γ}
    (a : PartialSection A φ) : Term (Presheaf.reindex A (restrictInclusion φ)) where
  val x := a.val ((restrictInclusion φ).mapElements.obj x) x.val.property
  property f := a.property ((restrictInclusion φ).mapElements.map f) _

def PartialSection.ofRestricted {Γ : Context.{u}} {A : Family Γ} {φ : Cofibration Γ}
    (a : Term (Presheaf.reindex A (restrictInclusion φ))) : PartialSection A φ where
  val x p := a.val ((restrictContext φ).elementsMk x.obj ⟨x.val,p⟩)
  property {x y} f p := by
    let q : (restrictContext φ).elementsMk x.obj ⟨x.val,p⟩ ⟶
        (restrictContext φ).elementsMk y.obj ⟨y.val,φ.full_natural f p⟩ :=
      Functor.Elements.homMk f.hom (Subtype.ext f.map_val)
    exact a.property q

theorem PartialSection.restricted_roundtrip {Γ : Context.{u}} {A : Family Γ} {φ : Cofibration Γ}
    (a : PartialSection A φ) : ofRestricted a.toRestricted = a := rfl

theorem PartialSection.term_roundtrip {Γ : Context.{u}} {A : Family Γ} {φ : Cofibration Γ}
    (a : Term (Presheaf.reindex A (restrictInclusion φ))) : (ofRestricted a).toRestricted = a := rfl

def PartialSection.Compatible {Γ : Context.{u}} {A : Family Γ} {φ ψ : Cofibration Γ}
    (a : PartialSection A φ) (b : PartialSection A ψ) : Prop :=
  ∀ x p q, a.val x p = b.val x q

noncomputable def glueValue {Γ : Context.{u}} {A : Family Γ} {φ ψ : Cofibration Γ}
    (a : PartialSection A φ) (b : PartialSection A ψ) (x : Γ.Elements) (p : (φ.join ψ).full x) : A.obj x :=
  if h : φ.full x then a.val x h else b.val x ((Cofibration.full_join φ ψ x).mp p |>.resolve_left h)

theorem glueValue_left {Γ : Context.{u}} {A : Family Γ} {φ ψ : Cofibration Γ}
    (a : PartialSection A φ) (b : PartialSection A ψ) (x : Γ.Elements)
    (p : (φ.join ψ).full x) (h : φ.full x) : glueValue a b x p = a.val x h := by
  simp only [glueValue,dite_eq_left h]

theorem glueValue_right {Γ : Context.{u}} {A : Family Γ} {φ ψ : Cofibration Γ}
    (a : PartialSection A φ) (b : PartialSection A ψ) (c : a.Compatible b) (x : Γ.Elements)
    (p : (φ.join ψ).full x) (h : ψ.full x) : glueValue a b x p = b.val x h := by
  classical
  by_cases q : φ.full x
  · exact (glueValue_left a b x p q).trans (c x q h)
  · simp only [glueValue,dite_eq_right q]

noncomputable def PartialSection.glue {Γ : Context.{u}} {A : Family Γ} {φ ψ : Cofibration Γ}
    (a : PartialSection A φ) (b : PartialSection A ψ) (c : a.Compatible b) : PartialSection A (φ.join ψ) where
  val := glueValue a b
  property {x y} f p := by
    rcases (Cofibration.full_join φ ψ x).mp p with h | h
    · rw [glueValue_left a b x p h,glueValue_left a b y _ (φ.full_natural f h)]
      exact a.property f h
    · rw [glueValue_right a b c x p h,glueValue_right a b c y _ (ψ.full_natural f h)]
      exact b.property f h

theorem PartialSection.Compatible.reindex {Γ Δ : Context.{u}} {A : Family Γ} {φ ψ : Cofibration Γ}
    {a : PartialSection A φ} {b : PartialSection A ψ} (c : a.Compatible b) (σ : Δ ⟶ Γ) :
    (a.reindex σ).Compatible (b.reindex σ) := fun x p q => c (σ.mapElements.obj x) p q

theorem PartialSection.glue_reindex {Γ Δ : Context.{u}} {A : Family Γ} {φ ψ : Cofibration Γ}
    (a : PartialSection A φ) (b : PartialSection A ψ) (c : a.Compatible b) (σ : Δ ⟶ Γ) :
    (a.glue b c).reindex σ = (a.reindex σ).glue (b.reindex σ) (c.reindex σ) := by
  apply PartialSection.ext
  intro x p
  rfl

theorem PartialSection.reindex_comp {Γ Δ Θ : Context.{u}} {A : Family Γ} {φ : Cofibration Γ}
    (a : PartialSection A φ) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    (a.reindex σ).reindex τ = a.reindex (τ ≫ σ) := rfl

end SquareKit.Cubical.Presheaf
