import SquareKit.Internal.Cubical.Faces
import SquareKit.Internal.Cubical.Interval

/-! The face classifier and actual restricted contexts. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def faceContext : Context.{u} where
  obj I := ULift.{u} (Face.Carrier I.unop.dimension)
  map f := TypeCat.ofHom (fun φ => ⟨Face.substitute f.unop φ.down⟩)
  map_id I := by
    apply ConcreteCategory.hom_ext
    intro φ
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro φ
    exact congrArg ULift.up (Face.substitute_comp g.unop f.unop φ.down).symm

abbrev Cofibration (Γ : Context.{u}) := Γ ⟶ faceContext.{u}

def Cofibration.full {Γ : Context.{u}} (φ : Cofibration Γ) (x : Γ.Elements) : Prop :=
  Face.Full (φ.app x.obj x.val).down

instance {Γ : Context.{u}} (φ : Cofibration Γ) (x : Γ.Elements) : Decidable (φ.full x) :=
  inferInstanceAs (Decidable ((φ.app x.obj x.val).down.holds (fun _ => none) = true))

theorem Cofibration.full_natural {Γ : Context.{u}} (φ : Cofibration Γ) {x y : Γ.Elements}
    (f : x ⟶ y) (h : φ.full x) : φ.full y := by
  have hp := Face.full_substitute f.hom.unop (φ.app x.obj x.val).down h
  have he := congrArg ULift.down (φ.naturality_apply f.hom x.val)
  change (φ.app y.obj (Γ.map f.hom x.val)).down = Face.substitute f.hom.unop (φ.app x.obj x.val).down at he
  rw [f.map_val] at he
  change Face.Full (φ.app y.obj y.val).down
  rw [he]
  exact hp

def Cofibration.reindex {Γ Δ : Context.{u}} (φ : Cofibration Γ) (σ : Δ ⟶ Γ) : Cofibration Δ := σ ≫ φ

@[simp] theorem Cofibration.full_reindex {Γ Δ : Context.{u}} (φ : Cofibration Γ) (σ : Δ ⟶ Γ)
    (x : Δ.Elements) : (φ.reindex σ).full x ↔ φ.full (σ.mapElements.obj x) := Iff.rfl

def Cofibration.top (Γ : Context.{u}) : Cofibration Γ where
  app I := TypeCat.ofHom (fun _ => ⟨Face.top I.unop.dimension⟩)
  naturality _ _ _ := rfl

def Cofibration.bot (Γ : Context.{u}) : Cofibration Γ where
  app I := TypeCat.ofHom (fun _ => ⟨Face.bot I.unop.dimension⟩)
  naturality _ _ _ := rfl

def Cofibration.meet {Γ : Context.{u}} (φ ψ : Cofibration Γ) : Cofibration Γ where
  app I := TypeCat.ofHom (fun x => ⟨Face.meet (φ.app I x).down (ψ.app I x).down⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg₂ (fun a b => ULift.up (Face.meet a.down b.down))
      (φ.naturality_apply f x) (ψ.naturality_apply f x)

def Cofibration.join {Γ : Context.{u}} (φ ψ : Cofibration Γ) : Cofibration Γ where
  app I := TypeCat.ofHom (fun x => ⟨Face.join (φ.app I x).down (ψ.app I x).down⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg₂ (fun a b => ULift.up (Face.join a.down b.down))
      (φ.naturality_apply f x) (ψ.naturality_apply f x)

@[simp] theorem Cofibration.full_meet {Γ : Context.{u}} (φ ψ : Cofibration Γ) (x : Γ.Elements) :
    (φ.meet ψ).full x ↔ φ.full x ∧ ψ.full x := Face.full_meet _ _
@[simp] theorem Cofibration.full_join {Γ : Context.{u}} (φ ψ : Cofibration Γ) (x : Γ.Elements) :
    (φ.join ψ).full x ↔ φ.full x ∨ ψ.full x := Face.full_join _ _

/-- The restricted context has precisely the elements where the face is full. -/
def restrictContext {Γ : Context.{u}} (φ : Cofibration Γ) : Context.{u} where
  obj I := {x : Γ.obj I // φ.full (Γ.elementsMk I x)}
  map f := TypeCat.ofHom (fun x => ⟨Γ.map f x.val,φ.full_natural (Functor.Elements.homMk f rfl) x.property⟩)
  map_id I := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun k => k x.val) (Γ.map_id I)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun k => k x.val) (Γ.map_comp f g)

def restrictInclusion {Γ : Context.{u}} (φ : Cofibration Γ) : restrictContext φ ⟶ Γ where
  app _ := TypeCat.ofHom Subtype.val
  naturality _ _ _ := rfl

def restrictSubstitution {Γ Δ : Context.{u}} (φ : Cofibration Γ) (σ : Δ ⟶ Γ) :
    restrictContext (φ.reindex σ) ⟶ restrictContext φ where
  app _ := TypeCat.ofHom (fun x => ⟨σ.app _ x.val,x.property⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact σ.naturality_apply f x.val

theorem restrictSubstitution_inclusion {Γ Δ : Context.{u}} (φ : Cofibration Γ) (σ : Δ ⟶ Γ) :
    restrictSubstitution φ σ ≫ restrictInclusion φ = restrictInclusion (φ.reindex σ) ≫ σ := rfl

@[simp] theorem Cofibration.reindex_id {Γ : Context.{u}} (φ : Cofibration Γ) : φ.reindex (𝟙 Γ) = φ := rfl
@[simp] theorem Cofibration.reindex_comp {Γ Δ Θ : Context.{u}} (φ : Cofibration Γ)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) : (φ.reindex σ).reindex τ = φ.reindex (τ ≫ σ) := rfl
@[simp] theorem Cofibration.meet_reindex {Γ Δ : Context.{u}} (φ ψ : Cofibration Γ) (σ : Δ ⟶ Γ) :
    (φ.meet ψ).reindex σ = (φ.reindex σ).meet (ψ.reindex σ) := rfl
@[simp] theorem Cofibration.join_reindex {Γ Δ : Context.{u}} (φ ψ : Cofibration Γ) (σ : Δ ⟶ Γ) :
    (φ.join ψ).reindex σ = (φ.reindex σ).join (ψ.reindex σ) := rfl

theorem restrictSubstitution_comp {Γ Δ Θ : Context.{u}} (φ : Cofibration Γ)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    restrictSubstitution (φ.reindex σ) τ ≫ restrictSubstitution φ σ = restrictSubstitution φ (τ ≫ σ) := rfl

end SquareKit.Cubical.Presheaf
