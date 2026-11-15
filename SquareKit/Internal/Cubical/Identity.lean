import SquareKit.Internal.Cubical.Paths
import SquareKit.Internal.Cubical.FaceContexts

/-! Identity elements retain a path and a face on which it is constant.
The face is data, not proof-irrelevant host equality. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

structure IdentityElement {Γ : Context.{u}} (A : Family Γ) (a b : Term A) (x : Γ.Elements) where
  path : PathElement (reindex A (projection (interval Γ))) a b x
  face : Face.Carrier x.obj.unop.dimension
  constant : ∀ {y : Γ.Elements} (f : x ⟶ y), Face.Full (Face.substitute f.hom.unop face) →
    ∀ r : (interval Γ).obj y, path.val.val f r = a.val y

@[ext] theorem IdentityElement.ext {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    {x : Γ.Elements} {p q : IdentityElement A a b x}
    (hp : p.path = q.path) (hf : p.face = q.face) : p = q := by
  cases p
  cases q
  cases hp
  cases hf
  rfl

theorem IdentityElement.hext_right {Γ : Context.{u}} {A : Family Γ} {a b c : Term A}
    (e : b = c) {x : Γ.Elements} (p : IdentityElement A a b x) (q : IdentityElement A a c x)
    (hp : p.path.val = q.path.val) (hf : p.face = q.face) : HEq p q := by
  cases e
  exact heq_of_eq (IdentityElement.ext (Subtype.ext hp) hf)

def IdentityElement.restrict {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    {x y : Γ.Elements} (f : x ⟶ y) (p : IdentityElement A a b x) : IdentityElement A a b y where
  path := (Presheaf.path (reindex A (projection (interval Γ))) a b).map f p.path
  face := Face.substitute f.hom.unop p.face
  constant g h r := by
    apply p.constant (f ≫ g) _ r
    exact (congrArg Face.Full (Face.substitute_comp g.hom.unop f.hom.unop p.face)).mp h

def identity {Γ : Context.{u}} (A : Family Γ) (a b : Term A) : Family Γ where
  obj x := IdentityElement A a b x
  map f := TypeCat.ofHom (IdentityElement.restrict f)
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro p
    apply IdentityElement.ext
    · exact congrArg (fun k => k p.path)
        ((Presheaf.path (reindex A (projection (interval Γ))) a b).map_id x)
    · rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro p
    apply IdentityElement.ext
    · exact congrArg (fun k => k p.path)
        ((Presheaf.path (reindex A (projection (interval Γ))) a b).map_comp f g)
    · exact (Face.substitute_comp g.hom.unop f.hom.unop p.face).symm

def identityPath {Γ : Context.{u}} (A : Family Γ) (a b : Term A) :
    identity A a b ⟶ path (reindex A (projection (interval Γ))) a b where
  app _ := TypeCat.ofHom IdentityElement.path
  naturality _ _ _ := rfl

def identityRefl {Γ : Context.{u}} {A : Family Γ} (a : Term A) : Term (identity A a a) where
  val x := {
    path := (pathLam (a.reindex (projection (interval Γ))) rfl rfl).val x
    face := Face.top x.obj.unop.dimension
    constant _ _ _ := rfl }
  property f := by
    apply IdentityElement.ext
    · rfl
    · rfl

def identityFace {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    (p : Term (identity A a b)) : Cofibration Γ where
  app I := TypeCat.ofHom (fun x => ⟨(p.val (Γ.elementsMk I x)).face⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun t => ULift.up t.face)
      (p.property (show Γ.elementsMk I x ⟶ Γ.elementsMk J (Γ.map f x) from
        Functor.Elements.homMk f rfl)).symm

theorem identityFace_refl {Γ : Context.{u}} {A : Family Γ} (a : Term A) :
    identityFace (identityRefl a) = Cofibration.top Γ := rfl

def identityIntro {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    (p : Term (path (reindex A (projection (interval Γ))) a b)) (φ : Cofibration Γ)
    (h : ∀ (x : Γ.Elements), φ.full x → ∀ r : (interval Γ).obj x,
      (p.val x).val.val (𝟙 _) r = a.val x) : Term (identity A a b) where
  val x := {
    path := p.val x
    face := (φ.app x.obj x.val).down
    constant := by
      intro y f hf r
      have he := congrArg ULift.down (φ.naturality_apply f.hom x.val)
      change (φ.app y.obj (Γ.map f.hom x.val)).down =
        Face.substitute f.hom.unop (φ.app x.obj x.val).down at he
      rw [f.map_val] at he
      have hy : φ.full y := (congrArg Face.Full he).mpr hf
      have hp := congrArg (fun q => q.val.val (𝟙 _) r) (p.property f)
      change (p.val x).val.val (f ≫ 𝟙 _) r = (p.val y).val.val (𝟙 _) r at hp
      have hp' : (p.val x).val.val f r = (p.val y).val.val (𝟙 _) r := by
        simpa only [Category.comp_id] using hp
      exact hp'.trans (h y hy r) }
  property {x y} f := by
    apply IdentityElement.ext
    · exact p.property f
    · have he := congrArg ULift.down (φ.naturality_apply f.hom x.val)
      change (φ.app y.obj (Γ.map f.hom x.val)).down = _ at he
      rw [f.map_val] at he
      exact he.symm

theorem identityPath_intro {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    (p : Term (path (reindex A (projection (interval Γ))) a b)) (φ : Cofibration Γ)
    (h : ∀ (x : Γ.Elements), φ.full x → ∀ r : (interval Γ).obj x,
      (p.val x).val.val (𝟙 _) r = a.val x) :
    Term.map (identityPath A a b) (identityIntro p φ h) = p := rfl

theorem identityFace_intro {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    (p : Term (path (reindex A (projection (interval Γ))) a b)) (φ : Cofibration Γ)
    (h : ∀ (x : Γ.Elements), φ.full x → ∀ r : (interval Γ).obj x,
      (p.val x).val.val (𝟙 _) r = a.val x) : identityFace (identityIntro p φ h) = φ := rfl

end SquareKit.Cubical.Presheaf
