import SquareKit.Internal.PathTransport.EliminationUniqueness

/-!
# Canonical operations in the based path context

Primitive transport applies the given set-valued functor to the identity
witness. Its section laws use the path-context commuting square and the input
section's naturality. The reflexive computation is an equality of sections.
-/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.DerivedSemantics
open CategoryTheory PathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w z
variable {Γ : Type u} [Category.{v} Γ]
variable {C : Type w} [Groupoid.{z} C]
variable (B : C ⥤ Type w) (x : Section (constant (Γ := Γ) C))

/-- The varying endpoint in the actual endpoint-and-path comprehension. -/
def endpoint : Section (constant (Γ := PathCtx (constant C) x) C) :=
  («variable» (constant C)).reindex (weaken (PathFamily (constant C) x))

variable (b : Section (primitiveFiber B x))

/-- Apply the primitive fiber action to the path and the given fiber element. -/
def transport : Section (primitiveFiber B (endpoint x)) where
  obj a := Discrete.mk (B.map a.fiber.as (b.obj a.base.base).as)
  map {a a'} f := Discrete.eqToHom (by
    have hp : a.fiber.as ≫ f.base.fiber = x.map f.base.base ≫ a'.fiber.as := by
      have h := f.fiber.eq
      change inv (x.map f.base.base) ≫ a.fiber.as ≫ f.base.fiber = a'.fiber.as at h
      rw [← h]
      simp
    have hb := Discrete.eq_of_hom (b.map f.base.base)
    change B.map (x.map f.base.base) (b.obj a.base.base).as = (b.obj a'.base.base).as at hb
    change B.map f.base.fiber (B.map a.fiber.as (b.obj a.base.base).as) =
      B.map a'.fiber.as (b.obj a'.base.base).as
    calc
      _ = B.map (a.fiber.as ≫ f.base.fiber) (b.obj a.base.base).as :=
        (B.map_comp_apply _ _ _).symm
      _ = B.map (x.map f.base.base ≫ a'.fiber.as) (b.obj a.base.base).as :=
        congrArg (fun q => B.map q (b.obj a.base.base).as) hp
      _ = B.map a'.fiber.as (B.map (x.map f.base.base) (b.obj a.base.base).as) :=
        B.map_comp_apply _ _ _
      _ = _ := congrArg (fun v => B.map a'.fiber.as v) hb)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Identity-path action recovers the original section strictly. -/
theorem transport_reflexive : (transport B x b).reindex (reflexive (constant C) x) = b := by
  apply Section.ext_discrete (A := primitiveFiber B x)
  intro γ
  apply Discrete.ext
  change B.map (𝟙 (x.obj γ)) (b.obj γ).as = (b.obj γ).as
  simp
@[simp] theorem transport_obj (a : PathCtx (constant C) x) :
    ((transport B x b).obj a).as = B.map a.fiber.as (b.obj a.base.base).as := rfl

/-- Canonical transport is the unique section with the specified reflexive
restriction because the primitive fibers are discrete. -/
theorem transport_unique [IsGroupoid Γ]
    (s : Section (primitiveFiber B (endpoint x)))
    (h : s.reindex (reflexive (constant C) x) = b) : s = transport B x b := by
  apply Section.reindex_injective_of_essSurj (pathEquivalence (constant C) x).functor
  exact h.trans (transport_reflexive B x b).symm
end SquareKit.Internal.PathTransport.GroupoidModel.DerivedSemantics

namespace SquareKit.Internal.PathTransport.GroupoidModel.DerivedSemantics
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w z
variable {Γ : Type u} [Category.{v} Γ]
variable (A : Γ ⥤ Grpd.{z,w}) (x y z : Section A)

/-- Compose identity witnesses fiberwise. The endpoint conjugations in their
naturality equations cancel at the shared endpoint. -/
def composePaths (p : Section (identityFamily A x y)) (q : Section (identityFamily A y z)) :
    Section (identityFamily A x z) where
  obj γ := Discrete.mk ((p.obj γ).as ≫ (q.obj γ).as)
  map {γ δ} f := Discrete.eqToHom (by
    have hp := Discrete.eq_of_hom (p.map f)
    have hq := Discrete.eq_of_hom (q.map f)
    change inv (x.map f) ≫ (A.map f).map (p.obj γ).as ≫ y.map f = (p.obj δ).as at hp
    change inv (y.map f) ≫ (A.map f).map (q.obj γ).as ≫ z.map f = (q.obj δ).as at hq
    change inv (x.map f) ≫ (A.map f).map ((p.obj γ).as ≫ (q.obj γ).as) ≫ z.map f =
      (p.obj δ).as ≫ (q.obj δ).as
    rw [← hp, ← hq]
    simp)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp] theorem composePaths_obj (p : Section (identityFamily A x y))
    (q : Section (identityFamily A y z)) (γ : Γ) :
    ((composePaths A x y z p q).obj γ).as = (p.obj γ).as ≫ (q.obj γ).as := rfl

@[simp] theorem composePaths_reflexive_left (q : Section (identityFamily A x z)) :
    composePaths A x x z (reflexivitySection A x) q = q := by
  apply Section.ext_discrete
  intro γ
  apply Discrete.ext
  exact Category.id_comp _

@[simp] theorem composePaths_reflexive_right (p : Section (identityFamily A x y)) :
    composePaths A x y y p (reflexivitySection A y) = p := by
  apply Section.ext_discrete
  intro γ
  apply Discrete.ext
  exact Category.comp_id _

@[simp] theorem composePaths_reindex {Δ : Type*} [Category* Δ] (σ : Δ ⥤ Γ)
    (p : Section (identityFamily A x y)) (q : Section (identityFamily A y z)) :
    (composePaths A x y z p q).reindex σ =
      composePaths (σ ⋙ A) (x.reindex σ) (y.reindex σ) (z.reindex σ)
        (p.reindex σ) (q.reindex σ) := rfl
end SquareKit.Internal.PathTransport.GroupoidModel.DerivedSemantics
