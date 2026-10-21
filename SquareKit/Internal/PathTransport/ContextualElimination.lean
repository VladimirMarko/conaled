import Mathlib.CategoryTheory.Grothendieck

/-!
# Normalization of categorical sections

A functor into a Grothendieck construction whose projection is naturally
isomorphic to a prescribed context map can be normalized to lie strictly
over that map. Normalization preserves a reflexive comparison by equality,
and commutes with precomposition.

These operations use Mathlib's Grothendieck infrastructure. No external
formalization declarations are copied.
-/

open CategoryTheory CategoryTheory.Functor
universe u v u' v' w w'
namespace SquareKit.Internal.PathTransport.GroupoidModel.ContextualElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {F : C ⥤ Cat.{w,w'}} (t : D ⥤ Grothendieck F) {K : D ⥤ C}
variable (α : t ⋙ Grothendieck.forget F ≅ K)

def normalizeObj (d : D) : Grothendieck F :=
  (t.obj d).transport (α.app d).hom

def normalizeIso (d : D) : normalizeObj t α d ≅ t.obj d :=
  Grothendieck.transportIso (t.obj d) (α.app d)

def normalize : D ⥤ Grothendieck F where
  obj := normalizeObj t α
  map {x y} f := (normalizeIso t α x).hom ≫ t.map f ≫ (normalizeIso t α y).inv
  map_id x := by simp
  map_comp f g := by simp

def normalizeComparison : normalize t α ≅ t :=
  NatIso.ofComponents (normalizeIso t α) (by intros; simp [normalize])

@[simp] theorem normalize_obj_base (d : D) : ((normalize t α).obj d).base = K.obj d := rfl

@[simp] theorem normalize_map_base {x y : D} (f : x ⟶ y) :
    ((normalize t α).map f).base = K.map f := by
  dsimp [normalize, normalizeIso, Grothendieck.transportIso, Grothendieck.isoMk]
  change α.inv.app x ≫ (t.map f).base ≫ α.hom.app y = K.map f
  have h := α.hom.naturality f
  dsimp [Grothendieck.forget] at h
  rw [h]
  simp

theorem normalize_over : normalize t α ⋙ Grothendieck.forget F = K := by
  fapply Functor.ext
  · intro x; rfl
  · intro x y f; simp [normalize_map_base, Grothendieck.forget]

theorem normalize_refl : normalize t (Iso.refl (t ⋙ Grothendieck.forget F)) = t := by
  refine Functor.ext_of_iso (normalizeComparison t (Iso.refl _)) ?_ ?_
  · intro x
    dsimp [normalize, normalizeObj, Grothendieck.transport]
    simp
  · intro x
    apply Grothendieck.ext
    · simp [normalizeComparison, normalizeIso, Grothendieck.transportIso, Grothendieck.isoMk]
    · simp [normalizeComparison, normalizeIso, Grothendieck.transportIso, Grothendieck.isoMk]


variable {E : Type*} [Category* E]

theorem normalize_precomp (L : E ⥤ D) :
    normalize (L ⋙ t) (isoWhiskerLeft L α) = L ⋙ normalize t α := rfl

theorem normalize_eqToIso (h : t ⋙ Grothendieck.forget F = K) :
    normalize t (eqToIso h) = t := by
  subst K
  exact normalize_refl t

def extend (r : C ⥤ D) (i : D ⥤ C)
    (ε : r ⋙ i ≅ 𝟭 C) (s : D ⥤ Grothendieck F)
    (hs : s ⋙ Grothendieck.forget F = i) : C ⥤ Grothendieck F :=
  normalize (r ⋙ s) ((eqToIso (congrArg (r ⋙ ·) hs)) ≪≫ ε)

theorem extend_over (r : C ⥤ D) (i : D ⥤ C)
    (ε : r ⋙ i ≅ 𝟭 C) (s : D ⥤ Grothendieck F)
    (hs : s ⋙ Grothendieck.forget F = i) :
    extend r i ε s hs ⋙ Grothendieck.forget F = 𝟭 C :=
  normalize_over _ _

-- A normalized reflexive restriction gives equality, not merely an isomorphism.
theorem normalize_restriction (L : E ⥤ D)
    (h : (L ⋙ t) ⋙ Grothendieck.forget F = L ⋙ K)
    (hα : isoWhiskerLeft L α = eqToIso h) :
    L ⋙ normalize t α = L ⋙ t := by
  rw [← normalize_precomp, hα]
  exact normalize_eqToIso _ _

end SquareKit.Internal.PathTransport.GroupoidModel.ContextualElimination
