import SquareKit.ElementSite
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! Locally bijective presheaf maps induce equivalent sheaf categories on their sites of elements. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.ElementSite
open CategoryTheory Opposite
universe u v w a b
variable {C : Type u} [Category.{v} C] {P Q : Cᵒᵖ ⥤ Type w}
variable (η : P ⟶ Q) (J : GrothendieckTopology C)

abbrev mapSite : Site P ⥤ Site Q := η.mapElements.op

instance : (mapSite η).Faithful where
  map_injective h := by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    exact congrArg (fun f => f.unop.hom) h

/-- Forgetting sections sends an element sieve to its underlying base sieve. -/
theorem projection_pushforward {X : Site P} (S : Sieve X) :
    S.functorPushforward (projection P) = down P S := by
  ext V f
  constructor
  · rintro ⟨Y, g, h, hg, rfl⟩
    exact (down P S).downward_closed ⟨Y.unop.val, g.unop.map_val, hg⟩ h
  · rintro ⟨y, hy, hs⟩
    exact ⟨_, _, 𝟙 _, hs, (Category.id_comp _).symm⟩

theorem projection_coverPreserving : CoverPreserving (topology P J) J (projection P) where
  cover_preserve hS := by rwa [projection_pushforward]

theorem projection_compatiblePreserving : CompatiblePreserving J (projection P) where
  compatible {_ Z _ _ hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ h} := by
    let W' := point P W (P.map f₁.op Y₁.unop.val)
    let k₁ : W' ⟶ Y₁ := arrow P f₁ Y₁.unop.val
    have he : P.map f₂.op Y₂.unop.val = P.map f₁.op Y₁.unop.val := by
      rw [← g₂.unop.map_val, ← g₁.unop.map_val]
      change P.map f₂.op (P.map g₂.unop.hom Z.unop.val) =
        P.map f₁.op (P.map g₁.unop.hom Z.unop.val)
      rw [← types_comp_apply, ← P.map_comp, ← types_comp_apply, ← P.map_comp]
      exact congrArg (fun k => P.map k.op Z.unop.val) h.symm
    let k₂ : W' ⟶ Y₂ := (Functor.Elements.homMk f₂.op he).op
    exact hx k₁ k₂ hg₁ hg₂ (by
      apply Quiver.Hom.unop_inj
      apply Functor.Elements.hom_ext
      exact congrArg Quiver.Hom.op h)

instance projection_isContinuous : (projection P).IsContinuous (topology P J) J :=
  Functor.isContinuous_of_coverPreserving (projection_compatiblePreserving J)
    (projection_coverPreserving J)

/-- The image sieve has exactly the same underlying base sieve. -/
theorem down_pushforward {X : Site P} (S : Sieve X) :
    down Q (S.functorPushforward (mapSite η)) = down P S := by
  ext V f
  constructor
  · rintro ⟨y, hy, Y, g, h, hg, heq⟩
    have hg' : down P S g.unop.hom.unop := ⟨Y.unop.val, g.unop.map_val, hg⟩
    have hh := (down P S).downward_closed hg' h.unop.hom.unop
    have heq' := congrArg (fun k => k.unop.hom.unop) heq
    change f = h.unop.hom.unop ≫ g.unop.hom.unop at heq'
    rw [heq']
    exact hh
  · rintro ⟨y, hy, hs⟩
    let g := (Functor.Elements.homMk (x := X.unop)
      (y := P.elementsMk (op V) y) f.op hy).op
    refine ⟨η.app (op V) y, ((mapSite η).map g).unop.map_val, ?_⟩
    refine ⟨_, g, 𝟙 _, hs, ?_⟩
    rw [Category.id_comp]
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    rfl

theorem mapSite_coverPreserving : CoverPreserving (topology P J) (topology Q J) (mapSite η) where
  cover_preserve hS := by
    change down Q _ ∈ J _
    rw [down_pushforward]
    exact hS

instance mapSite_isLocallyFull [Presheaf.IsLocallyInjective J η] :
    (mapSite η).IsLocallyFull (topology Q J) where
  functorPushforward_imageSieve_mem {X Y} f := by
    rw [covering_iff, down_pushforward]
    let R := Presheaf.equalizerSieve (F := P) (P.map f.unop.hom Y.unop.val) X.unop.val
    have hR : R ∈ J X.unop.obj.unop := Presheaf.equalizerSieve_mem J η _ _ (by
      exact (η.naturality_apply f.unop.hom Y.unop.val).trans f.unop.map_val)
    apply J.superset_covering ?_ hR
    intro V g hg
    refine ⟨_, rfl, ?_⟩
    let l : point P V (P.map g.op X.unop.val) ⟶ Y :=
      (Functor.Elements.homMk (F := P) (f.unop.hom ≫ g.op) (by
        change P.map (f.unop.hom ≫ g.op) Y.unop.val = P.map g.op X.unop.val
        simpa only [R, Presheaf.equalizerSieve, Functor.map_comp, types_comp_apply] using hg)).op
    refine ⟨l, ?_⟩
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    rfl

instance mapSite_isCoverDense [Presheaf.IsLocallySurjective J η] :
    (mapSite η).IsCoverDense (topology Q J) where
  is_cover X := by
    apply J.superset_covering ?_ (Presheaf.imageSieve_mem J η X.unop.val)
    intro V f hf
    obtain ⟨p, hp⟩ := hf
    let g : (mapSite η).obj (point P V p) ⟶ X :=
      (Functor.Elements.homMk f.op hp.symm).op
    refine ⟨_, g.unop.map_val, ?_⟩
    exact Presieve.in_coverByImage (mapSite η) g

instance mapSite_isDenseSubsite [Presheaf.IsLocallyInjective J η]
    [Presheaf.IsLocallySurjective J η] :
    (mapSite η).IsDenseSubsite (topology P J) (topology Q J) where
  functorPushforward_mem_iff := by
    intro X S
    change down Q _ ∈ J _ ↔ down P _ ∈ J _
    rw [down_pushforward]
    rfl

/-- Sheaves on locally bijective presheaf presentations have equivalent categories.
The inverse is restriction along the map of sites; Mathlib constructs the extension. -/
def localSheafEquivalence (A : Type a) [Category.{b} A]
    [∀ X, Limits.HasLimitsOfShape (StructuredArrow X (mapSite η).op) A]
    [Presheaf.IsLocallyInjective J η] [Presheaf.IsLocallySurjective J η] :
    Sheaf (topology P J) A ≌ Sheaf (topology Q J) A :=
  Functor.IsDenseSubsite.sheafEquiv (topology P J) (topology Q J) (mapSite η) A

/-- Restriction in the comparison keeps the original value at every presented section. -/
theorem localSheafEquivalence_inverse_obj (A : Type a) [Category.{b} A]
    [∀ X, Limits.HasLimitsOfShape (StructuredArrow X (mapSite η).op) A]
    [Presheaf.IsLocallyInjective J η] [Presheaf.IsLocallySurjective J η]
    (F : Sheaf (topology Q J) A) :
    ((localSheafEquivalence η J A).inverse.obj F).obj = (mapSite η).op ⋙ F.obj := rfl

end SquareKit.ElementSite

namespace SquareKit.ElementSite
open CategoryTheory Opposite
universe u
variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
/-- Sheafification does not change the sheaves on the site of elements. -/
def sheafificationEquivalence (P : Cᵒᵖ ⥤ Type u) :
    Sheaf (ElementSite.topology P J) (Type u) ≌
      Sheaf (ElementSite.topology (sheafify J P) J) (Type u) :=
  ElementSite.localSheafEquivalence (toSheafify J P) J (Type u)
end SquareKit.ElementSite
