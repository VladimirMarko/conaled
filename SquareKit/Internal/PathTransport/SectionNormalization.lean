import SquareKit.Internal.PathTransport.SplitFamily
import SquareKit.Internal.PathTransport.ContextualElimination
/-!
# Normalized sections from functors over the identity

The Grothendieck section functor and its component presentation agree by
strict equality. Elimination can therefore return an ordinary section while
retaining its computation and substitution equations.
-/

noncomputable section
open CategoryTheory
namespace SquareKit.Internal.PathTransport.GroupoidModel.Section
open ContextualElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w z
variable {Γ : Type u} [Category.{v} Γ] {A : Γ ⥤ Grpd.{z,w}}
variable (t : Γ ⥤ Extend A) (ht : t ⋙ weaken A = 𝟭 Γ)
abbrev normalized := normalize t (eqToIso ht)

def ofOver : Section A where
  obj γ := ((normalized t ht).obj γ).fiber
  map f := eqToHom (by rw [normalize_map_base]; rfl) ≫ ((normalized t ht).map f).fiber
  map_id γ := by
    have h := Grothendieck.congr ((normalized t ht).map_id γ)
    rw [h]
    simp
  map_comp f g := by
    have h := Grothendieck.congr ((normalized t ht).map_comp f g)
    rw [h]
    have hn := NatIso.naturality_2
      (eqToIso (congrArg A.map (normalize_map_base t (eqToIso ht) g)))
      ((normalized t ht).map f).fiber
    simp only [eqToIso.hom, eqToIso.inv, eqToHom_app] at hn
    simp only [Grothendieck.comp_fiber, Grpd.forgetToCat, Functor.map_comp, eqToHom_map, Category.assoc]
    dsimp only [Functor.comp_map, Grpd.forgetToCat, Functor.toCatHom_toFunctor]
    rw [← hn]
    simp

theorem ofOver_lift : (ofOver t ht).lift = t := by
  apply Eq.trans (b := normalized t ht) ?_ (normalize_eqToIso t ht)
  fapply CategoryTheory.Functor.ext
  · intro γ; rfl
  · intro γ δ f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    fapply Grothendieck.ext
    · exact (normalize_map_base t (eqToIso ht) f).symm
    · simp [ofOver, lift, normalized]
end SquareKit.Internal.PathTransport.GroupoidModel.Section

namespace SquareKit.Internal.PathTransport.GroupoidModel.Section
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Γ : Type u} [Category.{v} Γ] {A : Γ ⥤ Grpd.{z,w}}
/-- Equality of the functors presenting sections determines their components,
including after a change of base. -/
theorem ext_of_pair {Δ : Type*} [Category* Δ] (σ : Δ ⥤ Γ)
    {s t : Section (σ ⋙ A)} (h : pair A σ s = pair A σ t) : s = t := by
  cases s with
  | mk so sm si sc =>
    cases t with
    | mk tob tm ti tc =>
      have ho : so = tob := by
        funext γ
        have hh := CategoryTheory.Functor.congr_obj h γ
        injection hh
      cases ho
      congr
      funext γ δ f
      have hm := CategoryTheory.Functor.congr_hom h f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hm
      simpa [pair, Section.lift, Grothendieck.pre] using Grothendieck.congr hm

theorem lift_injective : Function.Injective (lift (A := A)) := by
  intro s t h
  exact ext_of_pair (𝟭 Γ) h

@[simp] theorem ofOver_section (s : Section A) : ofOver s.lift rfl = s :=
  lift_injective (ofOver_lift s.lift rfl)
end SquareKit.Internal.PathTransport.GroupoidModel.Section

namespace SquareKit.Internal.PathTransport.GroupoidModel
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w z
variable {Γ : Type u} [Category.{v} Γ] {A : Γ ⥤ Grpd.{z,w}}

theorem pair_injective {Δ : Type*} [Category* Δ] (σ : Δ ⥤ Γ) :
    Function.Injective (pair A σ) := by
  intro s t h
  exact Section.ext_of_pair σ h
end SquareKit.Internal.PathTransport.GroupoidModel
