import SquareKit.SheafFamilyCover
import Mathlib.CategoryTheory.Sites.Subcanonical

/-! Sheafified representables, their adjunction and original covering families. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.SheafifiedYoneda
open CategoryTheory Limits Opposite
universe u
variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)

/-- Representables followed by the existing left exact sheafification. -/
abbrev functor : C ⥤ Sheaf J (Type u) := yoneda ⋙ presheafToSheaf J (Type u)

/-- Evaluation uses the sheafification adjunction and Yoneda, rather than
identifying the sheafified presheaf with the raw representable. -/
def evaluation {U : C} {X : Sheaf J (Type u)} :
    ((functor J).obj U ⟶ X) ≃ X.obj.obj (op U) :=
  ((sheafificationAdjunction J (Type u)).homEquiv (yoneda.obj U) X).trans yonedaEquiv

theorem evaluation_apply {U : C} {X : Sheaf J (Type u)}
    (f : (functor J).obj U ⟶ X) :
    evaluation J f = f.hom.app (op U) ((toSheafify J (yoneda.obj U)).app (op U) (𝟙 U)) := rfl

theorem evaluation_comp {U : C} {X Y : Sheaf J (Type u)}
    (f : (functor J).obj U ⟶ X) (g : X ⟶ Y) :
    evaluation J (f ≫ g) = g.hom.app (op U) (evaluation J f) := rfl

theorem evaluation_naturality {U V : C} {X : Sheaf J (Type u)}
    (f : V ⟶ U) (g : (functor J).obj U ⟶ X) :
    evaluation J ((functor J).map f ≫ g) = X.obj.map f.op (evaluation J g) := by
  change yonedaEquiv ((sheafificationAdjunction J (Type u)).homEquiv _ _
    ((presheafToSheaf J (Type u)).map (yoneda.map f) ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact (CategoryTheory.yonedaEquiv_naturality
    ((sheafificationAdjunction J (Type u)).homEquiv (yoneda.obj U) X g) f).symm

/-- Original covering families cover after sheafification, including empty covers. -/
theorem jointlyLocallySurjective {I : Type u} {U : C} {V : I → C}
    (f : ∀ i, V i ⟶ U) (hf : Sieve.ofArrows V f ∈ J U) :
    SheafFamilyCover.JointlyLocallySurjective (fun i => (functor J).map (f i)) := by
  intro W x
  apply J.transitive (Presheaf.imageSieve_mem J (toSheafify J (yoneda.obj U)) x)
  rintro T k ⟨g, hg⟩
  apply J.superset_covering _ (J.pullback_stable g hf)
  rintro S l ⟨R, a, b, ⟨i⟩, hab⟩
  refine ⟨i, (toSheafify J (yoneda.obj (V i))).app (op S) a, ?_⟩
  have hn := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality J (yoneda.map (f i))) (op S)) a
  change (toSheafify J (yoneda.obj U)).app (op S) (a ≫ f i) = _ at hn
  change (toSheafify J (yoneda.obj U)).app (op S) (a ≫ f i) =
    ((functor J).map (f i)).hom.app (op S)
      ((toSheafify J (yoneda.obj (V i))).app (op S) a) at hn
  rw [← hn, hab]
  have hnat := NatTrans.naturality_apply (toSheafify J (yoneda.obj U)) l.op g
  change (toSheafify J (yoneda.obj U)).app (op S) (l ≫ g) = _ at hnat
  rw [hnat, hg]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  rfl

theorem covering_of_jointlyLocallySurjective {I : Type u} {U : C} {V : I → C}
    (f : ∀ i, V i ⟶ U)
    (hf : SheafFamilyCover.JointlyLocallySurjective (fun i => (functor J).map (f i))) :
    Sieve.ofArrows V f ∈ J U := by
  let e := (toSheafify J (yoneda.obj U)).app (op U) (𝟙 U)
  apply J.transitive (hf e)
  rintro W k ⟨i, y, hy⟩
  apply J.transitive (Presheaf.imageSieve_mem J (toSheafify J (yoneda.obj (V i))) y)
  rintro T l ⟨g, hg⟩
  have he : (toSheafify J (yoneda.obj U)).app (op T) (g ≫ f i) =
      (toSheafify J (yoneda.obj U)).app (op T) (l ≫ k) := by
    have hn := ConcreteCategory.congr_hom (NatTrans.congr_app
      (toSheafify_naturality J (yoneda.map (f i))) (op T)) g
    change (toSheafify J (yoneda.obj U)).app (op T) (g ≫ f i) =
      ((functor J).map (f i)).hom.app (op T)
        ((toSheafify J (yoneda.obj (V i))).app (op T) g) at hn
    rw [hn, hg]
    change ((functor J).map (f i)).hom.app (op T)
      (((functor J).obj (V i)).obj.map l.op y) = _
    rw [NatTrans.naturality_apply, hy]
    have hunit := NatTrans.naturality_apply (toSheafify J (yoneda.obj U)) (l ≫ k).op (𝟙 U)
    simpa [e, Category.comp_id, Functor.map_comp] using hunit.symm
  have hh := Presheaf.equalizerSieve_mem (D := Type u) J
    (toSheafify J (yoneda.obj U))
    (show (yoneda.obj U).obj (op T) from g ≫ f i)
    (show (yoneda.obj U).obj (op T) from l ≫ k) he
  apply J.superset_covering _ hh
  intro S m hm
  exact ⟨_, m ≫ g, _, ⟨i⟩, by simpa [Category.assoc] using hm⟩

/-- Covering is reflected using local injectivity of the unit, not global injectivity. -/
theorem jointlyLocallySurjective_iff {I : Type u} {U : C} {V : I → C}
    (f : ∀ i, V i ⟶ U) :
    SheafFamilyCover.JointlyLocallySurjective (fun i => (functor J).map (f i)) ↔
      Sieve.ofArrows V f ∈ J U :=
  ⟨covering_of_jointlyLocallySurjective J f, jointlyLocallySurjective J f⟩

/-- On a subcanonical site, the comparison is the adjunction counit. -/
def subcanonicalIso [J.Subcanonical] : functor J ≅ J.yoneda :=
  NatIso.ofComponents (fun U => asIso ((sheafificationAdjunction J (Type u)).counit.app
    (J.yoneda.obj U))) (by
      intro U V f
      exact (sheafificationAdjunction J (Type u)).counit.naturality (J.yoneda.map f))

end SquareKit.SheafifiedYoneda

namespace SquareKit.SheafifiedYoneda
open CategoryTheory Limits Opposite
universe u
variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable {P Q R : Cᵒᵖ ⥤ Type u} (f : P ⟶ R) (g : Q ⟶ R)

/-- Raw overlaps present the actual overlap of sheafified contexts by a local bijection. -/
def pullbackUnit : pullback f g ⟶
    (pullback ((presheafToSheaf J (Type u)).map f)
      ((presheafToSheaf J (Type u)).map g)).obj :=
  toSheafify J (pullback f g) ≫ (PreservesPullback.iso (presheafToSheaf J (Type u)) f g).hom.hom

instance pullbackUnit_isLocallyInjective : Presheaf.IsLocallyInjective J (pullbackUnit J f g) := by
  unfold pullbackUnit
  infer_instance

instance pullbackUnit_isLocallySurjective : Presheaf.IsLocallySurjective J (pullbackUnit J f g) := by
  unfold pullbackUnit
  infer_instance

theorem pullbackUnit_fst : pullbackUnit J f g ≫
    (pullback.fst ((presheafToSheaf J (Type u)).map f) ((presheafToSheaf J (Type u)).map g)).hom =
    pullback.fst f g ≫ toSheafify J P := by
  unfold pullbackUnit
  rw [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom,
    PreservesPullback.iso_hom_fst]
  exact (toSheafify_naturality J (pullback.fst f g)).symm

theorem pullbackUnit_snd : pullbackUnit J f g ≫
    (pullback.snd ((presheafToSheaf J (Type u)).map f) ((presheafToSheaf J (Type u)).map g)).hom =
    pullback.snd f g ≫ toSheafify J Q := by
  unfold pullbackUnit
  rw [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom,
    PreservesPullback.iso_hom_snd]
  exact (toSheafify_naturality J (pullback.snd f g)).symm

end SquareKit.SheafifiedYoneda
