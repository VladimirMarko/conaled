import SquareKit.Internal.RepresentableClassification

/-! Generic-element evaluation and recovery with values in any category. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.RepresentableClassification
open CategoryTheory
universe u v w a b
variable {C : Type v} [Category.{w} C] {Γ : Context.{u} C}

/-- The generic element of the context represented by an element. -/
abbrev evaluatedElement (x : Γ.Elements) : Γ.Elements :=
  (represented x).mapElements.obj (representableGeneric x.obj.unop)

/-- The arrow obtained by restricting a generic element and evaluating it. -/
def evaluatedMap {x y : Γ.Elements} (f : x ⟶ y) : evaluatedElement x ⟶ evaluatedElement y :=
  (represented x).mapElements.map (representableGenericHom f.hom.unop) ≫
    eqToHom (congrArg (fun σ => σ.mapElements.obj (representableGeneric y.obj.unop))
      (represented_restrict f))

theorem evaluatedMap_naturality {x y : Γ.Elements} (f : x ⟶ y) :
    evaluatedMap f ≫ eqToHom (represented_generic_source y) =
      eqToHom (represented_generic_source x) ≫ f := by
  apply Functor.Elements.hom_ext
  dsimp only [evaluatedMap]
  simp only [Functor.Elements.comp_hom, elements_eqToHom_hom]
  change (f.hom ≫ 𝟙 _) ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
  simp

/-- Generic-element evaluation is functorial before choosing a target category. -/
def evaluatedFunctor (Γ : Context.{u} C) : Γ.Elements ⥤ Γ.Elements where
  obj := evaluatedElement
  map := evaluatedMap
  map_id x := by
    apply (cancel_mono (eqToHom (represented_generic_source x))).1
    rw [evaluatedMap_naturality]
    simp
  map_comp f g := by
    apply (cancel_mono (eqToHom (represented_generic_source _))).1
    rw [evaluatedMap_naturality, Category.assoc, evaluatedMap_naturality]
    rw [← Category.assoc (evaluatedMap f), evaluatedMap_naturality, Category.assoc]

/-- Evaluation formulas for a family with values in an arbitrary category.
The map equation concerns evaluation at represented generic elements, before
transport to the original family. -/
structure CategoricalEvaluation {V : Type a} [Category.{b} V]
    (A D : Γ.Elements ⥤ V) : Prop where
  obj : ∀ x, D.obj x = A.obj (evaluatedElement x)
  map : ∀ {x y} (f : x ⟶ y),
    D.map f ≫ eqToHom (obj y) = eqToHom (obj x) ≫ A.map (evaluatedMap f)

namespace CategoricalEvaluation
variable {V : Type a} [Category.{b} V] {A D : Γ.Elements ⥤ V}
  (E : CategoricalEvaluation A D)

def component (x : Γ.Elements) : D.obj x ≅ A.obj x :=
  eqToIso (E.obj x) ≪≫ A.mapIso (eqToIso (represented_generic_source x))

/-- Local evaluation formulas derive the entire natural family comparison. -/
def iso : D ≅ A := NatIso.ofComponents E.component (by
  intro x y f
  change D.map f ≫ (eqToHom (E.obj y) ≫ A.map (eqToHom (represented_generic_source y))) =
    (eqToHom (E.obj x) ≫ A.map (eqToHom (represented_generic_source x))) ≫ A.map f
  rw [← Category.assoc, E.map, Category.assoc, ← A.map_comp,
    evaluatedMap_naturality, A.map_comp, Category.assoc])
end CategoricalEvaluation
private theorem type_eqToHom_apply {X Y : Type a} (e : X = Y) (z : X) :
    (eqToHom e : X ⟶ Y) z = cast e z := by
  cases e
  rfl

/-- The existing Type-valued equations satisfy the categorical interface. -/
theorem Evaluation.categorical {A D : Family Γ} (E : Evaluation A D) :
    CategoricalEvaluation A D where
  obj := E.obj
  map := by
    intro x y f
    apply ConcreteCategory.hom_ext
    intro z
    simp only [types_comp_apply, type_eqToHom_apply]
    let e := congrArg (fun σ => σ.mapElements.obj (representableGeneric y.obj.unop))
      (represented_restrict f)
    have hm := family_map_heq A (evaluatedMap f)
      ((represented x).mapElements.map (representableGenericHom f.hom.unop)) e.symm
      (heq_of_eq (by
        dsimp only [evaluatedMap]
        simp only [Functor.Elements.comp_hom, elements_eqToHom_hom]
        change f.hom ≫ 𝟙 _ = f.hom
        exact Category.comp_id _)) (cast (E.obj x) z)
    exact eq_of_heq ((cast_heq _ _).trans ((E.map f z).trans hm.symm))

/-- The category-valued derivation recovers the original Type-valued comparison. -/
theorem Evaluation.categorical_iso {A D : Family Γ} (E : Evaluation A D) :
    E.categorical.iso = E.iso := by
  apply Iso.ext
  ext x z
  change A.map (eqToHom (represented_generic_source x)) ((eqToHom (E.obj x)) z) =
    A.map (eqToHom (represented_generic_source x)) (cast (E.obj x) z)
  rw [type_eqToHom_apply]
end SquareKit.RepresentableClassification
