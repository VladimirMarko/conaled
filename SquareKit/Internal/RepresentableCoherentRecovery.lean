import SquareKit.Internal.CoherentFamilyClassification
import SquareKit.Internal.CoherentRepresentableCoding
import SquareKit.Internal.PresheafFamilyClassification
import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo

/-! Coherent recovery for category-valued families over presheaf contexts.
The coherent diagram presentation retains all squares and inverts restriction
comparisons. This concrete system has a decoder; no such claim is made for an
arbitrary context-indexed pseudofunctor. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.RepresentableClassification.CoherentFamily
open CategoryTheory CategoryTheory.Functor
open SquareKit.CoherentFamilyClassification
universe u v w a b
variable {C : Type v} [Category.{w} C] (V : Type a) [Category.{b} V]

/-- Context-indexed categories of families, with actual precomposition on arrows. -/
def families : (Context.{u} C)ᵒᵖ ⥤ Cat where
  obj Γ := Cat.of (Γ.unop.Elements ⥤ V)
  map σ := ((whiskeringLeft _ _ V).obj σ.unop.mapElements).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The existing coherent coding construction applied to category-valued families. -/
def system : Pseudofunctor (LocallyDiscrete (Context.{u} C)ᵒᵖ) Cat :=
  (families V).toPseudofunctor'

example (I : C) : (coherentCodes (system.{u} (C := C) V)).obj ⟨Opposite.op I⟩ =
    Cat.of ((representable.{u} I).Elements ⥤ V) := rfl

/-- Coherent local diagrams over each context. -/
def diagrams : (Context.{u} C)ᵒᵖ ⥤ Cat where
  obj Γ := Cat.of (Code Γ.unop.Elements V)
  map σ := (reindex (V := V) σ.unop.mapElements).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The concrete decoder packaged as a Mathlib pseudonatural transformation. -/
def decoder : Pseudofunctor.StrongTrans (diagrams (C := C) V).toPseudofunctor'
    (system (C := C) V) where
  app Γ := (decode Γ.as.unop.Elements V).toCatHom
  naturality σ := Cat.Hom.isoMk (decodeReindex σ.as.unop.mapElements)
  naturality_naturality := by
    intro Γ Δ σ τ h
    obtain rfl := LocallyDiscrete.eq_of_hom h
    have hh : h = 𝟙 σ := Subsingleton.elim _ _
    subst h
    simp only [PrelaxFunctor.map₂_id]
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext A
    apply NatTrans.ext
    funext x
    change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  naturality_id Γ := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext A
    apply NatTrans.ext
    funext x
    change ((decodeReindex (𝟭 Γ.as.unop.Elements)).hom.app A).app x ≫ 𝟙 _ =
      𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.comp_id]
    exact congrArg (fun η => η.app x) (decodeReindex_id A)
  naturality_comp σ τ := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext A
    apply NatTrans.ext
    funext x
    change ((decodeReindex (τ.as.unop.mapElements ⋙ σ.as.unop.mapElements)).hom.app A).app x ≫ 𝟙 _ =
      𝟙 _ ≫ 𝟙 _ ≫ ((decodeReindex τ.as.unop.mapElements).hom.app
        ((reindex σ.as.unop.mapElements).obj A)).app x ≫ 𝟙 _ ≫
        ((decodeReindex σ.as.unop.mapElements).hom.app A).app
          (τ.as.unop.mapElements.obj x) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    exact decodeReindex_comp _ _ _ _

/-- Coding is the pseudonatural inverse, with strict substitution comparisons. -/
def coder : Pseudofunctor.StrongTrans (system (C := C) V)
    (diagrams (C := C) V).toPseudofunctor' where
  app Γ := (code Γ.as.unop.Elements V).toCatHom
  naturality _ := Iso.refl _
  naturality_naturality := by
    intro Γ Δ σ τ h
    obtain rfl := LocallyDiscrete.eq_of_hom h
    have hh : h = 𝟙 σ := Subsingleton.elim _ _
    subst h
    simp only [PrelaxFunctor.map₂_id]
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext A
    apply ObjectProperty.hom_ext
    ext f
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    rfl
  naturality_id Γ := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext A
    apply ObjectProperty.hom_ext
    ext f
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.id_comp]
  naturality_comp σ τ := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext A
    apply ObjectProperty.hom_ext
    ext f
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.id_comp]

open scoped Pseudofunctor.StrongTrans

/-- Recovery is an invertible modification, compatible with every context substitution. -/
noncomputable def classificationUnit :
    𝟙 (diagrams (C := C) V).toPseudofunctor' ≅ decoder V ≫ coder V :=
  Pseudofunctor.StrongTrans.isoMk
    (fun Γ => Cat.Hom.isoMk (recoveryIso Γ.as.unop.Elements V)) (by
      intro Γ Δ σ
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext A
      apply ObjectProperty.hom_ext
      ext f
      change (recovery _ V ((reindex σ.as.unop.mapElements).obj A)).hom.app f ≫
        (𝟙 _ ≫ ((decodeReindex σ.as.unop.mapElements).hom.app A).app f.right ≫
          𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) =
        (𝟙 _ ≫ 𝟙 _) ≫ (recovery _ V A).hom.app (σ.as.unop.mapElements.mapArrow.obj f)
      simp only [Category.id_comp, Category.comp_id]
      change A.obj.map (σ.as.unop.mapElements.mapArrow.map (evaluationArrow _ f)) ≫
        (A.obj.map ((identityComparison σ.as.unop.mapElements).hom.app f.right) ≫ 𝟙 _) = _
      rw [Category.comp_id]
      exact recovery_reindex σ.as.unop.mapElements A f)

/-- Decoding a coded family is the identity, also as a modification. -/
def classificationCounit : coder (C := C) V ≫ decoder V ≅ 𝟙 (system V) :=
  Pseudofunctor.StrongTrans.isoMk (fun _ => Iso.refl _) (by
    intro Γ Δ σ
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext A
    apply NatTrans.ext
    funext x
    change 𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _) =
      (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ A.map (𝟙 _) ≫ 𝟙 _) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    exact (A.map_id _).symm)

/-- An actual element of a representable defines an arrow out of its named root. -/
def localArrow {Γ : Context.{u} C} (x : Γ.Elements) :
    (representable.{u} x.obj.unop).Elements ⥤ Arrow Γ.Elements where
  obj y := Arrow.mk (Functor.Elements.homMk y.val.down.op rfl :
    x ⟶ (represented x).mapElements.obj y)
  map {y z} f := Arrow.homMk (𝟙 x) ((represented x).mapElements.map f) (by
    apply Functor.Elements.hom_ext
    change 𝟙 x.obj ≫ z.val.down.op = y.val.down.op ≫ f.hom
    rw [Category.id_comp]
    have h := congrArg ULift.down f.map_val
    exact congrArg Quiver.Hom.op h.symm)
  map_id y := by apply Arrow.hom_ext <;> rfl
  map_comp f g := by
    apply Arrow.hom_ext
    · exact (Category.id_comp _).symm
    · rfl

/-- The target comparison in a represented restriction square. -/
def localTargetIso {Γ : Context.{u} C} {x y : Γ.Elements} (f : x ⟶ y) :
    (representableMap f.hom.unop).mapElements ⋙ (represented x).mapElements ≅
      (represented y).mapElements :=
  eqToIso (congrArg NatTrans.mapElements (represented_restrict f))

/-- Restriction changes the root of a local view and preserves its target up to iso. -/
def localRestriction {Γ : Context.{u} C} {x y : Γ.Elements} (f : x ⟶ y) :
    (representableMap f.hom.unop).mapElements ⋙ localArrow x ⟶ localArrow y where
  app z := Arrow.homMk f ((localTargetIso f).hom.app z) (by
    apply Functor.Elements.hom_ext
    change f.hom ≫ z.val.down.op =
      (z.val.down ≫ f.hom.unop).op ≫ ((localTargetIso f).hom.app z).hom
    have h : ((localTargetIso f).hom.app z).hom = 𝟙 _ := by
      change ((eqToHom (congrArg NatTrans.mapElements (represented_restrict f))).app z).hom = 𝟙 z.obj
      rw [eqToHom_app, elements_eqToHom_hom]
      rfl
    rw [h]
    exact (Category.comp_id _).symm)
  naturality z t g := by
    apply Arrow.hom_ext
    · change 𝟙 _ ≫ f = f ≫ 𝟙 _
      simp
    · exact (localTargetIso f).hom.naturality g

/-- Every coherent diagram supplies invertible representable restriction comparisons. -/
noncomputable def localRestrictionIso {Γ : Context.{u} C}
    (A : Code Γ.Elements V) {x y : Γ.Elements} (f : x ⟶ y) :
    (representableMap f.hom.unop).mapElements ⋙ localArrow x ⋙ A.obj ≅
      localArrow y ⋙ A.obj :=
  NatIso.ofComponents (fun z => by
    have hi : IsIso ((localRestriction f).app z).right := by
      change IsIso ((localTargetIso f).hom.app z)
      infer_instance
    exact @asIso _ _ _ _ (A.obj.map ((localRestriction f).app z))
      (A.property _ hi)) (by
        intro z t g
        change A.obj.map _ ≫ A.obj.map _ = A.obj.map _ ≫ A.obj.map _
        rw [← A.obj.map_comp, ← A.obj.map_comp]
        exact congrArg A.obj.map ((localRestriction f).naturality g))

/-- Local coherent data is a family over the actual representable context. -/
def localView {Γ : Context.{u} C} (x : Γ.Elements) :
    Code Γ.Elements V ⥤ ((representable.{u} x.obj.unop).Elements ⥤ V) :=
  (Coherent Γ.Elements V).ι ⋙ (whiskeringLeft _ _ V).obj (localArrow x)

/-- Coding then taking a local view is exactly the existing represented restriction,
including its action on natural transformations. -/
theorem code_localView {Γ : Context.{u} C} (x : Γ.Elements) :
    code Γ.Elements V ⋙ localView V x =
      ((system V).map (represented x).op.toLoc).toFunctor := rfl

/-- Recovery is an equivalence of categories at every context. -/
noncomputable def classification (Γ : Context.{u} C) :
    Code Γ.Elements V ≌ (Γ.Elements ⥤ V) := equivalence Γ.Elements V

/-- Evaluation in the represented generic-element coordinates used by the shared core. -/
def genericDecode {Γ : Context.{u} C} (A : Code Γ.Elements V) : Γ.Elements ⥤ V :=
  evaluatedFunctor Γ ⋙ (decode Γ.Elements V).obj A

/-- The established categorical evaluation argument supplies generic-element recovery. -/
noncomputable def genericRecovery {Γ : Context.{u} C} (A : Code Γ.Elements V) :
    genericDecode V A ≅ (decode Γ.Elements V).obj A :=
  CategoricalEvaluation.iso (A := (decode Γ.Elements V).obj A)
    (D := genericDecode V A) ⟨fun _ => rfl, fun f => by
      change ((decode Γ.Elements V).obj A).map (evaluatedMap f) ≫ 𝟙 _ =
        𝟙 _ ≫ ((decode Γ.Elements V).obj A).map (evaluatedMap f)
      simp⟩

/-- An actual local generic fiber compares to the decoded generic fiber. -/
noncomputable def localGenericRecovery {Γ : Context.{u} C}
    (A : Code Γ.Elements V) (x : Γ.Elements) :
    ((localView V x).obj A).obj (representableGeneric x.obj.unop) ≅
      (genericDecode V A).obj x :=
  (recovery Γ.Elements V A).app ((localArrow x).obj (representableGeneric x.obj.unop))

/-- Strict Type-family codes are the same represented restrictions. -/
theorem strict_code_localView {Γ : Context.{u} C} (A : Family Γ) (x : Γ.Elements) :
    (localView (Type (max u w)) x).obj ((code Γ.Elements _).obj A) =
      (PresheafFamily.system.code A).app x.obj ⟨x.val⟩ := rfl

/-- Existing generic-element recovery remains the comparison for the strict decoder. -/
theorem strict_recovery {Γ : Context.{u} C} (A : Family Γ) :
    (PresheafFamily.evaluation A).categorical.iso = PresheafFamily.recovery A :=
  (PresheafFamily.evaluation A).categorical_iso

end SquareKit.RepresentableClassification.CoherentFamily
