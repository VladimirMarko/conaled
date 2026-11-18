import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Types.Basic

/-! Representable coding and generic-element evaluation with independent base object and morphism universes.
No interval or selected filling operation is part of this interface. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.RepresentableClassification
open CategoryTheory
universe u v w
abbrev Context (C : Type v) [Category.{w} C] := Cᵒᵖ ⥤ Type (max u w)
abbrev Family {C : Type v} [Category.{w} C] (Γ : Context.{u} C) := Γ.Elements ⥤ Type (max u w)
variable {C : Type v} [Category.{w} C]
def representable (I : C) : Context.{u} C where
  obj J := ULift.{u} (J.unop ⟶ I)
  map f := TypeCat.ofHom (fun g => ⟨f.unop ≫ g.down⟩)
  map_id J := by
    apply ConcreteCategory.hom_ext
    intro g
    exact congrArg ULift.up (Category.id_comp g.down)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro h
    exact congrArg ULift.up (Category.assoc g.unop f.unop h.down)
def represented {Γ : Context.{u} C} (x : Γ.Elements) : representable x.obj.unop ⟶ Γ where
  app J := TypeCat.ofHom (fun f => Γ.map f.down.op x.val)
  naturality J K f := by
    apply ConcreteCategory.hom_ext
    intro g
    exact ConcreteCategory.congr_hom (Γ.map_comp g.down.op f) x.val

/-- Restriction of a represented context along a base-category map. -/
def representableMap {I J : C} (f : J ⟶ I) : representable J ⟶ representable I where
  app K := TypeCat.ofHom (fun g => ⟨g.down ≫ f⟩)
  naturality K L g := by
    apply ConcreteCategory.hom_ext
    intro h
    exact congrArg ULift.up (Category.assoc g.unop h.down f)

@[simp] theorem represented_id {Γ : Context.{u} C} (x : Γ.Elements) :
    (represented x).app x.obj ⟨𝟙 x.obj.unop⟩ = x.val := by
  exact ConcreteCategory.congr_hom (Γ.map_id x.obj) x.val

/-- The generic generalized element of a represented context. -/
def representableGeneric (I : C) : (representable.{u} I).Elements :=
  (representable I).elementsMk (Opposite.op I) ⟨𝟙 I⟩

@[simp] theorem represented_restrict {Γ : Context.{u} C} {x y : Γ.Elements} (f : x ⟶ y) :
    representableMap f.hom.unop ≫ represented x = represented y := by
  ext K g
  change Γ.map (g.down ≫ f.hom.unop).op x.val = Γ.map g.down.op y.val
  exact (ConcreteCategory.congr_hom (Γ.map_comp f.hom g.down.op) x.val).trans
    (congrArg (fun z => Γ.map g.down.op z) f.map_val)

theorem represented_naturality {Γ Δ : Context.{u} C} (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    represented (σ.mapElements.obj x) = represented x ≫ σ := by
  ext J f
  exact (ConcreteCategory.congr_hom (σ.naturality f.down.op) x.val).symm

theorem represented_generic_source {Γ : Context.{u} C} (x : Γ.Elements) :
    (represented x).mapElements.obj (representableGeneric x.obj.unop) = x :=
  Functor.Elements.ext _ _ rfl
    ((ConcreteCategory.congr_hom (Γ.map_id x.obj) _).trans (represented_id x))

theorem elements_eqToHom_hom {Γ : Context.{u} C} {x y : Γ.Elements} (e : x = y) :
    (eqToHom e : x ⟶ y).hom = eqToHom (congrArg (fun z : Γ.Elements => z.obj) e) := by
  cases e
  rfl

theorem represented_generic_identity (I : C) :
    represented (representableGeneric.{u} I) = 𝟙 (representable.{u} I) := by
  ext J f
  exact congrArg ULift.up (Category.comp_id f.down)

theorem represented_map_generic {Γ : Context.{u} C} {I : C} (σ : representable.{u} I ⟶ Γ) :
    represented (σ.mapElements.obj (representableGeneric I)) = σ := by
  exact (represented_naturality σ (representableGeneric I)).trans
    ((congrArg (fun τ => τ ≫ σ) (represented_generic_identity I)).trans (Category.id_comp σ))

def raisedContext (Γ : Context.{u} C) : Context.{max v (u+1) (w+1)} C where
  obj I := ULift.{max v (u+1) (w+1)} (Γ.obj I)
  map f := TypeCat.ofHom (fun x => ⟨Γ.map f x.down⟩)
  map_id I := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.up (ConcreteCategory.congr_hom (Γ.map_id I) x.down)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.up (ConcreteCategory.congr_hom (Γ.map_comp f g) x.down)

def raisedSub {Γ Δ : Context.{u} C} (σ : Δ ⟶ Γ) : raisedContext Δ ⟶ raisedContext Γ where
  app I := TypeCat.ofHom (fun x => ⟨σ.app I x.down⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.up (ConcreteCategory.congr_hom (σ.naturality f) x.down)

def raisedElements (Γ : Context.{u} C) : Γ.Elements ⥤ (raisedContext Γ).Elements where
  obj x := (raisedContext Γ).elementsMk x.obj ⟨x.val⟩
  map f := Functor.Elements.homMk f.hom (congrArg ULift.up f.map_val)
  map_id _ := rfl
  map_comp _ _ := rfl

def representableGenericHom {I J : C} (f : J ⟶ I) :
    representableGeneric.{u} I ⟶
      (representableMap f).mapElements.obj (representableGeneric.{u} J) :=
  Functor.Elements.homMk f.op (by
    change (ULift.up (f ≫ 𝟙 I) : ULift.{u} (J ⟶ I)) = ⟨𝟙 J ≫ f⟩
    exact congrArg ULift.up ((Category.comp_id f).trans (Category.id_comp f).symm))

theorem family_map_heq {Γ : Context.{u} C} (A : Family Γ) {x y z : Γ.Elements}
    (f : x ⟶ y) (g : x ⟶ z) (e : y = z) (h : HEq f.hom g.hom) (v : A.obj x) :
    HEq (A.map f v) (A.map g v) := by
  cases e
  have hfg : f = g := Functor.Elements.hom_ext (eq_of_heq h)
  cases hfg
  rfl

theorem family_map_identity_heq {Γ : Context.{u} C} (A : Family Γ) {x y : Γ.Elements}
    (f : x ⟶ y) (e : x = y) (h : HEq f.hom (𝟙 x.obj)) (v : A.obj x) :
    HEq (A.map f v) v := by
  cases e
  have hfid : f = 𝟙 x := Functor.Elements.hom_ext (eq_of_heq h)
  cases hfid
  exact heq_of_eq (ConcreteCategory.congr_hom (A.map_id x) v)

@[simp] theorem raisedSub_id (Γ : Context.{u} C) : raisedSub (𝟙 Γ) = 𝟙 (raisedContext Γ) := rfl
@[simp] theorem raisedSub_comp {Γ Δ Θ : Context.{u} C} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    raisedSub (τ ≫ σ) = raisedSub τ ≫ raisedSub σ := rfl

/-- Primitive strictly functorial restriction of family data. The data may include
chosen operations; these laws concern restriction, not decoder recovery. -/
structure System (C : Type v) [Category.{w} C] where
  Data : Context.{u} C → Type (max v (u+1) (w+1))
  restrict : {Γ Δ : Context.{u} C} → Data Γ → (Δ ⟶ Γ) → Data Δ
  restrict_id : ∀ {Γ} (A : Data Γ), restrict A (𝟙 Γ) = A
  restrict_comp : ∀ {Γ Δ Θ} (A : Data Γ) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ),
    restrict (restrict A σ) τ = restrict A (τ ≫ σ)

namespace System
variable (S : System.{u} C)
def codes : Context.{max v (u+1) (w+1)} C where
  obj I := S.Data (representable I.unop)
  map f := TypeCat.ofHom (fun A => S.restrict A (representableMap f.unop))
  map_id I := by
    apply ConcreteCategory.hom_ext
    intro A
    have e : representableMap (𝟙 I.unop) = 𝟙 (representable.{u} I.unop) := by
      ext J x
      exact congrArg ULift.up (Category.comp_id x.down)
    exact (congrArg (S.restrict A) e).trans (S.restrict_id A)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro A
    have e : representableMap (g.unop ≫ f.unop) =
        representableMap g.unop ≫ representableMap f.unop := by
      ext K x
      exact congrArg ULift.up (Category.assoc x.down g.unop f.unop).symm
    exact (congrArg (S.restrict A) e).trans (S.restrict_comp A _ _).symm

def code {Γ : Context.{u} C} (A : S.Data Γ) : raisedContext Γ ⟶ S.codes where
  app I := TypeCat.ofHom (fun x => S.restrict A (represented (Γ.elementsMk I x.down)))
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    let g : Γ.elementsMk I x.down ⟶ Γ.elementsMk J (Γ.map f x.down) :=
      Functor.Elements.homMk f rfl
    exact ((S.restrict_comp A _ _).trans
      (congrArg (S.restrict A) (represented_restrict g))).symm

theorem code_reindex {Γ Δ : Context.{u} C} (A : S.Data Γ) (σ : Δ ⟶ Γ) :
    S.code (S.restrict A σ) = raisedSub σ ≫ S.code A := by
  ext I x
  exact (S.restrict_comp A σ _).trans
    (congrArg (S.restrict A) (represented_naturality σ (Δ.elementsMk I x.down))).symm

theorem code_reindex_comp {Γ Δ Θ : Context.{u} C} (A : S.Data Γ)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    S.code (S.restrict (S.restrict A σ) τ) = raisedSub τ ≫ raisedSub σ ≫ S.code A := by
  rw [S.code_reindex, S.code_reindex]

/-- Pull back an existing small-fiber decoder; constructing that decoder remains
a responsibility of the supplied model. -/
def decode (U : S.codes.Elements ⥤ Type (max u w)) {Γ : Context.{u} C}
    (a : raisedContext Γ ⟶ S.codes) : Family Γ :=
  raisedElements Γ ⋙ a.mapElements ⋙ U

theorem decode_reindex (U : S.codes.Elements ⥤ Type (max u w)) {Γ Δ : Context.{u} C}
    (a : raisedContext Γ ⟶ S.codes) (σ : Δ ⟶ Γ) :
    S.decode U (raisedSub σ ≫ a) = σ.mapElements ⋙ S.decode U a := rfl
end System

/-- The primitive object and arrow calculation of a decoder. These are local
formulas, not a natural comparison or a selected-operation preservation field. -/
structure Evaluation {Γ : Context.{u} C} (A D : Family Γ) : Prop where
  obj : ∀ x, D.obj x = A.obj ((represented x).mapElements.obj (representableGeneric x.obj.unop))
  map : ∀ {x y} (f : x ⟶ y) (a : D.obj x),
    HEq (D.map f a)
      (A.map ((represented x).mapElements.map (representableGenericHom f.hom.unop)) (cast (obj x) a))

namespace Evaluation
variable {Γ : Context.{u} C} {A D : Family Γ} (E : Evaluation A D)
def component (x : Γ.Elements) : D.obj x ≅ A.obj x :=
  (Equiv.cast (E.obj x)).toIso ≪≫ A.mapIso (eqToIso (represented_generic_source x))

theorem component_heq (x : Γ.Elements) (a : D.obj x) : HEq ((E.component x).hom a) a := by
  exact (family_map_identity_heq A (eqToHom (represented_generic_source x))
    (represented_generic_source x) (heq_of_eq (elements_eqToHom_hom _))
    (cast (E.obj x) a)).trans (cast_heq _ _)

def iso : D ≅ A := NatIso.ofComponents E.component (by
  intro x y f
  apply ConcreteCategory.hom_ext
  intro a
  have ey := represented_generic_source y
  have targetRel : (represented x).mapElements.obj
      ((representableMap f.hom.unop).mapElements.obj (representableGeneric.{u} y.obj.unop)) = y :=
    (congrArg (fun σ => σ.mapElements.obj (representableGeneric.{u} y.obj.unop))
      (represented_restrict f)).trans ey
  have hm := family_map_heq A
    (eqToHom (represented_generic_source x) ≫ f)
    ((represented x).mapElements.map (representableGenericHom f.hom.unop)) targetRel.symm
    (heq_of_eq (by
      change (eqToHom (represented_generic_source x) : _ ⟶ x).hom ≫ f.hom = f.hom
      rw [elements_eqToHom_hom]
      exact Category.id_comp f.hom)) (cast (E.obj x) a)
  have hc := ConcreteCategory.congr_hom
    (A.map_comp (eqToHom (represented_generic_source x)) f) (cast (E.obj x) a)
  exact eq_of_heq ((E.component_heq y (D.map f a)).trans
    ((E.map f a).trans (hm.symm.trans (heq_of_eq hc)))))
end Evaluation
end SquareKit.RepresentableClassification
