import SquareKit.Internal.RepresentableEvaluation

/-! Classification of ordinary presheaf families, with no selected filling data. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.RepresentableClassification.PresheafFamily
open CategoryTheory
universe u v w
variable {C : Type v} [Category.{w} C]

def system : System.{u} C where
  Data := Family
  restrict A σ := σ.mapElements ⋙ A
  restrict_id _ := rfl
  restrict_comp _ _ _ := rfl

abbrev Code (I : C) := Family (representable.{u} I)

def CodeFiber {I : C} (A : Code.{u} I) : Type (max u w) :=
  A.obj (representableGeneric I)

def decodeMap {x y : (system.{u} (C := C)).codes.Elements} (f : x ⟶ y) : CodeFiber x.val → CodeFiber y.val :=
  fun a => cast (congrArg (fun A : Code.{u} y.obj.unop => CodeFiber A) f.map_val)
    (x.val.map (representableGenericHom f.hom.unop) a)

theorem decodeMap_id (x : (system.{u} (C := C)).codes.Elements) (a : CodeFiber x.val) :
    decodeMap (𝟙 x) a = a := by
  unfold decodeMap
  apply eq_of_heq
  apply (cast_heq _ _).trans
  have e : (representableMap (𝟙 x.obj.unop)).mapElements.obj
      (representableGeneric.{u} x.obj.unop) = representableGeneric x.obj.unop := by
    exact Functor.Elements.ext _ _ rfl
      ((ConcreteCategory.congr_hom ((representable.{u} x.obj.unop).map_id x.obj) _).trans
        (congrArg ULift.up (Category.id_comp (𝟙 x.obj.unop))))
  exact family_map_identity_heq x.val (representableGenericHom (𝟙 x.obj.unop))
    e.symm HEq.rfl a

theorem decodeMap_comp {x y z : (system.{u} (C := C)).codes.Elements} (f : x ⟶ y) (g : y ⟶ z)
    (a : CodeFiber x.val) : decodeMap (f ≫ g) a = decodeMap g (decodeMap f a) := by
  rcases x with @⟨I, A⟩
  rcases y with @⟨J, B⟩
  rcases z with @⟨K, C⟩
  rcases f with ⟨f, hf⟩
  rcases g with ⟨g, hg⟩
  change I ⟶ J at f
  change J ⟶ K at g
  change Code.{u} I.unop at A
  change Code.{u} J.unop at B
  change Code.{u} K.unop at C
  change (representableMap f.unop).mapElements ⋙ A = B at hf
  subst B
  change (representableMap g.unop).mapElements ⋙ (representableMap f.unop).mapElements ⋙ A = C at hg
  subst C
  unfold decodeMap
  change cast _ (A.map (representableGenericHom (g.unop ≫ f.unop)) a) =
    A.map ((representableMap f.unop).mapElements.map (representableGenericHom g.unop))
      (A.map (representableGenericHom f.unop) a)
  have e : (representableMap (g.unop ≫ f.unop)).mapElements.obj (representableGeneric.{u} K.unop) =
      (representableMap f.unop).mapElements.obj
        ((representableMap g.unop).mapElements.obj (representableGeneric.{u} K.unop)) := by
    exact Functor.Elements.ext _ _ rfl
      ((ConcreteCategory.congr_hom ((representable.{u} I.unop).map_id K) _).trans
        (congrArg ULift.up (Category.assoc (𝟙 K.unop) g.unop f.unop).symm))
  have hm := family_map_heq A (representableGenericHom (g.unop ≫ f.unop))
    (representableGenericHom f.unop ≫
      (representableMap f.unop).mapElements.map (representableGenericHom g.unop)) e HEq.rfl a
  exact eq_of_heq ((cast_heq _ _).trans (hm.trans
    (heq_of_eq (ConcreteCategory.congr_hom (A.map_comp _ _) a))))

/-- Universal decoding evaluates each represented family at its generic element.
The fibers stay in the original universe over the larger code context. -/
def universalDecode : (system.{u} (C := C)).codes.Elements ⥤ Type (max u w) where
  obj x := CodeFiber x.val
  map f := TypeCat.ofHom (decodeMap f)
  map_id x := by
    apply ConcreteCategory.hom_ext
    exact decodeMap_id x
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    exact decodeMap_comp f g

/-- Ordinary families satisfy the local evaluation formulas. -/
theorem evaluation {Γ : Context.{u} C} (A : Family Γ) :
    Evaluation A (system.decode universalDecode (system.code A)) :=
  ⟨fun _ => rfl, fun _ _ => cast_heq _ _⟩

def recovery {Γ : Context.{u} C} (A : Family Γ) :
    system.decode universalDecode (system.code A) ≅ A := (evaluation A).iso

end SquareKit.RepresentableClassification.PresheafFamily
