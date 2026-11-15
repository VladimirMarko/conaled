import SquareKit.Internal.Cubical.SmallFamilyCodes

/-! Evaluation of a code at the identity cube. The decoding fibers remain in
Type u although their code context lives in Type (u+1). -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def representableGenericHom {I J : Cube} (f : J ⟶ I) :
    representableGeneric.{u} I ⟶
      (representableMap f).mapElements.obj (representableGeneric.{u} J) :=
  Functor.Elements.homMk f.op (by
    change (ULift.up (f ≫ 𝟙 I) : ULift.{u} (J ⟶ I)) = ⟨𝟙 J ≫ f⟩
    exact congrArg ULift.up ((Category.comp_id f).trans (Category.id_comp f).symm))

def codeFiber {I : Cube} (A : SmallFamilyCode.{u} I) : Type u :=
  A.family.obj (representableGeneric I)

def decodeMap {x y : smallFamilyCodes.{u}.Elements} (f : x ⟶ y) : codeFiber x.val → codeFiber y.val :=
  fun a => cast (congrArg (fun A : SmallFamilyCode.{u} y.obj.unop => codeFiber A) f.map_val)
    (x.val.family.map (representableGenericHom f.hom.unop) a)

theorem decodeMap_id (x : smallFamilyCodes.{u}.Elements) (a : codeFiber x.val) :
    decodeMap (𝟙 x) a = a := by
  unfold decodeMap
  apply eq_of_heq
  apply (cast_heq _ _).trans
  have e : (representableMap (𝟙 x.obj.unop)).mapElements.obj
      (representableGeneric.{u} x.obj.unop) = representableGeneric x.obj.unop := by
    exact Functor.Elements.ext _ _ rfl
      ((ConcreteCategory.congr_hom ((representable.{u} x.obj.unop).map_id x.obj) _).trans
        (congrArg ULift.up (Category.id_comp (𝟙 x.obj.unop))))
  exact family_map_identity_heq x.val.family (representableGenericHom (𝟙 x.obj.unop))
    e.symm HEq.rfl a

theorem decodeMap_comp {x y z : smallFamilyCodes.{u}.Elements} (f : x ⟶ y) (g : y ⟶ z)
    (a : codeFiber x.val) : decodeMap (f ≫ g) a = decodeMap g (decodeMap f a) := by
  rcases x with @⟨I,A⟩
  rcases y with @⟨J,B⟩
  rcases z with @⟨K,C⟩
  rcases f with ⟨f,hf⟩
  rcases g with ⟨g,hg⟩
  change I ⟶ J at f
  change J ⟶ K at g
  change SmallFamilyCode.{u} I.unop at A
  change SmallFamilyCode.{u} J.unop at B
  change SmallFamilyCode.{u} K.unop at C
  change A.reindex (representableMap f.unop) = B at hf
  subst B
  change (A.reindex (representableMap f.unop)).reindex (representableMap g.unop) = C at hg
  subst C
  unfold decodeMap
  change cast _ (A.family.map (representableGenericHom (g.unop ≫ f.unop)) a) =
    A.family.map ((representableMap f.unop).mapElements.map (representableGenericHom g.unop))
      (A.family.map (representableGenericHom f.unop) a)
  have e : (representableMap (g.unop ≫ f.unop)).mapElements.obj (representableGeneric.{u} K.unop) =
      (representableMap f.unop).mapElements.obj
        ((representableMap g.unop).mapElements.obj (representableGeneric.{u} K.unop)) := by
    exact Functor.Elements.ext _ _ rfl
      ((ConcreteCategory.congr_hom ((representable.{u} I.unop).map_id K) _).trans
        (congrArg ULift.up (Category.assoc (𝟙 K.unop) g.unop f.unop).symm))
  have hm := family_map_heq A.family (representableGenericHom (g.unop ≫ f.unop))
    (representableGenericHom f.unop ≫
      (representableMap f.unop).mapElements.map (representableGenericHom g.unop)) e HEq.rfl a
  exact eq_of_heq ((cast_heq _ _).trans (hm.trans
    (heq_of_eq (ConcreteCategory.congr_hom (A.family.map_comp _ _) a))))

/-- The universal small decoding family uses small fibers over the larger code
context. It is an ordinary functor, without changing the native Family API. -/
def universalDecode : smallFamilyCodes.{u}.Elements ⥤ Type u where
  obj x := codeFiber x.val
  map f := TypeCat.ofHom (decodeMap f)
  map_id x := by
    apply ConcreteCategory.hom_ext
    exact decodeMap_id x
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    exact decodeMap_comp f g

end SquareKit.Cubical.Presheaf
