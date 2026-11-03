import SquareKit.SheafRelation

/-! Sectionwise indexed products, compared to the actual categorical product.
This extends the existing explicit binary-product interface to arbitrary indices. -/
noncomputable section
namespace SquareKit.SheafIndexedProduct
open CategoryTheory Opposite Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {I : Type w}

def data (A : I → Sheaf J (Type w)) : Cᵒᵖ ⥤ Type w where
  obj U := ∀ i, (A i).obj.obj U
  map f := ↾fun s i => (A i).obj.map f (s i)
  map_id U := by ext s i; simp
  map_comp f g := by ext s i; simp

theorem data_isSheaf (A : I → Sheaf J (Type w)) : Presieve.IsSheaf J (data A) := by
  intro U R hR x hx
  let xi (i : I) : Presieve.FamilyOfElements (A i).obj R.arrows := fun {_} f hf => x f hf i
  have hi (i : I) : (xi i).Compatible := by
    intro V W Z f g k l hk hl he
    exact congrFun (hx f g hk hl he) i
  have gl (i : I) := ((isSheaf_iff_isSheaf_of_type _ _).mp (A i).property) R hR (xi i) (hi i)
  choose a ha hua using gl
  refine ⟨a, ?_, ?_⟩
  · intro V f hf; funext i; exact ha i f hf
  · intro b hb; funext i
    exact hua i (b i) (fun {_} f hf => congrFun (hb f hf) i)

abbrev obj (A : I → Sheaf J (Type w)) : Sheaf J (Type w) :=
  ⟨data A, (isSheaf_iff_isSheaf_of_type _ _).mpr (data_isSheaf A)⟩

def proj (A : I → Sheaf J (Type w)) (i : I) : obj A ⟶ A i :=
  ⟨{ app _ := ↾fun s => s i }⟩

def lift {A : I → Sheaf J (Type w)} {B : Sheaf J (Type w)} (f : ∀ i, B ⟶ A i) :
    B ⟶ obj A :=
  ⟨{ app U := ↾fun b i => (f i).hom.app U b
     naturality := by
       intro U V k; ext b; funext i
       exact NatTrans.naturality_apply (f i).hom k b }⟩

def iso (A : I → Sheaf J (Type w)) : obj A ≅ ∏ᶜ A where
  hom := Pi.lift (proj A)
  inv := lift (Pi.π A)
  hom_inv_id := by
    ext U s; funext i
    exact congrArg (fun f : obj A ⟶ A i => f.hom.app U s) (Pi.lift_comp_π (proj A) i)
  inv_hom_id := by
    apply Pi.hom_ext
    intro i
    simp only [Category.assoc, Pi.lift_comp_π, Category.id_comp]
    rfl

theorem iso_projection (A : I → Sheaf J (Type w)) (i : I) :
    (iso A).hom ≫ Pi.π A i = proj A i := Pi.lift_comp_π _ _

end SquareKit.SheafIndexedProduct
