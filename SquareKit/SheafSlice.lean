import SquareKit.ElementSheaf
import SquareKit.SheafFamily

/-! Experimental presentation of the slice over an arbitrary sheaf by its site
of elements. Objects and arrows of the base may have independent universes;
sections stay in `Type w`, and element-site objects lie in `Type (max u w)`. -/
namespace SquareKit.SheafSlice
open CategoryTheory Opposite ElementSite ElementFamilies ElementSheaf
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (Γ : Sheaf J (Type w))

abbrev ElementSheaves := Sheaf (topology Γ.obj J) (Type w)

/-- Forget only the sheaf certificates, retaining the display map. -/
def underlying (p : Over Γ) : Over Γ.obj := Over.mk p.hom.hom

def forward : Over Γ ⥤ ElementSheaves Γ where
  obj p := ⟨presheaf Γ.obj (fibers Γ.obj (underlying Γ p)),
    (isSheaf_iff_isSheaf_of_type _ _).2 (fibers_isSheaf Γ.obj
      ((isSheaf_iff_isSheaf_of_type _ _).1 Γ.property) (underlying Γ p)
      ((isSheaf_iff_isSheaf_of_type _ _).1 p.left.property))⟩
  map k := ⟨Functor.whiskerLeft (opOpEquivalence Γ.obj.Elements).functor
    (fiberMap Γ.obj (Over.homMk k.left.hom (congrArg (fun h => h.hom) (Over.w k))))⟩

/-- Assemble a sheaf of fibers as its dependent total space over Γ. -/
def totalSheaf (Q : ElementSheaves Γ) : Sheaf J (Type w) :=
  ⟨total Γ.obj (family Γ.obj Q.obj), (isSheaf_iff_isSheaf_of_type _ _).2
    (total_isSheaf Γ.obj ((isSheaf_iff_isSheaf_of_type _ _).1 Γ.property) Q.obj
      ((isSheaf_iff_isSheaf_of_type _ _).1 Q.property))⟩

def backward : ElementSheaves Γ ⥤ Over Γ where
  obj Q := Over.mk (show totalSheaf Γ Q ⟶ Γ from ⟨display Γ.obj (family Γ.obj Q.obj)⟩)
  map k := Over.homMk ⟨totalNat Γ.obj
    (Functor.whiskerLeft (opOpEquivalence Γ.obj.Elements).inverse k.hom)⟩ rfl

/-- The reconstructed total sheaf is the original display, over Γ. -/
def reconstruction (p : Over Γ) : (forward Γ ⋙ backward Γ).obj p ≅ p :=
  Over.isoMk (ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U => (reconstructionEquiv Γ.obj (underlying Γ p) U).toIso)
      (by intro U V f; rfl))) (by ext U z; exact z.2.property)

def unitIso : 𝟭 (Over Γ) ≅ forward Γ ⋙ backward Γ :=
  (NatIso.ofComponents (reconstruction Γ) (by intro p q k; rfl)).symm

def recovery (Q : ElementSheaves Γ) : (backward Γ ⋙ forward Γ).obj Q ≅ Q :=
  ObjectProperty.isoMk _
    (Functor.isoWhiskerLeft (opOpEquivalence Γ.obj.Elements).functor
      (fiberTotalIso Γ.obj (family Γ.obj Q.obj)))

def counitIso : backward Γ ⋙ forward Γ ≅ 𝟭 (ElementSheaves Γ) :=
  NatIso.ofComponents (recovery Γ) (by
    intro Q R k
    ext X z
    exact (NatTrans.naturality_apply k.hom
      (vertical Γ.obj z.property).op.op z.val.2).symm)

/-- An actual categorical equivalence; Mathlib's constructor supplies the
adjoint triangle law from the two natural reconstruction isomorphisms. -/
def equivalence : Over Γ ≌ ElementSheaves Γ :=
  CategoryTheory.Equivalence.mk (forward Γ) (backward Γ) (unitIso Γ) (counitIso Γ)

/-- The forward equivalence computes actual section-map fibers of any ordinary
family display, including displays built by `Family.reindex`. -/
def fiberEquiv {A : Sheaf J (Type w)} (p : A ⟶ Γ) (U : C) (x : Γ.obj.obj (op U)) :
    ((equivalence Γ).functor.obj (Over.mk p)).obj.obj (op (point Γ.obj U x)) ≃
      {a : A.obj.obj (op U) // p.hom.app (op U) a = x} := Equiv.refl _

/-- Restricting in the element site restricts the actual ordinary section. -/
theorem fiber_restrict {A : Sheaf J (Type w)} (p : A ⟶ Γ) {U V : C}
    (f : V ⟶ U) (x : Γ.obj.obj (op U))
    (a : ((forward Γ).obj (Over.mk p)).obj.obj (op (point Γ.obj U x))) :
    (fiberEquiv Γ p V (Γ.obj.map f.op x)
      (((forward Γ).obj (Over.mk p)).obj.map (arrow Γ.obj f x).op a)).val =
        A.obj.map f.op (fiberEquiv Γ p U x a).val := rfl

/-- Total reconstruction retains the section as well as its fiber equation. -/
@[simp] theorem reconstruction_value (p : Over Γ) (U : Cᵒᵖ)
    (a : ((forward Γ ⋙ backward Γ).obj p).left.obj.obj U) :
    (reconstruction Γ p).hom.left.hom.app U a = a.2.val := rfl

/-- Reconstruction is an isomorphism over the original display. -/
theorem reconstruction_display (p : Over Γ) :
    (reconstruction Γ p).hom.left ≫ p.hom = ((forward Γ ⋙ backward Γ).obj p).hom :=
  Over.w (reconstruction Γ p).hom

/-- Reconstruction commutes with every ordinary restriction. -/
theorem reconstruction_restrict (p : Over Γ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (a : ((forward Γ ⋙ backward Γ).obj p).left.obj.obj U) :
    (reconstruction Γ p).hom.left.hom.app V
      (((forward Γ ⋙ backward Γ).obj p).left.obj.map f a) =
      p.left.obj.map f ((reconstruction Γ p).hom.left.hom.app U a) :=
  NatTrans.naturality_apply (reconstruction Γ p).hom.left.hom f a

/-- The total-space display forgets exactly the dependent fiber value. -/
@[simp] theorem total_projection (Q : ElementSheaves Γ) (U : Cᵒᵖ)
    (a : ((backward Γ).obj Q).left.obj.obj U) :
    ((backward Γ).obj Q).hom.hom.app U a = a.1 := rfl

/-- Restriction of a total section restricts its base and transports its value
along the corresponding element arrow. -/
theorem total_restriction (Q : ElementSheaves Γ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (a : ((backward Γ).obj Q).left.obj.obj U) :
    ((backward Γ).obj Q).left.obj.map f a =
      ⟨Γ.obj.map f a.1, Q.obj.map (along Γ.obj f a.1).op.op a.2⟩ := rfl

@[simp] theorem reconstruction_inverse (p : Over Γ) (U : Cᵒᵖ) (a : p.left.obj.obj U) :
    (reconstruction Γ p).inv.left.hom.app U a = ⟨p.hom.hom.app U a, ⟨a, rfl⟩⟩ := rfl

/-- The equivalence's actual (adjointified) unit and counit obey the triangle. -/
theorem triangle (p : Over Γ) :
    (equivalence Γ).functor.map ((equivalence Γ).unitIso.hom.app p) ≫
      (equivalence Γ).counitIso.hom.app ((equivalence Γ).functor.obj p) =
      𝟙 ((equivalence Γ).functor.obj p) :=
  (equivalence Γ).functor_unitIso_comp p

end SquareKit.SheafSlice
