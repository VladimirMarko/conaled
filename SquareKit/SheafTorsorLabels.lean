import SquareKit.SheafTorsor

/-! Sheaf-valued labels for arrows of the regular left torsor.
The label acts by right multiplication, so composition multiplies labels in order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafTorsor
open CategoryTheory Opposite
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{w}} {X Y : Sheaf J (Type w)}

def labelMul (g h : X ⟶ groupSheaf G) : X ⟶ groupSheaf G := ⟨{
  app U := ↾fun x => (show G.obj.obj U from g.hom.app U x) *
    (show G.obj.obj U from h.hom.app U x)
  naturality {U V} f := by
    apply ConcreteCategory.hom_ext
    intro x
    change _ = G.obj.map f (_ * _)
    rw [(G.obj.map f).hom.map_mul]
    exact congrArg₂ (fun a b : G.obj.obj V => a * b)
      (NatTrans.naturality_apply g.hom f x) (NatTrans.naturality_apply h.hom f x) }⟩

def labelOne (X : Sheaf J (Type w)) : X ⟶ groupSheaf G := ⟨{
  app U := ↾fun _ => (1 : G.obj.obj U)
  naturality {U V} f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact ((G.obj.map f).hom.map_one).symm }⟩

def labelInv (g : X ⟶ groupSheaf G) : X ⟶ groupSheaf G := ⟨{
  app U := ↾fun x => ((fun a : G.obj.obj U => a⁻¹) (g.hom.app U x))
  naturality {U V} f := by
    apply ConcreteCategory.hom_ext
    intro x
    change _ = G.obj.map f (_⁻¹)
    rw [(G.obj.map f).hom.map_inv]
    exact congrArg Inv.inv (NatTrans.naturality_apply g.hom f x) }⟩

theorem labelMul_precomp (f : Y ⟶ X) (g h : X ⟶ groupSheaf G) :
    f ≫ labelMul g h = labelMul (f ≫ g) (f ≫ h) := rfl
theorem labelOne_precomp (f : Y ⟶ X) :
    f ≫ labelOne (G := G) X = labelOne Y := rfl
theorem labelInv_precomp (f : Y ⟶ X) (g : X ⟶ groupSheaf G) :
    f ≫ labelInv g = labelInv (f ≫ g) := rfl

theorem labelMul_assoc (g h k : X ⟶ groupSheaf G) :
    labelMul (labelMul g h) k = labelMul g (labelMul h k) := by
  ext U x
  exact mul_assoc (show G.obj.obj U from g.hom.app U x) (h.hom.app U x) (k.hom.app U x)
theorem labelOne_mul (g : X ⟶ groupSheaf G) : labelMul (labelOne X) g = g := by
  ext U x
  exact one_mul (show G.obj.obj U from g.hom.app U x)
theorem labelMul_one (g : X ⟶ groupSheaf G) : labelMul g (labelOne X) = g := by
  ext U x
  exact mul_one (show G.obj.obj U from g.hom.app U x)
theorem labelInv_mul (g : X ⟶ groupSheaf G) : labelMul (labelInv g) g = labelOne X := by
  ext U x
  exact inv_mul_cancel (show G.obj.obj U from g.hom.app U x)
theorem labelMul_inv (g : X ⟶ groupSheaf G) : labelMul g (labelInv g) = labelOne X := by
  ext U x
  exact mul_inv_cancel (show G.obj.obj U from g.hom.app U x)
theorem labelInv_inv (g : X ⟶ groupSheaf G) : labelInv (labelInv g) = g := by
  ext U x
  exact inv_inv (show G.obj.obj U from g.hom.app U x)
theorem labelInv_mul_rev (g h : X ⟶ groupSheaf G) :
    labelInv (labelMul g h) = labelMul (labelInv h) (labelInv g) := by
  ext U x
  exact mul_inv_rev (show G.obj.obj U from g.hom.app U x) (h.hom.app U x)

/-- Evaluate an equivariant regular-torsor arrow at the identity section. -/
def regularArrowLabel (f : Arrow (trivial G X) (trivial G X)) :
    X ⟶ groupSheaf G := ⟨{
  app U := ↾fun x => f.iso.hom.app (X.obj.elementsMk U x) (1 : G.obj.obj U)
  naturality {U V} k := by
    apply ConcreteCategory.hom_ext
    intro x
    have h := NatTrans.naturality_apply f.iso.hom
      (ElementFamilies.along X.obj k x) (1 : G.obj.obj U)
    change f.iso.hom.app (X.obj.elementsMk V (X.obj.map k x)) (G.obj.map k 1) = _ at h
    rw [(G.obj.map k).hom.map_one] at h
    exact h }⟩

theorem regularArrowLabel_recovers (f : Arrow (trivial G X) (trivial G X)) :
    regularArrow (regularArrowLabel f) = f := by
  apply Arrow.ext
  ext x p
  change G.obj.obj x.obj at p
  have h := f.equivariant x p (1 : G.obj.obj x.obj)
  change f.iso.hom.app x (p * 1) =
    p * (show G.obj.obj x.obj from f.iso.hom.app x (1 : G.obj.obj x.obj)) at h
  rw [mul_one] at h
  exact h.symm

theorem regularArrowLabel_regularArrow (g : X ⟶ groupSheaf G) :
    regularArrowLabel (regularArrow g) = g := by
  ext U x
  exact one_mul (show G.obj.obj U from g.hom.app U x)

/-- Every regular equivariant arrow has exactly one sheaf-valued label. -/
def regularArrowEquiv : Arrow (trivial G X) (trivial G X) ≃ (X ⟶ groupSheaf G) where
  toFun := regularArrowLabel
  invFun := regularArrow
  left_inv := regularArrowLabel_recovers
  right_inv := regularArrowLabel_regularArrow

theorem regularArrow_ident : regularArrow (labelOne (G := G) X) = 𝟙 (trivial G X) := by
  apply Arrow.ext
  ext x p
  exact mul_one (show G.obj.obj x.obj from p)

theorem regularArrow_comp (g h : X ⟶ groupSheaf G) :
    (regularArrow g).comp (regularArrow h) =
      regularArrow (labelMul g h) := by
  apply Arrow.ext
  ext x p
  exact mul_assoc (show G.obj.obj x.obj from p) _ _

theorem regularArrow_inverse (g : X ⟶ groupSheaf G) :
    (regularArrow g).inverse = regularArrow (labelInv g) := by
  apply Arrow.ext
  rfl

theorem regularArrowLabel_ident :
    regularArrowLabel (𝟙 (trivial G X)) = labelOne X := rfl
theorem regularArrowLabel_comp (f g : Arrow (trivial G X) (trivial G X)) :
    regularArrowLabel (f.comp g) =
      labelMul (regularArrowLabel f) (regularArrowLabel g) := by
  apply regularArrow_injective
  rw [regularArrowLabel_recovers, ← regularArrow_comp,
    regularArrowLabel_recovers, regularArrowLabel_recovers]
theorem regularArrowLabel_inverse (f : Arrow (trivial G X) (trivial G X)) :
    regularArrowLabel f.inverse = labelInv (regularArrowLabel f) := by
  apply regularArrow_injective
  rw [regularArrowLabel_recovers, ← regularArrow_inverse, regularArrowLabel_recovers]
theorem regularArrowLabel_reindex (f : Arrow (trivial G X) (trivial G X)) (a : Y ⟶ X) :
    regularArrowLabel (f.reindex a) = a ≫ regularArrowLabel f := rfl

/-- The unique sheaf-valued displacement carrying the first section to the second. -/
def sectionDifference (P : Torsor G X) (s t : SplitSheaf.Tm P.family) : X ⟶ groupSheaf G :=
  regularArrowLabel ((ofSection P t).comp (ofSection P s).inverse)
theorem sectionDifference_act (P : Torsor G X) (s t : SplitSheaf.Tm P.family)
    (x : X.obj.Elements) :
    P.act x ((sectionDifference P s t).hom.app x.obj x.val) (s.val x) = t.val x := by
  change (fiberEquiv P x (s.val x))
    ((fiberEquiv P x (s.val x)).symm (P.act x 1 (t.val x))) = _
  rw [Equiv.apply_symm_apply, P.one_act]

end SquareKit.SheafTorsor
