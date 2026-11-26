import Mathlib.CategoryTheory.Comma.Over.Pullback
import SquareKit.SplitSheaf
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-! Sheaf displays with every natural map of their fibers. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.SplitSheaf
open CategoryTheory Opposite
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {X Y Z : Sheaf J (Type w)}

instance : Category (Ty X) where
  Hom A B := A.family ⟶ B.family
  id A := 𝟙 A.family
  comp f g := f ≫ g

/-- Restriction acts on arbitrary fiber maps, with strict identity and composition. -/
def restriction (f : Y ⟶ X) : Ty X ⥤ Ty Y where
  obj A := tySub A f
  map h := Functor.whiskerLeft f.hom.mapElements h

abbrev categoryFunctor : (Sheaf J (Type w))ᵒᵖ ⥤ Cat where
  obj X := Cat.of (Ty X.unop)
  map f := Cat.Hom.ofFunctor (restriction f.unop)
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev pseudofunctor := (categoryFunctor.{u,v,w} (J := J)).toPseudofunctor'

/-- An isomorphism of fibers is an isomorphism of displays. -/
def isoMk {A B : Ty X} (e : A.family ≅ B.family) : A ≅ B where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

/-- Total space retains the base section and every fiber map. -/
def totalMap {A B : Ty X} (h : A ⟶ B) : extension A ⟶ extension B :=
  ⟨ElementFamilies.totalNat X.obj h⟩

def toOver : Ty X ⥤ Over X where
  obj A := Over.mk (p A)
  map h := Over.homMk (totalMap h) rfl

def fromOver : Over X ⥤ Ty X where
  obj A := ofDisplay A.hom
  map h := ElementFamilies.fiberMap X.obj (Over.homMk h.left.hom
    (congrArg (fun f => f.hom) (Over.w h)))

/-- Display recovery keeps the actual map to the context. -/
def overRecovery : fromOver (X := X) ⋙ toOver ≅ 𝟭 (Over X) :=
  NatIso.ofComponents (fun A => Over.isoMk (displayIso A.hom)
    (displayIso_projection A.hom)) (by intro A B h; rfl)

def familyRecoveryIso : toOver (X := X) ⋙ fromOver ≅ 𝟭 (Ty X) :=
  NatIso.ofComponents (fun A => isoMk (ElementFamilies.fiberTotalIso X.obj A.family))
    (by intro A B h; exact (ElementFamilies.counitIso X.obj).hom.naturality h)

/-- Split sheaf families and ordinary sheaf displays agree on all maps. -/
def overEquivalence : Ty X ≌ Over X :=
  CategoryTheory.Equivalence.mk toOver fromOver familyRecoveryIso.symm overRecovery

/-- An invertible total map over the context has an invertible fiber map. -/
theorem isIso_of_totalMap {A B : Ty X} (h : A ⟶ B) [IsIso (totalMap h)] : IsIso h := by
  have : IsIso ((Over.forget X).map ((toOver (X := X)).map h)) := inferInstanceAs (IsIso (totalMap h))
  have : IsIso ((toOver (X := X)).map h) := isIso_of_reflects_iso _ (Over.forget X)
  have : (toOver (X := X)).IsEquivalence :=
    inferInstanceAs (overEquivalence (X := X)).functor.IsEquivalence
  exact isIso_of_reflects_iso h toOver

set_option backward.isDefEq.respectTransparency false in
/-- The display comparison is natural in arbitrary fiber maps under substitution. -/
def displayReindex (f : Y ⟶ X) :
    restriction f ⋙ toOver ≅ toOver ⋙ Over.pullback f :=
  NatIso.ofComponents (fun A => Over.isoMk (substitutionIso A f) (substitution_display A f)) (by
    intro A B h
    apply Over.OverMorphism.ext
    apply Limits.pullback.hom_ext
    · change totalMap ((restriction f).map h) ≫ (substitutionIso B f).hom ≫
          Limits.pullback.fst (p B) f =
        (substitutionIso A f).hom ≫
          Limits.pullback.lift (Limits.pullback.fst (p A) f ≫ totalMap h)
            (Limits.pullback.snd (p A) f) _ ≫ Limits.pullback.fst (p B) f
      rw [Limits.pullback.lift_fst, substitution_value, ← Category.assoc, substitution_value]
      rfl
    · change totalMap ((restriction f).map h) ≫ (substitutionIso B f).hom ≫
          Limits.pullback.snd (p B) f =
        (substitutionIso A f).hom ≫
          Limits.pullback.lift (Limits.pullback.fst (p A) f ≫ totalMap h)
            (Limits.pullback.snd (p A) f) _ ≫ Limits.pullback.snd (p B) f
      rw [Limits.pullback.lift_snd, substitution_display, substitution_display]
      rfl)

end SquareKit.SplitSheaf

namespace SquareKit.SplitSheaf
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {X : Sheaf J (Type w)} {A B : Ty X}

/-- Recover a fiber map from an arbitrary map of total spaces over the base. -/
def mapOfTotal (f : extension A ⟶ extension B) (hf : f ≫ p B = p A) : A.family ⟶ B.family :=
  overEquivalence.functor.preimage (Over.homMk f hf)

theorem totalMap_mapOfTotal (f : extension A ⟶ extension B) (hf : f ≫ p B = p A) :
    totalMap (mapOfTotal f hf) = f :=
  congrArg (fun h => h.left) (overEquivalence.functor.map_preimage (Over.homMk f hf))

theorem totalMap_injective : Function.Injective (totalMap (A := A) (B := B)) := by
  intro f g h
  apply overEquivalence.functor.map_injective
  exact Over.OverMorphism.ext h

theorem totalMap_value {Y Z : Sheaf J (Type w)} (k : A.family ⟶ B.family)
    (h : extension B ⟶ Z) (u : extension A ⟶ Y) (v : Y ⟶ Z)
    (he : totalMap k ≫ h = u ≫ v) (x : X.obj.Elements) (p : A.family.obj x) :
    h.hom.app x.obj ⟨x.val, k.app x p⟩ =
      v.hom.app x.obj (u.hom.app x.obj ⟨x.val, p⟩) :=
  congrArg (fun q => q.hom.app x.obj ⟨x.val, p⟩) he

theorem totalMap_projection (k : A.family ⟶ B.family) : totalMap k ≫ p B = p A := rfl

theorem conjugate_value {Y Z : Sheaf J (Type w)} (e : extension A ≅ Y) (f : extension B ≅ Z)
    (k : A.family ⟶ B.family) (x : X.obj.Elements) (p : A.family.obj x) :
    (e.inv ≫ totalMap k ≫ f.hom).hom.app x.obj (e.hom.hom.app x.obj ⟨x.val,p⟩) =
      f.hom.hom.app x.obj ⟨x.val,k.app x p⟩ := by
  have h : e.hom ≫ e.inv ≫ totalMap k ≫ f.hom = totalMap k ≫ f.hom := by simp
  exact congrArg (fun q => q.hom.app x.obj ⟨x.val,p⟩) h

end SquareKit.SplitSheaf

namespace SquareKit.SplitSheaf
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {X : Sheaf J (Type w)} {A B D : Ty X}
@[simp] theorem totalMap_id : totalMap (𝟙 A.family) = 𝟙 (extension A) := rfl
@[simp] theorem totalMap_comp (f : A.family ⟶ B.family) (g : B.family ⟶ D.family) :
    totalMap (f ≫ g) = totalMap f ≫ totalMap g := rfl
end SquareKit.SplitSheaf
