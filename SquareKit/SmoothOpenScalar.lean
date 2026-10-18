import SquareKit.SmoothOpenSheaf
import SquareKit.SmoothGeometricScalar

/-! Experimental scalar finite powers and smooth operations for arbitrary covers.
The underlying coordinate presheaves and their representations are shared with
the finite-principal site. Forgetting stronger sheafness changes no sections. -/
noncomputable section
namespace SquareKit.SmoothOpenSite
open CategoryTheory Opposite SmoothAlgebra SmoothPresentationSite

def scalarPower (n : ℕ) : Sheaf topology Type :=
  ⟨powerData n,(isSheaf_iff_isSheaf_of_type _ _).mpr
    (Presieve.isSheaf_iso topology (representablePowerIso n) (yoneda_isSheaf _))⟩

def operation {n : ℕ} (f : Operation n) : scalarPower n ⟶ scalar :=
  ⟨{app X := ↾fun z => act (A := Carrier X.unop.unop) f z
    naturality _ _ h := by ext z; exact ((smoothMap h.unop.unop).map_act f z).symm}⟩

def projection (n : ℕ) (i : Fin n) : scalarPower n ⟶ scalar :=
  ⟨{app _ := ↾fun z => z i}⟩

def tuple {n : ℕ} {F : Sheaf topology Type} (h : Fin n → (F ⟶ scalar)) : F ⟶ scalarPower n :=
  ⟨{app X := ↾fun x i => (h i).hom.app X x
    naturality X Y f := by
      ext x
      funext i
      exact congrFun (congrArg (fun k => k.hom) ((h i).hom.naturality f)) x}⟩

theorem tuple_projection {n : ℕ} {F : Sheaf topology Type} (h : Fin n → (F ⟶ scalar)) (i : Fin n) :
    tuple h ≫ projection n i=h i := rfl

theorem tuple_unique {n : ℕ} {F : Sheaf topology Type} (h : Fin n → (F ⟶ scalar))
    (g : F ⟶ scalarPower n) (hg : ∀ i, g ≫ projection n i=h i) : g=tuple h := by
  ext X x
  funext i
  exact congrArg (fun f : F ⟶ scalar => f.hom.app X x) (hg i)

def powerIsLimit (n : ℕ) : Limits.IsLimit (Limits.Fan.mk (scalarPower n) (projection n)) :=
  Limits.Fan.IsLimit.mk _ (fun c => tuple c.proj) (fun c i => tuple_projection c.proj i)
    (fun c g hg => tuple_unique c.proj g hg)

def toFinite : Sheaf topology Type ⥤ Sheaf SmoothPresentationSite.topology Type where
  obj F := ⟨F.obj,(isSheaf_iff_isSheaf_of_type _ _).mpr
    (Presieve.isSheaf_of_le _ finite_topology_le ((isSheaf_iff_isSheaf_of_type _ _).mp F.property))⟩
  map f := ⟨f.hom⟩

def scalarComparison : toFinite.obj scalar ≅ SmoothPresentationSite.scalar := Iso.refl _
def powerComparison (n : ℕ) : toFinite.obj (scalarPower n) ≅ SmoothPresentationSite.scalarPower n := Iso.refl _

theorem operation_comparison {n : ℕ} (f : Operation n) :
    (toFinite.map (operation f)).hom = (SmoothPresentationSite.operation f).hom := rfl

end SquareKit.SmoothOpenSite
