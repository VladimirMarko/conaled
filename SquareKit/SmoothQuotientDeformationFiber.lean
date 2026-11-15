import SquareKit.SmoothQuotientDeformations
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! A deformation of an arbitrary quotient torsor determines the actual
infinitesimal quotient object and its boundary arrow. -/
noncomputable section
namespace SquareKit.SmoothQuotientDeformations
open CategoryTheory SheafActionQuotient SmoothOpenSite SheafRelation
set_option backward.isDefEq.respectTransparency false
variable {H : Type} [Group H] {M : Sheaf topology Type}
variable {a : Action (locallyConstantGroup H) M} {X : Sheaf topology Type}
local notation "D" => SmoothOpenSite.infinitesimal

/-- The homotopy fiber over any quotient object, with its boundary retained. -/
abbrev Fiber (P : Object a X) := StructuredArrow P (restriction (a := a) (parameterZero X))

def Deformation.arcObject {P : Object a X} (h : Deformation P) : Object a (product D X) where
  torsor := SheafTorsor.reindex P.torsor (snd D X)
  value y p := h.map.hom.app y.obj (y.val.1,⟨y.val.2,p⟩)
  natural {y z} f p := by
    have hn := NatTrans.naturality_apply h.map.hom f.hom (show (product D (SplitSheaf.Ext P.torsor.family)).obj.obj y.obj from (y.val.1,⟨y.val.2,p⟩))
    apply hn.symm.trans
    apply congrArg (h.map.hom.app z.obj)
    apply Prod.ext
    · change (D).obj.map f.hom y.val.1 = z.val.1
      exact congrArg Prod.fst f.map_val
    · apply ElementFamilies.total_ext X.obj (congrArg Prod.snd f.map_val)
      change P.torsor.family.family.map _ (P.torsor.family.family.map _ p) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      congr 2
  equivariant y g p := h.equivariant y.obj y.val.1 y.val.2 g p

def Deformation.boundary {P : Object a X} (h : Deformation P) :
    P ⟶ reindex h.arcObject (parameterZero X) where
  torsorArrow := SheafTorsor.Arrow.ident P.torsor
  preserves x p := congrArg (fun k => k.hom.app x.obj ⟨x.val,p⟩) h.zero

def Deformation.fiber {P : Object a X} (h : Deformation P) : Fiber P :=
  StructuredArrow.mk h.boundary


def comparison (P : Object a X) : Discrete (Deformation P) ⥤ Fiber P :=
  Discrete.functor fun h => h.fiber

instance comparison_faithful (P : Object a X) : (comparison P).Faithful where
  map_injective _ := Subsingleton.elim _ _

theorem comparison_arrow_underlying {P : Object a X} {h k : Discrete (Deformation P)}
    (e : (comparison P).obj h ⟶ (comparison P).obj k) :
    e.right.torsorArrow = SheafTorsor.Arrow.ident (SheafTorsor.reindex P.torsor (snd D X)) := by
  apply (SheafTorsor.restriction (parameterZero X)).map_injective
  exact congrArg SheafActionQuotient.Arrow.torsorArrow (StructuredArrow.w e)

theorem comparison_arrow_eq {P : Object a X} {h k : Discrete (Deformation P)}
    (e : (comparison P).obj h ⟶ (comparison P).obj k) : h = k := by
  apply Discrete.ext
  apply Deformation.ext
  ext U y
  have hp := e.right.preserves ((product D X).obj.elementsMk U (y.1,y.2.1)) y.2.2
  rw [comparison_arrow_underlying e] at hp
  exact hp.symm

instance comparison_full (P : Object a X) : (comparison P).Full where
  map_surjective {h k} e := by
    have he := comparison_arrow_eq e
    subst k
    refine ⟨𝟙 h, ?_⟩
    rw [CategoryTheory.Functor.map_id]
    apply StructuredArrow.hom_ext
    apply SheafActionQuotient.Arrow.ext
    exact (comparison_arrow_underlying e).symm

def liftBoundary {P : Object a X} (F : Fiber P) :
    SheafTorsor.Arrow (SheafTorsor.reindex P.torsor (snd D X)) F.right.torsor :=
  (SheafTorsor.restriction (parameterZero X)).preimage F.hom.torsorArrow

theorem liftBoundary_zero {P : Object a X} (F : Fiber P) :
    (liftBoundary F).reindex (parameterZero X) = F.hom.torsorArrow :=
  (SheafTorsor.restriction (parameterZero X)).map_preimage
    (X := SheafTorsor.reindex P.torsor (snd D X)) (Y := F.right.torsor) F.hom.torsorArrow

/-- Reassociate the parameter and torsor element without choosing a section. -/
def parameterTotal (P : Object a X) :
    product D (SplitSheaf.Ext P.torsor.family) ⟶
      SplitSheaf.Ext (SheafTorsor.reindex P.torsor (snd D X)).family :=
  ⟨{ app U := ↾fun y => ⟨(y.1,y.2.1),y.2.2⟩
     naturality {_ _} _ := by rfl }⟩

def fromFiber {P : Object a X} (F : Fiber P) : Deformation P where
  map := parameterTotal P ≫
    (show SplitSheaf.Ext (SheafTorsor.reindex P.torsor (snd D X)).family ⟶
      SplitSheaf.Ext F.right.torsor.family from
      ⟨ElementFamilies.totalNat (product D X).obj (liftBoundary F).iso.hom⟩) ≫ F.right.totalMap
  zero := by
    ext U p
    have he := congrArg (fun c => c.iso.hom.app (X.obj.elementsMk U p.1) p.2) (liftBoundary_zero F)
    change F.right.value ((product D X).obj.elementsMk U (⟨0,by simp⟩,p.1))
      ((liftBoundary F).iso.hom.app ((product D X).obj.elementsMk U (⟨0,by simp⟩,p.1)) p.2) = _
    exact (congrArg (F.right.value _) he).trans (F.hom.preserves (X.obj.elementsMk U p.1) p.2)
  equivariant U d x g p := by
    change F.right.value ((product D X).obj.elementsMk U (d,x))
      ((liftBoundary F).iso.hom.app _ (P.torsor.act _ g p)) =
        a.act U g (F.right.value ((product D X).obj.elementsMk U (d,x))
          ((liftBoundary F).iso.hom.app ((product D X).obj.elementsMk U (d,x)) p))
    exact (congrArg (F.right.value _) ((liftBoundary F).equivariant ((product D X).obj.elementsMk U (d,x)) g p)).trans
      (F.right.equivariant ((product D X).obj.elementsMk U (d,x)) g ((liftBoundary F).iso.hom.app ((product D X).obj.elementsMk U (d,x)) p))

def recovery {P : Object a X} (F : Fiber P) : (fromFiber F).fiber ≅ F :=
  StructuredArrow.isoMk (Arrow.toIso {
    torsorArrow := liftBoundary F
    preserves _ _ := rfl }) (by
      apply SheafActionQuotient.Arrow.ext
      exact liftBoundary_zero F)

instance comparison_essSurj (P : Object a X) : (comparison P).EssSurj where
  mem_essImage F := ⟨⟨fromFiber F⟩, ⟨recovery F⟩⟩

/-- The fixed fiber of the infinitesimal quotient restriction is discrete,
even over quotient objects represented by nontrivial torsors. -/
def equivalence (P : Object a X) : Discrete (Deformation P) ≌ Fiber P := by
  letI : (comparison P).IsEquivalence := {}
  exact (comparison P).asEquivalence

/-- Forward boundary transport over arbitrary quotient objects. -/
def fiberTransport {P Q : Object a X} (c : P ⟶ Q) : Fiber P ⥤ Fiber Q :=
  StructuredArrow.map (Arrow.inverse c)

/-- Transport of deformations retains the entire coherent boundary fiber. -/
def transportComparison {P Q : Object a X} (c : P ⟶ Q) (h : Deformation P) :
    (transport c h).fiber ≅ (fiberTransport c).obj h.fiber :=
  StructuredArrow.isoMk (Arrow.toIso {
    torsorArrow := (Arrow.inverse c).torsorArrow.reindex (snd D X)
    preserves _ _ := rfl }) (by
      apply SheafActionQuotient.Arrow.ext
      rfl)

/-- Restrict the whole homotopy-fiber datum, including its boundary arrow. -/
def fiberRestriction {Y : Sheaf topology Type} (f : Y ⟶ X) (P : Object a X) :
    Fiber P ⥤ Fiber (reindex P f) where
  obj F := StructuredArrow.mk (Y := reindex F.right (SheafFunction.parameterMap D f))
    (F.hom.reindex f)
  map {_F _K} e := StructuredArrow.homMk (e.right.reindex (SheafFunction.parameterMap D f))
    (congrArg (fun c => c.reindex f) (StructuredArrow.w e))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The comparison with the boundary fiber respects all parameter maps. -/
theorem comparison_restrict {Y : Sheaf topology Type} (f : Y ⟶ X)
    {P : Object a X} (h : Deformation P) :
    (restrict f h).fiber = (fiberRestriction f P).obj h.fiber := by
  apply StructuredArrow.obj_ext _ _ rfl
  rfl

end SquareKit.SmoothQuotientDeformations
