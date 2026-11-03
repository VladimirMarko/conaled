import SquareKit.SheafTorsor
import SquareKit.SmoothConstantRigidity
import SquareKit.SmoothDualSheaf

/-! Dual extension of arbitrary locally trivial torsors. The actual sheaf of
dual-stage sections is used; nontrivial torsors are not replaced by pointwise
trivial bundles. -/
noncomputable section
namespace SquareKit.SmoothOpenSite
open CategoryTheory Opposite SmoothPresentationSite SmoothGeometricKL SheafTorsor

variable {H : Type} [Group H]
local notation "G" => locallyConstantGroup H
variable {X : Sheaf topology Type}

abbrev dualElements (X : Sheaf topology Type) : (dualSheaf X).obj.Elements ⥤ X.obj.Elements where
  obj x := X.obj.elementsMk (dualStages.obj x.obj) x.val
  map f := Functor.Elements.homMk (dualStages.map f.hom) f.map_val
  map_id x := by apply Functor.Elements.hom_ext; exact dualStages.map_id x.obj
  map_comp f g := by apply Functor.Elements.hom_ext; exact dualStages.map_comp f.hom g.hom

/-- This total space is precisely the constructed dual-section sheaf of the
original total space. Its sheaf certificate comes from exponential comparison. -/
abbrev dualTorsorFamily (P : Torsor G X) : SplitSheaf.Ty (dualSheaf X) where
  family := dualElements X ⋙ P.family.family
  isSheaf := (dualSheaf (SplitSheaf.Ext P.family)).property

/-- A locally constant group acts on the dual family through its proved
infinitesimal pullback isomorphism. -/
def dualTorsor (P : Torsor G X) : Torsor G (dualSheaf X) where
  family := dualTorsorFamily P
  act x g p := P.act ((dualElements X).obj x)
    ((G).obj.map (stageMap (inl x.obj.unop.unop)) g) p
  one_act x p := by
    rw [((G).obj.map (stageMap (inl x.obj.unop.unop))).hom.map_one]
    exact P.one_act _ _
  mul_act x g h p := by
    rw [((G).obj.map (stageMap (inl x.obj.unop.unop))).hom.map_mul]
    exact P.mul_act _ _ _ _
  natural {x y} f g p := by
    change P.family.family.obj ((dualElements X).obj x) at p
    change P.family.family.map ((dualElements X).map f)
      (P.act ((dualElements X).obj x) ((G).obj.map (stageMap (inl x.obj.unop.unop)) g) p) =
      P.act ((dualElements X).obj y)
        ((G).obj.map (stageMap (inl y.obj.unop.unop)) ((G).obj.map f.hom g))
        (P.family.family.map ((dualElements X).map f) p)
    rw [P.natural]
    congr 1
    change (G).obj.map (stageMap (dualMap f.hom.unop.unop))
      ((G).obj.map (stageMap (inl x.obj.unop.unop)) g) =
      (G).obj.map (stageMap (inl y.obj.unop.unop)) ((G).obj.map f.hom g)
    rw [← ConcreteCategory.comp_apply, ← (G).obj.map_comp,
      ← ConcreteCategory.comp_apply, ← (G).obj.map_comp]
    exact congrArg (fun k => (G).obj.map (stageMap k) g) (dualMap_inl f.hom.unop.unop)
  principal x p q := by
    obtain ⟨g, hg, hu⟩ := P.principal ((dualElements X).obj x) p q
    let e := constantGroupDualEquiv H x.obj.unop.unop
    refine ⟨e.symm g, ?_, ?_⟩
    · change P.act ((dualElements X).obj x) (e (e.symm g)) p = q
      exact (congrArg (fun k => P.act ((dualElements X).obj x) k p)
        (e.apply_symm_apply g)).trans hg
    · intro k hk
      apply e.injective
      exact (hu (e k) hk).trans (e.apply_symm_apply g).symm
  locallySurjective := by
    constructor
    intro A x
    have h := dualParameterSieve_cover
      (Presheaf.imageSieve (SplitSheaf.p P.family).hom x)
      (Presheaf.imageSieve_mem topology (SplitSheaf.p P.family).hom x)
      A.unop (𝟙 (op (dual A.unop)))
    exact h

/-- The zero map acts in the original category of elements. -/
def zeroElement (x : (dualSheaf X).obj.Elements) :
    (dualElements X).obj x ⟶ (dualSheafZero X).hom.mapElements.obj x :=
  Functor.Elements.homMk (stageMap (dualZero x.obj.unop.unop)) rfl

/-- Restriction along zero is equivariant; its inverse follows from the
proved theorem that every map of locally trivial torsors is invertible. -/
def dualTorsorZeroMap (P : Torsor G X) :
    EquivariantMap (dualTorsor P) (reindex P (dualSheafZero X)) where
  hom := {
    app x := P.family.family.map (zeroElement x)
    naturality {x y} f := by
      change P.family.family.map ((dualElements X).map f) ≫
        P.family.family.map (zeroElement y) =
        P.family.family.map (zeroElement x) ≫
          P.family.family.map ((dualSheafZero X).hom.mapElements.map f)
      rw [← P.family.family.map_comp, ← P.family.family.map_comp]
      congr 1
      apply Functor.Elements.hom_ext
      exact congrArg (fun k => stageMap k) (dualZero_natural f.hom.unop.unop) }
  equivariant x g p := by
    change P.family.family.obj ((dualElements X).obj x) at p
    change P.family.family.map (zeroElement x)
      (P.act ((dualElements X).obj x) ((G).obj.map (stageMap (inl x.obj.unop.unop)) g) p) = _
    rw [P.natural]
    congr 1
    change (G).obj.map (stageMap (dualZero x.obj.unop.unop))
      ((G).obj.map (stageMap (inl x.obj.unop.unop)) g) = g
    rw [← ConcreteCategory.comp_apply, ← (G).obj.map_comp]
    change (G).obj.map (stageMap (inl x.obj.unop.unop ≫ dualZero x.obj.unop.unop)) g = g
    rw [inl_dualZero]
    exact congrArg (fun k => k g) ((G).obj.map_id x.obj)

def dualTorsorZero (P : Torsor G X) :
    Arrow (dualTorsor P) (reindex P (dualSheafZero X)) := (dualTorsorZeroMap P).toArrow

def dualTorsorArrow {P Q : Torsor G X} (f : Arrow P Q) : Arrow (dualTorsor P) (dualTorsor Q) where
  iso := Functor.isoWhiskerLeft (dualElements X) f.iso
  equivariant x g p := f.equivariant ((dualElements X).obj x)
    ((G).obj.map (stageMap (inl x.obj.unop.unop)) g) p

def dualTorsorFunctor (X : Sheaf topology Type) : Torsor G X ⥤ Torsor G (dualSheaf X) where
  obj := dualTorsor
  map := dualTorsorArrow

theorem dualTorsorZero_natural {P Q : Torsor G X} (f : Arrow P Q) :
    Arrow.comp (dualTorsorArrow f) (dualTorsorZero Q) =
      Arrow.comp (dualTorsorZero P) (f.reindex (dualSheafZero X)) := by
  apply SheafTorsor.Arrow.ext
  ext x p
  exact (NatTrans.naturality_apply f.iso.hom (zeroElement x) p).symm

/-- Every actual torsor fiber over a represented dual parameter is determined
by its zero restriction, with existence as well as uniqueness. -/
theorem torsor_zero_bijective (P : Torsor G X) (x : (dualSheaf X).obj.Elements) :
    Function.Bijective (P.family.family.map (zeroElement x)) :=
  (dualTorsorZeroMap P).bijective x

end SquareKit.SmoothOpenSite
