import SquareKit.SmoothQuotientDeformations
import SquareKit.SheafActionQuotientDescent

/-! Descent of deformation maps along arbitrary locally surjective parameter
maps. Compatibility is the actual matching condition on the total-space cover. -/
noncomputable section
namespace SquareKit.SmoothQuotientDeformations
open CategoryTheory SheafActionQuotient SmoothOpenSite SheafRelation Opposite
set_option backward.isDefEq.respectTransparency false
variable {H : Type} [Group H] {M : Sheaf topology Type}
variable {a : Action (locallyConstantGroup H) M} {X Y : Sheaf topology Type}
local notation "D" => SmoothOpenSite.infinitesimal

instance totalLift_locallySurjective (P : Object a X) (f : Y ⟶ X)
    [Presheaf.IsLocallySurjective topology f.hom] :
    Presheaf.IsLocallySurjective topology (SplitSheaf.lift P.torsor.family f).hom where
  imageSieve_mem {U} t := by
    apply topology.superset_covering _ (Presheaf.imageSieve_mem topology f.hom t.1)
    intro V k hk
    obtain ⟨y,hy⟩ := hk
    let p := P.torsor.family.family.map (ElementFamilies.along X.obj k.op t.1) t.2
    refine ⟨⟨y, cast (congrArg (fun x => P.torsor.family.family.obj (X.obj.elementsMk (op V) x)) hy.symm) p⟩, ?_⟩
    exact Sigma.ext hy (cast_heq _ _)

abbrev cover (P : Object a X) (f : Y ⟶ X) :=
  SheafFunction.parameterMap D (SplitSheaf.lift P.torsor.family f)


instance productMap_locallySurjective (A : Sheaf topology Type) {B E : Sheaf topology Type}
    (f : B ⟶ E) [Presheaf.IsLocallySurjective topology f.hom] :
    Presheaf.IsLocallySurjective topology (SheafFunction.parameterMap A f).hom where
  imageSieve_mem {U} x := by
    apply topology.superset_covering _ (Presheaf.imageSieve_mem topology f.hom x.2)
    intro V k hk
    obtain ⟨y,hy⟩ := hk
    exact ⟨(A.obj.map k.op x.1,y), Prod.ext rfl hy⟩

/-- The action on the torsor component leaves the infinitesimal parameter fixed. -/
def actOnTotal (P : Object a X) :
    product (SheafTorsor.groupSheaf (locallyConstantGroup H))
      (product D (SplitSheaf.Ext P.torsor.family)) ⟶ product D (SplitSheaf.Ext P.torsor.family) :=
  ⟨{ app U := ↾fun y => (y.2.1,⟨y.2.2.1,P.torsor.act (X.obj.elementsMk U y.2.2.1) y.1 y.2.2.2⟩)
     naturality {U V} f := by
       apply ConcreteCategory.hom_ext
       intro y
       change (show (product D (SplitSheaf.Ext P.torsor.family)).obj.obj V from ((D).obj.map f y.2.1,
         ⟨X.obj.map f y.2.2.1, P.torsor.act (X.obj.elementsMk V (X.obj.map f y.2.2.1))
           ((locallyConstantGroup H).obj.map f y.1)
           (P.torsor.family.family.map (ElementFamilies.along X.obj f y.2.2.1) y.2.2.2)⟩)) =
         (show (product D (SplitSheaf.Ext P.torsor.family)).obj.obj V from ((D).obj.map f y.2.1,
           ⟨X.obj.map f y.2.2.1, P.torsor.family.family.map (ElementFamilies.along X.obj f y.2.2.1)
             (P.torsor.act (X.obj.elementsMk U y.2.2.1) y.1 y.2.2.2)⟩))
       exact congrArg (fun p => (show (product D (SplitSheaf.Ext P.torsor.family)).obj.obj V from
         ((D).obj.map f y.2.1, ⟨X.obj.map f y.2.2.1,p⟩)))
         (P.torsor.natural (ElementFamilies.along X.obj f y.2.2.1) y.1 y.2.2.2).symm }⟩

/-- No effectiveness is assumed: this is only the usual matching condition. -/
structure DescentDatum (P : Object a X) (f : Y ⟶ X) where
  localDeformation : Deformation (reindex P f)
  compatible : ∀ U (p q : (product D (SplitSheaf.Ext (reindex P f).torsor.family)).obj.obj U),
    (cover P f).hom.app U p = (cover P f).hom.app U q →
      localDeformation.map.hom.app U p = localDeformation.map.hom.app U q

namespace DescentDatum
variable {P : Object a X} {f : Y ⟶ X} [Presheaf.IsLocallySurjective topology f.hom]
variable (d : DescentDatum P f)

def map : product D (SplitSheaf.Ext P.torsor.family) ⟶ M :=
  SheafActionQuotient.Descent.descendMap (cover P f) d.localDeformation.map d.compatible

theorem map_fac : cover P f ≫ d.map = d.localDeformation.map :=
  SheafActionQuotient.Descent.descendMap_fac (cover P f) d.localDeformation.map d.compatible

theorem map_zero : parameterZero (SplitSheaf.Ext P.torsor.family) ≫ d.map = P.totalMap := by
  apply (cancel_epi (SplitSheaf.lift P.torsor.family f)).mp
  ext U p
  have he := congrArg (fun k => k.hom.app U
    (⟨0,by simp⟩,p)) d.map_fac
  exact he.trans (congrArg (fun k => k.hom.app U p) d.localDeformation.zero)

theorem map_equivariant : actOnTotal P ≫ d.map =
    a.onMap (fst (SheafTorsor.groupSheaf (locallyConstantGroup H)) _)
      (snd (SheafTorsor.groupSheaf (locallyConstantGroup H)) _ ≫ d.map) := by
  apply (cancel_epi (SheafFunction.parameterMap (SheafTorsor.groupSheaf (locallyConstantGroup H)) (cover P f))).mp
  ext U y
  have he := congrArg (fun k => k.hom.app U
    (y.2.1,⟨y.2.2.1, (reindex P f).torsor.act (Y.obj.elementsMk U y.2.2.1) y.1 y.2.2.2⟩)) d.map_fac
  have he' := congrArg (fun k => k.hom.app U (y.2.1,y.2.2)) d.map_fac
  exact he.trans ((d.localDeformation.equivariant U y.2.1 y.2.2.1 y.1 y.2.2.2).trans
    (congrArg (a.act U y.1) he'.symm))

/-- Compatible local deformations descend; the zero and equivariance equations
are proved after descent, rather than assumed as part of the datum. -/
def descend : Deformation P where
  map := d.map
  zero := d.map_zero
  equivariant U t x g p := congrArg (fun k => k.hom.app U (g,t,⟨x,p⟩)) d.map_equivariant

theorem descend_restrict : restrict f d.descend = d.localDeformation :=
  Deformation.ext _ _ d.map_fac

theorem descend_unique (h : Deformation P) (hh : restrict f h = d.localDeformation) : h = d.descend := by
  apply Deformation.ext
  apply (cancel_epi (cover P f)).mp
  exact (congrArg Deformation.map hh).trans d.map_fac.symm

end DescentDatum
end SquareKit.SmoothQuotientDeformations
