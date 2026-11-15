import SquareKit.SmoothCechComparison

/-! Recover actual quotient objects from represented local trivializations. -/
noncomputable section
open scoped Manifold ContDiff
namespace SquareKit.SmoothCech
open CategoryTheory CategoryTheory.Limits Opposite EuclideanOpen SmoothOpenSite
open SmoothRepresentedCover SmoothManifoldAction ManifoldRealization SheafActionQuotient
variable {X : Sheaf topology Type} {I : Type} (A : Atlas X I)
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (Model d) ∞ M]
variable (smoothAction : ∀ g : G, ContMDiff (Model d) (Model d) ∞ (fun x : M => g • x))

/-- Admission asks for equivariant chart trivializations of the actual torsor.
No global section or quotient comparison is an input. -/
structure TrivializedOn (P : Object (representation smoothAction).action X) where
  trivialization : ∀ i, SheafTorsor.Arrow
    (SheafTorsor.trivial (locallyConstantGroup G) (embedding.obj (A.domain i)))
    (SheafTorsor.reindex P.torsor (A.chart i))

/-- Conjugate canonical descent through an actual local quotient isomorphism.
The cocycle is derived from cancellation of that isomorphism. -/
def descentOfLocalIso {B : SplitSheaf.Ty X}
    (P : Object (representation smoothAction).action X)
    (Q : Object (representation smoothAction).action (SplitSheaf.Ext B))
    (e : SheafActionQuotient.Arrow Q (reindex P (SplitSheaf.p B))) :
    Descent.Datum (a := (representation smoothAction).action) B where
  localObject := Q
  torsorDatum := {
    transport x b c z := e.torsorArrow.iso.inv.app (SheafTorsor.Descent.point B x c)
      (e.torsorArrow.iso.hom.app (SheafTorsor.Descent.point B x b) z)
    identity x b z := congrArg (fun h => h.app (SheafTorsor.Descent.point B x b) z)
      e.torsorArrow.iso.hom_inv_id
    cocycle x b c k z := by
      have h := congrArg (fun h => h.app (SheafTorsor.Descent.point B x c)
        (e.torsorArrow.iso.hom.app (SheafTorsor.Descent.point B x b) z))
        e.torsorArrow.iso.inv_hom_id
      exact congrArg (e.torsorArrow.iso.inv.app (SheafTorsor.Descent.point B x k)) h
    natural {x y} f b c z := by
      have hi := NatTrans.naturality_apply e.torsorArrow.iso.inv
        (SplitFunctionDiagram.pairArrow B.family f c)
        (e.torsorArrow.iso.hom.app (SheafTorsor.Descent.point B x b) z)
      have hh := NatTrans.naturality_apply e.torsorArrow.iso.hom
        (SplitFunctionDiagram.pairArrow B.family f b) z
      exact hi.symm.trans (congrArg
        (e.torsorArrow.iso.inv.app (SheafTorsor.Descent.point B y (B.family.map f c))) hh.symm)
    equivariant x b c g z := by
      rw [e.torsorArrow.equivariant]
      exact e.inverse.torsorArrow.equivariant (SheafTorsor.Descent.point B x c) g
        (e.torsorArrow.iso.hom.app (SheafTorsor.Descent.point B x b) z) }
  value_compatible x b c z :=
    (e.inverse.preserves (SheafTorsor.Descent.point B x c)
      (e.torsorArrow.iso.hom.app (SheafTorsor.Descent.point B x b) z)).trans
      (e.preserves (SheafTorsor.Descent.point B x b) z)

def descentOfLocalIsoMap {B : SplitSheaf.Ty X}
    (P : Object (representation smoothAction).action X)
    (Q : Object (representation smoothAction).action (SplitSheaf.Ext B))
    (e : SheafActionQuotient.Arrow Q (reindex P (SplitSheaf.p B))) :
    Descent.Map (descentOfLocalIso smoothAction P Q e) (Descent.canonicalDatum B P) where
  torsorMap := {
    hom := e.torsorArrow.iso.hom
    equivariant := e.torsorArrow.equivariant
    transport x b c z := by
      exact (congrArg (fun h => h.app (SheafTorsor.Descent.point B x c)
        (e.torsorArrow.iso.hom.app (SheafTorsor.Descent.point B x b) z))
        e.torsorArrow.iso.inv_hom_id) }
  preserves := e.preserves

/-- A selected global recovery isomorphism, constructed through effective descent. -/
def descentOfLocalIsoRecovery {B : SplitSheaf.Ty X}
    [Presheaf.IsLocallySurjective topology (SplitSheaf.p B).hom]
    (P : Object (representation smoothAction).action X)
    (Q : Object (representation smoothAction).action (SplitSheaf.Ext B))
    (e : SheafActionQuotient.Arrow Q (reindex P (SplitSheaf.p B))) :
    SheafActionQuotient.Arrow (descentOfLocalIso smoothAction P Q e).object P :=
  ((descentOfLocalIsoMap smoothAction P Q e).arrow).comp (Descent.canonicalRecovery B P)

namespace TrivializedOn
variable {A smoothAction} {P : Object (representation smoothAction).action X}
variable (t : TrivializedOn A smoothAction P)

def sectionMap : A.total ⟶ SplitSheaf.Ext P.torsor.family :=
  SheafCoproductLocal.desc A.family (fun i => SplitSheaf.pair P.torsor.family (A.chart i)
    (SheafTorsor.sectionOfArrow (t.trivialization i)))

theorem sectionMap_projection : t.sectionMap ≫ SplitSheaf.p P.torsor.family = A.cover := by
  apply colimit.hom_ext
  intro ⟨i⟩
  change A.inclusion i ≫ _ = A.inclusion i ≫ _
  rw [← Category.assoc, sectionMap, SheafCoproductLocal.inclusion_desc]
  erw [SplitSheaf.pair_p]
  exact (A.inclusion_cover i).symm

/-- The section is on the coproduct cover, not on the original parameter. -/
def localSection : SplitSheaf.Tm (SheafTorsor.reindex P.torsor A.cover).family :=
  SplitSheaf.readTerm P.torsor.family t.sectionMap t.sectionMap_projection

def regularization : SheafActionQuotient.Arrow
    (chart (representation smoothAction).action ((reindex P A.cover).sectionMap t.localSection))
    (reindex P A.cover) where
  torsorArrow := SheafTorsor.ofSection (SheafTorsor.reindex P.torsor A.cover) t.localSection
  preserves x g := (reindex P A.cover).equivariant x g (t.localSection.val x)


/-- The actual local value map reconstructs a smooth map by full faithfulness. -/
def localMap (i : I) : External.SmoothMap (A.domain i) d M :=
  ⟨ManifoldRealization.reconstruct ((principalIso (A.domain i)).hom ≫
    (reindex P (A.chart i)).sectionMap (SheafTorsor.sectionOfArrow (t.trivialization i))),
    ManifoldRealization.reconstruct_smooth _⟩

theorem localMap_hat (i : I) : hat (t.localMap i).val (t.localMap i).property =
    (reindex P (A.chart i)).sectionMap (SheafTorsor.sectionOfArrow (t.trivialization i)) := by
  unfold localMap hat
  rw [ManifoldRealization.map_reconstruct, Iso.inv_hom_id_assoc]

theorem localValue_factorization :
    (reindex P A.cover).sectionMap t.localSection = t.sectionMap ≫ P.totalMap := by
  change SplitSheaf.pair P.torsor.family A.cover t.localSection ≫ P.totalMap = _
  rw [localSection, SplitSheaf.pair_read]

theorem localValue_chart (i : I) :
    A.inclusion i ≫ (reindex P A.cover).sectionMap t.localSection =
      hat (t.localMap i).val (t.localMap i).property := by
  rw [localValue_factorization, ← Category.assoc, sectionMap,
    SheafCoproductLocal.inclusion_desc, localMap_hat]
  rfl

/-- All reconstructed smooth maps assemble to the actual chosen local value map. -/
theorem localValue_assembled :
    SheafCoproductLocal.desc A.family (fun i => hat (t.localMap i).val (t.localMap i).property) =
      (reindex P A.cover).sectionMap t.localSection := by
  apply colimit.hom_ext
  intro ⟨i⟩
  change A.inclusion i ≫ _ = A.inclusion i ≫ _
  rw [SheafCoproductLocal.inclusion_desc, localValue_chart]

def splitRegularization : SheafActionQuotient.Arrow
    (chart (representation smoothAction).action
      ((SplitSheaf.displayIso A.cover).hom ≫ (reindex P A.cover).sectionMap t.localSection))
    (reindex P (SplitSheaf.p (SplitSheaf.ofDisplay A.cover))) :=
  (t.regularization.reindex (SplitSheaf.displayIso A.cover).hom).comp
    (eqToHom (congrArg (reindex P) (SplitSheaf.displayIso_projection A.cover)))

/-- Canonical descent expressed through the actually chosen cover trivialization. -/
def regularDescent : Descent.Datum (a := (representation smoothAction).action)
    (SplitSheaf.ofDisplay A.cover) :=
  descentOfLocalIso smoothAction P _ t.splitRegularization

/-- Recovery includes the chosen equivariant value map, not only the torsor. -/
def recovery : SheafActionQuotient.Arrow t.regularDescent.object P :=
  descentOfLocalIsoRecovery smoothAction P _ t.splitRegularization

end TrivializedOn
end SquareKit.SmoothCech
