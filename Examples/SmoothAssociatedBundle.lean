import SquareKit.SheafAssociatedBundleDescent
import SquareKit.SmoothBundlePullbackRealization

/-! Regular and one-point associated fibers of ordinary discrete principal bundles. -/
noncomputable section
namespace Examples.SmoothAssociatedBundle
open CategoryTheory SquareKit SquareKit.SheafAssociatedBundle
open SquareKit.SmoothPrincipalBundle SquareKit.ManifoldRealization SquareKit.SmoothOpenSite
open scoped Manifold ContDiff

variable {n m : ℕ} {G B E B' E' : Type} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] [MulAction G E] [MulAction G E']
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace B'] [TopologicalSpace E']
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
  [ChartedSpace (Space m) B'] [ChartedSpace (Space m) E']
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E]
  [IsManifold (modelWithCorners m) ∞ B'] [IsManifold (modelWithCorners m) ∞ E']
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))
  (Q : Bundle (n := m) (G := G) (B := B') (E := E'))

/-- The regular associated sheaf is the actual independently supplied ordinary total. -/
def regularTotalIso : SplitSheaf.extension (associated P.realizedTorsor
    (regularAction (locallyConstantGroup G))) ≅ object n E :=
  (SplitSheaf.toOver ⋙ Over.forget _).mapIso (regularIso P.realizedTorsor) ≪≫ P.realizedTotalIso

theorem regularTotalIso_projection :
    (regularTotalIso P).hom ≫ ManifoldRealization.map P.projection P.smooth_projection =
      SplitSheaf.p (associated P.realizedTorsor (regularAction (locallyConstantGroup G))) := by
  change SplitSheaf.totalMap (regularRecoveryMap P.realizedTorsor) ≫
    P.realizedTotalIso.hom ≫ ManifoldRealization.map P.projection P.smooth_projection = _
  rw [P.realizedTotalIso_projection]
  exact SplitSheaf.totalMap_projection _

variable (f : B' → B) (hf : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ f)
  (k : E' → E) (hk : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ k)
  (hp : ∀ e, P.projection (k e) = f (Q.projection e))
  (ha : ∀ (g : G) e, k (g • e) = g • k e)

/-- Associated maps over changing bases use the actual ordinary bundle map. -/
def regularAlong : associated Q.realizedTorsor (regularAction (locallyConstantGroup G)) ⟶
    SplitSheaf.tySub (associated P.realizedTorsor (regularAction (locallyConstantGroup G)))
      (ManifoldRealization.map f hf) :=
  (functor (regularAction (locallyConstantGroup G)) _).map (P.arrowAlong Q f hf k hk hp ha) ≫
    reindexMap P.realizedTorsor (regularAction (locallyConstantGroup G)) (ManifoldRealization.map f hf)

set_option backward.isDefEq.respectTransparency false in
theorem regularAlong_recovery :
    regularAlong P Q f hf k hk hp ha ≫
      (SplitSheaf.restriction (ManifoldRealization.map f hf)).map (regularRecoveryMap P.realizedTorsor) =
    regularRecoveryMap Q.realizedTorsor ≫ (P.arrowAlong Q f hf k hk hp ha).iso.hom := by
  apply hom_ext
  intro x p a
  change (regularRecoveryMap P.realizedTorsor).app _
    ((reindexMap P.realizedTorsor _ _).app x
      (((functor (regularAction (locallyConstantGroup G)) _).map
        (P.arrowAlong Q f hf k hk hp ha)).app x (classOf _ _ x p a))) =
    (P.arrowAlong Q f hf k hk hp ha).iso.hom.app x
      ((regularRecoveryMap Q.realizedTorsor).app x (classOf _ _ x p a))
  rw [functor_map_classOf, reindexMap_classOf, regularRecoveryMap_classOf, regularRecoveryMap_classOf]
  exact ((P.arrowAlong Q f hf k hk hp ha).equivariant x _ p).symm

set_option backward.isDefEq.respectTransparency false in
/-- Total recovery commutes with every equivariant ordinary map, including base change. -/
theorem regularAlong_total :
    SplitSheaf.totalMap (regularAlong P Q f hf k hk hp ha) ≫
      SplitSheaf.lift (associated P.realizedTorsor (regularAction (locallyConstantGroup G)))
        (ManifoldRealization.map f hf) ≫ (regularTotalIso P).hom =
      (regularTotalIso Q).hom ≫ ManifoldRealization.map k hk := by
  change SplitSheaf.totalMap (regularAlong P Q f hf k hk hp ha) ≫
    SplitSheaf.lift _ _ ≫ SplitSheaf.totalMap (regularRecoveryMap P.realizedTorsor) ≫
      P.realizedTotalIso.hom =
    SplitSheaf.totalMap (regularRecoveryMap Q.realizedTorsor) ≫
      Q.realizedTotalIso.hom ≫ ManifoldRealization.map k hk
  rw [← Category.assoc (SplitSheaf.lift _ _) (SplitSheaf.totalMap _) _,
    ← SplitSheaf.totalMap_reindex_lift, Category.assoc,
    ← Category.assoc (SplitSheaf.totalMap _) (SplitSheaf.totalMap _) _,
    ← SplitSheaf.totalMap_comp, regularAlong_recovery, SplitSheaf.totalMap_comp]
  simp only [Category.assoc]
  rw [P.arrowAlong_total Q f hf k hk hp ha]

def pointFiber : Sheaf topology Type := Sheaf.terminal topology Limits.Types.isTerminalPUnit

/-- The trivial one-point fiber has exactly the realized ordinary base as total. -/
def pointTotalIso : SplitSheaf.extension (associated P.realizedTorsor
    (trivialAction (locallyConstantGroup G) pointFiber)) ≅
      object n B :=
  (SplitSheaf.toOver ⋙ Over.forget _).mapIso
    (trivialIso P.realizedTorsor pointFiber) ≪≫
  { hom := SplitSheaf.p _
    inv := ⟨{ app U := ↾fun x => ⟨x, (PUnit.unit : pointFiber.obj.obj U)⟩
              naturality {U V} f := by ext x; apply Sigma.ext rfl; exact heq_of_eq (Subsingleton.elim (α := PUnit) _ _) }⟩
    hom_inv_id := by ext U x; apply Sigma.ext rfl; exact heq_of_eq (Subsingleton.elim (α := PUnit) _ _)
    inv_hom_id := by ext U x; rfl }

theorem pointTotalIso_projection :
    (pointTotalIso P).hom = SplitSheaf.p (associated P.realizedTorsor
      (trivialAction (locallyConstantGroup G) pointFiber)) :=
  SplitSheaf.totalMap_projection _

end Examples.SmoothAssociatedBundle
