import SquareKit.SheafActionQuotientDescent

/-! Conjugating canonical torsor descent through a chosen local isomorphism. -/
noncomputable section
namespace SquareKit.SheafTorsor.Descent
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {X : Sheaf J (Type (max u v))}
variable {B : SplitSheaf.Ty X}

/-- Local isomorphisms determine transport by conjugating canonical descent. -/
def ofLocalIso (P : Torsor G X) (Q : Torsor G (SplitSheaf.extension B))
    (e : Arrow Q (reindex P (SplitSheaf.p B))) : Datum B Q where
    transport x b c z := e.iso.inv.app (SheafTorsor.Descent.point B x c)
      (e.iso.hom.app (SheafTorsor.Descent.point B x b) z)
    identity x b z := congrArg (fun h => h.app (SheafTorsor.Descent.point B x b) z)
      e.iso.hom_inv_id
    cocycle x b c k z := by
      have h := congrArg (fun h => h.app (SheafTorsor.Descent.point B x c)
        (e.iso.hom.app (SheafTorsor.Descent.point B x b) z))
        e.iso.inv_hom_id
      exact congrArg (e.iso.inv.app (SheafTorsor.Descent.point B x k)) h
    natural {x y} f b c z := by
      have hi := NatTrans.naturality_apply e.iso.inv
        (SplitFunctionDiagram.pairArrow B.family f c)
        (e.iso.hom.app (SheafTorsor.Descent.point B x b) z)
      have hh := NatTrans.naturality_apply e.iso.hom
        (SplitFunctionDiagram.pairArrow B.family f b) z
      exact hi.symm.trans (congrArg
        (e.iso.inv.app (SheafTorsor.Descent.point B y (B.family.map f c))) hh.symm)
    equivariant x b c g z := by
      rw [e.equivariant]
      exact e.inverse.equivariant (SheafTorsor.Descent.point B x c) g
        (e.iso.hom.app (SheafTorsor.Descent.point B x b) z)

def ofLocalIsoMap (P : Torsor G X) (Q : Torsor G (SplitSheaf.extension B))
    (e : Arrow Q (reindex P (SplitSheaf.p B))) :
    Map (ofLocalIso P Q e) (canonicalDatum B P) where
  hom := e.iso.hom
  equivariant := e.equivariant
  transport x b c z := congrArg (fun h => h.app (point B x c)
    (e.iso.hom.app (point B x b) z)) e.iso.inv_hom_id

/-- Effective descent recovers the original torsor from the chosen local isomorphism. -/
def ofLocalIsoRecovery [Presheaf.IsLocallySurjective J (SplitSheaf.p B).hom]
    (P : Torsor G X) (Q : Torsor G (SplitSheaf.extension B))
    (e : Arrow Q (reindex P (SplitSheaf.p B))) :
    Arrow (torsor (ofLocalIso P Q e)) P :=
  ((ofLocalIsoMap P Q e).arrow).comp (canonicalRecovery B P)

/-- Effective descent recovers each local arrow after evaluation. -/
theorem map_comparison {P Q : Torsor G (SplitSheaf.extension B)}
    {d : Datum B P} {e : Datum B Q}
    [Presheaf.IsLocallySurjective J (SplitSheaf.p B).hom] (h : Map d e) :
    (h.arrow.reindex (SplitSheaf.p B)).comp (comparison e) =
      (comparison d).comp h.toEquivariantMap.toArrow := by
  apply Arrow.ext
  ext x t
  exact h.evaluation (X.obj.elementsMk x.obj x.val.1) x.val.2 t

theorem canonicalRecovery_reindex
    [Presheaf.IsLocallySurjective J (SplitSheaf.p B).hom] (P : Torsor G X) :
    (canonicalRecovery B P).reindex (SplitSheaf.p B) = comparison (canonicalDatum B P) := by
  apply Arrow.ext
  have h := congrArg (fun k => k.iso.hom) (canonicalEmbedding_evaluation B P)
  have hh := congrArg (fun k =>
    ((canonicalEmbedding B P).toArrow.reindex (SplitSheaf.p B)).iso.inv ≫ k) h
  dsimp only [Arrow.comp, Arrow.ident, Iso.trans_hom, Iso.refl_hom] at hh
  rw [Iso.inv_hom_id_assoc, Category.comp_id] at hh
  exact hh.symm

theorem ofLocalIsoRecovery_reindex
    [Presheaf.IsLocallySurjective J (SplitSheaf.p B).hom]
    (P : Torsor G X) (Q : Torsor G (SplitSheaf.extension B))
    (e : Arrow Q (reindex P (SplitSheaf.p B))) :
    (ofLocalIsoRecovery P Q e).reindex (SplitSheaf.p B) =
      (comparison (ofLocalIso P Q e)).comp e := by
  change ((ofLocalIsoMap P Q e).arrow.reindex (SplitSheaf.p B)).comp
    ((canonicalRecovery B P).reindex (SplitSheaf.p B)) = _
  rw [canonicalRecovery_reindex]
  have he : (ofLocalIsoMap P Q e).toEquivariantMap.toArrow = e := by
    apply Arrow.ext
    rfl
  exact (map_comparison (ofLocalIsoMap P Q e)).trans (congrArg ((comparison (ofLocalIso P Q e)).comp) he)

/-- Restriction along a cover detects every equivariant torsor arrow. -/
theorem reindex_injective [Presheaf.IsLocallySurjective J (SplitSheaf.p B).hom]
    {P Q : Torsor G X} {h k : Arrow P Q}
    (eq : h.reindex (SplitSheaf.p B) = k.reindex (SplitSheaf.p B)) : h = k := by
  apply Arrow.ext
  ext x p
  apply fiber_ext Q.family x (Presheaf.imageSieve (SplitSheaf.p B).hom x.val)
    (Presheaf.imageSieve_mem J (SplitSheaf.p B).hom x.val)
  intro V f hf
  obtain ⟨⟨y, b⟩, hy⟩ := hf
  change y = X.obj.map f.op x.val at hy
  subst y
  have hh := NatTrans.naturality_apply h.iso.hom (ElementFamilies.along X.obj f.op x.val) p
  have hk := NatTrans.naturality_apply k.iso.hom (ElementFamilies.along X.obj f.op x.val) p
  have he := congrArg (fun e : Arrow (reindex P (SplitSheaf.p B)) (reindex Q (SplitSheaf.p B)) =>
    e.iso.hom.app ((SplitSheaf.extension B).obj.elementsMk (op V) ⟨X.obj.map f.op x.val, b⟩)
      (P.family.family.map (ElementFamilies.along X.obj f.op x.val) p)) eq
  exact hh.symm.trans (he.trans hk)

end SquareKit.SheafTorsor.Descent

namespace SquareKit.SheafActionQuotient.Descent
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M X : Sheaf J (Type (max u v))}
variable {a : Action G M} {B : SplitSheaf.Ty X}

def ofLocalIso (P : Object a X) (Q : Object a (SplitSheaf.extension B))
    (e : Arrow Q (reindex P (SplitSheaf.p B))) : Datum (a := a) B where
  localObject := Q
  torsorDatum := SheafTorsor.Descent.ofLocalIso P.torsor Q.torsor e.torsorArrow
  value_compatible x b c z :=
    (e.inverse.preserves (SheafTorsor.Descent.point B x c)
      (e.torsorArrow.iso.hom.app (SheafTorsor.Descent.point B x b) z)).trans
      (e.preserves (SheafTorsor.Descent.point B x b) z)

def ofLocalIsoMap (P : Object a X) (Q : Object a (SplitSheaf.extension B))
    (e : Arrow Q (reindex P (SplitSheaf.p B))) :
    Map (ofLocalIso P Q e) (canonicalDatum B P) where
  torsorMap := SheafTorsor.Descent.ofLocalIsoMap P.torsor Q.torsor e.torsorArrow
  preserves := e.preserves

def ofLocalIsoRecovery [Presheaf.IsLocallySurjective J (SplitSheaf.p B).hom]
    (P : Object a X) (Q : Object a (SplitSheaf.extension B))
    (e : Arrow Q (reindex P (SplitSheaf.p B))) : Arrow (ofLocalIso P Q e).object P :=
  ((ofLocalIsoMap P Q e).arrow).comp (canonicalRecovery B P)

theorem ofLocalIsoRecovery_reindex
    [Presheaf.IsLocallySurjective J (SplitSheaf.p B).hom]
    (P : Object a X) (Q : Object a (SplitSheaf.extension B))
    (e : Arrow Q (reindex P (SplitSheaf.p B))) :
    (ofLocalIsoRecovery P Q e).reindex (SplitSheaf.p B) =
      (ofLocalIso P Q e).comparison.comp e := by
  apply Arrow.ext
  exact SheafTorsor.Descent.ofLocalIsoRecovery_reindex P.torsor Q.torsor e.torsorArrow

end SquareKit.SheafActionQuotient.Descent
