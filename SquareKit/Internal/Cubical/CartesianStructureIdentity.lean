import SquareKit.Internal.Cubical.StructureIdentity
import SquareKit.Internal.Cubical.CartesianSmallFamilyClassification
import SquareKit.Internal.Cubical.CartesianDependentFamilies

/-! Structure paths in the Cartesian restriction of an admitted carrier line.
This compares actual native path sections. It does not identify a newly selected
Cartesian ua with restriction of the De Morgan choice. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.StructureIdentity
open CategoryTheory SquareKit.StructureIdentity

variable (F : Transport.{0}) {S T : Type}
  (A : Presheaf.Family (Presheaf.total (Presheaf.interval Presheaf.terminal.{0})))
  (j : A ≅ Presheaf.constantFamily _ T)
  (e : S ≃ T) (s : F.Data S) (t : F.Data T)

abbrev base := restrict Presheaf.terminal.{0}

def family : Family (total (interval base)) := relativeFamily (Presheaf.StructureIdentity.family F A j)

def presentation : family F A j ≅ constantFamily _ (F.Data T) :=
  Functor.isoWhiskerLeft (intervalElements _) (Presheaf.StructureIdentity.presentation F A j)

def localFamily : LocalFamily (total (interval base)) :=
  LocalFamily.ofFilling (family F A j) (presentedFilling (presentation F A j))
    (presentedFilling_lawful (presentation F A j))

def pull (v : F.Data T) : Term (family F A j) := relativeTerm (Presheaf.StructureIdentity.pull F A j v)

abbrev StructuredPath := Term (path (family F A j)
  (Term.reindex (pull F A j (F.map e s)) (endpointSub base false))
  (Term.reindex (pull F A j t) (endpointSub base true)))

def point : base.Elements := base.elementsMk (.op ⟨0⟩) PUnit.unit

theorem observe_pull (v : F.Data T) (x : (total (interval base)).Elements) :
    (presentation F A j).hom.app x ((pull F A j v).val x) = v :=
  Presheaf.StructureIdentity.observe_pull F A j v ((intervalElements _).obj x)

theorem path_preserves (p : StructuredPath F A j e s t) : F.map e s = t := by
  let z₀ := extendObj (interval base) point ((endpoint base false).val point)
  let z₁ := extendObj (interval base) point ((endpoint base true).val point)
  let q := Term.map (presentation F A j).hom (pathApp p)
  have h₀ := congrArg (fun v => (presentation F A j).hom.app z₀ (v.val point)) (pathApp_zero p)
  have h₁ := congrArg (fun v => (presentation F A j).hom.app z₁ (v.val point)) (pathApp_one p)
  have hq := constant_section_interval q point ((endpoint base false).val point)
    ((endpoint base true).val point)
  exact (observe_pull F A j (F.map e s) z₀).symm.trans
    (h₀.symm.trans (hq.trans (h₁.trans (observe_pull F A j t z₁))))

def preservesPath (h : F.map e s = t) : StructuredPath F A j e s t :=
  pathLam (pull F A j (F.map e s)) rfl
    (congrArg (fun a => Term.reindex (pull F A j a) (endpointSub base true)) h)

theorem path_unique (p q : StructuredPath F A j e s t) : p = q := by
  apply pathApp_injective
  apply Term.ext
  intro x
  rcases x with @⟨I, γ, r⟩
  let y := base.elementsMk I γ
  let z := extendObj (interval base) y r
  have hp := constant_section_interval (Term.map (presentation F A j).hom (pathApp p))
    y r ((endpoint base false).val y)
  have hq := constant_section_interval (Term.map (presentation F A j).hom (pathApp q))
    y r ((endpoint base false).val y)
  have h₀ := congrArg
    (fun a => (presentation F A j).hom.app
      (extendObj (interval base) y ((endpoint base false).val y)) (a.val y))
    ((pathApp_zero p).trans (pathApp_zero q).symm)
  exact ((presentation F A j).app z).toEquiv.injective (hp.trans (h₀.trans hq.symm))

def identityEquiv : StructuredPath F A j e s t ≃ PLift (F.map e s = t) where
  toFun p := ⟨path_preserves F A j e s t p⟩
  invFun h := preservesPath F A j e s t h.down
  left_inv p := path_unique F A j e s t _ p
  right_inv _ := Subsingleton.elim _ _

def restrictPath (p : Presheaf.StructureIdentity.StructuredPath F A j e s t) : StructuredPath F A j e s t :=
  pathLam (relativeTerm (Presheaf.pathApp p))
    (congrArg restrictTerm (Presheaf.pathApp_zero p))
    (congrArg restrictTerm (Presheaf.pathApp_one p))

theorem restriction_observation (p : Presheaf.StructureIdentity.StructuredPath F A j e s t) :
    path_preserves F A j e s t (restrictPath F A j e s t p) =
      Presheaf.StructureIdentity.path_preserves F A j e s t p := rfl

/-- Both directions recover whole native paths in this discrete presentation. -/
def restrictionEquiv : Presheaf.StructureIdentity.StructuredPath F A j e s t ≃ StructuredPath F A j e s t :=
  (Presheaf.StructureIdentity.identityEquiv F A j e s t).trans (identityEquiv F A j e s t).symm

theorem restrictionEquiv_apply (p : Presheaf.StructureIdentity.StructuredPath F A j e s t) :
    restrictionEquiv F A j e s t p = restrictPath F A j e s t p :=
  path_unique F A j e s t _ _

end SquareKit.Cubical.Cartesian.StructureIdentity
