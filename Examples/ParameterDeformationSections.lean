import SquareKit.SmoothQuotientParameterSections
import SquareKit.SheafActionQuotientDescentDisplay
import Examples.LocalDeformationSections

/-! Usable parameter-local section families and recovery of their full sections. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Examples.ParameterDeformationSections
open CategoryTheory SquareKit SheafActionQuotient SmoothOpenSite
open SmoothQuotientDeformations Internal.PathTransport.GroupoidModel
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable {a : Action (locallyConstantGroup H) M} {A : SplitSheaf.Ty X}

private def setSection {Γ : Type*} [Category* Γ] (F : Γ ⥤ Type*)
    (x : ∀ γ, F.obj γ) (hx : ∀ {γ δ} (f : γ ⟶ δ), F.map f (x γ) = x δ) :
    Section (setFamily F) where
  obj γ := Discrete.mk (x γ)
  map f := eqToHom (congrArg Discrete.mk (hx f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def constantSection : Section (setFamily (family a X)) :=
  setSection _ SmoothQuotientDeformations.constant (fun f =>
    GlobalSectionDescent.transport_constant f)

/-- A usable family over every parameter, with both compatibility obligations
proved directly. No global reconstructed section is stored in the contract. -/
def constantFamily : LocalSection.ParameterFamily (a := a) A where
  sections _ := constantSection
  natural _ _ _ := by apply Deformation.ext; rfl
  matching _ _ _ _ := rfl

variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

/-- The public theorem recovers the complete local section at every local
parameter, not only at contexts known to extend globally. -/
example (g : Y ⟶ SplitSheaf.Ext A) :
    ((constantFamily (a := a) (A := A)).baseChange (g ≫ SplitSheaf.p A)).glue =
      constantSection (a := a) (X := Y) :=
  (constantFamily (a := a) (A := A)).recover_local_section g

/-- Further restriction applies to the whole parameter family and glued values. -/
example (f : Y ⟶ X) (P : Object a X) :
    restrict f ((((constantFamily (a := a) (A := A)).glue).obj P).as) =
      ((((constantFamily (a := a) (A := A)).baseChange f).glue).obj (reindex P f)).as :=
  (constantFamily (a := a) (A := A)).glue_natural f P

/-- The full local section recovery retains selected distinct quotient loops. -/
example (g : Y ⟶ SplitSheaf.Ext A) (P : Object a Y) (p q : P ⟶ P) (hpq : p ≠ q) :
    (((constantFamily (a := a) (A := A)).baseChange
      (g ≫ SplitSheaf.p A)).glue).lift.map p ≠
    (((constantFamily (a := a) (A := A)).baseChange
      (g ≫ SplitSheaf.p A)).glue).lift.map q := by
  intro h
  exact hpq (congrArg Grothendieck.Hom.base h)

/-- Identity-display cover gives an explicit instance at the nontrivial,
ineffective doubled-origin torsor, with its actual local parameter map. -/
example (K : Type) [Group K] (c : K) :
    let B := SplitSheaf.ofDisplay (𝟙 SmoothClutching.base)
    let g := (SplitSheaf.displayIso (𝟙 SmoothClutching.base)).inv
    let s := constantFamily (a := ActionQuotientEvidence.ineffective K) (A := B)
    (((s.baseChange (g ≫ SplitSheaf.p B)).glue).obj
      (ActionQuotientEvidence.nontrivialObject K c)).as =
      SmoothQuotientDeformations.constant (ActionQuotientEvidence.nontrivialObject K c) :=
  (constantFamily (a := ActionQuotientEvidence.ineffective K)
    (A := SplitSheaf.ofDisplay (𝟙 SmoothClutching.base))).recover_local
      (SplitSheaf.displayIso (𝟙 SmoothClutching.base)).inv _

end Examples.ParameterDeformationSections
