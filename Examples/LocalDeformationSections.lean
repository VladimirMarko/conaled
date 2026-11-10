import SquareKit.SmoothQuotientLocalSections
import Examples.GlobalSectionDescent

/-! Covering-context sections can supply matching deformation data without an
assumed global section or a trivialization of each torsor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Examples.LocalDeformationSections
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

/-- Constant deformation is a section on all objects over the cover. -/
def localConstant : Section (setFamily (family a (SplitSheaf.Ext A))) :=
  setSection _ SmoothQuotientDeformations.constant (fun f =>
    GlobalSectionDescent.transport_constant f)

/-- Its matching law follows from the quotient cocycle's actual value equation. -/
theorem localConstant_matching : LocalSection.Matching (localConstant (a := a) (A := A)) := by
  intro d x b c t p
  exact d.value_compatible x b c p

variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

/-- The public assembly theorem computes the resulting section at any cocycle. -/
example (d : Descent.Datum (a := a) A) :
    transport d.comparison (restrict (SplitSheaf.p A)
      (((LocalSection.glue (localConstant (a := a) (A := A)) localConstant_matching).obj
        d.object).as)) = SmoothQuotientDeformations.constant d.localObject :=
  LocalSection.glue_recover _ _ d

/-- Restricting the constant covering section supplies the input compatibility,
so the public gluing comparison applies after an arbitrary parameter map. -/
example (d : Descent.Datum (a := a) A) (f : Y ⟶ X) :
    transport (d.baseChangeComparison f)
      (restrict f (((LocalSection.glue (localConstant (a := a) (A := A))
        localConstant_matching).obj d.object).as)) =
    ((LocalSection.glue (localConstant (a := a) (A := SplitSheaf.tySub A f))
      localConstant_matching).obj (d.baseChange f).object).as := by
  apply LocalSection.glue_baseChange
  apply Deformation.ext
  rfl

/-- The assembled section is defined at the ineffective nontrivial torsor,
even without selecting a chart. -/
example (K : Type) [Group K] (c : K) (B : SplitSheaf.Ty SmoothClutching.base)
    [Presheaf.IsLocallySurjective topology (SplitSheaf.p B).hom] :
    Deformation (ActionQuotientEvidence.nontrivialObject K c) :=
  ((LocalSection.glue (localConstant (a := ActionQuotientEvidence.ineffective K) (A := B))
    localConstant_matching).obj (ActionQuotientEvidence.nontrivialObject K c)).as

end Examples.LocalDeformationSections
