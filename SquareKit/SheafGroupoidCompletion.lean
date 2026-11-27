import SquareKit.SheafGroupoidAction
import SquareKit.SheafGroupoidChartPresentation
import SquareKit.SheafActionPresentationRecovery

/-! Completion of represented action groupoids by the constructed torsor stack.
The input retains actual arrows in any isomorphic arrow representation. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoidCompletion
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
private def postcomposeSquare {B : Type*} [Bicategory B] {W X Y Z : B}
    (f : W ⟶ X) (g : X ⟶ Y) (h : W ⟶ Y) (e : f ≫ g ≅ h) (k : Y ⟶ Z) :
    f ≫ (g ≫ k) ≅ h ≫ k :=
  (Bicategory.associator f g k).symm ≪≫ (Bicategory.postcomp W k).mapIso e

private def precomposeSquare {B : Type*} [Bicategory B] {W X Y Z : B}
    (f : W ⟶ X) (g : X ⟶ Y) (h : W ⟶ Y) (e : f ≫ g ≅ h) :
    Bicategory.precomp Z g ⋙ Bicategory.precomp Z f ≅ Bicategory.precomp Z h :=
  (Bicategory.associatorNatIsoRight f g Z).symm ≪≫
    (Bicategory.precomposing W Y Z).mapIso e
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M A : Sheaf J (Type (max u v))}
variable (a : SheafActionQuotient.Action G M)
  (e : A ≅ SheafGroupoidAction.arrows (G := G) (M := M))

abbrev operations := (SheafGroupoidAction.operations a).changeArrows e
instance operations_laws : (operations a e).Laws :=
  (SheafGroupoidAction.operations a).changeArrows_laws e
abbrev presentation := (operations a e).pseudofunctor
/-- The output is the existing explicit torsor-and-equivariant-target construction. -/
abbrev completion := SheafActionQuotient.Stack.pseudofunctor a

variable {X Y : Sheaf J (Type (max u v))}

def toPresentation : (operations a e).Object X ⥤ SheafActionPresentation.Object a X :=
  (SheafGroupoidAction.operations a).changeFunctor e ⋙ SheafGroupoidAction.toPresentation a

def quotient : (operations a e).Object X ⥤ SheafActionQuotient.Object a X :=
  toPresentation a e ⋙ SheafActionPresentation.quotient a

def toPresentationFullyFaithful : (toPresentation (X := X) a e).FullyFaithful :=
  ((SheafGroupoidAction.operations a).changeFullyFaithful e).comp
    (SheafGroupoidAction.fullyFaithful a)

def quotientFullyFaithful : (quotient (X := X) a e).FullyFaithful :=
  (toPresentationFullyFaithful a e).comp (SheafActionPresentation.quotientFullyFaithful a)

/-- The original chart presentation is recovered without strengthening its action assumptions. -/
def presentationEquivalence : (operations a e).Object X ≌ SheafActionPresentation.Object a X := by
  letI := (toPresentationFullyFaithful (X := X) a e).full
  letI := (toPresentationFullyFaithful (X := X) a e).faithful
  letI : (toPresentation (X := X) a e).EssSurj :=
    ⟨fun m => ⟨⟨m.map⟩, ⟨Iso.refl _⟩⟩⟩
  letI : (toPresentation (X := X) a e).IsEquivalence := {}
  exact (toPresentation a e).asEquivalence

def presentationTransformation : presentation a e ⟶ SheafActionPresentation.pseudofunctor a :=
  Pseudofunctor.StrongTrans.vcomp
    ((SheafGroupoidAction.operations a).changeTransformation e)
    (SheafGroupoidAction.transformation a)

/-- Actual-arrow recovery followed by the constructed regular torsor. -/
def unit : presentation a e ⟶ completion a :=
  Pseudofunctor.StrongTrans.vcomp (presentationTransformation a e)
    (SheafActionPresentation.transformation a)

@[simp] theorem quotient_restriction (r : Y ⟶ X) :
    (operations a e).restriction r ⋙ quotient a e =
      quotient a e ⋙ SheafActionQuotient.restriction r := rfl

/-- The unit remembers the original full inverse label at every parameter. -/
theorem quotient_label {m n : (operations a e).Object X} (f : m ⟶ n) :
    SheafActionQuotient.arrowLabel ((quotient a e).map f) =
      SheafTorsor.labelInv (f.map ≫ e.hom ≫ SheafGroupoidAction.label) :=
  SheafTorsor.regularArrowLabel_regularArrow _

/-- The existing total-space cover and tautological section generate the new input. -/
theorem locallyGenerating : StackLocalGeneration.LocallyGenerating
    (SheafCover.topology (J := J)) (unit a e) := by
  intro X P
  obtain ⟨Y, p, hp, m, hm⟩ := SheafActionPresentation.locallyGenerating a X P
  exact ⟨Y, p, hp, ⟨m.map⟩, hm⟩

/-- Arrows already descend; this completion does not identify distinct arrows. -/
instance isPrestack : (presentation a e).IsPrestack (SheafCover.topology (J := J)) :=
  StackObjectPropertyDescent.isPrestack_of_fullyFaithful (unit a e)
    (fun _ => quotientFullyFaithful a e) _

variable (T : Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ)
  Cat.{max u v, max (u + 1) (v + 1)}) [T.IsStack (SheafCover.topology (J := J))]

/-- Full mapping-category recovery, including modifications. -/
def universalEquivalence : (completion a ⟶ T) ≌ (presentation a e ⟶ T) :=
  StackificationUniversal.universalEquivalence (fun _ => quotientFullyFaithful a e)
    (locallyGenerating a e) T

@[simp] theorem universalEquivalence_functor : (universalEquivalence a e T).functor =
    StackLocalGeneration.restriction (unit a e) T := rfl

def modificationEquiv (Φ Ψ : completion a ⟶ T) :
    (Φ ⟶ Ψ) ≃ (unit a e ≫ Φ ⟶ unit a e ≫ Ψ) :=
  (universalEquivalence a e T).fullyFaithfulFunctor.homEquiv

/-- The extension is the existing cover-descent construction, with its full recovery. -/
def extensionRecovery (θ : presentation a e ⟶ T) :=
  StackificationUniversal.extensionRecovery (η := unit a e)
    (fun _ => quotientFullyFaithful a e) θ (locallyGenerating a e)

end SquareKit.SheafGroupoidCompletion

namespace SquareKit.SheafGroupoidCompletion
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M A U : Sheaf J (Type (max u v))}
variable (a : SheafActionQuotient.Action G M)
  (e : A ≅ SheafGroupoidAction.arrows (G := G) (M := M))
  {atlas : U ⟶ M} (D : SheafGroupoid.Chart (operations a e) atlas atlas)

/-- Branch coordinates enter the unit through their actual arrow assembly map. -/
def chartUnit : D.pseudofunctor ⟶ completion a :=
  Pseudofunctor.StrongTrans.vcomp D.transformation (unit a e)

def chartQuotient {X : Sheaf J (Type (max u v))} :
    D.Object X ⥤ SheafActionQuotient.Object a X := D.toGroupoid ⋙ quotient a e

def chartFullyFaithful {X : Sheaf J (Type (max u v))} :
    (chartQuotient (X := X) a e D).FullyFaithful :=
  D.fullyFaithful.comp (quotientFullyFaithful a e)

/-- Independent branch coordinates produce exactly the same quotient arrows. -/
theorem changeChart_quotient (E : SheafGroupoid.Chart (operations a e) atlas atlas)
    {X : Sheaf J (Type (max u v))} :
    D.changeFunctor (T := X) E ⋙ chartQuotient a e E = chartQuotient a e D := by
  change (D.changeFunctor E ⋙ E.toGroupoid) ⋙ quotient a e = _
  rw [D.changeFunctor_toGroupoid E]
  rfl

/-- Changing branch coordinates commutes with the completion unit as an invertible modification. -/
def chartUnitComparison (E : SheafGroupoid.Chart (operations a e) atlas atlas) :
    PseudofunctorCoherence.ModificationIso
      (Pseudofunctor.StrongTrans.vcomp (D.changeTransformation E) (chartUnit a e E))
      (chartUnit a e D) :=
  postcomposeSquare
    (B := Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ)
      Cat.{max u v, max (u + 1) (v + 1)})
    (D.changeTransformation E) E.transformation D.transformation
    (D.changeTransformation_toGroupoid E) (unit a e)

@[simp] theorem chartUnitComparison_hom_app
    (E : SheafGroupoid.Chart (operations a e) atlas atlas)
    (X : LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ) (m : D.Object X.as.unop) :
    ((chartUnitComparison a e D E).hom.as.app X).toNatTrans.app m =
      𝟙 ((chartQuotient a e D).obj m) := by
  change 𝟙 _ ≫ (quotient a e).map (𝟙 _) = 𝟙 _
  erw [(quotient a e).map_id, Category.comp_id]


section AtlasMap
variable {V : Sheaf J (Type (max u v))} {other : V ⟶ M}
  (E : SheafGroupoid.Chart (operations a e) other other)
  (r : U ⟶ V) (comm : r ≫ other = atlas)

/-- A change of object atlas preserves the full quotient functor. -/
theorem atlasMap_quotient {X : Sheaf J (Type (max u v))} :
    D.atlasMap (T := X) E r comm ⋙ chartQuotient a e E = chartQuotient a e D := by
  change (D.atlasMap E r comm ⋙ E.toGroupoid) ⋙ quotient a e = _
  rw [D.atlasMap_toGroupoid E r comm]
  rfl

/-- The actual atlas map commutes with completion as an invertible modification. -/
def atlasUnitComparison : PseudofunctorCoherence.ModificationIso
    (Pseudofunctor.StrongTrans.vcomp (D.atlasTransformation E r comm) (chartUnit a e E))
    (chartUnit a e D) :=
  postcomposeSquare
    (B := Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ)
      Cat.{max u v, max (u + 1) (v + 1)})
    (D.atlasTransformation E r comm) E.transformation D.transformation
    (D.atlasTransformation_toGroupoid E r comm) (unit a e)

/-- Atlas restriction compares full mapping functors, including modifications. -/
def atlasRestrictionComparison
    (T : Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ)
      Cat.{max u v, max (u + 1) (v + 1)}) :
    StackLocalGeneration.restriction (chartUnit a e E) T ⋙
        StackLocalGeneration.restriction (D.atlasTransformation E r comm) T ≅
      StackLocalGeneration.restriction (chartUnit a e D) T :=
  precomposeSquare
    (B := Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ)
      Cat.{max u v, max (u + 1) (v + 1)})
    (D.atlasTransformation E r comm) (chartUnit a e E) (chartUnit a e D)
    (atlasUnitComparison a e D E r comm)

end AtlasMap

/-- Arrow descent holds before completing any full arrow chart. -/
instance chartIsPrestack : D.pseudofunctor.IsPrestack (SheafCover.topology (J := J)) :=
  StackObjectPropertyDescent.isPrestack_of_fullyFaithful (chartUnit a e D)
    (fun _ => chartFullyFaithful a e D) _

/-- The torsor cover followed by the object-atlas cover supplies local branch coordinates. -/
theorem chartLocallyGenerating [Presheaf.IsLocallySurjective J atlas.hom] :
    StackLocalGeneration.LocallyGenerating (SheafCover.topology (J := J))
      (chartUnit a e D) := by
  intro X P
  obtain ⟨Y, p, hp, m, ⟨hm⟩⟩ := locallyGenerating a e X P
  obtain ⟨Z, q, n, hq, hn⟩ := SheafCover.cover_pullback atlas m.map
  have hq' : Sieve.ofArrows _ (fun _ : Unit => q) ∈
      SheafCover.topology (J := J) Y :=
    ⟨Z, q, hq, Sieve.ofArrows_mk _ _ ()⟩
  refine ⟨Z, q ≫ p,
    StackObjectPropertyDescent.singleton_comp _ p q hp hq', ⟨n⟩, ⟨?_⟩⟩
  have hobj : (D.toGroupoid).obj (⟨n⟩ : D.Object Z) =
      ((operations a e).restriction q).obj m := by
    exact congrArg SheafGroupoid.Operations.Object.mk hn
  exact (quotient a e).mapIso (eqToIso hobj) ≪≫
    StackLocalGeneration.refinedImageIso (unit a e) p q hm

variable [Presheaf.IsLocallySurjective J atlas.hom]
variable (T : Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ)
  Cat.{max u v, max (u + 1) (v + 1)}) [T.IsStack (SheafCover.topology (J := J))]

/-- Completion of a branch presentation is the same constructed torsor stack. -/
def chartUniversalEquivalence : (completion a ⟶ T) ≌ (D.pseudofunctor ⟶ T) :=
  StackificationUniversal.universalEquivalence (fun _ => chartFullyFaithful a e D)
    (chartLocallyGenerating a e D) T

@[simp] theorem chartUniversalEquivalence_functor :
    (chartUniversalEquivalence a e D T).functor =
      StackLocalGeneration.restriction (chartUnit a e D) T := rfl

def chartModificationEquiv (Φ Ψ : completion a ⟶ T) :
    (Φ ⟶ Ψ) ≃ (chartUnit a e D ≫ Φ ⟶ chartUnit a e D ≫ Ψ) :=
  (chartUniversalEquivalence a e D T).fullyFaithfulFunctor.homEquiv

/-- The full mapping-category comparison is induced by the independently defined coordinate change. -/
def changeChartRestrictionComparison
    (E : SheafGroupoid.Chart (operations a e) atlas atlas) :
    (chartUniversalEquivalence a e E T).functor ⋙
        StackLocalGeneration.restriction (D.changeTransformation E) T ≅
      (chartUniversalEquivalence a e D T).functor :=
  precomposeSquare
    (B := Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ)
      Cat.{max u v, max (u + 1) (v + 1)})
    (D.changeTransformation E) (chartUnit a e E) (chartUnit a e D)
    (chartUnitComparison a e D E)

/-- Recovery includes arbitrary substitution and covering refinements. -/
def chartExtensionRecovery (θ : D.pseudofunctor ⟶ T) :=
  StackificationUniversal.extensionRecovery (η := chartUnit a e D)
    (fun _ => chartFullyFaithful a e D) θ (chartLocallyGenerating a e D)

end SquareKit.SheafGroupoidCompletion
