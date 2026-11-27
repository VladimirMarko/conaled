import SquareKit.SheafActionQuotientStack
import SquareKit.StackLocalGeneration
import SquareKit.StackObjectPropertyDescent
import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty

/-! Globally trivializable objects inside the torsor action quotient. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.SheafActionStackification

open CategoryTheory Opposite
open SheafActionQuotient

universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M : Sheaf J (Type (max u v))}
variable (a : Action G M)

/-- The full subcategory condition forgets the choice of a trivialization,
while retaining every equivariant arrow between the objects. -/
def globallyTrivial : (Stack.pseudofunctor a).ObjectProperty where
  prop _ P := Nonempty (SplitSheaf.Tm P.torsor.family)

instance : (globallyTrivial a).IsClosedUnderMapObj where
  map_obj h f := by
    obtain ⟨t⟩ := h
    exact ⟨SplitSheaf.tmSub t f.as.unop⟩

/-- The local presentation of globally trivializable quotient objects. -/
abbrev presentation := (globallyTrivial a).fullsubcategory

/-- Inclusion retains all arrows, including ineffective stabilizers. -/
abbrev unit := (globallyTrivial a).ι

/-- A quotient object becomes trivial on the total space of its own torsor. -/
theorem locallyGenerating :
    StackLocalGeneration.LocallyGenerating (SheafCover.topology (J := J)) (unit a) := by
  intro X P
  refine ⟨SplitSheaf.extension P.torsor.family, SplitSheaf.p P.torsor.family, ?_,
    ⟨reindex P (SplitSheaf.p P.torsor.family), ⟨SplitSheaf.q P.torsor.family⟩⟩,
    ⟨Iso.refl _⟩⟩
  exact ⟨_, _, inferInstance, Sieve.ofArrows_mk _ _ ()⟩

/-- Full faithfulness is inherited from the full subcategory inclusion. -/
def unitFullyFaithful (X : Sheaf J (Type (max u v))) :
    ((unit a).app (.mk (op X))).toFunctor.FullyFaithful :=
  ((globallyTrivial a).prop (.mk (op X))).fullyFaithfulι

/-- Arrow descent already holds before completing the local objects. -/
instance isPrestack : (presentation a).IsPrestack (SheafCover.topology (J := J)) :=
  StackObjectPropertyDescent.isPrestack_of_fullyFaithful (unit a)
    (unitFullyFaithful a) _

variable {a} {X : Sheaf J (Type (max u v))}

/-- The canonical total-space cover presents every quotient object by globally
trivializable local objects. -/
def canonicalData (P : Object a X) : (presentation a).DescentData
    (fun _ : Unit => SplitSheaf.p P.torsor.family) :=
  StackObjectPropertyDescent.lift (globallyTrivial a)
    (((Stack.pseudofunctor a).toDescentData
      (fun _ : Unit => SplitSheaf.p P.torsor.family)).obj P)
    (fun _ => ⟨SplitSheaf.q P.torsor.family⟩)

/-- Effective realization of this canonical datum forces global triviality. -/
theorem section_of_effective_canonicalData (P : Object a X)
    (N : (globallyTrivial a).Obj (.mk (op X)))
    (e : ((presentation a).toDescentData
      (fun _ : Unit => SplitSheaf.p P.torsor.family)).obj N ≅ canonicalData P) :
    Nonempty (SplitSheaf.Tm P.torsor.family) := by
  let f := fun _ : Unit => SplitSheaf.p P.torsor.family
  have hf : Sieve.ofArrows _ f ∈ SheafCover.topology (J := J) X :=
    ⟨_, _, inferInstance, Sieve.ofArrows_mk _ _ ()⟩
  let e'' := StackObjectPropertyDescent.recoveryIso (globallyTrivial a)
    (SheafCover.topology (J := J)) hf P (fun _ => ⟨SplitSheaf.q P.torsor.family⟩) N e
  obtain ⟨t⟩ := N.property
  exact ⟨SheafTorsor.sectionOfArrow
    ((SheafTorsor.ofSection N.obj.torsor t).comp e''.hom.torsorArrow)⟩

end SquareKit.SheafActionStackification
