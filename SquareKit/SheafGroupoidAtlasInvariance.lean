import SquareKit.SheafGroupoidCompletionEquivalence
import SquareKit.SheafGroupoidAtlasComparison

/-! Covering changes of object atlas preserve general sheaf-groupoid completion. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Chart
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Operations J} [G.Laws]
variable {U V : Sheaf J (Type (max u v))} {p : U ⟶ G.objects} {q : V ⟶ G.objects}
variable (D : Chart G p p) (E : Chart G q q)
variable (r : U ⟶ V) (comm : r ≫ q = p)

def atlasMapFullyFaithful (X : Sheaf J (Type (max u v))) :
    (D.atlasMap (T := X) E r comm).FullyFaithful := by
  letI := (E.fullyFaithful (T := X)).faithful
  apply Functor.FullyFaithful.ofCompFaithful (G := E.toGroupoid)
  rw [D.atlasMap_toGroupoid E r comm]
  exact D.fullyFaithful

def representedMapFullyFaithful (X : Sheaf J (Type (max u v))) :
    (StackDescentTransformation.component (D.representedMap E r comm) X).FullyFaithful :=
  (D.atlasPresentationEquivalence.fullyFaithfulFunctor.comp
    (D.atlasMapFullyFaithful E r comm X)).comp E.atlasPresentationEquivalence.symm.fullyFaithfulFunctor

theorem representedMapLocallyGenerating [Presheaf.IsLocallySurjective J r.hom] :
    StackLocalGeneration.LocallyGenerating (SheafCover.topology (J := J))
      (D.representedMap E r comm) := by
  intro X m
  obtain ⟨Y, f, n, hf, hn⟩ := SheafCover.cover_pullback r m.map
  refine ⟨Y, f, ⟨Y, f, hf, Sieve.ofArrows_mk _ _ ()⟩, ⟨n⟩, ⟨eqToIso ?_⟩⟩
  exact congrArg Operations.Object.mk hn

def ambientFullyFaithful (X : Sheaf J (Type (max u v))) :
    (StackDescentTransformation.component D.ambientTransformation X).FullyFaithful :=
  D.atlasPresentationEquivalence.fullyFaithfulFunctor.comp D.fullyFaithful

theorem ambientLocallyGenerating [Presheaf.IsLocallySurjective J p.hom] :
    StackLocalGeneration.LocallyGenerating (SheafCover.topology (J := J))
      D.ambientTransformation := by
  intro X m
  obtain ⟨Y, f, n, hf, hn⟩ := SheafCover.cover_pullback p m.map
  refine ⟨Y, f, ⟨Y, f, hf, Sieve.ofArrows_mk _ _ ()⟩, ⟨n⟩, ⟨eqToIso ?_⟩⟩
  exact congrArg Operations.Object.mk hn
end SquareKit.SheafGroupoid.Chart

namespace SquareKit.SheafGroupoid.Chart
open CategoryTheory Opposite Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Operations J} [G.Laws]
variable {U V : Sheaf J (Type (max u v))} {p : U ⟶ G.objects} {q : V ⟶ G.objects}
variable (D : Chart G p p) (E : Chart G q q)
variable (r : U ⟶ V) (comm : r ≫ q = p)

/-- A covering source atlas suffices even when the refinement map itself is not a cover. -/
theorem representedMapLocallyGenerating_of_sourceCover
    [Presheaf.IsLocallySurjective J p.hom] :
    StackLocalGeneration.LocallyGenerating (SheafCover.topology (J := J))
      (D.representedMap E r comm) := by
  intro X m
  obtain ⟨Y, f, n, hf, hn⟩ := SheafCover.cover_pullback p (m.map ≫ q)
  refine ⟨Y, f, ⟨Y, f, hf, Sieve.ofArrows_mk _ _ ()⟩, ⟨n⟩, ⟨?_⟩⟩
  apply (E.ambientFullyFaithful Y).preimageIso
  apply eqToIso
  apply congrArg Operations.Object.mk
  change (n ≫ r) ≫ q = (f ≫ m.map) ≫ q
  simpa only [Category.assoc, comm] using hn

def completedEquivalence [Presheaf.IsLocallySurjective J r.hom] :
    Bicategory.Equivalence (Bundle.pseudofunctor D.atlasOperations)
      (Bundle.pseudofunctor E.atlasOperations) :=
  Bundle.completeMapEquivalence (D.representedMap E r comm)
    (D.representedMapFullyFaithful E r comm) (D.representedMapLocallyGenerating E r comm)

def completedEquivalenceOfSourceCover [Presheaf.IsLocallySurjective J p.hom] :
    Bicategory.Equivalence (Bundle.pseudofunctor D.atlasOperations)
      (Bundle.pseudofunctor E.atlasOperations) :=
  Bundle.completeMapEquivalence (D.representedMap E r comm)
    (D.representedMapFullyFaithful E r comm)
    (D.representedMapLocallyGenerating_of_sourceCover E r comm)

@[simp] theorem completedEquivalence_hom [Presheaf.IsLocallySurjective J r.hom] :
    (D.completedEquivalence E r comm).hom = D.completedMap E r comm := rfl

@[simp] theorem completedEquivalenceOfSourceCover_hom [Presheaf.IsLocallySurjective J p.hom] :
    (D.completedEquivalenceOfSourceCover E r comm).hom = D.completedMap E r comm := rfl

def completedAmbientEquivalence [Presheaf.IsLocallySurjective J p.hom] :
    Bicategory.Equivalence (Bundle.pseudofunctor D.atlasOperations) (Bundle.pseudofunctor G) :=
  Bundle.completeMapEquivalence D.ambientTransformation D.ambientFullyFaithful
    D.ambientLocallyGenerating

@[simp] theorem completedAmbientEquivalence_hom [Presheaf.IsLocallySurjective J p.hom] :
    D.completedAmbientEquivalence.hom = D.completedAmbient := rfl

def completedFiberEquivalence [Presheaf.IsLocallySurjective J r.hom]
    (X : Sheaf J (Type (max u v))) : Bundle.Principal D.atlasOperations X ≌
      Bundle.Principal E.atlasOperations X :=
  Bundle.completeMapComponentEquivalence (D.representedMap E r comm)
    (D.representedMapFullyFaithful E r comm) (D.representedMapLocallyGenerating E r comm) X

def completedFiberEquivalenceOfSourceCover [Presheaf.IsLocallySurjective J p.hom]
    (X : Sheaf J (Type (max u v))) : Bundle.Principal D.atlasOperations X ≌
      Bundle.Principal E.atlasOperations X :=
  Bundle.completeMapComponentEquivalence (D.representedMap E r comm)
    (D.representedMapFullyFaithful E r comm)
    (D.representedMapLocallyGenerating_of_sourceCover E r comm) X

variable (T : Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ)
  Cat.{max u v, max (u + 1) (v + 1)}) [T.IsStack (SheafCover.topology (J := J))]

def completedMappingEquivalence [Presheaf.IsLocallySurjective J r.hom] :
    (Bundle.pseudofunctor E.atlasOperations ⟶ T) ≌
      (Bundle.pseudofunctor D.atlasOperations ⟶ T) :=
  Bundle.completeMapMappingEquivalence (D.representedMap E r comm)
    (D.representedMapFullyFaithful E r comm) (D.representedMapLocallyGenerating E r comm) T

def completedMappingEquivalenceOfSourceCover [Presheaf.IsLocallySurjective J p.hom] :
    (Bundle.pseudofunctor E.atlasOperations ⟶ T) ≌
      (Bundle.pseudofunctor D.atlasOperations ⟶ T) :=
  Bundle.completeMapMappingEquivalence (D.representedMap E r comm)
    (D.representedMapFullyFaithful E r comm)
    (D.representedMapLocallyGenerating_of_sourceCover E r comm) T

end SquareKit.SheafGroupoid.Chart
