import SquareKit.SheafGroupoidBundleLocal
import SquareKit.StackificationUniversal

/-! The regular-bundle unit and its full mapping-category comparison. Effective
bundle descent is a separate obligation from this comparison. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bundle
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (G : Operations J) [G.Laws]

abbrev functor : (Sheaf J (Type (max u v)))ᵒᵖ ⥤ Cat where
  obj X := Cat.of (Principal G X.unop)
  map r := (restriction r.unop).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev pseudofunctor := (functor G).toPseudofunctor'

/-- The actual regular bundle, on objects and arrows, defines the unit. -/
def unit : G.pseudofunctor ⟶ pseudofunctor G where
  app X := (regularFunctor G (X := X.as.unop)).toCatHom
  naturality _ := Iso.refl _
  naturality_naturality := by
    intro X Y f g h
    obtain rfl := LocallyDiscrete.eq_of_hom h
    have hh : h = 𝟙 f := Subsingleton.elim _ _
    subst h
    simp only [PrelaxFunctor.map₂_id]
    apply Cat.Hom₂.ext
    ext m
    simp
  naturality_id X := by
    cases X
    apply Cat.Hom₂.ext
    ext m
    dsimp [Operations.pseudofunctor, Operations.functor, pseudofunctor, functor,
      Functor.toPseudofunctor']
    simp
    exact ((regularFunctor G).map_id _).symm
  naturality_comp f g := by
    cases f
    cases g
    apply Cat.Hom₂.ext
    ext m
    exact (regularMap_id G _).symm

/-- Every bundle is regular on its own locally surjective total-space cover. -/
theorem locallyGenerating : StackLocalGeneration.LocallyGenerating
    (SheafCover.topology (J := J)) (unit G) := by
  intro X P
  refine ⟨total P, projection P, ?_, localObject P, ⟨localIso P⟩⟩
  exact ⟨total P, projection P, P.isLocallySurjective, Sieve.ofArrows_mk _ _ ()⟩

variable (T : Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ)
  Cat.{max u v, max (u + 1) (v + 1)}) [T.IsStack (SheafCover.topology (J := J))]

/-- Actual precomposition is an equivalence on full categories of transformations. -/
def universalEquivalence : (pseudofunctor G ⟶ T) ≌ (G.pseudofunctor ⟶ T) :=
  StackificationUniversal.universalEquivalence (fun _ => regularFullyFaithful G)
    (locallyGenerating G) T

@[simp] theorem universalEquivalence_functor : (universalEquivalence G T).functor =
    StackLocalGeneration.restriction (unit G) T := rfl

def modificationEquiv (Φ Ψ : pseudofunctor G ⟶ T) :
    (Φ ⟶ Ψ) ≃ (unit G ≫ Φ ⟶ unit G ≫ Ψ) :=
  (universalEquivalence G T).fullyFaithfulFunctor.homEquiv

end SquareKit.SheafGroupoid.Bundle
