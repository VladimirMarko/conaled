import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Types

/-! A concrete presentation of the actual constant sheaf on a topological space.
The identification with sheafification is proved by local bijectivity. -/
noncomputable section
namespace SquareKit.LocallyConstantSheaf
open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (X : TopCat.{0})
abbrev site := Opens.grothendieckTopology X
abbrev Sh := Sheaf (site X) (Type 0)

def data (A : Type) : (Opens X)ᵒᵖ ⥤ Type where
  obj U := LocallyConstant U.unop A
  map f := ↾fun s => s.comap ⟨f.unop, (Opens.isOpenEmbedding_of_le f.unop.le).continuous⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem data_isSheaf (A : Type) : Presheaf.IsSheaf (site X) (data X A) := by
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  let P := TopCat.continuousLocal X A
  let e : TopCat.subpresheafToTypes P.toPrelocalPredicate ≅ data X A :=
    NatIso.ofComponents (fun U =>
      (show { f : U.unop → A // Continuous f } ≃ LocallyConstant U.unop A from
        { toFun := fun f => ⟨f.val, (IsLocallyConstant.iff_continuous _).mpr f.property⟩
          invFun := fun f => ⟨f, f.continuous⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }).toIso)
      (by intro U V f; rfl)
  exact (Presheaf.isSheaf_of_iso_iff e).mp (TopCat.subpresheafToTypes.isSheaf P)

abbrev obj (A : Type) : Sh X := ⟨data X A, data_isSheaf X A⟩

def map {A B : Type} (f : A → B) : obj X A ⟶ obj X B :=
  ⟨{ app _ := ↾fun s => s.map f }⟩

def delta : Type ⥤ Sh X where
  obj := obj X
  map f := map X f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Constants give a locally bijective map from the constant presheaf. -/
def unit (A : Type) : (Functor.const (Opens X)ᵒᵖ).obj A ⟶ data X A where
  app U := ↾fun a => LocallyConstant.const U.unop a

instance unit_locallyInjective (A : Type) : Presheaf.IsLocallyInjective (site X) (unit X A) where
  equalizerSieve_mem {U} a b h := by
    intro x hx
    refine ⟨U.unop, 𝟙 _, ?_, hx⟩
    change a = b
    exact congrArg (fun s : LocallyConstant U.unop A => s ⟨x, hx⟩) h

instance unit_locallySurjective (A : Type) : Presheaf.IsLocallySurjective (site X) (unit X A) where
  imageSieve_mem {U} s := by
    change LocallyConstant U A at s
    intro x hx
    let V : Opens X := ⟨Subtype.val '' { y : U | s y = s ⟨x, hx⟩ },
      U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ (s.isLocallyConstant.isOpen_fiber _)⟩
    have hVU : V ≤ U := by rintro _ ⟨y, _, rfl⟩; exact y.property
    refine ⟨V, homOfLE hVU, ?_, ?_⟩
    · refine ⟨s ⟨x, hx⟩, ?_⟩
      apply LocallyConstant.ext
      intro y
      obtain ⟨z, hz, he⟩ := y.property
      change s ⟨x, hx⟩ = s ⟨y.val, hVU y.property⟩
      simpa only [← he] using hz.symm
    · exact ⟨⟨x, hx⟩, rfl, rfl⟩

/-- This is the usual constant sheaf, not the constant presheaf. -/
def constantIso (A : Type) : (constantSheaf (site X) (Type 0)).obj A ≅ obj X A := by
  haveI : IsIso ((presheafToSheaf (site X) (Type 0)).map (unit X A)) :=
    ((site X).W_iff _).mp ((site X).W_of_isLocallyBijective (unit X A))
  exact asIso ((presheafToSheaf (site X) (Type 0)).map (unit X A)) ≪≫
    asIso ((sheafificationAdjunction (site X) (Type 0)).counit.app (obj X A))

theorem unit_natural {A B : Type} (f : A ⟶ B) :
    (Functor.const (Opens X)ᵒᵖ).map f ≫ unit X B =
      unit X A ≫ (map X f).hom := rfl

/-- The identification is natural in the set, so delta is the constant-sheaf functor. -/
def constantFunctorIso : constantSheaf (site X) (Type 0) ≅ delta X :=
  NatIso.ofComponents (constantIso X) (by
    intro A B f
    change (presheafToSheaf (site X) (Type 0)).map ((Functor.const _).map f) ≫
      ((presheafToSheaf (site X) (Type 0)).map (unit X B) ≫
        (sheafificationAdjunction (site X) (Type 0)).counit.app (obj X B)) =
      ((presheafToSheaf (site X) (Type 0)).map (unit X A) ≫
        (sheafificationAdjunction (site X) (Type 0)).counit.app (obj X A)) ≫ map X f
    rw [← Functor.map_comp_assoc, unit_natural, Functor.map_comp, Category.assoc]
    exact congrArg (fun k => (presheafToSheaf (site X) (Type 0)).map (unit X A) ≫ k)
      ((sheafificationAdjunction (site X) (Type 0)).counit.naturality (map X f)))

end SquareKit.LocallyConstantSheaf
