import SquareKit.Kunneth
import SquareKit.AdjointComparison
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! Coherently indexed inputs for the ordinary Künneth calculation. The native
pseudofunctor retains all identity and composition coherence. -/
namespace SquareKit.Kunneth
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped CategoryTheory.Bicategory
universe u v w z
variable {C : Type u} [Category.{v} C]

/-- A contravariant indexed category, with monoidal pullbacks and chosen right
adjoints. No exceptional operations or invertibility laws are required. -/
structure Indexed (C : Type u) [Category.{v} C] where
  fibers : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{w,z}
  monoidal (X : C) : MonoidalCategory (fibers.obj ⟨op X⟩)
  symmetric (X : C) : @SymmetricCategory _ _ (monoidal X)
  pullBraided {X Y : C} (f : X ⟶ Y) :
    letI := monoidal Y
    letI := monoidal X
    letI := symmetric Y
    letI := symmetric X
    ((fibers.map f.op.toLoc).toFunctor).Braided
  push {X Y : C} (f : X ⟶ Y) : fibers.obj ⟨op X⟩ ⥤ fibers.obj ⟨op Y⟩
  adj {X Y : C} (f : X ⟶ Y) : (fibers.map f.op.toLoc).toFunctor ⊣ push f

attribute [instance] Indexed.monoidal Indexed.symmetric Indexed.pullBraided
namespace Indexed
variable (D : Indexed C)
abbrev Fiber (X : C) := D.fibers.obj ⟨op X⟩
abbrev pull {X Y : C} (f : X ⟶ Y) : D.Fiber Y ⥤ D.Fiber X :=
  (D.fibers.map f.op.toLoc).toFunctor

/-- The pullback comparison is extracted from the specified compositor. -/
def pullComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    D.pull (f ≫ g) ≅ D.pull g ⋙ D.pull f :=
  Cat.Hom.toNatIso (D.fibers.mapComp g.op.toLoc f.op.toLoc)

def pullId (X : C) : D.pull (𝟙 X) ≅ 𝟭 (D.Fiber X) :=
  Cat.Hom.toNatIso (D.fibers.mapId ⟨op X⟩)

/-- Both routes around a commuting base square, with their actual comparisons. -/
def square {W X Y S : C} {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (h : p ≫ f = q ≫ g) : D.pull f ⋙ D.pull p ≅ D.pull g ⋙ D.pull q :=
  (D.pullComp p f).symm ≪≫ eqToIso (congrArg (fun k : W ⟶ S => D.pull k) h) ≪≫
    D.pullComp q g

/-- The iterated pushforward is compared with the chosen pushforward along
its composite by uniqueness of right adjoints, retaining the chosen adjunction. -/
noncomputable def pushComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    D.push f ⋙ D.push g ≅ D.push (f ≫ g) :=
  ((D.adj g).comp (D.adj f)).rightAdjointUniq
    ((D.adj (f ≫ g)).ofNatIsoLeft (D.pullComp f g))

/-- Monoidal identity and composition comparisons, in addition to the native
pseudofunctor's associator and unitor laws. -/
structure Coherent : Prop where
  composition {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.IsMonoidal (D.pullComp f g).hom
  identity (X : C) : NatTrans.IsMonoidal
    (D.pullId X).hom

/-- Admissibility and laws belong to the indexed provider, separately from the
canonical maps. The pullback premise is an actual universal-property witness. -/
structure Proper where
  coherent : D.Coherent
  admissible : ∀ {X Y : C}, (X ⟶ Y) → Prop
  identity (X : C) : admissible (𝟙 X)
  composition {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} :
    admissible f → admissible g → admissible (f ≫ g)
  pullback {W X Y S : C} {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S} :
    IsPullback p q f g → admissible g → admissible p
  projection {X Y : C} (f : X ⟶ Y) : admissible f →
    ∀ (A : D.Fiber X) (B : D.Fiber Y), IsIso (Kunneth.projection (D.adj f) A B)
  baseChange {W X Y S : C} {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (h : IsPullback p q f g) : admissible g → ∀ B : D.Fiber Y,
      IsIso (Kunneth.baseChange (D.adj g) (D.adj p) (D.square h.w).hom B)

variable {D}
/-- The indexed Künneth map uses the adjunction-induced pushforward compositor. -/
noncomputable def kunneth {W X Y S : C} {p : W ⟶ X} {q : W ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (h : IsPullback p q f g)
    (A : D.Fiber X) (B : D.Fiber Y) :
    (D.push f).obj A ⊗ (D.push g).obj B ⟶
      (D.push (p ≫ f)).obj ((D.pull p).obj A ⊗ (D.pull q).obj B) :=
  Kunneth.map (D.adj f) (D.adj g) (D.adj p) (D.square h.w).hom A B ≫
    (D.pushComp p f).hom.app _

/-- Properness discharges exactly the three invertibility obligations in (K). -/
noncomputable def kunnethIso (laws : D.Proper)
    {W X Y S : C} {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (h : IsPullback p q f g) (hf : laws.admissible f) (hg : laws.admissible g)
    (A : D.Fiber X) (B : D.Fiber Y) :
    (D.push f).obj A ⊗ (D.push g).obj B ≅
      (D.push (p ≫ f)).obj ((D.pull p).obj A ⊗ (D.pull q).obj B) := by
  letI := laws.projection f hf A ((D.push g).obj B)
  letI := laws.baseChange h hg B
  letI := laws.projection p (laws.pullback h hg) ((D.pull q).obj B) A
  letI : IsIso (projectionRight (D.adj p) A ((D.pull q).obj B)) := by
    rw [projectionRight_eq]
    infer_instance
  exact Kunneth.iso (D.adj f) (D.adj g) (D.adj p) (D.square h.w).hom A B ≪≫
    (D.pushComp p f).app _

@[simp] theorem kunnethIso_hom (laws : D.Proper)
    {W X Y S : C} {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (h : IsPullback p q f g) (hf : laws.admissible f) (hg : laws.admissible g)
    (A : D.Fiber X) (B : D.Fiber Y) :
    (kunnethIso laws h hf hg A B).hom = kunneth h A B := rfl

/-- Counit characterization after converting to the chosen composite right
adjoint. The endpoint conversion is the canonical uniqueness isomorphism. -/
theorem kunneth_counit
    {W X Y S : C} {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (h : IsPullback p q f g) (A : D.Fiber X) (B : D.Fiber Y) :
    (((D.adj (p ≫ f)).ofNatIsoLeft (D.pullComp p f)).homEquiv _ _).symm
        (kunneth h A B) =
    (D.pull p).map (Functor.OplaxMonoidal.δ (D.pull f) _ _) ≫
      Functor.OplaxMonoidal.δ (D.pull p) _ _ ≫
      ((D.pull p).map ((D.adj f).counit.app A) ⊗ₘ
        ((D.square h.w).hom.app ((D.push g).obj B) ≫
          (D.pull q).map ((D.adj g).counit.app B))) := by
  unfold kunneth pushComp
  exact (AdjointComparison.uncurry ((D.adj f).comp (D.adj p))
    ((D.adj (p ≫ f)).ofNatIsoLeft (D.pullComp p f)) _).trans
    (counit_characterization (D.adj f) (D.adj g) (D.adj p) (D.square h.w).hom A B)

end Indexed
end SquareKit.Kunneth
