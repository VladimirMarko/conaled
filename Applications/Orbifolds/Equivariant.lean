import Mathlib.CategoryTheory.Action
import SquareKit.CategoryMap
import Squares

/-! Algebraic coordinate changes retain arrow labels and isotropy, including
ineffective actions. Smooth structure is supplied separately. -/

noncomputable section
open CategoryTheory MulAction
namespace Orbifolds

universe u
variable {G H K : Type*} {X Y Z : Type u} [Group G] [Group H] [Group K]
  [MulAction G X] [MulAction H Y] [MulAction K Z]

/-- An equivariant map induces a functor on action groupoids. -/
def actionFunctor (φ : G →* H) (f : X → Y) (hf : ∀ g x, f (g • x) = φ g • f x) :
    ActionCategory G X ⥤ ActionCategory H Y where
  obj x := ↑(f x.back)
  map a := Functor.Elements.homMk (φ a.hom) (by
    change φ a.hom • f _ = f _
    rw [← hf]
    exact congrArg f a.map_val)
  map_id _ := by apply Functor.Elements.Hom.ext; exact φ.map_one
  map_comp _ _ := by apply Functor.Elements.Hom.ext; exact φ.map_mul _ _

/-- Orbit descent only needs equivariance. -/
def orbitMap (φ : G →* H) (f : X → Y) (hf : ∀ g x, f (g • x) = φ g • f x) :
    Quotient (orbitRel G X) → Quotient (orbitRel H Y) :=
  Quotient.map f (by
    intro a b hab
    obtain ⟨g, rfl⟩ := hab
    exact ⟨φ g, (hf g b).symm⟩)

/-- Descent of an invariant observation along the orbit projection. -/
def invariantLift {W : Type*} (f : X → W) (hi : ∀ (g : G) x, f (g • x) = f x) :
    Quotient (orbitRel G X) → W := Quotient.lift f (by
  intro a b hab
  obtain ⟨g, rfl⟩ := hab
  exact hi g b)

/-- The quotient projection square. -/
def orbitSquare (φ : G →* H) (f : X → Y) (hf : ∀ g x, f (g • x) = φ g • f x) :
    Squares.Square ⟨X, Quotient (orbitRel G X), Quotient.mk _⟩
      ⟨Y, Quotient (orbitRel H Y), Quotient.mk _⟩ where
  impl := f
  spec := orbitMap φ f hf
  commutes _ := rfl

theorem orbitMap_id :
    orbitMap (MonoidHom.id G) (id : X → X) (fun _ _ => rfl) = id := by
  funext q
  exact Quotient.inductionOn q fun _ => rfl

theorem orbitMap_comp (φ : G →* H) (ψ : H →* K) (f : X → Y) (g : Y → Z)
    (hf : ∀ a x, f (a • x) = φ a • f x) (hg : ∀ b y, g (b • y) = ψ b • g y) :
    orbitMap (ψ.comp φ) (g ∘ f) (fun a x => by simp [hf, hg]) =
      orbitMap ψ g hg ∘ orbitMap φ f hf := by
  funext q
  exact Quotient.inductionOn q fun _ => rfl

/-- Quotient squares compose through the existing square consumer. -/
theorem orbitSquare_comp (φ : G →* H) (ψ : H →* K) (f : X → Y) (g : Y → Z)
    (hf : ∀ a x, f (a • x) = φ a • f x) (hg : ∀ b y, g (b • y) = ψ b • g y) :
    orbitSquare (ψ.comp φ) (g ∘ f) (fun a x => by simp [hf, hg]) =
      Squares.compose (orbitSquare ψ g hg) (orbitSquare φ f hf) := by
  apply Squares.Square.ext
  · intro x; rfl
  · intro q
    exact congrFun (orbitMap_comp φ ψ f g hf hg) q

/-- Coordinate changes are algebraic bijections; this layer imposes no smoothness. -/
structure CoordinateChange (φ : G ≃* H) (X Y : Type*) [MulAction G X] [MulAction H Y]
    extends X ≃ Y where
  equivariant : ∀ g x, toEquiv (g • x) = φ g • toEquiv x

namespace CoordinateChange
variable {φ : G ≃* H} (e : CoordinateChange φ X Y)

def symm : CoordinateChange φ.symm Y X where
  toEquiv := e.toEquiv.symm
  equivariant g y := e.toEquiv.injective (by
    simp only [Equiv.apply_symm_apply, e.equivariant, MulEquiv.apply_symm_apply])

def functor : ActionCategory G X ⥤ ActionCategory H Y :=
  actionFunctor φ.toMonoidHom e.toEquiv e.equivariant

instance : e.functor.Faithful where
  map_injective h := by
    apply Functor.Elements.Hom.ext
    exact φ.injective (congrArg Functor.Elements.Hom.hom h)

instance : e.functor.Full where
  map_surjective {a b} f := by
    refine ⟨Functor.Elements.homMk (φ.symm f.hom) ?_, ?_⟩
    · apply e.toEquiv.injective
      change e.toEquiv (φ.symm f.hom • a.back) = e.toEquiv b.back
      rw [e.equivariant, φ.apply_symm_apply]
      exact f.map_val
    · apply Functor.Elements.Hom.ext
      exact φ.apply_symm_apply _

instance : e.functor.EssSurj := e.functor.essSurj_of_surj (by
  intro y
  refine ⟨↑(e.toEquiv.symm y.back), ?_⟩
  change (↑(e.toEquiv (e.toEquiv.symm y.back)) : ActionCategory H Y) = y
  simp)

instance : e.functor.IsEquivalence where

/-- The equivalence retains the explicit equivariant functor as its forward map. -/
def groupoidEquivalence : ActionCategory G X ≌ ActionCategory H Y := e.functor.asEquivalence

/-- Isotropy comparison uses precisely the given group isomorphism. -/
def stabilizerEquiv (x : X) : stabilizer G x ≃* stabilizer H (e.toEquiv x) where
  toFun g := ⟨φ g, by
    change φ g • e.toEquiv x = e.toEquiv x
    rw [← e.equivariant, g.property]⟩
  invFun h := ⟨φ.symm h, by
    apply e.toEquiv.injective
    rw [e.equivariant, φ.apply_symm_apply]
    exact h.property⟩
  left_inv g := Subtype.ext (φ.symm_apply_apply g)
  right_inv h := Subtype.ext (φ.apply_symm_apply h)
  map_mul' _ _ := Subtype.ext (φ.map_mul _ _)

/-- Equivariant bijections descend to bijections of orbit spaces. -/
def quotientEquiv : Quotient (orbitRel G X) ≃ Quotient (orbitRel H Y) where
  toFun := orbitMap φ.toMonoidHom e.toEquiv e.equivariant
  invFun := orbitMap φ.symm.toMonoidHom e.symm.toEquiv e.symm.equivariant
  left_inv q := Quotient.inductionOn q fun x => congrArg (Quotient.mk _) (e.toEquiv.symm_apply_apply x)
  right_inv q := Quotient.inductionOn q fun y => congrArg (Quotient.mk _) (e.toEquiv.apply_symm_apply y)

/-- The standard SquareKit consumer requires no internal-language context. -/
def rawMap := SquareKit.RawMap.ofFunctor e.functor

theorem rawMap_laws : SquareKit.MapLaws e.rawMap (SquareKit.equality _) (SquareKit.equality _) :=
  SquareKit.RawMap.ofFunctor_laws e.functor

end CoordinateChange
end Orbifolds
