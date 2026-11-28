import Applications.AlgebraicGeometry.Polynomial
import Mathlib.AlgebraicGeometry.AffineSpace

/-! Actual affine scheme morphisms over the coefficient base, with exact
coordinate recovery and an independently assembled cartesian compiler target. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
namespace PolynomialMap
variable (R σ τ : Type) [CommRing R]
abbrev coefficient (σ : Type) : CommRingCat.of R ⟶ CommRingCat.of (MvPolynomial σ R) :=
  CommRingCat.ofHom C
abbrev leftInclusion : CommRingCat.of (MvPolynomial σ R) ⟶ CommRingCat.of (MvPolynomial (σ ⊕ τ) R) :=
  CommRingCat.ofHom (rename Sum.inl).toRingHom
abbrev rightInclusion : CommRingCat.of (MvPolynomial τ R) ⟶ CommRingCat.of (MvPolynomial (σ ⊕ τ) R) :=
  CommRingCat.ofHom (rename Sum.inr).toRingHom

theorem coefficient_square : coefficient R σ ≫ leftInclusion R σ τ =
    coefficient R τ ≫ rightInclusion R σ τ := by
  ext r; simp

def sumDesc (s : PushoutCocone (coefficient R σ) (coefficient R τ)) :
    CommRingCat.of (MvPolynomial (σ ⊕ τ) R) ⟶ s.pt :=
  CommRingCat.ofHom (eval₂Hom (s.inl.hom.comp C)
    (Sum.elim (fun i => s.inl (X i)) (fun j => s.inr (X j))))

theorem sumDesc_left (s : PushoutCocone (coefficient R σ) (coefficient R τ)) :
    leftInclusion R σ τ ≫ sumDesc R σ τ s = s.inl := by
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro r; simp [sumDesc]
  · intro i; simp [sumDesc]

theorem sumDesc_right (s : PushoutCocone (coefficient R σ) (coefficient R τ)) :
    rightInclusion R σ τ ≫ sumDesc R σ τ s = s.inr := by
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    simpa [sumDesc] using ConcreteCategory.congr_hom s.condition r
  · intro i; simp [sumDesc]

theorem sumDesc_unique (s : PushoutCocone (coefficient R σ) (coefficient R τ))
    (m : CommRingCat.of (MvPolynomial (σ ⊕ τ) R) ⟶ s.pt)
    (hl : leftInclusion R σ τ ≫ m = s.inl)
    (hr : rightInclusion R σ τ ≫ m = s.inr) : m = sumDesc R σ τ s := by
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    simpa [sumDesc] using ConcreteCategory.congr_hom hl (C r)
  · intro i
    cases i with
    | inl i => simpa [sumDesc] using ConcreteCategory.congr_hom hl (X i)
    | inr i => simpa [sumDesc] using ConcreteCategory.congr_hom hr (X i)

theorem isPushout_polynomial : IsPushout (coefficient R σ) (coefficient R τ)
    (leftInclusion R σ τ) (rightInclusion R σ τ) :=
  IsPushout.of_isColimit (PushoutCocone.IsColimit.mk (coefficient_square R σ τ)
    (sumDesc R σ τ) (sumDesc_left R σ τ) (sumDesc_right R σ τ) (sumDesc_unique R σ τ))
end PolynomialMap

namespace AffinePolynomialCompiler
open FirstOrderCompiler MatrixCompiler PolynomialMap MvPolynomial
open CategoryTheory AlgebraicGeometry
variable (R : Type) [CommRing R]

abbrev CoordinateRing (a : Ty) := MvPolynomial (Slots a) R
abbrev space (a : Ty) : Scheme := Spec (CommRingCat.of (CoordinateRing R a))
def baseMap (a : Ty) : space R a ⟶ Spec (CommRingCat.of R) :=
  Spec.algebraMap R (CoordinateRing R a)

/-- All scheme morphisms over the base, not a wrapper containing polynomial code. -/
abbrev GeometricHom (a b : Ty) :=
  {f : space R a ⟶ space R b // f ≫ baseMap R b = baseMap R a}

def geometricEquiv {a b : Ty} : Code R a b ≃ GeometricHom R a b :=
  PolynomialMap.coordEquiv.trans Spec.homEquivAlgHom.symm

def realize {a b : Ty} (f : Code R a b) : GeometricHom R a b := geometricEquiv R f

def recover {a b : Ty} (f : GeometricHom R a b) : Code R a b := (geometricEquiv R).symm f

@[simp] theorem recover_realize {a b : Ty} (f : Code R a b) : recover R (realize R f) = f :=
  (geometricEquiv R).symm_apply_apply f
@[simp] theorem realize_recover {a b : Ty} (f : GeometricHom R a b) : realize R (recover R f) = f :=
  (geometricEquiv R).apply_symm_apply f

theorem realize_injective {a b : Ty} : Function.Injective (realize R : Code R a b → _) :=
  (geometricEquiv R).injective

@[simp] theorem realize_val {a b : Ty} (f : Code R a b) :
    (realize R f).val = Spec.map (CommRingCat.ofHom (coordHom f).toRingHom) := rfl

def geometricIdentity (a : Ty) : GeometricHom R a a := ⟨𝟙 _, by simp⟩
def geometricComp {a b c : Ty} (g : GeometricHom R b c) (f : GeometricHom R a b) :
    GeometricHom R a c := ⟨f.val ≫ g.val, by rw [Category.assoc, g.property, f.property]⟩

@[simp] theorem realize_identity (a : Ty) :
    realize R (PolynomialMap.identity : Code R a a) = geometricIdentity R a := by
  apply Subtype.ext
  simp [realize_val, geometricIdentity, PolynomialMap.identity, coordHom]

@[simp] theorem realize_comp {a b c : Ty} (g : Code R b c) (f : Code R a b) :
    realize R (PolynomialMap.comp g f) = geometricComp R (realize R g) (realize R f) := by
  apply Subtype.ext
  simp only [realize_val, coordHom_comp, geometricComp]
  rw [← Spec.map_comp]
  congr 1

/-- Comparison to Mathlib's ordinary affine space. -/
def affineSpaceIso (a : Ty) :
    AlgebraicGeometry.AffineSpace (Slots a) (Spec (CommRingCat.of R)) ≅ space R a :=
  AlgebraicGeometry.AffineSpace.SpecIso _ _

@[reassoc (attr := simp)] theorem affineSpaceIso_over (a : Ty) :
    (affineSpaceIso R a).inv ≫
      AlgebraicGeometry.AffineSpace (Slots a) (Spec (CommRingCat.of R)) ↘ Spec (CommRingCat.of R) =
      baseMap R a :=
  AlgebraicGeometry.AffineSpace.SpecIso_inv_over _

/-- The zero-coordinate affine scheme is the base itself. -/
instance unit_baseMap_isIso : IsIso (baseMap R .unit) := by
  let e : CommRingCat.of R ≅ CommRingCat.of (CoordinateRing R .unit) :=
    (MvPolynomial.isEmptyAlgEquiv R Empty).symm.toRingEquiv.toCommRingCatIso
  change IsIso (Spec.map e.hom)
  infer_instance

def unitIso : space R .unit ≅ Spec (CommRingCat.of R) := asIso (baseMap R .unit)

theorem terminal_unique {X : Scheme} (f : X ⟶ Spec (CommRingCat.of R))
    (g h : X ⟶ space R .unit) (hg : g ≫ baseMap R .unit = f)
    (hh : h ≫ baseMap R .unit = f) : g = h :=
  (cancel_mono (baseMap R .unit)).mp (hg.trans hh.symm)

/-- This is a pullback in all schemes, so the product property is not restricted
    to affine test objects or to points over the coefficient ring. -/
theorem product_isPullback (a b : Ty) :
    IsPullback (realize R (first R a b)).val (realize R (second R a b)).val
      (baseMap R a) (baseMap R b) := by
  have hl : coordHom (first R a b) = MvPolynomial.rename Sum.inl := by
    ext i; simp [first]
  have hr : coordHom (second R a b) = MvPolynomial.rename Sum.inr := by
    ext i; simp [second]
  simp only [realize_val, hl, hr]
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_polynomial R (Slots a) (Slots b))

def geometricPair {a b c : Ty} (f : GeometricHom R a b) (g : GeometricHom R a c) :
    GeometricHom R a (.prod b c) := realize R (pair R (recover R f) (recover R g))

def geometricTarget : Target (Prim R) where
  Hom := GeometricHom R
  ident := geometricIdentity R _
  comp := geometricComp R
  terminal := realize R Empty.elim
  fst := realize R (first R _ _)
  snd := realize R (second R _ _)
  pair := geometricPair R
  primitive p := realize R (primitive R p)

def realizationMap : SquareKit.RawMap (SquareKit.FirstOrderCategory.ops (target R))
    (SquareKit.FirstOrderCategory.ops (geometricTarget R)) where
  obj := id
  map := realize R

theorem realizationMap_laws : SquareKit.MapLaws (realizationMap R)
    (SquareKit.equality _) (SquareKit.equality _) where
  congr h := congrArg (realize R) h
  ident := realize_identity R _
  comp := realize_comp R

theorem realization_preserves : SquareKit.FirstOrderNaturality.Preserves
    (realizationMap R) (SquareKit.equality _)
    (SquareKit.FirstOrderNaturality.ofTarget (target R))
    (SquareKit.FirstOrderNaturality.ofTarget (geometricTarget R)) where
  terminal := rfl
  fst := rfl
  snd := rfl
  pair f g := by
    change realize R (pair R f g) = geometricPair R (realize R f) (realize R g)
    simp [geometricPair]
  primitive _ := rfl

/-- Shared interpretation preservation handles every source constructor, including let. -/
theorem compile_realize (t : Term (Prim R) Γ a) :
    realize R (compile (target R) t) = compile (geometricTarget R) t := by
  rw [← SquareKit.FirstOrderNaturality.compile_ofTarget (target R),
    ← SquareKit.FirstOrderNaturality.compile_ofTarget (geometricTarget R)]
  exact SquareKit.FirstOrderNaturality.naturality
    (F := realizationMap R)
    (M := SquareKit.FirstOrderNaturality.ofTarget (target R))
    (N := SquareKit.FirstOrderNaturality.ofTarget (geometricTarget R))
    (realizationMap_laws R) (SquareKit.equality_congr _)
    ⟨fun hf hg => congrArg₂ (geometricPair R) hf hg⟩
    (realization_preserves R) t

/-- Exact recovery is stronger than agreement on points of one coefficient ring. -/
theorem recover_compile (t : Term (Prim R) Γ a) :
    recover R (compile (geometricTarget R) t) = compile (target R) t := by
  rw [← compile_realize, recover_realize]

variable (A : Type) [CommRing A] [Algebra R A]
/-- A-valued points are actual maps Spec A → the affine space over Spec R. -/
abbrev Points (a : Ty) :=
  {f : Spec (CommRingCat.of A) ⟶ space R a //
    f ≫ baseMap R a = Spec.algebraMap R A}

def pointEquiv (a : Ty) : (Slots a → A) ≃ Points R A a :=
  { toFun := fun x => Spec.homEquivAlgHom.symm (aeval x)
    invFun := fun f i => Spec.homEquivAlgHom f (X i)
    left_inv := by intro x; funext i; simp
    right_inv := by
      intro f
      apply Spec.homEquivAlgHom.injective
      rw [Equiv.apply_symm_apply]
      exact (aeval_unique (Spec.homEquivAlgHom f)).symm }

@[simp] theorem pointEquiv_val (a : Ty) (x : Slots a → A) :
    (pointEquiv R A a x).val = Spec.map (CommRingCat.ofHom (aeval x).toRingHom) := rfl

def mapPoint {a b : Ty} (f : GeometricHom R a b) (x : Points R A a) : Points R A b :=
  ⟨x.val ≫ f.val, by rw [Category.assoc, f.property, x.property]⟩

/-- Evaluation describes the action of the actual scheme morphism on A-valued points. -/
theorem realize_point {a b : Ty} (f : Code R a b) (x : Slots a → A) :
    mapPoint R A (realize R f) (pointEquiv R A a x) =
      pointEquiv R A b (PolynomialMap.evaluate f x) := by
  apply Subtype.ext
  simp only [mapPoint, pointEquiv_val, realize_val]
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact congrArg (fun h : MvPolynomial (Slots b) R →ₐ[R] A => h p)
    (show (aeval x).comp (coordHom f) = aeval (PolynomialMap.evaluate f x) by
      ext i; simp [coordHom, PolynomialMap.evaluate])

theorem compile_points (t : Term (Prim R) Γ a) (x : Val A (context Γ)) :
    mapPoint R A (compile (geometricTarget R) t) (pointEquiv R A _ (encode _ x)) =
      pointEquiv R A a (encode a (eval (meaning R A) t x)) := by
  rw [← compile_realize, realize_point]
  congr 1
  have h := congrArg (encode a) (compile_correct R A t x)
  simpa only [denote, encode_decode] using h

end AffinePolynomialCompiler

namespace AffinePolynomialCompiler
open FirstOrderCompiler MatrixCompiler PolynomialMap MvPolynomial CategoryTheory AlgebraicGeometry
variable (R : Type) [CommRing R]

theorem geometricPair_first {a b c : Ty} (f : GeometricHom R a b) (g : GeometricHom R a c) :
    geometricComp R (realize R (first R b c)) (geometricPair R f g) = f := by
  rw [geometricPair, ← realize_comp, ← realize_recover R f]
  apply congrArg (realize R)
  funext i
  simp [PolynomialMap.comp, first, pair]

theorem geometricPair_second {a b c : Ty} (f : GeometricHom R a b) (g : GeometricHom R a c) :
    geometricComp R (realize R (second R b c)) (geometricPair R f g) = g := by
  rw [geometricPair, ← realize_comp, ← realize_recover R g]
  apply congrArg (realize R)
  funext i
  simp [PolynomialMap.comp, second, pair]

theorem geometricPair_unique {a b c : Ty} (f : GeometricHom R a b) (g : GeometricHom R a c)
    (h : GeometricHom R a (.prod b c))
    (hf : geometricComp R (realize R (first R b c)) h = f)
    (hg : geometricComp R (realize R (second R b c)) h = g) : h = geometricPair R f g := by
  apply Subtype.ext
  apply (product_isPullback R b c).hom_ext
  · exact congrArg Subtype.val (hf.trans (geometricPair_first R f g).symm)
  · exact congrArg Subtype.val (hg.trans (geometricPair_second R f g).symm)

variable (A : Type) [CommRing A] [Algebra R A]
variable {B : Type} [CommRing B] [Algebra R B]

theorem pointEquiv_change (a : Ty) (h : A →ₐ[R] B) (x : Slots a → A) :
    (pointEquiv R B a (fun i => h (x i))).val =
      Spec.map (CommRingCat.ofHom h.toRingHom) ≫ (pointEquiv R A a x).val := by
  simp only [pointEquiv_val]
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (MvPolynomial.comp_aeval x h).symm

/-- Change of the point algebra is precomposition of actual scheme morphisms. -/
theorem mapPoint_natural {a b : Ty} (f : GeometricHom R a b)
    (h : A →ₐ[R] B) (x : Slots a → A) :
    Spec.map (CommRingCat.ofHom h.toRingHom) ≫
        (mapPoint R A f (pointEquiv R A a x)).val =
      (mapPoint R B f (pointEquiv R B a (fun i => h (x i)))).val := by
  simp only [mapPoint, pointEquiv_change R A a h x, Category.assoc]
end AffinePolynomialCompiler
