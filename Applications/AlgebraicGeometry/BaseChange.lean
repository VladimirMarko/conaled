import Applications.AlgebraicGeometry.AffineCompiler
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! Coefficient change and geometric base change for polynomial compilation. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped TensorProduct

namespace PolynomialMap
open MvPolynomial
variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
variable {σ τ υ : Type*}

def changeCoefficients (φ : R →+* S) (f : Map R σ τ) : Map S σ τ :=
  fun i => MvPolynomial.map φ (f i)

@[simp] theorem changeCoefficients_id (f : Map R σ τ) :
    changeCoefficients (RingHom.id R) f = f := by
  funext i; exact MvPolynomial.map_id (f i)

@[simp] theorem changeCoefficients_comp (ψ : S →+* T) (φ : R →+* S) (f : Map R σ τ) :
    changeCoefficients ψ (changeCoefficients φ f) = changeCoefficients (ψ.comp φ) f := by
  funext i; simp [changeCoefficients, MvPolynomial.map_map]

@[simp] theorem changeCoefficients_identity (φ : R →+* S) :
    changeCoefficients φ (identity (σ := σ)) = identity := by
  funext i; simp [changeCoefficients, identity]

theorem changeCoefficients_substitute (φ : R →+* S) (g : Map R τ υ) (f : Map R σ τ) :
    changeCoefficients φ (comp g f) = comp (changeCoefficients φ g) (changeCoefficients φ f) := by
  funext i
  exact MvPolynomial.map_eval₂ φ f (g i)

/-- The square of coordinate rings reverses the direction of polynomial maps. -/
theorem coordHom_changeCoefficients (φ : R →+* S) (f : Map R σ τ) :
    (MvPolynomial.map φ).comp (coordHom f).toRingHom =
      (coordHom (changeCoefficients φ f)).toRingHom.comp (MvPolynomial.map φ) := by
  apply MvPolynomial.ringHom_ext
  · intro r; simp [coordHom]
  · intro i; simp [changeCoefficients]

end PolynomialMap

namespace AffinePolynomialCompiler
open FirstOrderCompiler MvPolynomial PolynomialMap
open MatrixCompiler (Slots)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]

def changePrimitive (φ : R →+* S) : Prim R a b → Prim S a b
  | .constant r => .constant (φ r)
  | .add => .add
  | .mul => .mul

/-- The original literal vocabulary interpreted with translated coefficients. -/
def coefficientTarget (φ : R →+* S) : Target (Prim R) :=
  { target S with primitive := fun p => primitive S (changePrimitive φ p) }

def coefficientMap (φ : R →+* S) :
    SquareKit.RawMap (SquareKit.FirstOrderCategory.ops (target R))
      (SquareKit.FirstOrderCategory.ops (coefficientTarget φ)) where
  obj := id
  map := changeCoefficients φ

theorem coefficientMap_laws (φ : R →+* S) : SquareKit.MapLaws (coefficientMap φ)
    (SquareKit.equality _) (SquareKit.equality _) where
  congr h := congrArg (changeCoefficients φ) h
  ident := changeCoefficients_identity φ
  comp := changeCoefficients_substitute φ

theorem coefficient_preserves (φ : R →+* S) : SquareKit.FirstOrderNaturality.Preserves
    (coefficientMap φ) (SquareKit.equality _)
    (SquareKit.FirstOrderNaturality.ofTarget (target R))
    (SquareKit.FirstOrderNaturality.ofTarget (coefficientTarget φ)) where
  terminal := by intro a; funext i; exact Empty.elim i
  fst := by
    intro a b
    change changeCoefficients φ (first R a b) = first S a b
    funext i; simp [first, changeCoefficients]
  snd := by
    intro a b
    change changeCoefficients φ (second R a b) = second S a b
    funext i; simp [second, changeCoefficients]
  pair f g := by funext i; cases i <;> rfl
  primitive p := by
    change changeCoefficients φ (primitive R p) = primitive S (changePrimitive φ p)
    cases p <;> funext i <;>
      simp [primitive, changePrimitive, changeCoefficients]

theorem compile_changeCoefficients (φ : R →+* S) (t : Term (Prim R) Γ a) :
    changeCoefficients φ (compile (target R) t) = compile (coefficientTarget φ) t := by
  rw [← SquareKit.FirstOrderNaturality.compile_ofTarget (target R),
    ← SquareKit.FirstOrderNaturality.compile_ofTarget (coefficientTarget φ)]
  exact SquareKit.FirstOrderNaturality.naturality
    (F := coefficientMap φ)
    (M := SquareKit.FirstOrderNaturality.ofTarget (target R))
    (N := SquareKit.FirstOrderNaturality.ofTarget (coefficientTarget φ))
    (coefficientMap_laws φ) (SquareKit.equality_congr _)
    ⟨fun hf hg => congrArg₂ (pair S) hf hg⟩ (coefficient_preserves φ) t

def scalarMap (φ : R →+* S) (a : Ty) : space S a ⟶ space R a :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.map φ))

@[reassoc] theorem scalarMap_over (φ : R →+* S) (a : Ty) :
    scalarMap φ a ≫ baseMap R a = baseMap S a ≫ Spec.map (CommRingCat.ofHom φ) := by
  simp only [scalarMap, baseMap, Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r; simp

@[simp] theorem scalarMap_id (a : Ty) : scalarMap (RingHom.id R) a = 𝟙 (space R a) := by
  unfold scalarMap
  rw [← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext MvPolynomial.map_id

@[reassoc] theorem scalarMap_comp (ψ : S →+* T) (φ : R →+* S) (a : Ty) :
    scalarMap ψ a ≫ scalarMap φ a = scalarMap (ψ.comp φ) a := by
  simp only [scalarMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext <;> simp

theorem realize_changeCoefficients (φ : R →+* S) {a b : Ty} (f : Code R a b) :
    (realize S (changeCoefficients φ f)).val ≫ scalarMap φ b =
      scalarMap φ a ≫ (realize R f).val := by
  simp only [realize_val, scalarMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h))
    (coordHom_changeCoefficients φ f).symm

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Polynomial extension of scalars is the actual tensor product over R. -/
def tensorComparison [Algebra R S] (a : Ty) :
    S ⊗[R] CoordinateRing R a ≃ₐ[S] CoordinateRing S a :=
  MvPolynomial.algebraTensorAlgEquiv R S

theorem tensorComparison_tmul [Algebra R S] (a : Ty) (s : S) (p : CoordinateRing R a) :
    tensorComparison a (s ⊗ₜ[R] p) = s • MvPolynomial.map (algebraMap R S) p :=
  MvPolynomial.algebraTensorAlgEquiv_tmul R S s p

theorem scalarMap_isPullback (φ : R →+* S) (a : Ty) :
    IsPullback (scalarMap φ a) (baseMap S a) (baseMap R a)
      (Spec.map (CommRingCat.ofHom φ)) := by
  let : Algebra R S := φ.toAlgebra
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R (CoordinateRing R a) S (CoordinateRing S a))

def baseChangeIso (φ : R →+* S) (a : Ty) :
    space S a ≅ pullback (baseMap R a) (Spec.map (CommRingCat.ofHom φ)) :=
  (scalarMap_isPullback φ a).isoPullback

@[reassoc (attr := simp)] theorem baseChangeIso_fst (φ : R →+* S) (a : Ty) :
    (baseChangeIso φ a).hom ≫ pullback.fst _ _ = scalarMap φ a :=
  (scalarMap_isPullback φ a).isoPullback_hom_fst

@[reassoc (attr := simp)] theorem baseChangeIso_snd (φ : R →+* S) (a : Ty) :
    (baseChangeIso φ a).hom ≫ pullback.snd _ _ = baseMap S a :=
  (scalarMap_isPullback φ a).isoPullback_hom_snd

/-- Base change acts on every geometric arrow over R, independently of syntax. -/
def baseChangedHom (φ : R →+* S) {a b : Ty} (f : GeometricHom R a b) : GeometricHom S a b :=
  realize S (changeCoefficients φ (recover R f))

@[simp] theorem baseChangedHom_realize (φ : R →+* S) {a b : Ty} (f : Code R a b) :
    baseChangedHom φ (realize R f) = realize S (changeCoefficients φ f) := by
  simp [baseChangedHom]

@[reassoc] theorem baseChangedHom_square (φ : R →+* S) {a b : Ty} (f : GeometricHom R a b) :
    (baseChangedHom φ f).val ≫ scalarMap φ b = scalarMap φ a ≫ f.val := by
  simpa [baseChangedHom] using realize_changeCoefficients φ (recover R f)

/-- The map between the chosen scheme fibre products is their universal lift. -/
def pullbackHom (φ : R →+* S) {a b : Ty} (f : GeometricHom R a b) :
    pullback (baseMap R a) (Spec.map (CommRingCat.ofHom φ)) ⟶
      pullback (baseMap R b) (Spec.map (CommRingCat.ofHom φ)) :=
  pullback.lift (pullback.fst _ _ ≫ f.val) (pullback.snd _ _)
    (by rw [Category.assoc, f.property]; exact pullback.condition)

/-- Realization of coefficient change is the actual pullback map under the object isomorphisms. -/
theorem baseChangedHom_compare (φ : R →+* S) {a b : Ty} (f : GeometricHom R a b) :
    (baseChangedHom φ f).val ≫ (baseChangeIso φ b).hom =
      (baseChangeIso φ a).hom ≫ pullbackHom φ f := by
  apply pullback.hom_ext
  · simpa [Category.assoc, pullbackHom] using baseChangedHom_square φ f
  · simpa [Category.assoc, pullbackHom] using (baseChangedHom φ f).property

@[simp] theorem baseChangedHom_id {a b : Ty} (f : GeometricHom R a b) :
    baseChangedHom (RingHom.id R) f = f := by
  simp [baseChangedHom]

theorem baseChangedHom_comp (ψ : S →+* T) (φ : R →+* S) {a b : Ty} (f : GeometricHom R a b) :
    baseChangedHom ψ (baseChangedHom φ f) = baseChangedHom (ψ.comp φ) f := by
  simp [baseChangedHom]

theorem baseChangedHom_identity (φ : R →+* S) (a : Ty) :
    baseChangedHom φ (geometricIdentity R a) = geometricIdentity S a := by
  rw [← realize_identity, baseChangedHom_realize, changeCoefficients_identity, realize_identity]

theorem baseChangedHom_geometricComp (φ : R →+* S) {a b c : Ty}
    (g : GeometricHom R b c) (f : GeometricHom R a b) :
    baseChangedHom φ (geometricComp R g f) =
      geometricComp S (baseChangedHom φ g) (baseChangedHom φ f) := by
  have h : recover R (geometricComp R g f) =
      PolynomialMap.comp (recover R g) (recover R f) := by
    apply realize_injective R
    rw [realize_recover, realize_comp, realize_recover, realize_recover]
  simp only [baseChangedHom, h, changeCoefficients_substitute, realize_comp]

theorem baseChangedHom_pair (φ : R →+* S) {a b c : Ty}
    (f : GeometricHom R a b) (g : GeometricHom R a c) :
    baseChangedHom φ (geometricPair R f g) =
      geometricPair S (baseChangedHom φ f) (baseChangedHom φ g) := by
  simp only [geometricPair, baseChangedHom, recover_realize]
  congr 1
  funext i; cases i <;> rfl

def coefficientGeometricTarget (φ : R →+* S) : Target (Prim R) :=
  { geometricTarget S with primitive := fun p => realize S (primitive S (changePrimitive φ p)) }

def coefficientRealization (φ : R →+* S) :
    SquareKit.RawMap (SquareKit.FirstOrderCategory.ops (coefficientTarget φ))
      (SquareKit.FirstOrderCategory.ops (coefficientGeometricTarget φ)) where
  obj := id
  map := realize S

theorem coefficientRealization_laws (φ : R →+* S) :
    SquareKit.MapLaws (coefficientRealization φ) (SquareKit.equality _) (SquareKit.equality _) where
  congr h := congrArg (realize S) h
  ident := realize_identity S _
  comp := realize_comp S

theorem coefficientRealization_preserves (φ : R →+* S) :
    SquareKit.FirstOrderNaturality.Preserves (coefficientRealization φ) (SquareKit.equality _)
      (SquareKit.FirstOrderNaturality.ofTarget (coefficientTarget φ))
      (SquareKit.FirstOrderNaturality.ofTarget (coefficientGeometricTarget φ)) where
  terminal := rfl
  fst := rfl
  snd := rfl
  pair f g := by
    change realize S (pair S f g) = geometricPair S (realize S f) (realize S g)
    simp [geometricPair]
  primitive _ := rfl

theorem compile_coefficientRealization (φ : R →+* S) (t : Term (Prim R) Γ a) :
    realize S (compile (coefficientTarget φ) t) = compile (coefficientGeometricTarget φ) t := by
  rw [← SquareKit.FirstOrderNaturality.compile_ofTarget (coefficientTarget φ),
    ← SquareKit.FirstOrderNaturality.compile_ofTarget (coefficientGeometricTarget φ)]
  exact SquareKit.FirstOrderNaturality.naturality
    (F := coefficientRealization φ)
    (M := SquareKit.FirstOrderNaturality.ofTarget (coefficientTarget φ))
    (N := SquareKit.FirstOrderNaturality.ofTarget (coefficientGeometricTarget φ))
    (coefficientRealization_laws φ) (SquareKit.equality_congr _)
    ⟨fun hf hg => congrArg₂ (geometricPair S) hf hg⟩ (coefficientRealization_preserves φ) t

/-- All terms, including substitutions and let bindings, compile compatibly with base change. -/
theorem compile_baseChange (φ : R →+* S) (t : Term (Prim R) Γ a) :
    baseChangedHom φ (compile (geometricTarget R) t) =
      compile (coefficientGeometricTarget φ) t := by
  rw [← compile_realize, baseChangedHom_realize, compile_changeCoefficients,
    compile_coefficientRealization]

theorem compile_pullback (φ : R →+* S) (t : Term (Prim R) Γ a) :
    (compile (coefficientGeometricTarget φ) t).val ≫ (baseChangeIso φ a).hom =
      (baseChangeIso φ (context Γ)).hom ≫ pullbackHom φ (compile (geometricTarget R) t) := by
  rw [← compile_baseChange]
  exact baseChangedHom_compare φ _

theorem compile_coefficients_comp (ψ : S →+* T) (φ : R →+* S) (t : Term (Prim R) Γ a) :
    changeCoefficients ψ (compile (coefficientTarget φ) t) =
      compile (coefficientTarget (ψ.comp φ)) t := by
  rw [← compile_changeCoefficients, changeCoefficients_comp, compile_changeCoefficients]

theorem compile_baseChange_comp (ψ : S →+* T) (φ : R →+* S) (t : Term (Prim R) Γ a) :
    baseChangedHom ψ (compile (coefficientGeometricTarget φ) t) =
      compile (coefficientGeometricTarget (ψ.comp φ)) t := by
  rw [← compile_baseChange, baseChangedHom_comp, compile_baseChange]

theorem iterated_isPullback (ψ : S →+* T) (φ : R →+* S) (a : Ty) :
    IsPullback (scalarMap ψ a ≫ (baseChangeIso φ a).hom) (baseMap T a)
      (pullback.snd (baseMap R a) (Spec.map (CommRingCat.ofHom φ)))
      (Spec.map (CommRingCat.ofHom ψ)) :=
  (scalarMap_isPullback ψ a).of_iso (Iso.refl _) (baseChangeIso φ a)
    (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

/-- The iterated chosen fibre product, compared through the intermediate affine object. -/
def iteratedBaseChangeIso (ψ : S →+* T) (φ : R →+* S) (a : Ty) :
    space T a ≅ pullback
      (pullback.snd (baseMap R a) (Spec.map (CommRingCat.ofHom φ)))
      (Spec.map (CommRingCat.ofHom ψ)) :=
  (iterated_isPullback ψ φ a).isoPullback

@[reassoc (attr := simp)] theorem iteratedBaseChangeIso_fst (ψ : S →+* T) (φ : R →+* S) (a : Ty) :
    (iteratedBaseChangeIso ψ φ a).hom ≫ pullback.fst _ _ =
      scalarMap ψ a ≫ (baseChangeIso φ a).hom :=
  IsPullback.isoPullback_hom_fst _

@[reassoc (attr := simp)] theorem iteratedBaseChangeIso_snd (ψ : S →+* T) (φ : R →+* S) (a : Ty) :
    (iteratedBaseChangeIso ψ φ a).hom ≫ pullback.snd _ _ = baseMap T a :=
  IsPullback.isoPullback_hom_snd _

def successivePullbackIso (ψ : S →+* T) (φ : R →+* S) (a : Ty) :
    pullback (pullback.snd (baseMap R a) (Spec.map (CommRingCat.ofHom φ)))
      (Spec.map (CommRingCat.ofHom ψ)) ≅
      pullback (baseMap R a) (Spec.map (CommRingCat.ofHom (ψ.comp φ))) :=
  pullbackLeftPullbackSndIso _ _ _ ≪≫
    pullback.congrHom rfl (by rw [← Spec.map_comp]; rfl)

theorem baseChangeIso_comp (ψ : S →+* T) (φ : R →+* S) (a : Ty) :
    (iteratedBaseChangeIso ψ φ a).hom ≫ (successivePullbackIso ψ φ a).hom =
      (baseChangeIso (ψ.comp φ) a).hom := by
  apply pullback.hom_ext
  · rw [baseChangeIso_fst]
    simp [successivePullbackIso, pullback.congrHom_hom, Category.assoc, scalarMap_comp]
  · rw [baseChangeIso_snd]
    simp [successivePullbackIso, pullback.congrHom_hom, Category.assoc]

theorem baseChangeIso_id_fst (a : Ty) :
    (baseChangeIso (RingHom.id R) a).hom ≫ pullback.fst _ _ = 𝟙 (space R a) := by
  rw [baseChangeIso_fst, scalarMap_id]

theorem tensorComparison_natural [Algebra R S] {a b : Ty} (f : Code R a b)
    (z : S ⊗[R] CoordinateRing R b) :
    tensorComparison a (Algebra.TensorProduct.map (AlgHom.id R S) (coordHom f) z) =
      coordHom (changeCoefficients (algebraMap R S) f) (tensorComparison b z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul s p =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, tensorComparison_tmul,
      map_smul]
    exact congrArg (fun q => s • q)
      (RingHom.congr_fun (coordHom_changeCoefficients (algebraMap R S) f) p)

/-- The exponential by the unit object exists inside the polynomial fragment. -/
def unitCurryEquiv (R : Type) [CommRing R] (x b : Ty) :
    Code R (.prod .unit x) b ≃ Code R x b :=
  Equiv.piCongrRight fun _ =>
    (MvPolynomial.renameEquiv R (Equiv.emptySum Empty (Slots x))).toEquiv

theorem unitCurryEquiv_symm (g : Code R x b) :
    (unitCurryEquiv R x b).symm g = PolynomialMap.comp g (second R .unit x) := by
  funext i
  change MvPolynomial.rename Sum.inr (g i) = aeval (second R .unit x) (g i)
  rw [rename_eq_aeval]
  rfl

/-- Evaluation after currying recovers the full polynomial map. -/
theorem unitCurry_beta (f : Code R (.prod .unit x) b) :
    PolynomialMap.comp (unitCurryEquiv R x b f) (second R .unit x) = f := by
  rw [← unitCurryEquiv_symm]
  exact (unitCurryEquiv R x b).symm_apply_apply f

theorem unitCurry_unique (f : Code R (.prod .unit x) b) (g : Code R x b) :
    PolynomialMap.comp g (second R .unit x) = f ↔ g = unitCurryEquiv R x b f := by
  rw [← unitCurryEquiv_symm]
  exact (unitCurryEquiv R x b).symm_apply_eq

theorem unitCurry_changeCoefficients (φ : R →+* S) (f : Code R (.prod .unit x) b) :
    changeCoefficients φ (unitCurryEquiv R x b f) =
      unitCurryEquiv S x b (changeCoefficients φ f) := by
  funext i
  exact MvPolynomial.map_rename φ (Equiv.emptySum Empty (Slots x)) (f i)

/-- Here the exponential comparison is an actual invertible geometric map for every ring map. -/
def unitExponentialComparison (_φ : R →+* S) (b : Ty) : GeometricHom S b b :=
  geometricIdentity S b

instance unitExponentialComparison_isIso (φ : R →+* S) (b : Ty) :
    IsIso (unitExponentialComparison φ b).val := by
  change IsIso (𝟙 _)
  infer_instance

theorem unitExponentialComparison_curry (φ : R →+* S) (f : Code R (.prod .unit x) b) :
    geometricComp S (unitExponentialComparison φ b)
      (realize S (changeCoefficients φ (unitCurryEquiv R x b f))) =
      realize S (unitCurryEquiv S x b (changeCoefficients φ f)) := by
  apply Subtype.ext
  change (realize S (changeCoefficients φ (unitCurryEquiv R x b f))).val ≫ 𝟙 _ = _
  rw [Category.comp_id, unitCurry_changeCoefficients]

/-- Over a finite nontrivial ring no selected affine object represents the ground-type exponential.
Even the required currying round trip at the unit test object is impossible. -/
theorem no_ground_exponential [Finite R] [Nontrivial R] (e : Ty)
    (curry : Code R (.prod .unit .base) .base → Code R .unit e)
    (uncurry : Code R .unit e → Code R (.prod .unit .base) .base)
    (roundTrip : ∀ f, uncurry (curry f) = f) : False := by
  let : Finite (MvPolynomial Empty R) :=
    Finite.of_equiv R (MvPolynomial.isEmptyAlgEquiv R Empty).symm.toEquiv
  let : Finite (Code R .unit e) := inferInstance
  let : Infinite (Code R (.prod .unit .base) .base) :=
    Infinite.of_injective
      (fun p : MvPolynomial (Empty ⊕ Unit) R => (fun _ => p : Code R (.prod .unit .base) .base))
      (fun _ _ h => congrFun h ())
  let : Finite (Code R (.prod .unit .base) .base) :=
    Finite.of_injective curry (Function.LeftInverse.injective roundTrip)
  exact (inferInstance : Infinite (Code R (.prod .unit .base) .base)).not_finite inferInstance

theorem no_geometric_ground_exponential [Finite R] [Nontrivial R] (e : Ty)
    (curry : GeometricHom R (.prod .unit .base) .base → GeometricHom R .unit e)
    (uncurry : GeometricHom R .unit e → GeometricHom R (.prod .unit .base) .base)
    (roundTrip : ∀ f, uncurry (curry f) = f) : False := by
  apply no_ground_exponential e
    (fun f => recover R (curry (realize R f)))
    (fun g => recover R (uncurry (realize R g)))
  intro f
  simp [roundTrip]

end AffinePolynomialCompiler
