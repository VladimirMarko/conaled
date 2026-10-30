import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-! Left-fold fusion from initial list algebras. The proof uses the exponentials
`I^I`, `S^S`, and `S^I`; Cartesian closure is a sufficient interface. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.ListInitial
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [MonoidalClosed C]

/-- The list signature, with the chosen Cartesian product. -/
def signature [HasBinaryCoproducts C] (A : C) : C ⥤ C where
  obj X := (𝟙_ C) ⨿ (A ⊗ X)
  map f := coprod.map (𝟙 _) (𝟙 A ⊗ₘ f)
  map_id X := by simp
  map_comp f g := by ext <;> simp

/-- Application to generalized elements; no well-pointedness assumption. -/
def applyHom {X I S : C} (k : X ⟶ I ⟶[C] S) (x : X ⟶ I) : X ⟶ S :=
  lift x k ≫ (ihom.ev I).app S

@[simp] theorem applyHom_comp {W X I S : C} (q : W ⟶ X)
    (k : X ⟶ I ⟶[C] S) (x : X ⟶ I) :
    applyHom (q ≫ k) (q ≫ x) = q ≫ applyHom k x := by
  simp only [applyHom, ← comp_lift, Category.assoc]

@[simp] theorem applyHom_curry {X Y I S : C} (k : I ⊗ Y ⟶ S)
    (q : X ⟶ Y) (x : X ⟶ I) :
    applyHom (q ≫ curry k) x = lift x q ≫ k := by
  rw [applyHom, ← lift_whiskerLeft, Category.assoc]
  change lift x q ≫ uncurry (curry k) = _
  simp

/-- Generalized application detects equality of maps into an exponential. -/
theorem hom_ext {X I S : C} {k l : X ⟶ I ⟶[C] S}
    (h : applyHom (snd I X ≫ k) (fst I X) =
      applyHom (snd I X ≫ l) (fst I X)) : k = l := by
  apply uncurry_injective
  simpa [applyHom, ← lift_whiskerLeft, uncurry_eq] using h

/-- Extend an action by one input, applying the next step before its tail. -/
def consAction {A I S : C} (f : I ⊗ A ⟶ I) :
    A ⊗ (I ⟶[C] S) ⟶ I ⟶[C] S :=
  curry (applyHom (snd _ _ ≫ snd _ _)
    (lift (fst _ _) (snd _ _ ≫ fst _ _) ≫ f))

@[simp] theorem apply_cons {X A I S : C} (f : I ⊗ A ⟶ I)
    (a : X ⟶ A) (k : X ⟶ I ⟶[C] S) (x : X ⟶ I) :
    applyHom (lift a k ≫ consAction f) x =
      applyHom k (lift x a ≫ f) := by
  simp [consAction, applyHom_curry, ← applyHom_comp, comp_lift_assoc]

/-- Algebra of continuations into `S`, with an arbitrary initial observation. -/
def actionAlgebra [HasBinaryCoproducts C] {A I S : C} (f : I ⊗ A ⟶ I) (h : I ⟶ S) :
    Endofunctor.Algebra (signature A) where
  a := I ⟶[C] S
  str := coprod.desc (curry (fst I (𝟙_ C) ≫ h)) (consAction f)

/-- Postcomposition on internal functions. -/
def post {I S : C} (h : I ⟶ S) : (I ⟶[C] I) ⟶ (I ⟶[C] S) :=
  curry ((ihom.ev I).app I ≫ h)

/-- Precomposition on internal functions. -/
def pre {I S : C} (h : I ⟶ S) : (S ⟶[C] S) ⟶ (I ⟶[C] S) :=
  curry (applyHom (snd _ _) (fst _ _ ≫ h))

@[simp] theorem apply_post {X I S : C} (h : I ⟶ S)
    (k : X ⟶ I ⟶[C] I) (x : X ⟶ I) :
    applyHom (k ≫ post h) x = applyHom k x ≫ h := by
  unfold post
  rw [applyHom_curry]
  simp [applyHom, Category.assoc]

@[simp] theorem apply_pre {X I S : C} (h : I ⟶ S)
    (k : X ⟶ S ⟶[C] S) (x : X ⟶ I) :
    applyHom (k ≫ pre h) x = applyHom k (x ≫ h) := by
  simp [pre, applyHom_curry, ← applyHom_comp]


@[simp] theorem apply_post_assoc {X Y I S : C} (h : I ⟶ S)
    (q : X ⟶ Y) (k : Y ⟶ I ⟶[C] I) (x : X ⟶ I) :
    applyHom (q ≫ k ≫ post h) x = applyHom (q ≫ k) x ≫ h := by
  rw [← Category.assoc, apply_post]

@[simp] theorem apply_pre_assoc {X Y I S : C} (h : I ⟶ S)
    (q : X ⟶ Y) (k : Y ⟶ S ⟶[C] S) (x : X ⟶ I) :
    applyHom (q ≫ k ≫ pre h) x = applyHom (q ≫ k) (x ≫ h) := by
  rw [← Category.assoc, apply_pre]

@[simp] theorem apply_cons_general {X A I S : C} (f : I ⊗ A ⟶ I)
    (q : X ⟶ A ⊗ (I ⟶[C] S)) (x : X ⟶ I) :
    applyHom (q ≫ consAction f) x =
      applyHom (q ≫ snd _ _) (lift x (q ≫ fst _ _) ≫ f) := by
  conv_lhs => rw [← lift_comp_fst_snd q]
  rw [apply_cons]

@[simp] theorem apply_cons_assoc {X Y A I S : C} (f : I ⊗ A ⟶ I)
    (p : X ⟶ Y) (q : Y ⟶ A ⊗ (I ⟶[C] S)) (x : X ⟶ I) :
    applyHom (p ≫ q ≫ consAction f) x =
      applyHom (p ≫ q ≫ snd _ _) (lift x (p ≫ q ≫ fst _ _) ≫ f) := by
  rw [← Category.assoc, apply_cons_general]
  simp only [Category.assoc]

variable [HasBinaryCoproducts C]

/-- Postcomposition respects the continuation list algebra. -/
def postMorphism {A I S : C} (f : I ⊗ A ⟶ I) (h : I ⟶ S) :
    actionAlgebra f (𝟙 I) ⟶ actionAlgebra f h where
  f := post h
  h := by
    apply coprod.hom_ext
    · simp only [signature, actionAlgebra, coprod.inl_map_assoc,
        coprod.inl_desc, Category.id_comp, coprod.inl_desc_assoc]
      apply hom_ext
      simp [applyHom_curry]
    · simp only [signature, actionAlgebra, coprod.inr_map_assoc,
        coprod.inr_desc, coprod.inr_desc_assoc]
      apply hom_ext
      simp [← lift_fst_comp_snd_comp]

/-- The local square is precisely the obligation for precomposition. -/
def preMorphism {A I S : C} (f : I ⊗ A ⟶ I) (g : S ⊗ A ⟶ S)
    (h : I ⟶ S) (square : f ≫ h = (h ⊗ₘ 𝟙 A) ≫ g) :
    actionAlgebra g (𝟙 S) ⟶ actionAlgebra f h where
  f := pre h
  h := by
    apply coprod.hom_ext
    · simp only [signature, actionAlgebra, coprod.inl_map_assoc,
        coprod.inl_desc, Category.id_comp, coprod.inl_desc_assoc]
      apply hom_ext
      simp [applyHom_curry]
    · simp only [signature, actionAlgebra, coprod.inr_map_assoc,
        coprod.inr_desc, coprod.inr_desc_assoc]
      apply hom_ext
      simp [Category.assoc, ← lift_fst_comp_snd_comp]
      rw [square]
      simp only [← Category.assoc, lift_map, Category.comp_id]

/-- Left-fold action obtained by the unique continuation-algebra morphism. -/
def run {A I : C} {L : Endofunctor.Algebra (signature A)} (initial : IsInitial L)
    (f : I ⊗ A ⟶ I) : I ⊗ L.a ⟶ I :=
  uncurry (initial.to (actionAlgebra f (𝟙 I))).f

/-- One recursive fusion proof, using uniqueness in Mathlib's algebra category. -/
theorem fusion {A I S : C} {L : Endofunctor.Algebra (signature A)}
    (initial : IsInitial L) (f : I ⊗ A ⟶ I) (g : S ⊗ A ⟶ S)
    (h : I ⟶ S) (square : f ≫ h = (h ⊗ₘ 𝟙 A) ≫ g) :
    run initial f ≫ h = (h ⊗ₘ 𝟙 L.a) ≫ run initial g := by
  have same := initial.hom_ext
    (initial.to (actionAlgebra f (𝟙 I)) ≫ postMorphism f h)
    (initial.to (actionAlgebra g (𝟙 S)) ≫ preMorphism f g h square)
  have arrows := congrArg Endofunctor.Algebra.Hom.f same
  have applied := congrArg (fun k => applyHom (snd I L.a ≫ k) (fst I L.a)) arrows
  simp only [Endofunctor.Algebra.comp_f, postMorphism, preMorphism,
    apply_post_assoc, apply_pre_assoc] at applied
  simp only [applyHom] at applied
  have ev (X Y Z : C) (k : X ⟶ Y ⟶[C] Z) :
      lift (fst Y X) (snd Y X ≫ k) ≫ (ihom.ev Y).app Z = uncurry k := by
    rw [← lift_whiskerLeft, lift_fst_snd, Category.id_comp]
    rfl
  rw [ev] at applied
  rw [run, run]
  conv_rhs => rw [uncurry_eq, ← Category.assoc]
  have prod : (h ⊗ₘ 𝟙 L.a) ≫ S ◁ (initial.to (actionAlgebra g (𝟙 S))).f =
      lift (fst I L.a ≫ h) (snd I L.a ≫ (initial.to (actionAlgebra g (𝟙 S))).f) := by
    ext <;> simp
  rw [prod]
  exact applied

end SquareKit.ListInitial
