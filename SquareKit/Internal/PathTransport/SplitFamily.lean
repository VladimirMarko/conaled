import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Groupoid.Grpd.Basic

/-!
# Split groupoid families and sections

A family is a strict functor into groupoids. Context comprehension is its
Grothendieck construction. Sections record their fiber components, so their
projection to the context is definitionally the identity functor.
-/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w z

set_option linter.checkUnivs false in
abbrev Family (Γ : Type u) [Category.{v} Γ] := Γ ⥤ Grpd.{z, w}
abbrev Extend {Γ : Type u} [Category.{v} Γ] (A : Γ ⥤ Grpd.{z, w}) :=
  Grothendieck (A ⋙ Grpd.forgetToCat)

variable {Γ : Type u} [Category.{v} Γ] (A : Γ ⥤ Grpd.{z, w})

instance [IsGroupoid Γ] : IsGroupoid (Extend A) where
  all_isIso {X Y} f := by
    let : Groupoid ((A ⋙ Grpd.forgetToCat).obj Y.base) := inferInstanceAs (Groupoid (A.obj Y.base))
    let e := Grothendieck.isoMk (asIso f.base) (asIso f.fiber)
    have he : e.hom = f := rfl
    rw [← he]
    infer_instance

/-- A term consists of objects and coherent arrows in the varying fibers. -/
structure Section where
  obj : ∀ γ, A.obj γ
  map : ∀ {γ δ} (f : γ ⟶ δ), (A.map f).obj (obj γ) ⟶ obj δ
  map_id : ∀ γ, map (𝟙 γ) = eqToHom (by simp [Grpd.id_eq_id])
  map_comp : ∀ {γ δ ε} (f : γ ⟶ δ) (g : δ ⟶ ε),
    map (f ≫ g) = eqToHom (by simp [Grpd.comp_eq_comp]) ≫ (A.map g).map (map f) ≫ map g

namespace Section
variable {A}

/-- The section's functor into context comprehension. -/
def lift (s : Section A) : Γ ⥤ Extend A where
  obj γ := ⟨γ, s.obj γ⟩
  map f := ⟨f, s.map f⟩
  map_id γ := by
    exact Grothendieck.ext _ _ rfl (by simpa using s.map_id γ)
  map_comp f g := by
    fapply Grothendieck.ext
    · rfl
    · dsimp [Grothendieck.comp, Grpd.forgetToCat]
      simpa using s.map_comp f g

@[simp] theorem lift_forget (s : Section A) :
    s.lift ⋙ Grothendieck.forget (A ⋙ Grpd.forgetToCat) = 𝟭 Γ := rfl

theorem map_congr (s : Section A) {γ δ : Γ} {f g : γ ⟶ δ} (h : f = g) :
    s.map f = eqToHom (congrArg (fun k => (A.map k).obj (s.obj γ)) h) ≫ s.map g := by
  subst g
  simp

/-- Reindex a section along a simultaneous semantic substitution. -/
def reindex {Δ : Type*} [Category* Δ] (s : Section A) (σ : Δ ⥤ Γ) :
    Section (σ ⋙ A) where
  obj δ := s.obj (σ.obj δ)
  map f := s.map (σ.map f)
  map_id δ := by
    dsimp
    rw [s.map_congr (σ.map_id δ), s.map_id]
    simp
  map_comp f g := by
    dsimp
    rw [s.map_congr (σ.map_comp f g), s.map_comp]
    simp

@[simp] theorem reindex_id (s : Section A) : s.reindex (𝟭 Γ) = s := rfl

@[simp] theorem reindex_comp {Δ Θ : Type*} [Category* Δ] [Category* Θ]
    (s : Section A) (σ : Δ ⥤ Γ) (τ : Θ ⥤ Δ) :
    (s.reindex σ).reindex τ = s.reindex (τ ⋙ σ) := rfl

end Section
/-- A constant base groupoid forms a family in every context. -/
def constant (C : Type w) [Groupoid.{z} C] : Γ ⥤ Grpd.{z,w} :=
  Functor.const Γ |>.obj (Grpd.of C)

/-- A set is regarded as a groupoid with only equality arrows. -/
def discrete : Type w ⥤ Grpd.{w,w} where
  obj α := @Grpd.of _ (Groupoid.ofIsGroupoid (C := Discrete α))
  map f := Discrete.functor (fun a => Discrete.mk (f a))
  map_id α := by
    fapply CategoryTheory.Functor.ext
    · intro a; rfl
    · intro X Y f
      change @Eq (Discrete.Hom _ _) _ _
      exact congrArg Discrete.Hom.mk rfl
  map_comp f g := by
    fapply CategoryTheory.Functor.ext
    · intro a; rfl
    · intro X Y f
      change @Eq (Discrete.Hom _ _) _ _
      exact congrArg Discrete.Hom.mk rfl

/-- Primitive set-valued families use their given action on context arrows. -/
def setFamily (B : Γ ⥤ Type w) : Γ ⥤ Grpd.{w,w} := B ⋙ discrete

/-- Context projection forgets the newest variable. -/
def weaken : Extend A ⥤ Γ := Grothendieck.forget (A ⋙ Grpd.forgetToCat)

/-- The newest variable is the fiber component of a comprehension object. -/
def «variable» : Section (weaken A ⋙ A) where
  obj X := X.fiber
  map f := f.fiber
  map_id _X := rfl
  map_comp _f _g := rfl

/-- Extend a semantic simultaneous substitution by its newest term. -/
def pair {Δ : Type*} [Category* Δ] (σ : Δ ⥤ Γ) (t : Section (σ ⋙ A)) :
    Δ ⥤ Extend A := t.lift ⋙ Grothendieck.pre (A ⋙ Grpd.forgetToCat) σ

@[simp] theorem pair_weaken {Δ : Type*} [Category* Δ]
    (σ : Δ ⥤ Γ) (t : Section (σ ⋙ A)) : pair A σ t ⋙ weaken A = σ := rfl

@[simp] theorem pair_variable : pair A (weaken A) («variable» A) = 𝟭 (Extend A) := by
  fapply CategoryTheory.Functor.ext
  · intro X; cases X; rfl
  · intro X Y f; cases X; cases Y; cases f; simp [pair, weaken, «variable», Section.lift, Grothendieck.pre]



/-- Fiber-arrow identity transports by endpoint conjugation. -/
def directIdentity (x y : Section A) : Γ ⥤ Type z where
  obj γ := x.obj γ ⟶ y.obj γ
  map f := ↾fun p => inv (x.map f) ≫ (A.map f).map p ≫ y.map f
  map_id γ := by
    ext p
    change inv (x.map (𝟙 γ)) ≫ (A.map (𝟙 γ)).map p ≫ y.map (𝟙 γ) = p
    rw [x.map_id, y.map_id]
    have h := NatIso.naturality_2 (eqToIso (A.map_id γ)) p
    simp only [eqToIso.hom, eqToHom_app, Grpd.id_eq_id, Functor.id_map] at h
    rw [← h]
    simp
  map_comp f g := by
    ext p
    change inv (x.map (f ≫ g)) ≫ (A.map (f ≫ g)).map p ≫ y.map (f ≫ g) =
      inv (x.map g) ≫ (A.map g).map (inv (x.map f) ≫ (A.map f).map p ≫ y.map f) ≫ y.map g
    rw [x.map_comp, y.map_comp]
    have h := NatIso.naturality_2 (eqToIso (A.map_comp f g)) p
    simp only [eqToIso.hom, eqToHom_app, Grpd.comp_eq_comp, Functor.comp_map] at h
    simp [Category.assoc, ← h]

@[simp] theorem directIdentity_substitution {Δ : Type*} [Category* Δ]
    (x y : Section A) (σ : Δ ⥤ Γ) :
    directIdentity (σ ⋙ A) (x.reindex σ) (y.reindex σ) = σ ⋙ directIdentity A x y := rfl

/-- The identity type is discrete, with arrow data as its objects. -/
def identityFamily (x y : Section A) : Γ ⥤ Grpd.{z,z} :=
  setFamily (directIdentity A x y)

/-- Objects of source identity retain precisely the arrows in the type fiber. -/
def identityFiberEquiv (x y : Section A) (γ : Γ) :
    (identityFamily A x y).obj γ ≃ (x.obj γ ⟶ y.obj γ) := discreteEquiv

@[simp] theorem identityFiberEquiv_naturality (x y : Section A) {γ δ : Γ}
    (f : γ ⟶ δ) (p : (identityFamily A x y).obj γ) :
    identityFiberEquiv A x y δ (((identityFamily A x y).map f).obj p) =
      inv (x.map f) ≫ (A.map f).map (identityFiberEquiv A x y γ p) ≫ y.map f := rfl

/-- Reflexivity is a coherent section of the arrow-valued identity family. -/
def reflexivitySection (x : Section A) : Section (identityFamily A x x) where
  obj γ := Discrete.mk (𝟙 (x.obj γ))
  map f := Discrete.eqToHom (by simp [identityFamily, setFamily, discrete, directIdentity])
  map_id _ := congrArg Discrete.Hom.mk rfl
  map_comp _ _ := congrArg Discrete.Hom.mk rfl

@[simp] theorem identityFiberEquiv_reflexivity (x : Section A) (γ : Γ) :
    identityFiberEquiv A x x γ ((reflexivitySection A x).obj γ) = 𝟙 (x.obj γ) := rfl

@[simp] theorem variable_pair {Δ : Type*} [Category* Δ]
    (σ : Δ ⥤ Γ) (t : Section (σ ⋙ A)) :
    («variable» A).reindex (pair A σ t) = t := rfl

@[simp] theorem pair_substitution {Δ Θ : Type*} [Category* Δ] [Category* Θ]
    (σ : Δ ⥤ Γ) (τ : Θ ⥤ Δ) (t : Section (σ ⋙ A)) :
    τ ⋙ pair A σ t = pair A (τ ⋙ σ) (t.reindex τ) := rfl

@[simp] theorem identityFamily_substitution {Δ : Type*} [Category* Δ]
    (x y : Section A) (σ : Δ ⥤ Γ) :
    identityFamily (σ ⋙ A) (x.reindex σ) (y.reindex σ) = σ ⋙ identityFamily A x y := rfl

@[simp] theorem reflexivitySection_substitution {Δ : Type*} [Category* Δ]
    (x : Section A) (σ : Δ ⥤ Γ) :
    reflexivitySection (σ ⋙ A) (x.reindex σ) = (reflexivitySection A x).reindex σ := rfl

section Base
variable {C : Type w} [Groupoid.{z} C]

/-- Sections of the constant base are exactly functors into the base groupoid. -/
def constantSection (f : Γ ⥤ C) : Section (constant (Γ := Γ) C) where
  obj := f.obj
  map g := f.map g
  map_id γ := by simp [constant, Grpd.id_eq_id]
  map_comp g h := by simp [constant, Grpd.id_eq_id]

/-- Recover the base functor from a section of the constant family. -/
def baseFunctor (x : Section (constant (Γ := Γ) C)) : Γ ⥤ C where
  obj := x.obj
  map f := x.map f
  map_id γ := x.map_id γ
  map_comp f g := by simpa [constant, Grpd.id_eq_id] using x.map_comp f g

@[simp] theorem baseFunctor_reindex {Δ : Type*} [Category* Δ]
    (x : Section (constant (Γ := Γ) C)) (σ : Δ ⥤ Γ) :
    baseFunctor (x.reindex σ) = σ ⋙ baseFunctor x := rfl

@[simp] theorem baseFunctor_constantSection (f : Γ ⥤ C) :
    baseFunctor (constantSection f) = f := rfl

/-- Interpret the primitive set-valued fiber at a source base term. -/
def primitiveFiber (B : C ⥤ Type w) (x : Section (constant (Γ := Γ) C)) :
    Γ ⥤ Grpd.{w,w} := setFamily (baseFunctor x ⋙ B)

@[simp] theorem primitiveFiber_substitution {Δ : Type*} [Category* Δ]
    (B : C ⥤ Type w) (x : Section (constant (Γ := Γ) C)) (σ : Δ ⥤ Γ) :
    primitiveFiber B (x.reindex σ) = σ ⋙ primitiveFiber B x := rfl
end Base

end SquareKit.Internal.PathTransport.GroupoidModel
