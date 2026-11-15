import SquareKit.Internal.Cubical.Presheaf

/-! Dependent sums and products of actual presheaf families. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

/-- An element of a family becomes an element of its comprehension. -/
def extendObj {Γ : Context.{u}} (A : Family Γ) (x : Γ.Elements) (a : A.obj x) :
    (total A).Elements := (total A).elementsMk x.obj ⟨x.val, a⟩

/-- Restriction in a family gives the corresponding comprehension arrow. -/
def extendHom {Γ : Context.{u}} (A : Family Γ) {x y : Γ.Elements}
    (f : x ⟶ y) (a : A.obj x) : extendObj A x a ⟶ extendObj A y (A.map f a) :=
  Functor.Elements.homMk f.hom (totalMap_ofHom A f a)

def extendAlong {Γ : Context.{u}} (A : Family Γ) {x y : Γ.Elements}
    (f : x ⟶ y) {a : A.obj x} {a' : A.obj y} (h : A.map f a = a') :
    extendObj A x a ⟶ extendObj A y a' :=
  Functor.Elements.homMk f.hom ((totalMap_ofHom A f a).trans (by rw [h]; rfl))

def sigmaMap {Γ : Context.{u}} (A : Family Γ) (B : Family (total A))
    {x y : Γ.Elements} (f : x ⟶ y) (z : Σ a : A.obj x, B.obj (extendObj A x a)) :
    Σ a : A.obj y, B.obj (extendObj A y a) :=
  ⟨A.map f z.1, B.map (extendHom A f z.1) z.2⟩

theorem sigmaMap_ofHom {Γ : Context.{u}} (A : Family Γ) (B : Family (total A))
    {x y : Γ.Elements} (f : x ⟶ y) {a : A.obj x} {a' : A.obj y}
    (h : A.map f a = a') (b : B.obj (extendObj A x a)) :
    sigmaMap A B f ⟨a,b⟩ = ⟨a', B.map (extendAlong A f h) b⟩ := by
  subst a'
  rfl

/-- The dependent sum retains both the selected argument and its dependent value. -/
def sigma {Γ : Context.{u}} (A : Family Γ) (B : Family (total A)) : Family Γ where
  obj x := Σ a : A.obj x, B.obj (extendObj A x a)
  map f := TypeCat.ofHom (sigmaMap A B f)
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro z
    rcases z with ⟨a,b⟩
    have h : A.map (𝟙 x) a = a := by simp
    have he : extendAlong A (𝟙 x) h = 𝟙 (extendObj A x a) := rfl
    change sigmaMap A B (𝟙 x) ⟨a,b⟩ = ⟨a,b⟩
    simpa only [he, Functor.map_id, types_id_apply] using sigmaMap_ofHom A B (𝟙 x) h b
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro z
    rcases z with ⟨a,b⟩
    have h : A.map (f ≫ g) a = A.map g (A.map f a) := by simp
    have he : extendAlong A (f ≫ g) h = extendHom A f a ≫ extendHom A g (A.map f a) := rfl
    change sigmaMap A B (f ≫ g) ⟨a,b⟩ = sigmaMap A B g (sigmaMap A B f ⟨a,b⟩)
    have hs := sigmaMap_ofHom A B (f ≫ g) h b
    rw [he, B.map_comp] at hs
    exact hs

/-- Introduce a dependent pair from its two sections. -/
def sigmaIntro {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (a : Term A) (b : Term (reindex B (pair (𝟙 Γ) a))) : Term (sigma A B) where
  val x := ⟨a.val x, b.val x⟩
  property {x y} f := by
    have h := sigmaMap_ofHom A B f (a.property f) (b.val x)
    have hb := b.property f
    exact h.trans (congrArg (Sigma.mk _) hb)

/-- First projection of a dependent sum. -/
def sigmaFst {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (s : Term (sigma A B)) : Term A where
  val x := (s.val x).1
  property f := congrArg Sigma.fst (s.property f)

/-- Second projection has the family reindexed by the first projection. -/
def sigmaSnd {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (s : Term (sigma A B)) : Term (reindex B (pair (𝟙 Γ) (sigmaFst s))) where
  val x := (s.val x).2
  property {x y} f := by
    have h := s.property f
    have he := sigmaMap_ofHom A B f ((sigmaFst s).property f) (s.val x).2
    change sigmaMap A B f (s.val x) = s.val y at h
    have h' := he.symm.trans h
    exact (Sigma.mk.inj h').2.eq

@[simp] theorem sigmaFst_intro {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (a : Term A) (b : Term (reindex B (pair (𝟙 Γ) a))) :
    sigmaFst (sigmaIntro a b) = a := rfl

@[simp] theorem sigmaSnd_intro {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (a : Term A) (b : Term (reindex B (pair (𝟙 Γ) a))) :
    sigmaSnd (sigmaIntro a b) = b := rfl

theorem sigma_eta {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (s : Term (sigma A B)) : sigmaIntro (sigmaFst s) (sigmaSnd s) = s := rfl

/-- Extend a context substitution by the generic argument. -/
def liftSub {Γ Δ : Context.{u}} (A : Family Γ) (σ : Δ ⟶ Γ) :
    total (reindex A σ) ⟶ total A :=
  pair (projection (reindex A σ) ≫ σ) (generic (reindex A σ))

@[simp] theorem sigma_reindex {Γ Δ : Context.{u}} (A : Family Γ)
    (B : Family (total A)) (σ : Δ ⟶ Γ) :
    reindex (sigma A B) σ = sigma (reindex A σ) (reindex B (liftSub A σ)) := rfl

theorem sigmaIntro_reindex {Γ Δ : Context.{u}} {A : Family Γ}
    {B : Family (total A)} (a : Term A) (b : Term (reindex B (pair (𝟙 Γ) a)))
    (σ : Δ ⟶ Γ) :
    Term.reindex (sigmaIntro a b) σ =
      sigmaIntro (B := reindex B (liftSub A σ)) (Term.reindex a σ) (Term.reindex b σ) := rfl

/-- A dependent function supplies compatible values after every restriction.
The restriction quantifier is essential: pointwise functions alone are not a
presheaf exponential. -/
structure PiElement {Γ : Context.{u}} (A : Family Γ) (B : Family (total A))
    (x : Γ.Elements) where
  val : ∀ {y : Γ.Elements} (_f : x ⟶ y) (a : A.obj y), B.obj (extendObj A y a)
  naturality : ∀ {y z : Γ.Elements} (f : x ⟶ y) (g : y ⟶ z) (a : A.obj y),
    B.map (extendHom A g a) (val f a) = val (f ≫ g) (A.map g a)

@[ext] theorem PiElement.ext {Γ : Context.{u}} {A : Family Γ}
    {B : Family (total A)} {x : Γ.Elements} {p q : PiElement A B x}
    (h : ∀ {y} (f : x ⟶ y) a, p.val f a = q.val f a) : p = q := by
  cases p
  cases q
  congr
  funext y f a
  exact h f a

/-- Restriction precomposes the indexing arrow of a dependent function. -/
def PiElement.restrict {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {x y : Γ.Elements} (f : x ⟶ y) (p : PiElement A B x) : PiElement A B y where
  val g a := p.val (f ≫ g) a
  naturality g h a := by simpa only [Category.assoc] using p.naturality (f ≫ g) h a

/-- The Kripke dependent product, with its constructed restriction maps. -/
def pi {Γ : Context.{u}} (A : Family Γ) (B : Family (total A)) : Family Γ where
  obj x := PiElement A B x
  map f := TypeCat.ofHom (PiElement.restrict f)
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro p
    apply PiElement.ext
    intro y f a
    simp [PiElement.restrict]
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro p
    apply PiElement.ext
    intro y h a
    simp [PiElement.restrict]

/-- Abstraction uses the body at every generalized argument. -/
def lam {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)} (b : Term B) :
    Term (pi A B) where
  val _ := {
    val := fun {_} _ a => b.val (extendObj A _ a)
    naturality := fun _ g a => b.property (extendHom A g a) }
  property _ := rfl

/-- Application at the generic argument is a section over comprehension. -/
def app {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)} (p : Term (pi A B)) :
    Term B where
  val z := (p.val (Γ.elementsMk z.obj z.val.1)).val (𝟙 _) z.val.2
  property {x y} f := by
    rcases x with @⟨I, x, a⟩
    rcases y with @⟨J, y, b⟩
    rcases f with ⟨f, h⟩
    change I ⟶ J at f
    change totalMap A f ⟨x,a⟩ = ⟨y,b⟩ at h
    cases h
    let g : Γ.elementsMk I x ⟶ Γ.elementsMk J (Γ.map f x) :=
      Functor.Elements.homMk f rfl
    have hn := (p.val (Γ.elementsMk I x)).naturality (𝟙 _) g a
    have hp := congrArg (fun q : PiElement A B (Γ.elementsMk J (Γ.map f x)) =>
      q.val (𝟙 _) (A.map g a)) (p.property g)
    have hn' : B.map (extendHom A g a) ((p.val (Γ.elementsMk I x)).val (𝟙 _) a) =
        (p.val (Γ.elementsMk I x)).val g (A.map g a) := by
      simpa only [Category.id_comp] using hn
    change (p.val (Γ.elementsMk I x)).val (g ≫ 𝟙 _) (A.map g a) = _ at hp
    exact hn'.trans (by simpa only [Category.comp_id] using hp)

@[simp] theorem app_lam {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (b : Term B) : app (lam b) = b := rfl

theorem lam_app {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (p : Term (pi A B)) : lam (app p) = p := by
  apply Term.ext
  intro x
  apply PiElement.ext
  intro y f a
  have h := congrArg (fun q : PiElement A B y => q.val (𝟙 _) a) (p.property f)
  change (p.val x).val (f ≫ 𝟙 _) a = (p.val y).val (𝟙 _) a at h
  change (p.val y).val (𝟙 _) a = (p.val x).val f a
  simpa only [Category.comp_id] using h.symm

/-- Apply a family morphism to a coherent section. -/
def Term.map {Γ : Context.{u}} {A B : Family Γ} (η : A ⟶ B) (t : Term A) : Term B where
  val x := η.app x (t.val x)
  property f := by
    rw [← η.naturality_apply, t.property f]

/-- Restrict all generalized arguments along a context substitution. -/
def piReindex {Γ Δ : Context.{u}} (A : Family Γ) (B : Family (total A))
    (σ : Δ ⟶ Γ) : reindex (pi A B) σ ⟶ pi (reindex A σ) (reindex B (liftSub A σ)) where
  app x := TypeCat.ofHom (fun p => {
    val := fun f a => p.val (σ.mapElements.map f) a
    naturality := fun f g a => p.naturality (σ.mapElements.map f) (σ.mapElements.map g) a })
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply PiElement.ext
    intro z g a
    rfl

theorem lam_reindex {Γ Δ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (b : Term B) (σ : Δ ⟶ Γ) :
    Term.map (piReindex A B σ) (Term.reindex (lam b) σ) =
      lam (A := reindex A σ) (Term.reindex b (liftSub A σ)) := rfl

theorem app_reindex {Γ Δ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (p : Term (pi A B)) (σ : Δ ⟶ Γ) :
    app (Term.map (piReindex A B σ) (Term.reindex p σ)) =
      Term.reindex (app p) (liftSub A σ) := rfl

end SquareKit.Cubical.Presheaf
