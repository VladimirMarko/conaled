import SquareKit.Internal.Cubical.CartesianFilling
import SquareKit.Internal.Cubical.CartesianWitnesses

/-! Dependent family operations in arbitrary Cartesian contexts. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u

def endpoint (Γ : Context.{u}) (b : Bool) : Term (interval Γ) where
  val x := ⟨Cube.endpoint x.obj.unop b⟩
  property _ := rfl

def endpointSub (Γ : Context.{u}) (b : Bool) := graph (endpoint Γ b)

def pair {Γ Δ : Context.{u}} {A : Family Γ} (σ : Δ ⟶ Γ)
    (t : Term (reindex A σ)) : Δ ⟶ total A where
  app I := TypeCat.ofHom (fun x => ⟨σ.app I x, t.val (Δ.elementsMk I x)⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    let p : Δ.elementsMk I x ⟶ Δ.elementsMk J (Δ.map f x) :=
      Functor.Elements.homMk f rfl
    have h := totalMap_ofHom A (σ.mapElements.map p) (t.val (Δ.elementsMk I x))
    change ⟨σ.app J (Δ.map f x), t.val (Δ.elementsMk J (Δ.map f x))⟩ =
      totalMap A f ⟨σ.app I x, t.val (Δ.elementsMk I x)⟩
    exact (h.trans (congrArg (Sigma.mk _) (t.property p))).symm

@[simp] theorem pair_projection {Γ Δ : Context.{u}} {A : Family Γ}
    (σ : Δ ⟶ Γ) (t : Term (reindex A σ)) : pair σ t ≫ projection A = σ := rfl

/-- The generic term returns the selected fiber component of a dependent pair. -/
def generic {Γ : Context.{u}} (A : Family Γ) : Term (reindex A (projection A)) where
  val x := x.val.2
  property {x y} f := by
    rcases x with @⟨I, x⟩
    rcases y with @⟨J, y⟩
    rcases f with ⟨f, h⟩
    change I ⟶ J at f
    change totalMap A f x = y at h
    subst y
    rfl


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


abbrev PathElement {Γ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) (x : Γ.Elements) :=
  { p : PiElement (interval Γ) B x // ∀ {y} (f : x ⟶ y),
    p.val f ((endpoint Γ false).val y) = a₀.val y ∧
    p.val f ((endpoint Γ true).val y) = a₁.val y }

def path {Γ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) : Family Γ where
  obj x := PathElement B a₀ a₁ x
  map f := TypeCat.ofHom (fun p => ⟨p.val.restrict f, fun g => p.property (f ≫ g)⟩)
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    apply PiElement.ext
    intro y f a
    simp [PiElement.restrict]
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    apply PiElement.ext
    intro y h a
    simp [PiElement.restrict]

def pathInclusion {Γ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) : path B a₀ a₁ ⟶ pi (interval Γ) B where
  app _ := TypeCat.ofHom Subtype.val
  naturality _ _ _ := rfl

def pathLam {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))}
    (b : Term B) (h₀ : Term.reindex b (endpointSub Γ false) = a₀)
    (h₁ : Term.reindex b (endpointSub Γ true) = a₁) : Term (path B a₀ a₁) where
  val x := ⟨(lam b).val x, fun {y} _ =>
    ⟨congrArg (fun t : Term (reindex B (endpointSub Γ false)) => t.val y) h₀,
      congrArg (fun t : Term (reindex B (endpointSub Γ true)) => t.val y) h₁⟩⟩
  property _ := rfl

def pathApp {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))} (p : Term (path B a₀ a₁)) : Term B :=
  app (Term.map (pathInclusion B a₀ a₁) p)

@[simp] theorem pathApp_lam {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))}
    (b : Term B) (h₀ : Term.reindex b (endpointSub Γ false) = a₀)
    (h₁ : Term.reindex b (endpointSub Γ true) = a₁) : pathApp (pathLam b h₀ h₁) = b := rfl

theorem pathApp_zero {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))} (p : Term (path B a₀ a₁)) :
    Term.reindex (pathApp p) (endpointSub Γ false) = a₀ := by
  apply Term.ext
  intro x
  exact ((p.val x).property (𝟙 x)).1

theorem pathApp_one {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))} (p : Term (path B a₀ a₁)) :
    Term.reindex (pathApp p) (endpointSub Γ true) = a₁ := by
  apply Term.ext
  intro x
  exact ((p.val x).property (𝟙 x)).2

theorem pathLam_app {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))} (p : Term (path B a₀ a₁)) :
    pathLam (pathApp p) (pathApp_zero p) (pathApp_one p) = p := by
  apply Term.ext
  intro x
  apply Subtype.ext
  have h := congrArg (fun t : Term (pi (interval Γ) B) => t.val x)
    (lam_app (Term.map (pathInclusion B a₀ a₁) p))
  exact h

theorem pathApp_injective {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))} :
    Function.Injective (pathApp (B := B) (a₀ := a₀) (a₁ := a₁)) := by
  intro s t h
  apply Term.ext
  intro x
  have hs := congrArg (fun p => p.val x) (pathLam_app s)
  have ht := congrArg (fun p => p.val x) (pathLam_app t)
  apply Subtype.ext
  have hv := congrArg (fun q => (lam q).val x) h
  exact (congrArg Subtype.val hs).symm.trans (hv.trans (congrArg Subtype.val ht))


def restrictContext {Γ : Context.{u}} (φ : Subcontext Γ) : Context.{u} where
  obj I := {x : Γ.obj I // φ.Holds (Γ.elementsMk I x)}
  map f := TypeCat.ofHom (fun x => ⟨Γ.map f x.val,φ.natural (Functor.Elements.homMk f rfl) x.property⟩)
  map_id I := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun k => k x.val) (Γ.map_id I)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun k => k x.val) (Γ.map_comp f g)

def restrictInclusion {Γ : Context.{u}} (φ : Subcontext Γ) : restrictContext φ ⟶ Γ where
  app _ := TypeCat.ofHom Subtype.val
  naturality _ _ _ := rfl

def restrictSubstitution {Γ Δ : Context.{u}} (φ : Subcontext Γ) (σ : Δ ⟶ Γ) :
    restrictContext (φ.reindex σ) ⟶ restrictContext φ where
  app _ := TypeCat.ofHom (fun x => ⟨σ.app _ x.val,x.property⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact σ.naturality_apply f x.val

def PartialSection.toRestricted {Γ : Context.{u}} {A : Family Γ} {φ : Subcontext Γ}
    (a : PartialSection A φ) : Term (Cartesian.reindex A (restrictInclusion φ)) where
  val x := a.val ((restrictInclusion φ).mapElements.obj x) x.val.property
  property f := a.natural ((restrictInclusion φ).mapElements.map f) _

def PartialSection.ofRestricted {Γ : Context.{u}} {A : Family Γ} {φ : Subcontext Γ}
    (a : Term (Cartesian.reindex A (restrictInclusion φ))) : PartialSection A φ where
  val x p := a.val ((restrictContext φ).elementsMk x.obj ⟨x.val,p⟩)
  natural {x y} f p := by
    let q : (restrictContext φ).elementsMk x.obj ⟨x.val,p⟩ ⟶
        (restrictContext φ).elementsMk y.obj ⟨y.val,φ.natural f p⟩ :=
      Functor.Elements.homMk f.hom (Subtype.ext f.map_val)
    exact a.property q

theorem PartialSection.restricted_roundtrip {Γ : Context.{u}} {A : Family Γ} {φ : Subcontext Γ}
    (a : PartialSection A φ) : ofRestricted a.toRestricted = a := rfl

theorem PartialSection.term_roundtrip {Γ : Context.{u}} {A : Family Γ} {φ : Subcontext Γ}
    (a : Term (Cartesian.reindex A (restrictInclusion φ))) : (ofRestricted a).toRestricted = a := rfl


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


def pathReindex {Γ Δ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) (σ : Δ ⟶ Γ) :
    reindex (path B a₀ a₁) σ ⟶
      path (reindex B (liftSub (interval Γ) σ)) (Term.reindex a₀ σ) (Term.reindex a₁ σ) where
  app x := TypeCat.ofHom (fun p => ⟨(piReindex (interval Γ) B σ).app x p.val,
    fun f => p.property (σ.mapElements.map f)⟩)
  naturality _ _ _ := rfl

theorem pathLam_reindex {Γ Δ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))}
    (b : Term B) (h₀ : Term.reindex b (endpointSub Γ false) = a₀)
    (h₁ : Term.reindex b (endpointSub Γ true) = a₁) (σ : Δ ⟶ Γ) :
    Term.map (pathReindex B a₀ a₁ σ) (Term.reindex (pathLam b h₀ h₁) σ) =
      pathLam (Term.reindex b (liftSub (interval Γ) σ))
        (congrArg (fun t => Term.reindex t σ) h₀)
        (congrArg (fun t => Term.reindex t σ) h₁) := rfl

theorem pathApp_reindex {Γ Δ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))} (t : Term (path B a₀ a₁)) (σ : Δ ⟶ Γ) :
    pathApp (Term.map (pathReindex B a₀ a₁ σ) (Term.reindex t σ)) =
      Term.reindex (pathApp t) (liftSub (interval Γ) σ) := rfl


def restrictedInterval {Γ : Context.{u}} (φ : Subcontext Γ) :
    restrictContext (φ.reindex (projection (interval Γ))) ⟶ total (interval (restrictContext φ)) where
  app _ := TypeCat.ofHom (fun z => ⟨⟨z.val.1,z.property⟩,z.val.2⟩)
  naturality _ _ _ := rfl


end SquareKit.Cubical.Cartesian
