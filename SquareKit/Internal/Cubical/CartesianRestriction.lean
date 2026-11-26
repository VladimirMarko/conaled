import SquareKit.Internal.Cubical.CartesianDimensions

/-! Change of cube category on contexts, dependent families and selected sections. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u

abbrev Context := Cubeᵒᵖ ⥤ Type u
abbrev Family (Γ : Context.{u}) := Γ.Elements ⥤ Type u
abbrev Term {Γ : Context.{u}} (A : Family Γ) := A.sections

@[ext] theorem Term.ext {Γ : Context.{u}} {A : Family Γ} {s t : Term A}
    (h : ∀ x, s.val x = t.val x) : s = t := Subtype.ext (funext h)

def restrict (Γ : Presheaf.Context.{u}) : Context.{u} := inclusion.op ⋙ Γ

def restrictMap {Γ Δ : Presheaf.Context.{u}} (f : Γ ⟶ Δ) : restrict Γ ⟶ restrict Δ :=
  Functor.whiskerLeft inclusion.op f

/-- The functor on generalized elements induced by the cube inclusion. -/
def elements (Γ : Presheaf.Context.{u}) : (restrict Γ).Elements ⥤ Γ.Elements where
  obj x := Γ.elementsMk (inclusion.op.obj x.obj) x.val
  map f := Functor.Elements.homMk (inclusion.op.map f.hom) f.map_val
  map_id _ := rfl
  map_comp f g := by
    apply Functor.Elements.Hom.ext
    exact inclusion.op.map_comp f.hom g.hom

def restrictFamily {Γ : Presheaf.Context.{u}} (A : Presheaf.Family Γ) :
    Family (restrict Γ) := elements Γ ⋙ A

def restrictTerm {Γ : Presheaf.Context.{u}} {A : Presheaf.Family Γ}
    (s : Presheaf.Term A) : Term (restrictFamily A) where
  val x := s.val ((elements Γ).obj x)
  property f := s.property ((elements Γ).map f)

def restrictFamilyMap {Γ : Presheaf.Context.{u}} {A B : Presheaf.Family Γ}
    (f : A ⟶ B) : restrictFamily A ⟶ restrictFamily B := Functor.whiskerLeft (elements Γ) f

/-- Restriction does not forget the value at any source cube. -/
theorem restrictTerm_injective {Γ : Presheaf.Context.{u}} {A : Presheaf.Family Γ} :
    Function.Injective (restrictTerm (A := A)) := by
  intro s t h
  apply Presheaf.Term.ext
  intro x
  rcases x with @⟨⟨⟨n⟩⟩, x⟩
  have hh := congrArg (fun q => q.val ((restrict Γ).elementsMk (.op ⟨n⟩) x)) h
  exact hh

@[simp] theorem restrictMap_comp {Γ Δ Θ : Presheaf.Context.{u}}
    (f : Γ ⟶ Δ) (g : Δ ⟶ Θ) : restrictMap (f ≫ g) = restrictMap f ≫ restrictMap g := rfl

/-- Target comprehension, with its own Cartesian substitution action. -/
def totalMap {Γ : Context.{u}} (A : Family Γ) {I J : Cubeᵒᵖ} (f : I ⟶ J)
    (z : Σ x : Γ.obj I, A.obj (Γ.elementsMk I x)) :
    Σ y : Γ.obj J, A.obj (Γ.elementsMk J y) :=
  ⟨Γ.map f z.1, A.map (Functor.Elements.homMk f rfl) z.2⟩

theorem totalMap_hom {Γ : Context.{u}} (A : Family Γ) {x y : Γ.Elements}
    (f : x ⟶ y) (a : A.obj x) :
    totalMap A f.hom ⟨x.val, a⟩ = ⟨y.val, A.map f a⟩ := by
  rcases x with @⟨I, x⟩
  rcases y with @⟨J, y⟩
  rcases f with ⟨f, h⟩
  change I ⟶ J at f
  change Γ.map f x = y at h
  subst y
  rfl

def total {Γ : Context.{u}} (A : Family Γ) : Context.{u} where
  obj I := Σ x : Γ.obj I, A.obj (Γ.elementsMk I x)
  map f := TypeCat.ofHom (totalMap A f)
  map_id I := by
    apply ConcreteCategory.hom_ext
    intro z
    rcases z with ⟨x,a⟩
    simpa using totalMap_hom A (𝟙 (Γ.elementsMk I x)) a
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro z
    rcases z with ⟨x,a⟩
    let p : Γ.elementsMk _ x ⟶ Γ.elementsMk _ (Γ.map f x) :=
      Functor.Elements.homMk f rfl
    let q : Γ.elementsMk _ (Γ.map f x) ⟶ Γ.elementsMk _ (Γ.map g (Γ.map f x)) :=
      Functor.Elements.homMk g rfl
    change totalMap A (f ≫ g) ⟨x,a⟩ = totalMap A g (totalMap A f ⟨x,a⟩)
    calc
      _ = ⟨Γ.map g (Γ.map f x), A.map (p ≫ q) a⟩ := totalMap_hom A (p ≫ q) a
      _ = ⟨Γ.map g (Γ.map f x), A.map q (A.map p a)⟩ := by simp
      _ = totalMap A g ⟨Γ.map f x, A.map p a⟩ := (totalMap_hom A q _).symm
      _ = _ := congrArg (totalMap A g) (totalMap_hom A p a).symm

/-- Both comprehension presentations have exactly the same dependent pairs. -/
def totalComparison {Γ : Presheaf.Context.{u}} (A : Presheaf.Family Γ) :
    restrict (Presheaf.total A) ≅ total (restrictFamily A) where
  hom := { app := fun _ => TypeCat.ofHom (fun z => z), naturality := fun _ _ _ => rfl }
  inv := { app := fun _ => TypeCat.ofHom (fun z => z), naturality := fun _ _ _ => rfl }

def projection {Γ : Context.{u}} (A : Family Γ) : total A ⟶ Γ where
  app _ := TypeCat.ofHom (fun z => z.1)
  naturality _ _ _ := rfl

def Term.map {Γ : Context.{u}} {A B : Family Γ} (η : A ⟶ B) (t : Term A) : Term B where
  val x := η.app x (t.val x)
  property f := by rw [← η.naturality_apply, t.property f]

def extendObj {Γ : Context.{u}} (A : Family Γ) (x : Γ.Elements) (a : A.obj x) :
    (total A).Elements := (total A).elementsMk x.obj ⟨x.val, a⟩

def extendHom {Γ : Context.{u}} (A : Family Γ) {x y : Γ.Elements}
    (f : x ⟶ y) (a : A.obj x) : extendObj A x a ⟶ extendObj A y (A.map f a) :=
  Functor.Elements.homMk f.hom (totalMap_hom A f a)

def extendAlong {Γ : Context.{u}} (A : Family Γ) {x y : Γ.Elements}
    (f : x ⟶ y) {a : A.obj x} {a' : A.obj y} (h : A.map f a = a') :
    extendObj A x a ⟶ extendObj A y a' :=
  Functor.Elements.homMk f.hom ((totalMap_hom A f a).trans (by rw [h]; rfl))

def sigmaMap {Γ : Context.{u}} (A : Family Γ) (B : Family (total A))
    {x y : Γ.Elements} (f : x ⟶ y) (z : Σ a : A.obj x, B.obj (extendObj A x a)) :
    Σ a : A.obj y, B.obj (extendObj A y a) :=
  ⟨A.map f z.1, B.map (extendHom A f z.1) z.2⟩

theorem sigmaMap_extendAlong {Γ : Context.{u}} (A : Family Γ) (B : Family (total A))
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
    simpa only [he, Functor.map_id, types_id_apply] using sigmaMap_extendAlong A B (𝟙 x) h b
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro z
    rcases z with ⟨a,b⟩
    have h : A.map (f ≫ g) a = A.map g (A.map f a) := by simp
    have he : extendAlong A (f ≫ g) h = extendHom A f a ≫ extendHom A g (A.map f a) := rfl
    change sigmaMap A B (f ≫ g) ⟨a,b⟩ = sigmaMap A B g (sigmaMap A B f ⟨a,b⟩)
    have hs := sigmaMap_extendAlong A B (f ≫ g) h b
    rw [he, B.map_comp] at hs
    exact hs

/-- Cartesian dependent functions quantify over all Cartesian generalized inputs. -/
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

def PiElement.restrict {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {x y : Γ.Elements} (f : x ⟶ y) (p : PiElement A B x) : PiElement A B y where
  val g a := p.val (f ≫ g) a
  naturality g h a := by simpa only [Category.assoc] using p.naturality (f ≫ g) h a

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

/-- Forward comparison for general dependent products; no inverse is assumed. -/
def piComparison {Γ : Presheaf.Context.{u}} (A : Presheaf.Family Γ)
    (B : Presheaf.Family (Presheaf.total A)) :
    restrictFamily (Presheaf.pi A B) ⟶ pi (restrictFamily A) ((totalComparison A).inv.mapElements ⋙ restrictFamily B) where
  app x := TypeCat.ofHom (fun p => {
    val := fun f a => p.val ((elements Γ).map f) a
    naturality := fun f g a => by
      have h := p.naturality ((elements Γ).map f) ((elements Γ).map g) a
      rw [← (elements Γ).map_comp] at h
      exact h })
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply PiElement.ext
    intro z g a
    change p.val ((elements Γ).map f ≫ (elements Γ).map g) a =
      p.val ((elements Γ).map (f ≫ g)) a
    rw [(elements Γ).map_comp]


/-- Substitute a whole section, retaining all dependent values. -/
def Term.reindex {Γ Δ : Context.{u}} {A : Family Γ} (s : Term A) (τ : Δ ⟶ Γ) :
    Term (τ.mapElements ⋙ A) where
  val x := s.val (τ.mapElements.obj x)
  property f := s.property (τ.mapElements.map f)

theorem Term.reindex_comp {Γ Δ Θ : Context.{u}} {A : Family Γ} (s : Term A)
    (τ : Δ ⟶ Γ) (σ : Θ ⟶ Δ) : Term.reindex (Term.reindex s τ) σ = Term.reindex s (σ ≫ τ) := rfl

/-- Dependent sums retain the coefficient as well as the first projection. -/
def sigmaComparison {Γ : Presheaf.Context.{u}} (A : Presheaf.Family Γ)
    (B : Presheaf.Family (Presheaf.total A)) :
    restrictFamily (Presheaf.sigma A B) ≅
      sigma (restrictFamily A) ((totalComparison A).inv.mapElements ⋙ restrictFamily B) where
  hom := { app := fun _ => TypeCat.ofHom (fun z => z)
           naturality := fun _ _ _ => rfl }
  inv := { app := fun _ => TypeCat.ofHom (fun z => z)
           naturality := fun _ _ _ => rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

end SquareKit.Cubical.Cartesian
