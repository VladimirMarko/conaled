import SquareKit.Internal.Cubical.Dimensions
import Mathlib.CategoryTheory.Elements

/-!
# Dependent presheaf families

Families are actual functors on categories of elements. This constructs
reindexing and comprehension before any fibrancy or identity elimination claim.
-/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

abbrev Context := Cubeᵒᵖ ⥤ Type u
abbrev Family (Γ : Context.{u}) := Γ.Elements ⥤ Type u

/-- Terms reuse Mathlib's coherent sections on the category of elements. -/
abbrev Term {Γ : Context.{u}} (A : Family Γ) : Type u := A.sections

@[ext] theorem Term.ext {Γ : Context.{u}} {A : Family Γ} {s t : Term A}
    (h : ∀ x, s.val x = t.val x) : s = t := Subtype.ext (funext h)

/-- Reindexing changes the generalized base element by the given substitution. -/
def reindex {Γ Δ : Context.{u}} (A : Family Γ) (σ : Δ ⟶ Γ) : Family Δ :=
  σ.mapElements ⋙ A

def Term.reindex {Γ Δ : Context.{u}} {A : Family Γ} (t : Term A) (σ : Δ ⟶ Γ) :
    Term (Presheaf.reindex A σ) where
  val x := t.val (σ.mapElements.obj x)
  property f := t.property (σ.mapElements.map f)

@[simp] theorem reindex_id {Γ : Context.{u}} (A : Family Γ) :
    reindex A (𝟙 Γ) = A := by rfl

@[simp] theorem reindex_comp {Γ Δ Θ : Context.{u}} (A : Family Γ)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    reindex (reindex A σ) τ = reindex A (τ ≫ σ) := by rfl

/-- Restrict a dependent pair along a cube substitution. -/
def totalMap {Γ : Context.{u}} (A : Family Γ) {I J : Cubeᵒᵖ} (f : I ⟶ J)
    (z : Σ x : Γ.obj I, A.obj (Γ.elementsMk I x)) :
    Σ y : Γ.obj J, A.obj (Γ.elementsMk J y) :=
  ⟨Γ.map f z.1, A.map (Functor.Elements.homMk f rfl) z.2⟩

theorem totalMap_ofHom {Γ : Context.{u}} (A : Family Γ) {x y : Γ.Elements}
    (f : x ⟶ y) (a : A.obj x) :
    totalMap A f.hom ⟨x.val, a⟩ = ⟨y.val, A.map f a⟩ := by
  rcases x with @⟨I, x⟩
  rcases y with @⟨J, y⟩
  rcases f with ⟨f, h⟩
  change I ⟶ J at f
  change Γ.map f x = y at h
  subst y
  rfl

/-- The comprehension context has actual dependent pairs at every cube. -/
def total {Γ : Context.{u}} (A : Family Γ) : Context.{u} where
  obj I := Σ x : Γ.obj I, A.obj (Γ.elementsMk I x)
  map f := TypeCat.ofHom (totalMap A f)
  map_id I := by
    apply ConcreteCategory.hom_ext
    intro z
    rcases z with ⟨x,a⟩
    simpa using totalMap_ofHom A (𝟙 (Γ.elementsMk I x)) a
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
      _ = ⟨Γ.map g (Γ.map f x), A.map (p ≫ q) a⟩ := totalMap_ofHom A (p ≫ q) a
      _ = ⟨Γ.map g (Γ.map f x), A.map q (A.map p a)⟩ := by simp
      _ = totalMap A g ⟨Γ.map f x, A.map p a⟩ := (totalMap_ofHom A q _).symm
      _ = _ := congrArg (totalMap A g) (totalMap_ofHom A p a).symm

/-- Comprehension projection is natural, not a choice of representatives. -/
def projection {Γ : Context.{u}} (A : Family Γ) : total A ⟶ Γ where
  app _ := TypeCat.ofHom (fun z => z.1)
  naturality _ _ _ := rfl

/-- Pair a substitution with its dependent section. -/
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

/-- The generic component after pairing is exactly the supplied section. -/
@[simp] theorem generic_pair {Γ Δ : Context.{u}} {A : Family Γ}
    (σ : Δ ⟶ Γ) (t : Term (reindex A σ)) :
    Term.reindex (generic A) (pair σ t) = t := rfl

/-- Every map into comprehension is recovered from its two components. -/
theorem pair_eta {Γ Δ : Context.{u}} {A : Family Γ} (τ : Δ ⟶ total A) :
    pair (τ ≫ projection A) (Term.reindex (generic A) τ) = τ := rfl

/-- Pairing commutes with simultaneous substitution. -/
theorem pair_reindex {Γ Δ Θ : Context.{u}} {A : Family Γ}
    (σ : Δ ⟶ Γ) (t : Term (reindex A σ)) (τ : Θ ⟶ Δ) :
    τ ≫ pair σ t = pair (τ ≫ σ) (Term.reindex t τ) := rfl

/-- Two substitutions retain the whole dependent term, including its fiber. -/
theorem Term.reindex_comp {Γ Δ Θ : Context.{u}} {A : Family Γ} (t : Term A)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    Term.reindex (Term.reindex t σ) τ = Term.reindex t (τ ≫ σ) := rfl

/-- The terminal context is the constant singleton presheaf. -/
def terminal : Context.{u} := (Functor.const Cubeᵒᵖ).obj PUnit

def terminalSub (Γ : Context.{u}) : Γ ⟶ terminal where
  app _ := TypeCat.ofHom (fun _ => PUnit.unit)
  naturality _ _ _ := rfl

theorem terminal_unique {Γ : Context.{u}} (σ : Γ ⟶ terminal) :
    σ = terminalSub Γ := by
  ext I x
  change (σ.app I x : PUnit) = PUnit.unit
  cases σ.app I x
  rfl

@[simp] theorem Term.reindex_id {Γ : Context.{u}} {A : Family Γ} (t : Term A) :
    Term.reindex t (𝟙 Γ) = t := rfl

end SquareKit.Cubical.Presheaf
