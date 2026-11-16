import SquareKit.Internal.Cubical.CartesianRepresentables

/-! Filling tested only on represented contexts. The uniformity law is retained
as separate evidence; an operation alone does not certify a family. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u

@[ext] theorem PartialSection.ext {Γ : Context.{u}} {A : Family Γ} {φ : Subcontext Γ}
    {s t : PartialSection A φ} (h : ∀ x hx, s.val x hx = t.val x hx) : s = t := by
  cases s
  cases t
  congr
  funext x hx
  exact h x hx

@[ext] theorem OpenBox.ext {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {φ : Subcontext Γ} {r : Term (interval Γ)} {b c : OpenBox A φ r}
    (ht : b.tube = c.tube) (hb : b.base = c.base) : b = c := by
  cases b
  cases c
  cases ht
  cases hb
  rfl

def PartialSection.map {Γ : Context.{u}} {A B : Family Γ} {φ : Subcontext Γ}
    (η : A ⟶ B) (s : PartialSection A φ) : PartialSection B φ where
  val x hx := η.app x (s.val x hx)
  natural f hx := (ConcreteCategory.congr_hom (η.naturality f) _).symm.trans
    (congrArg (η.app _) (s.natural f hx))

def OpenBox.map {Γ : Context.{u}} {A B : Family (total (interval Γ))}
    {φ : Subcontext Γ} {r : Term (interval Γ)} (η : A ⟶ B) (b : OpenBox A φ r) :
    OpenBox B φ r where
  tube := b.tube.map η
  base := Term.map (Functor.whiskerLeft (graph r).mapElements η) b.base
  boundary x h := congrArg (η.app (extendObj (interval Γ) x (r.val x))) (b.boundary x h)

structure LocalFilling {Γ : Context.{u}} (A : Family Γ) where
  fill : {I : Cube} → (p : total (interval (representable.{u} I)) ⟶ Γ) →
    (φ : Subcontext (representable.{u} I)) → (r : Term (interval (representable I))) →
    OpenBox (reindex A p) φ r → Term (reindex A p)

structure LocalFilling.Lawful {Γ : Context.{u}} {A : Family Γ} (F : LocalFilling A) : Prop where
  fills : ∀ {I : Cube} (p : total (interval (representable.{u} I)) ⟶ Γ)
    (φ : Subcontext (representable.{u} I)) (r : Term (interval (representable I)))
    (b : OpenBox (reindex A p) φ r),
    b.Fills (F.fill p φ r b)
  uniform : ∀ {I J : Cube} (p : total (interval (representable.{u} I)) ⟶ Γ)
    (φ : Subcontext (representable.{u} I)) (r : Term (interval (representable I)))
    (b : OpenBox (reindex A p) φ r) (f : J ⟶ I),
    F.fill (intervalSub (representableMap f) ≫ p)
      (φ.reindex (representableMap f)) (Term.reindex r (representableMap f)) (b.reindex (representableMap f)) =
      Term.reindex (F.fill p φ r b) (intervalSub (representableMap f))

def Filling.toLocal {Γ : Context.{u}} {A : Family Γ} (F : Filling A) : LocalFilling A where
  fill := F.fill

theorem Filling.toLocal_lawful {Γ : Context.{u}} {A : Family Γ} {F : Filling A}
    (h : F.Lawful) : F.toLocal.Lawful where
  fills := h.fills
  uniform p φ r b f := h.uniform p φ r b (representableMap f)

def LocalFilling.reindex {Γ Δ : Context.{u}} {A : Family Γ} (F : LocalFilling A)
    (σ : Δ ⟶ Γ) : LocalFilling (Cartesian.reindex A σ) where
  fill p φ r b := F.fill (p ≫ σ) φ r b

theorem LocalFilling.Lawful.reindex {Γ Δ : Context.{u}} {A : Family Γ}
    {F : LocalFilling A} (hF : F.Lawful) (σ : Δ ⟶ Γ) : (F.reindex σ).Lawful where
  fills p φ r b := hF.fills (p ≫ σ) φ r b
  uniform p φ r b f := hF.uniform (p ≫ σ) φ r b f

end SquareKit.Cubical.Cartesian
