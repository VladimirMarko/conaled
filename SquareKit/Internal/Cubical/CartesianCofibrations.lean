import SquareKit.Internal.Cubical.CartesianSievePatterns

/-! Extensional Cartesian cofibrations and quantification over the whole interval. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u
/-- The interval coordinate of a generalized pair. -/
def intervalCoordinate (Γ : Context.{u}) : total (interval Γ) ⟶ representable ⟨1⟩ where
  app _ := TypeCat.ofHom (fun z => z.2)
  naturality _ _ _ := rfl

namespace Subcontext
variable {Γ Δ Θ : Context.{u}}

@[ext] theorem ext {φ ψ : Subcontext Γ} (h : ∀ x, φ.Holds x ↔ ψ.Holds x) : φ = ψ := by
  cases φ; cases ψ
  congr
  funext x
  exact propext (h x)

@[simp] theorem reindex_id (φ : Subcontext Γ) : φ.reindex (𝟙 Γ) = φ := rfl
@[simp] theorem reindex_comp (φ : Subcontext Γ) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    (φ.reindex σ).reindex τ = φ.reindex (τ ≫ σ) := rfl

def bot : Subcontext Γ where
  Holds _ := False
  natural _ := False.elim

def top : Subcontext Γ where
  Holds _ := True
  natural _ _ := trivial

def meet (φ ψ : Subcontext Γ) : Subcontext Γ where
  Holds x := φ.Holds x ∧ ψ.Holds x
  natural f h := ⟨φ.natural f h.1, ψ.natural f h.2⟩

def join (φ ψ : Subcontext Γ) : Subcontext Γ where
  Holds x := φ.Holds x ∨ ψ.Holds x
  natural f h := h.elim (fun h => Or.inl (φ.natural f h)) (fun h => Or.inr (ψ.natural f h))

/-- This is equality of interval terms, including proper diagonals. -/
def intervalEq (r s : Term (interval Γ)) : Subcontext Γ where
  Holds x := r.val x = s.val x
  natural f h := (r.property f).symm.trans ((congrArg ((interval Γ).map f) h).trans (s.property f))

/-- Endpoint faces are subobjects of the full interval context. -/
def intervalFace (Γ : Context.{u}) (b : Bool) : Subcontext (total (interval Γ)) :=
  ((Face.eq (.var 0) (.endpoint b)).cofibration.reindex (intervalCoordinate Γ)).toSubcontext

def le (φ ψ : Subcontext Γ) : Prop := ∀ x, φ.Holds x → ψ.Holds x

/-- The sieve obtained by pulling a subcontext back to a generalized point. -/
def sieveAt (φ : Subcontext Γ) (x : Γ.Elements) : Sieve x.obj.unop where
  arrows _ f := φ.Holds (Γ.elementsMk _ (Γ.map (Quiver.Hom.op f) x.val))
  downward_closed {Y Z f} h g := by
    let a := Γ.elementsMk (.op Y) (Γ.map (Quiver.Hom.op f) x.val)
    let b := Γ.elementsMk (.op Z) (Γ.map (Quiver.Hom.op (g ≫ f)) x.val)
    let k : a ⟶ b := Functor.Elements.homMk (Quiver.Hom.op g) (by
      change Γ.map (Quiver.Hom.op g) (Γ.map (Quiver.Hom.op f) x.val) = _
      exact (Γ.map_comp_apply (Quiver.Hom.op f) (Quiver.Hom.op g) x.val).symm)
    exact φ.natural k h

theorem localFormula (φ : Subcontext Γ) (x : Γ.Elements) :
    ∃ p : Face x.obj.unop.dimension, ∀ {y : Γ.Elements} (f : x ⟶ y),
      φ.Holds y ↔ (p.subst f.hom.unop).Holds := by
  refine ⟨Face.ofSieve (φ.sieveAt x), fun {y} f => ?_⟩
  rw [Face.ofSieve_holds]
  change φ.Holds y ↔ φ.Holds (Γ.elementsMk _ (Γ.map f.hom x.val))
  rw [f.map_val]

/-- The certificate is a proposition, not a choice of raw formula exposed to fillers. -/
noncomputable def toCofibration (φ : Subcontext Γ) : Cofibration Γ where
  toSubcontext := φ
  localFormula := φ.localFormula

@[simp] theorem toCofibration_subcontext (φ : Subcontext Γ) :
    φ.toCofibration.toSubcontext = φ := rfl

/-- Membership at the fresh variable represents quantification at all refinements. -/
def forallInterval (φ : Subcontext (total (interval Γ))) : Subcontext Γ where
  Holds x := φ.Holds (freshExtension x)
  natural {_x y} f h := φ.natural
    (intervalArgument (f ≫ freshBaseHom y) ⟨Cube.fresh y.obj.unop⟩) h

theorem forallInterval_iff (φ : Subcontext (total (interval Γ))) (x : Γ.Elements) :
    (φ.forallInterval).Holds x ↔
      ∀ {y : Γ.Elements} (_f : x ⟶ y) (r : (interval Γ).obj y),
        φ.Holds (extendObj (interval Γ) y r) := by
  constructor
  · intro h y f r
    exact φ.natural (intervalArgument f r) h
  · intro h
    exact h (freshBaseHom x) ⟨Cube.fresh x.obj.unop⟩

theorem forallInterval_reindex (φ : Subcontext (total (interval Γ))) (σ : Δ ⟶ Γ) :
    (φ.reindex (intervalSub σ)).forallInterval = φ.forallInterval.reindex σ := by
  apply ext
  intro x
  change φ.Holds ((intervalSub σ).mapElements.obj (freshExtension x)) ↔
    φ.Holds (freshExtension (σ.mapElements.obj x))
  have he : (intervalSub σ).mapElements.obj (freshExtension x) =
      freshExtension (σ.mapElements.obj x) := by
    change (total (interval Γ)).elementsMk _ ⟨σ.app _ (Δ.map (dropOpp x.obj) x.val), _⟩ =
      (total (interval Γ)).elementsMk _ ⟨Γ.map (dropOpp x.obj) (σ.app _ x.val), _⟩
    rw [σ.naturality_apply]
    rfl
  rw [he]

/-- Interval quantification is right adjoint to weakening a subcontext. -/
theorem forallInterval_adjunction (φ : Subcontext (total (interval Γ))) (ψ : Subcontext Γ) :
    (ψ.reindex (projection (interval Γ))).le φ ↔ ψ.le φ.forallInterval := by
  constructor
  · intro h x hx
    exact h (freshExtension x) (ψ.natural (freshBaseHom x) hx)
  · intro h x hx
    rcases x with @⟨I, γ, r⟩
    exact (forallInterval_iff φ (Γ.elementsMk I γ)).mp (h _ hx) (𝟙 _) r

@[simp] theorem meet_reindex (φ ψ : Subcontext Γ) (σ : Δ ⟶ Γ) :
    (φ.meet ψ).reindex σ = (φ.reindex σ).meet (ψ.reindex σ) := rfl
@[simp] theorem join_reindex (φ ψ : Subcontext Γ) (σ : Δ ⟶ Γ) :
    (φ.join ψ).reindex σ = (φ.reindex σ).join (ψ.reindex σ) := rfl
@[simp] theorem intervalEq_reindex (r s : Term (interval Γ)) (σ : Δ ⟶ Γ) :
    (intervalEq r s).reindex σ = intervalEq (Term.reindex r σ) (Term.reindex s σ) := rfl

@[simp] theorem forallInterval_meet (φ ψ : Subcontext (total (interval Γ))) :
    (φ.meet ψ).forallInterval = φ.forallInterval.meet ψ.forallInterval := rfl

@[simp] theorem forallInterval_top :
    (top : Subcontext (total (interval Γ))).forallInterval = top := rfl

@[simp] theorem forallInterval_bot :
    (bot : Subcontext (total (interval Γ))).forallInterval = bot := rfl
end Subcontext

/-- All stable Cartesian subobjects, with no additional filling hypothesis. -/
noncomputable def cofibrationEquiv (Γ : Context.{u}) : Cofibration Γ ≃ Subcontext Γ where
  toFun := Cofibration.toSubcontext
  invFun := Subcontext.toCofibration
  left_inv φ := by cases φ; rfl
  right_inv _ := rfl

namespace Cofibration
variable {Γ Δ : Context.{u}}
@[ext] theorem ext {φ ψ : Cofibration Γ} (h : ∀ x, φ.Holds x ↔ ψ.Holds x) : φ = ψ :=
  (cofibrationEquiv Γ).injective (Subcontext.ext h)

noncomputable def forallInterval (φ : Cofibration (total (interval Γ))) : Cofibration Γ :=
  φ.toSubcontext.forallInterval.toCofibration

@[simp] theorem forallInterval_reindex (φ : Cofibration (total (interval Γ))) (σ : Δ ⟶ Γ) :
    (φ.reindex (intervalSub σ)).forallInterval = φ.forallInterval.reindex σ := by
  apply (cofibrationEquiv Δ).injective
  exact Subcontext.forallInterval_reindex φ.toSubcontext σ
end Cofibration

@[simp] theorem Subcontext.toCofibration_reindex {Γ Δ : Context.{u}}
    (φ : Subcontext Γ) (σ : Δ ⟶ Γ) :
    (φ.reindex σ).toCofibration = φ.toCofibration.reindex σ := by
  apply Cofibration.ext
  intro x
  rfl
end SquareKit.Cubical.Cartesian
