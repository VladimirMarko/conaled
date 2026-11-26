import SquareKit.Internal.Cubical.CartesianSubstitution
import SquareKit.Internal.Cubical.CartesianDependentFilling
import SquareKit.Internal.Cubical.CartesianCofibrations

/-! Homotopy fibers of arbitrary Cartesian family maps. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u

def homogeneousRefl {Γ : Context.{u}} {A : Family Γ} (a : Term A) :
    Term (homogeneousPath A a a) :=
  pathLam (Term.reindex a (projection (interval Γ))) rfl rfl

namespace Homotopy

def fiber {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (b : Term B) : Family Γ :=
  sigma A (homogeneousPath (reindex B (projection A))
    (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
    (Term.reindex b (projection A)))

abbrev genericFiber {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) :=
  fiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)


def sigmaSecondIso {Γ : Context.{u}} (A : Family Γ) {B C : Family (total A)}
    (e : B ≅ C) : sigma A B ≅ sigma A C where
  hom := {
    app := fun x => TypeCat.ofHom (fun z => ⟨z.1, e.hom.app (extendObj A x z.1) z.2⟩)
    naturality := fun x y f => by
      apply ConcreteCategory.hom_ext
      intro z
      exact congrArg (Sigma.mk (A.map f z.1)) (e.hom.naturality_apply (extendHom A f z.1) z.2) }
  inv := {
    app := fun x => TypeCat.ofHom (fun z => ⟨z.1, e.inv.app (extendObj A x z.1) z.2⟩)
    naturality := fun x y f => by
      apply ConcreteCategory.hom_ext
      intro z
      exact congrArg (Sigma.mk (A.map f z.1)) (e.inv.naturality_apply (extendHom A f z.1) z.2) }
  hom_inv_id := by
    ext x z
    exact congrArg (Sigma.mk z.1) (e.hom_inv_id_app_apply (extendObj A x z.1) z.2)
  inv_hom_id := by
    ext x z
    exact congrArg (Sigma.mk z.1) (e.inv_hom_id_app_apply (extendObj A x z.1) z.2)

theorem pathInverse_reindex {Γ Δ Θ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (p : Term (path (reindex B (liftSub (interval Γ) σ))
      (Term.reindex a₀ σ) (Term.reindex a₁ σ))) :
    Term.reindex (Term.map (pathReindexIso B a₀ a₁ σ).inv p) τ =
      Term.map (pathReindexIso B a₀ a₁ (τ ≫ σ)).inv
        (Term.map (pathReindexIso (reindex B (liftSub (interval Γ) σ))
          (Term.reindex a₀ σ) (Term.reindex a₁ σ) τ).hom (Term.reindex p τ)) := by
  let e := pathReindexIso B a₀ a₁ σ
  let d := pathReindexIso (reindex B (liftSub (interval Γ) σ))
    (Term.reindex a₀ σ) (Term.reindex a₁ σ) τ
  let c := pathReindexIso B a₀ a₁ (τ ≫ σ)
  apply Term.map_injective_of_iso c
  apply Term.ext
  intro x
  exact (congrArg (d.hom.app x) (e.inv_hom_id_app_apply (τ.mapElements.obj x)
    (p.val (τ.mapElements.obj x)))).trans
    (c.inv_hom_id_app_apply x (d.hom.app x (p.val (τ.mapElements.obj x)))).symm

def fiberReindexIso {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (b : Term B)
    (σ : Δ ⟶ Γ) : reindex (fiber f b) σ ≅
      fiber (Functor.whiskerLeft σ.mapElements f) (Term.reindex b σ) :=
  sigmaSecondIso (reindex A σ)
    (pathReindexIso (intervalCoefficient (reindex B (projection A)))
      (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
      (Term.reindex b (projection A)) (liftSub A σ))

/-- Fiber introduction directly over a context substitution. -/
def fiberIntroOver {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (b : Term B)
    (σ : Δ ⟶ Γ) (a : Term (reindex A σ))
    (p : Term (homogeneousPath (reindex B σ)
      (Term.map (Functor.whiskerLeft σ.mapElements f) a) (Term.reindex b σ))) :
    Term (reindex (fiber f b) σ) :=
  sigmaIntro (B := reindex (homogeneousPath (reindex B (projection A))
    (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
    (Term.reindex b (projection A))) (liftSub A σ)) a (Term.map (pathReindexIso (intervalCoefficient (reindex B (projection A)))
    (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
    (Term.reindex b (projection A)) (pair σ a)).inv p)

def fiberIntro {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (b : Term B)
    (a : Term A) (p : Term (homogeneousPath B (Term.map f a) b)) : Term (fiber f b) :=
  sigmaIntro a (Term.map (pathReindexIso (intervalCoefficient (reindex B (projection A)))
    (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
    (Term.reindex b (projection A)) (pair (𝟙 Γ) a)).inv p)

def fiberPath {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (b : Term B)
    (z : Term (fiber f b)) : Term (homogeneousPath B (Term.map f (sigmaFst z)) b) :=
  Term.map (pathReindexIso (intervalCoefficient (reindex B (projection A)))
    (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
    (Term.reindex b (projection A)) (pair (𝟙 Γ) (sigmaFst z))).hom (sigmaSnd z)

@[simp] theorem fiberIntro_fst {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (b : Term B)
    (a : Term A) (p : Term (homogeneousPath B (Term.map f a) b)) :
    sigmaFst (fiberIntro f b a p) = a := rfl

@[simp] theorem fiber_eta {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (b : Term B)
    (z : Term (fiber f b)) : fiberIntro f b (sigmaFst z) (fiberPath f b z) = z := by
  let e := pathReindexIso (intervalCoefficient (reindex B (projection A)))
    (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
    (Term.reindex b (projection A)) (pair (𝟙 Γ) (sigmaFst z))
  exact congrArg (sigmaIntro (sigmaFst z)) (Term.map_iso_roundtrip e (sigmaSnd z))

def fiberPathOver {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (b : Term B)
    (σ : Δ ⟶ Γ) (z : Term (reindex (fiber f b) σ)) :
    Term (homogeneousPath (reindex B σ)
      (Term.map (Functor.whiskerLeft σ.mapElements f) (sigmaFst (B := reindex (homogeneousPath (reindex B (projection A)) (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A)) (Term.reindex b (projection A))) (liftSub A σ)) z)) (Term.reindex b σ)) :=
  Term.map (pathReindexIso (intervalCoefficient (reindex B (projection A)))
    (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
    (Term.reindex b (projection A)) (pair σ (sigmaFst (B := reindex (homogeneousPath (reindex B (projection A)) (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A)) (Term.reindex b (projection A))) (liftSub A σ)) z))).hom (sigmaSnd (B := reindex (homogeneousPath (reindex B (projection A)) (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A)) (Term.reindex b (projection A))) (liftSub A σ)) z)

theorem fiberIntroOver_eta {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (b : Term B)
    (σ : Δ ⟶ Γ) (z : Term (reindex (fiber f b) σ)) :
    fiberIntroOver f b σ (sigmaFst (B := reindex (homogeneousPath (reindex B (projection A)) (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A)) (Term.reindex b (projection A))) (liftSub A σ)) z) (fiberPathOver f b σ z) = z := by
  let e := pathReindexIso (intervalCoefficient (reindex B (projection A)))
    (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
    (Term.reindex b (projection A)) (pair σ (sigmaFst (B := reindex (homogeneousPath (reindex B (projection A)) (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A)) (Term.reindex b (projection A))) (liftSub A σ)) z))
  exact congrArg (sigmaIntro (B := reindex (homogeneousPath (reindex B (projection A)) (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A)) (Term.reindex b (projection A))) (liftSub A σ)) (sigmaFst (B := reindex (homogeneousPath (reindex B (projection A)) (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A)) (Term.reindex b (projection A))) (liftSub A σ)) z)) (Term.map_iso_roundtrip e (sigmaSnd (B := reindex (homogeneousPath (reindex B (projection A)) (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A)) (Term.reindex b (projection A))) (liftSub A σ)) z))

end Homotopy

/-- The chosen contraction covers every generalized target and every path body. -/
structure HomotopyEquivalence {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) where
  fibers : Contractible (Homotopy.genericFiber f)

def HomotopyEquivalence.reindex {Γ Δ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (e : HomotopyEquivalence f) (σ : Δ ⟶ Γ) :
    HomotopyEquivalence (Functor.whiskerLeft σ.mapElements f) where
  fibers := Contractible.map (Homotopy.fiberReindexIso
    (Functor.whiskerLeft (projection B).mapElements f) (generic B) (liftSub B σ))
    (e.fibers.reindex (liftSub B σ))

namespace NativeSquare
variable {Γ : Context.{u}} {A : Family Γ}

def sides (Γ : Context.{u}) : Subcontext (total (interval Γ)) :=
  (Subcontext.intervalFace Γ false).join (Subcontext.intervalFace Γ true)

theorem endpoint_iff (b : Bool) (x : (total (interval Γ)).Elements) :
    (Subcontext.intervalFace Γ b).Holds x ↔ x.val.2 = ⟨Cube.endpoint x.obj.unop b⟩ := by
  constructor
  · intro h
    apply ULift.ext
    funext i
    rw [Fin.eq_zero i]
    exact h
  · intro h
    change x.val.2.down 0 = .endpoint b
    rw [h]
    rfl

theorem endpoints_disjoint (x : (total (interval Γ)).Elements)
    (h₀ : (Subcontext.intervalFace Γ false).Holds x)
    (h₁ : (Subcontext.intervalFace Γ true).Holds x) : False := by
  change x.val.2.down 0 = .endpoint false at h₀
  change x.val.2.down 0 = .endpoint true at h₁
  cases h₀.symm.trans h₁

abbrev squareBase (Γ : Context.{u}) :=
  projection (interval (total (interval Γ))) ≫ projection (interval Γ)

abbrev vertical (Γ : Context.{u}) := intervalSub (projection (interval Γ))

def verticalTerm (l : Term (intervalCoefficient A)) : Term (reindex A (squareBase Γ)) :=
  Term.reindex l (vertical Γ)

noncomputable def tube (l r : Term (intervalCoefficient A)) :
    PartialSection (reindex A (squareBase Γ))
      ((sides Γ).reindex (projection (interval (total (interval Γ))))) where
  val x _ := by
    classical
    exact if (Subcontext.intervalFace Γ false).Holds
      ((projection (interval (total (interval Γ)))).mapElements.obj x) then
    (verticalTerm l).val x else (verticalTerm r).val x
  natural {x y} f hx := by
    classical
    let px := (projection (interval (total (interval Γ)))).mapElements.obj x
    let py := (projection (interval (total (interval Γ)))).mapElements.obj y
    let pf := (projection (interval (total (interval Γ)))).mapElements.map f
    by_cases h₀ : (Subcontext.intervalFace Γ false).Holds px
    · have hy := (Subcontext.intervalFace Γ false).natural pf h₀
      change (reindex A (squareBase Γ)).map f
        (if (Subcontext.intervalFace Γ false).Holds px then _ else _) =
        (if (Subcontext.intervalFace Γ false).Holds py then _ else _)
      rw [ite_eq_left h₀, ite_eq_left hy]
      exact (verticalTerm l).property f
    · have h₁ : (Subcontext.intervalFace Γ true).Holds px := hx.resolve_left h₀
      have hy₁ := (Subcontext.intervalFace Γ true).natural pf h₁
      have hy₀ : ¬ (Subcontext.intervalFace Γ false).Holds py := fun h => endpoints_disjoint py h hy₁
      change (reindex A (squareBase Γ)).map f
        (if (Subcontext.intervalFace Γ false).Holds px then _ else _) =
        (if (Subcontext.intervalFace Γ false).Holds py then _ else _)
      rw [ite_eq_right h₀, ite_eq_right hy₀]
      exact (verticalTerm r).property f


theorem tube_left (l r : Term (intervalCoefficient A))
    (x : (total (interval (total (interval Γ)))).Elements)
    (h : (Subcontext.intervalFace Γ false).Holds
      ((projection (interval (total (interval Γ)))).mapElements.obj x)) :
    (tube l r).val x (Or.inl h) = (verticalTerm l).val x := by
  classical
  exact ite_eq_left h

theorem tube_right (l r : Term (intervalCoefficient A))
    (x : (total (interval (total (interval Γ)))).Elements)
    (h : (Subcontext.intervalFace Γ true).Holds
      ((projection (interval (total (interval Γ)))).mapElements.obj x)) :
    (tube l r).val x (Or.inr h) = (verticalTerm r).val x := by
  classical
  exact ite_eq_right (fun h₀ => endpoints_disjoint _ h₀ h)

noncomputable def box (ε : Bool) (l r base : Term (intervalCoefficient A))
    (h₀ : Term.reindex base (endpointSub Γ false) = Term.reindex l (endpointSub Γ ε))
    (h₁ : Term.reindex base (endpointSub Γ true) = Term.reindex r (endpointSub Γ ε)) :
    OpenBox (reindex A (squareBase Γ)) (sides Γ) (endpoint (total (interval Γ)) ε) where
  tube := tube l r
  base := base
  boundary x hx := by
    rcases hx with hx | hx
    · rw [tube_left l r _ hx]
      have he := (endpoint_iff false x).mp hx
      rcases x with @⟨I, γ, i⟩
      change i = ⟨Cube.endpoint I.unop false⟩ at he
      subst i
      exact (congrArg (fun t => t.val (Γ.elementsMk I γ)) h₀).symm
    · rw [tube_right l r _ hx]
      have he := (endpoint_iff true x).mp hx
      rcases x with @⟨I, γ, i⟩
      change i = ⟨Cube.endpoint I.unop true⟩ at he
      subst i
      exact (congrArg (fun t => t.val (Γ.elementsMk I γ)) h₁).symm

noncomputable def fill (F : Filling A) (ε : Bool) (l r base : Term (intervalCoefficient A))
    (h₀ : Term.reindex base (endpointSub Γ false) = Term.reindex l (endpointSub Γ ε))
    (h₁ : Term.reindex base (endpointSub Γ true) = Term.reindex r (endpointSub Γ ε)) :
    Term (reindex A (squareBase Γ)) :=
  F.fill (squareBase Γ) (sides Γ) (endpoint (total (interval Γ)) ε) (box ε l r base h₀ h₁)

variable (F : Filling A) (hF : F.Lawful) (ε : Bool) (l r base : Term (intervalCoefficient A))
  (h₀ : Term.reindex base (endpointSub Γ false) = Term.reindex l (endpointSub Γ ε))
  (h₁ : Term.reindex base (endpointSub Γ true) = Term.reindex r (endpointSub Γ ε))

include hF in
theorem fill_left :
    Term.reindex (fill F ε l r base h₀ h₁) (intervalSub (endpointSub Γ false)) = l := by
  apply Term.ext
  intro x
  let y := (intervalSub (endpointSub Γ false)).mapElements.obj x
  have hy : (Subcontext.intervalFace Γ false).Holds
      ((projection (interval (total (interval Γ)))).mapElements.obj y) := rfl
  exact ((hF.fills (squareBase Γ) (sides Γ) (endpoint (total (interval Γ)) ε)
    (box ε l r base h₀ h₁)).2 y (Or.inl hy)).trans (tube_left l r y hy)

include hF in
theorem fill_right :
    Term.reindex (fill F ε l r base h₀ h₁) (intervalSub (endpointSub Γ true)) = r := by
  apply Term.ext
  intro x
  let y := (intervalSub (endpointSub Γ true)).mapElements.obj x
  have hy : (Subcontext.intervalFace Γ true).Holds
      ((projection (interval (total (interval Γ)))).mapElements.obj y) := rfl
  exact ((hF.fills (squareBase Γ) (sides Γ) (endpoint (total (interval Γ)) ε)
    (box ε l r base h₀ h₁)).2 y (Or.inr hy)).trans (tube_right l r y hy)

include hF in
theorem fill_source :
    Term.reindex (fill F ε l r base h₀ h₁) (endpointSub (total (interval Γ)) ε) = base :=
  (hF.fills (squareBase Γ) (sides Γ) (endpoint (total (interval Γ)) ε)
    (box ε l r base h₀ h₁)).1

def slice (q : Term (reindex A (squareBase Γ))) (b : Bool) : Term (intervalCoefficient A) :=
  Term.reindex q (endpointSub (total (interval Γ)) b)

include hF in
theorem slice_left (b : Bool) :
    Term.reindex (slice (fill F ε l r base h₀ h₁) b) (endpointSub Γ false) =
      Term.reindex l (endpointSub Γ b) :=
  congrArg (fun t => Term.reindex t (endpointSub Γ b)) (fill_left F hF ε l r base h₀ h₁)

include hF in
theorem slice_right (b : Bool) :
    Term.reindex (slice (fill F ε l r base h₀ h₁) b) (endpointSub Γ true) =
      Term.reindex r (endpointSub Γ b) :=
  congrArg (fun t => Term.reindex t (endpointSub Γ b)) (fill_right F hF ε l r base h₀ h₁)

end NativeSquare

/-- Reversal is a Kan square construction, not a Cartesian dimension operation. -/
noncomputable def homogeneousReverse {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) {a b : Term A}
    (p : Term (homogeneousPath A a b)) : Term (homogeneousPath A b a) := by
  let c := Term.reindex b (projection (interval Γ))
  let q := NativeSquare.fill F true c (pathApp p) c rfl (pathApp_one p).symm
  exact pathLam (NativeSquare.slice q false)
    (NativeSquare.slice_left F hF true c (pathApp p) c rfl (pathApp_one p).symm false)
    ((NativeSquare.slice_right F hF true c (pathApp p) c rfl (pathApp_one p).symm false).trans
      (pathApp_zero p))

/-- Concatenation fills the square with bottom p, right q and constant left edge. -/
noncomputable def homogeneousConcat {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) {a b c : Term A}
    (p : Term (homogeneousPath A a b)) (q : Term (homogeneousPath A b c)) :
    Term (homogeneousPath A a c) := by
  let l := Term.reindex a (projection (interval Γ))
  let h := (pathApp_one p).trans (pathApp_zero q).symm
  let z := NativeSquare.fill F false l (pathApp q) (pathApp p) (pathApp_zero p) h
  exact pathLam (NativeSquare.slice z true)
    (NativeSquare.slice_left F hF false l (pathApp q) (pathApp p) (pathApp_zero p) h true)
    ((NativeSquare.slice_right F hF false l (pathApp q) (pathApp p) (pathApp_zero p) h true).trans
      (pathApp_one q))

def homogeneousReindex {Γ Δ : Context.{u}} {A : Family Γ} {a b : Term A}
    (p : Term (homogeneousPath A a b)) (σ : Δ ⟶ Γ) :
    Term (homogeneousPath (reindex A σ) (Term.reindex a σ) (Term.reindex b σ)) :=
  Term.map (pathReindexIso (intervalCoefficient A) a b σ).hom (Term.reindex p σ)

theorem Homotopy.fiberIntroOver_reindex {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (b : Term B) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (a : Term (reindex A σ))
    (p : Term (homogeneousPath (reindex B σ)
      (Term.map (Functor.whiskerLeft σ.mapElements f) a) (Term.reindex b σ))) :
    Term.reindex (fiberIntroOver f b σ a p) τ =
      fiberIntroOver f b (τ ≫ σ) (Term.reindex a τ) (homogeneousReindex p τ) := by
  exact congrArg (sigmaIntro (B := reindex (homogeneousPath (reindex B (projection A))
    (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
    (Term.reindex b (projection A))) (liftSub A (τ ≫ σ))) (Term.reindex a τ))
    (pathInverse_reindex (intervalCoefficient (reindex B (projection A)))
      (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
      (Term.reindex b (projection A)) (pair σ a) τ p)

/-- A generic contraction term gives the entire pointwise natural contraction record. -/
def Contractible.ofContraction {Γ : Context.{u}} {A : Family Γ} (c : Term A)
    (p : Term (homogeneousPath (Cartesian.reindex A (projection A))
      (Term.reindex c (projection A)) (generic A))) : Contractible A where
  center := c
  contraction x a := ⟨{
    val := fun {y} f r => (pathApp p).val
      (extendObj (interval (total A)) (extendObj A y (A.map f a)) r)
    naturality := fun {y z} f g r => by
      have h := (pathApp p).property
        (extendHom (interval (total A)) (extendHom A g (A.map f a)) r)
      change A.map g _ = _ at h ⊢
      exact h.trans (congrArg (fun v => (show A.obj z from (pathApp p).val
        (extendObj (interval (total A)) (extendObj A z v) ((interval Γ).map g r))))
        (A.map_comp_apply f g a).symm) }, by
    intro y f
    constructor
    · exact (congrArg (fun t => t.val (extendObj A y (A.map f a)))
        (pathApp_zero p)).trans (c.property f).symm
    · exact congrArg (fun t => t.val (extendObj A y (A.map f a))) (pathApp_one p)⟩
  naturality {_x _y z} f g a r := by
    exact congrArg (fun v => (show A.obj z from (pathApp p).val
      (extendObj (interval (total A)) (extendObj A z v) r))) (A.map_comp_apply f g a)


def Contractible.pathTo {Γ : Context.{u}} {A : Family Γ} (c : Contractible A) (a : Term A) :
    Term (homogeneousPath A c.center a) where
  val x := ⟨(c.contraction x (a.val x)).val, fun f =>
    ⟨((c.contraction x (a.val x)).property f).1.trans (c.center.property f),
      ((c.contraction x (a.val x)).property f).2.trans (a.property f)⟩⟩
  property {x y} f := by
    apply Subtype.ext
    apply PiElement.ext
    intro z g r
    change (c.contraction x (a.val x)).val.val (f ≫ g) r =
      (c.contraction y (a.val y)).val.val g r
    exact (c.naturality f g (a.val x) r).trans
      (congrArg (fun v => (c.contraction y v).val.val g r) (a.property f))

def Contractible.toContraction {Γ : Context.{u}} {A : Family Γ} (c : Contractible A) :
    Term (homogeneousPath (Cartesian.reindex A (projection A))
      (Term.reindex c.center (projection A)) (generic A)) :=
  (c.reindex (projection A)).pathTo (generic A)

theorem Contractible.of_toContraction {Γ : Context.{u}} {A : Family Γ} (c : Contractible A) :
    ofContraction c.center c.toContraction = c := by
  refine Contractible.ext (c := ofContraction c.center c.toContraction) (d := c) rfl ?_
  intro x a y f r
  change (c.contraction y (A.map f a)).val.val (𝟙 y) r = (c.contraction x a).val.val f r
  simpa only [Category.comp_id] using (c.naturality f (𝟙 y) a r).symm

theorem Contractible.to_ofContraction {Γ : Context.{u}} {A : Family Γ} (c : Term A)
    (p : Term (homogeneousPath (Cartesian.reindex A (projection A))
      (Term.reindex c (projection A)) (generic A))) : (ofContraction c p).toContraction = p := by
  apply pathApp_injective
  apply Term.ext
  intro x
  rcases x with @⟨I, ⟨γ, a⟩, r⟩
  change (pathApp p).val (extendObj (interval (total A))
    (extendObj A (Γ.elementsMk I γ) (A.map (𝟙 _) a)) r) = _
  rw [A.map_id]
  rfl

namespace Homotopy

def fiberFstOver {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (b : Term B)
    (σ : Δ ⟶ Γ) (z : Term (reindex (fiber f b) σ)) : Term (reindex A σ) :=
  sigmaFst (B := reindex (homogeneousPath (reindex B (projection A))
    (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
    (Term.reindex b (projection A))) (liftSub A σ)) z

theorem fiberIntroOver_congr {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (b : Term B)
    (σ : Δ ⟶ Γ) (a a' : Term (reindex A σ))
    (p : Term (homogeneousPath (reindex B σ)
      (Term.map (Functor.whiskerLeft σ.mapElements f) a) (Term.reindex b σ)))
    (p' : Term (homogeneousPath (reindex B σ)
      (Term.map (Functor.whiskerLeft σ.mapElements f) a') (Term.reindex b σ)))
    (ha : a = a') (hp : HEq (pathApp p) (pathApp p')) :
    fiberIntroOver f b σ a p = fiberIntroOver f b σ a' p' := by
  subst a'
  have h := pathApp_injective (eq_of_heq hp)
  subst p'
  rfl

end Homotopy

noncomputable def identityFiberContractible {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) (b : Term A) : Contractible (Homotopy.fiber (𝟙 A) b) := by
  let S := Homotopy.fiber (𝟙 A) b
  let σ := projection S
  let a := Homotopy.fiberFstOver (𝟙 A) b σ (generic S)
  let p := Homotopy.fiberPathOver (𝟙 A) b σ (generic S)
  let c := Term.reindex (Term.reindex b σ) (projection (interval (total S)))
  let q := NativeSquare.fill (F.reindex σ) true c (pathApp p) c rfl (pathApp_one p).symm
  let d := NativeSquare.slice q false
  let v : Term (homogeneousPath (intervalCoefficient (reindex A σ)) d c) :=
    pathLam q rfl (NativeSquare.fill_source (F.reindex σ) (hF.reindex σ)
      true c (pathApp p) c rfl (pathApp_one p).symm)
  let body := Homotopy.fiberIntroOver (𝟙 A) b
    (projection (interval (total S)) ≫ σ) d v
  let center := Homotopy.fiberIntro (𝟙 A) b b (homogeneousRefl b)
  have hzero : Term.reindex body (endpointSub (total S) false) = Term.reindex center σ := by
    refine (Homotopy.fiberIntroOver_reindex (𝟙 A) b
      (projection (interval (total S)) ≫ σ) (endpointSub (total S) false) d v).trans ?_
    change Homotopy.fiberIntroOver (𝟙 A) b σ _ _ = _
    have hc : Term.reindex center σ = Homotopy.fiberIntroOver (𝟙 A) b σ
        (Term.reindex b σ) (homogeneousReindex (homogeneousRefl b) σ) :=
      Homotopy.fiberIntroOver_reindex (𝟙 A) b (𝟙 Γ) σ b (homogeneousRefl b)
    rw [hc]
    apply Homotopy.fiberIntroOver_congr
    · exact NativeSquare.slice_left (F.reindex σ) (hF.reindex σ)
        true c (pathApp p) c rfl (pathApp_one p).symm false
    · exact heq_of_eq (NativeSquare.fill_left (F.reindex σ) (hF.reindex σ)
        true c (pathApp p) c rfl (pathApp_one p).symm)
  have hone : Term.reindex body (endpointSub (total S) true) = generic S := by
    refine (Homotopy.fiberIntroOver_reindex (𝟙 A) b
      (projection (interval (total S)) ≫ σ) (endpointSub (total S) true) d v).trans ?_
    change Homotopy.fiberIntroOver (𝟙 A) b σ _ _ = _
    rw [← Homotopy.fiberIntroOver_eta (𝟙 A) b σ (generic S)]
    apply Homotopy.fiberIntroOver_congr
    · exact (NativeSquare.slice_right (F.reindex σ) (hF.reindex σ)
        true c (pathApp p) c rfl (pathApp_one p).symm false).trans (pathApp_zero p)
    · exact heq_of_eq (NativeSquare.fill_right (F.reindex σ) (hF.reindex σ)
        true c (pathApp p) c rfl (pathApp_one p).symm)
  exact Contractible.ofContraction center (pathLam body hzero hone)

theorem pathApp_castLeft {Γ : Context.{u}} {A : Family Γ} {a a' b : Term A}
    (h : a = a') (p : Term (homogeneousPath A a b)) :
    pathApp (h ▸ p) = pathApp p := by subst a'; rfl

noncomputable def isoFiberContractible {Γ : Context.{u}} {A B : Family Γ}
    (e : A ≅ B) (F : Filling B) (hF : F.Lawful) (b : Term B) : Contractible (Homotopy.fiber e.hom b) := by
  let S := Homotopy.fiber e.hom b
  let σ := projection S
  let a := Homotopy.fiberFstOver e.hom b σ (generic S)
  let p := Homotopy.fiberPathOver e.hom b σ (generic S)
  let c := Term.reindex (Term.reindex b σ) (projection (interval (total S)))
  let q := NativeSquare.fill (F.reindex σ) true c (pathApp p) c rfl (pathApp_one p).symm
  let d := NativeSquare.slice q false
  let eσ : reindex A (projection (interval (total S)) ≫ σ) ≅ reindex B (projection (interval (total S)) ≫ σ) :=
    Functor.isoWhiskerLeft (projection (interval (total S)) ≫ σ).mapElements e
  let v : Term (homogeneousPath (intervalCoefficient (reindex B σ)) (Term.map eσ.hom (Term.map eσ.inv d)) c) :=
    pathLam q (Term.map_iso_roundtrip eσ.symm d).symm
      (NativeSquare.fill_source (F.reindex σ) (hF.reindex σ)
        true c (pathApp p) c rfl (pathApp_one p).symm)
  have hv : pathApp v = q := rfl
  let body := Homotopy.fiberIntroOver e.hom b
    (projection (interval (total S)) ≫ σ) (Term.map eσ.inv d) v
  let refl : Term (homogeneousPath B (Term.map e.hom (Term.map e.inv b)) b) :=
    pathLam (Term.reindex b (projection (interval Γ)))
      (Term.map_iso_roundtrip e.symm b).symm rfl
  have hr : pathApp refl = Term.reindex b (projection (interval Γ)) :=
    rfl
  let center := Homotopy.fiberIntro e.hom b (Term.map e.inv b) refl
  have hzero : Term.reindex body (endpointSub (total S) false) = Term.reindex center σ := by
    refine (Homotopy.fiberIntroOver_reindex e.hom b
      (projection (interval (total S)) ≫ σ) (endpointSub (total S) false) (Term.map eσ.inv d) v).trans ?_
    change Homotopy.fiberIntroOver e.hom b σ _ _ = _
    have hc : Term.reindex center σ = Homotopy.fiberIntroOver e.hom b σ
        (Term.reindex (Term.map e.inv b) σ) (homogeneousReindex refl σ) :=
      Homotopy.fiberIntroOver_reindex e.hom b (𝟙 Γ) σ (Term.map e.inv b) refl
    rw [hc]
    apply Homotopy.fiberIntroOver_congr
    · exact congrArg (Term.map (Functor.whiskerLeft σ.mapElements e.inv)) (NativeSquare.slice_left (F.reindex σ) (hF.reindex σ)
        true c (pathApp p) c rfl (pathApp_one p).symm false)
    · apply heq_of_eq
      change Term.reindex (pathApp v) (intervalSub (endpointSub (total S) false)) =
        Term.reindex (pathApp refl) (intervalSub σ)
      rw [hv, hr]
      exact NativeSquare.fill_left (F.reindex σ) (hF.reindex σ)
        true c (pathApp p) c rfl (pathApp_one p).symm
  have hone : Term.reindex body (endpointSub (total S) true) = generic S := by
    refine (Homotopy.fiberIntroOver_reindex e.hom b
      (projection (interval (total S)) ≫ σ) (endpointSub (total S) true) (Term.map eσ.inv d) v).trans ?_
    change Homotopy.fiberIntroOver e.hom b σ _ _ = _
    rw [← Homotopy.fiberIntroOver_eta e.hom b σ (generic S)]
    apply Homotopy.fiberIntroOver_congr
    · exact (congrArg (Term.map (Functor.whiskerLeft σ.mapElements e.inv)) ((NativeSquare.slice_right (F.reindex σ) (hF.reindex σ)
        true c (pathApp p) c rfl (pathApp_one p).symm false).trans (pathApp_zero p))).trans (Term.map_iso_roundtrip (Functor.isoWhiskerLeft σ.mapElements e) a)
    · apply heq_of_eq
      change Term.reindex (pathApp v) (intervalSub (endpointSub (total S) true)) = pathApp p
      rw [hv]
      exact NativeSquare.fill_right (F.reindex σ) (hF.reindex σ)
        true c (pathApp p) c rfl (pathApp_one p).symm
  exact Contractible.ofContraction center (pathLam body hzero hone)

noncomputable def HomotopyEquivalence.ofIso {Γ : Context.{u}} {A B : Family Γ}
    (e : A ≅ B) (F : Filling B) (hF : F.Lawful) : HomotopyEquivalence e.hom where
  fibers := isoFiberContractible (Functor.isoWhiskerLeft (projection B).mapElements e)
    (F.reindex (projection B)) (hF.reindex (projection B)) (generic B)

noncomputable def HomotopyEquivalence.identity {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) : HomotopyEquivalence (𝟙 A) :=
  ofIso (Iso.refl A) F hF

namespace NativeSquare
variable {Γ Δ : Context.{u}} {A : Family Γ}
theorem fill_reindex (F : Filling A) (hF : F.Lawful) (ε : Bool)
    (l r base : Term (intervalCoefficient A))
    (h₀ : Term.reindex base (endpointSub Γ false) = Term.reindex l (endpointSub Γ ε))
    (h₁ : Term.reindex base (endpointSub Γ true) = Term.reindex r (endpointSub Γ ε))
    (σ : Δ ⟶ Γ) :
    fill (F.reindex σ) ε (Term.reindex l (intervalSub σ))
      (Term.reindex r (intervalSub σ)) (Term.reindex base (intervalSub σ))
      (congrArg (fun t => Term.reindex t σ) h₀)
      (congrArg (fun t => Term.reindex t σ) h₁) =
    Term.reindex (fill F ε l r base h₀ h₁) (intervalSub (intervalSub σ)) := by
  exact hF.uniform (squareBase Γ) (sides Γ) (endpoint (total (interval Γ)) ε)
    (box ε l r base h₀ h₁) (intervalSub σ)
end NativeSquare
namespace Homotopy
theorem fiberReindexIso_introOver {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (b : Term B) (σ : Δ ⟶ Γ) (a : Term (reindex A σ))
    (p : Term (homogeneousPath (reindex B σ)
      (Term.map (Functor.whiskerLeft σ.mapElements f) a) (Term.reindex b σ))) :
    Term.map (fiberReindexIso f b σ).hom (fiberIntroOver f b σ a p) =
      fiberIntro (Functor.whiskerLeft σ.mapElements f) (Term.reindex b σ) a p := by
  let D := homogeneousPath (reindex (reindex B σ) (projection (reindex A σ)))
    (Term.map (Functor.whiskerLeft (projection (reindex A σ)).mapElements
      (Functor.whiskerLeft σ.mapElements f)) (generic (reindex A σ)))
    (Term.reindex (Term.reindex b σ) (projection (reindex A σ)))
  let z := Term.map (fiberReindexIso f b σ).hom (fiberIntroOver f b σ a p)
  let w := fiberIntro (Functor.whiskerLeft σ.mapElements f) (Term.reindex b σ) a p
  have h : sigmaSnd (B := D) z = sigmaSnd (B := D) w := by
    let out := pathReindexIso (intervalCoefficient (reindex (reindex B σ) (projection (reindex A σ))))
      (Term.map (Functor.whiskerLeft (projection (reindex A σ)).mapElements
        (Functor.whiskerLeft σ.mapElements f)) (generic (reindex A σ)))
      (Term.reindex (Term.reindex b σ) (projection (reindex A σ))) (pair (𝟙 Δ) a)
    let orig := pathReindexIso (intervalCoefficient (reindex B (projection A)))
      (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
      (Term.reindex b (projection A)) (pair σ a)
    apply Term.map_injective_of_iso out
    apply Term.ext
    intro x
    exact (orig.inv_hom_id_app_apply x (p.val x)).trans (out.inv_hom_id_app_apply x (p.val x)).symm
  exact congrArg (sigmaIntro (B := D) a) h
end Homotopy

namespace Homotopy
theorem homogeneous_eval_extend {Γ : Context.{u}} {A B : Family Γ}
    {x y : Γ.Elements} (g : x ⟶ y) (a : A.obj x) (a' : A.obj y)
    (ha : A.map g a = a')
    (p : PiElement (interval (total A)) (intervalCoefficient (reindex B (projection A)))
      (extendObj A x a)) (r : (interval Γ).obj y) :
    p.val (extendHom A g a) r = p.val
      (show extendObj A x a ⟶ extendObj A y a' from Functor.Elements.homMk g.hom
        ((totalMap_ofHom A g a).trans (congrArg (Sigma.mk y.val) ha))) r := by
  subst a'
  rfl

theorem fiberIntroOver_path_eval {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (b : Term B) (σ : Δ ⟶ Γ) (a : Term (reindex A σ))
    (p : Term (homogeneousPath (reindex B σ)
      (Term.map (Functor.whiskerLeft σ.mapElements f) a) (Term.reindex b σ)))
    {x y : Δ.Elements} (g : x ⟶ y) (r : (interval Δ).obj y) :
    ((fiberIntroOver f b σ a p).val x).2.val.val
      (extendHom A (σ.mapElements.map g) (a.val x)) r = (p.val x).val.val g r := by
  refine (homogeneous_eval_extend (B := B) (σ.mapElements.map g) (a.val x) (a.val y)
    (a.property g) ((fiberIntroOver f b σ a p).val x).2.val r).trans ?_
  exact piInverseValue_map (A := interval (total A))
    (B := intervalCoefficient (reindex B (projection A))) (pair σ a) (p.val x).val g r
end Homotopy
theorem NativeSquare.fill_congr_right {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (ε : Bool) (l r r' base : Term (intervalCoefficient A))
    (h₀ : Term.reindex base (endpointSub Γ false) = Term.reindex l (endpointSub Γ ε))
    (h₁ : Term.reindex base (endpointSub Γ true) = Term.reindex r (endpointSub Γ ε))
    (h₁' : Term.reindex base (endpointSub Γ true) = Term.reindex r' (endpointSub Γ ε))
    (h : r = r') : fill F ε l r base h₀ h₁ = fill F ε l r' base h₀ h₁' := by
  subst r'
  rfl

namespace Homotopy

def fiberContextMap {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (b : Term B)
    (σ : Δ ⟶ Γ) : total (fiber (Functor.whiskerLeft σ.mapElements f) (Term.reindex b σ)) ⟶ total (fiber f b) :=
  pair (projection (fiber (Functor.whiskerLeft σ.mapElements f) (Term.reindex b σ)) ≫ σ)
    (Term.map (Functor.whiskerLeft (projection (fiber (Functor.whiskerLeft σ.mapElements f)
      (Term.reindex b σ))).mapElements (fiberReindexIso f b σ).inv)
      (generic (fiber (Functor.whiskerLeft σ.mapElements f) (Term.reindex b σ))))

theorem genericFiberPath_reindex {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (b : Term B)
    (σ : Δ ⟶ Γ) :
    Term.reindex (pathApp (fiberPathOver f b (projection (fiber f b)) (generic (fiber f b))))
      (intervalSub (fiberContextMap f b σ)) =
    pathApp (fiberPathOver (Functor.whiskerLeft σ.mapElements f) (Term.reindex b σ)
      (projection (fiber (Functor.whiskerLeft σ.mapElements f) (Term.reindex b σ)))
      (generic (fiber (Functor.whiskerLeft σ.mapElements f) (Term.reindex b σ)))) := by
  apply Term.ext
  intro x
  rcases x with @⟨I, ⟨γ, a, p⟩, r⟩
  change piInverseValue (A := interval (total A)) (B := intervalCoefficient (reindex B (projection A))) (liftSub A σ) p.val ((liftSub A σ).mapElements.map (𝟙 (extendObj (reindex A σ) (Δ.elementsMk I γ) a))) r = _
  exact piInverseValue_map (A := interval (total A)) (B := intervalCoefficient (reindex B (projection A))) (liftSub A σ) p.val (𝟙 _) r

noncomputable def fiberSquare {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (F : Filling B) (b : Term B) :
    Term (reindex B (NativeSquare.squareBase (total (fiber f b)) ≫ projection (fiber f b))) :=
  let σ := projection (fiber f b)
  let p := fiberPathOver f b σ (generic (fiber f b))
  let c := Term.reindex (Term.reindex b σ) (projection (interval (total (fiber f b))))
  NativeSquare.fill (F.reindex σ) true c (pathApp p) c rfl (pathApp_one p).symm

theorem fiberSquare_reindex {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (F : Filling B) (hF : F.Lawful) (b : Term B) (σ : Δ ⟶ Γ) :
    Term.reindex (fiberSquare f F b) (intervalSub (intervalSub (fiberContextMap f b σ))) =
    fiberSquare (Functor.whiskerLeft σ.mapElements f) (F.reindex σ) (Term.reindex b σ) := by
  let p := fiberPathOver f b (projection (fiber f b)) (generic (fiber f b))
  let c := Term.reindex (Term.reindex b (projection (fiber f b))) (projection (interval (total (fiber f b))))
  have h := (NativeSquare.fill_reindex (F.reindex (projection (fiber f b)))
    (hF.reindex _) true c (pathApp p) c rfl (pathApp_one p).symm (fiberContextMap f b σ)).symm
  refine h.trans ?_
  exact NativeSquare.fill_congr_right _ _ _ _ _ _ _ _ _ (genericFiberPath_reindex f b σ)

def squarePoint {Γ : Context.{u}} (x : Γ.Elements)
    (r s : (interval Γ).obj x) :=
  extendObj (interval (total (interval Γ))) (extendObj (interval Γ) x r) s

theorem fiberSquare_value_reindex {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (F : Filling B) (hF : F.Lawful) (b : Term B) (σ : Δ ⟶ Γ)
    {x y : Δ.Elements} (g : x ⟶ y)
    (a : (fiber (Functor.whiskerLeft σ.mapElements f) (Term.reindex b σ)).obj x)
    (r s : (interval Δ).obj y) :
    (fiberSquare f F b).val (squarePoint (extendObj (fiber f b) (σ.mapElements.obj y)
      ((fiber f b).map (σ.mapElements.map g) ((fiberReindexIso f b σ).inv.app x a))) r s) =
    (fiberSquare (Functor.whiskerLeft σ.mapElements f) (F.reindex σ) (Term.reindex b σ)).val
      (squarePoint (extendObj (fiber (Functor.whiskerLeft σ.mapElements f) (Term.reindex b σ)) y
        ((fiber (Functor.whiskerLeft σ.mapElements f) (Term.reindex b σ)).map g a)) r s) := by
  have hn := (fiberReindexIso f b σ).inv.naturality_apply g a
  have hq := congrArg (fun t => t.val (squarePoint
    (extendObj (fiber (Functor.whiskerLeft σ.mapElements f) (Term.reindex b σ)) y
      ((fiber (Functor.whiskerLeft σ.mapElements f) (Term.reindex b σ)).map g a)) r s))
      (fiberSquare_reindex f F hF b σ)
  exact (congrArg (fun z => (show B.obj (σ.mapElements.obj y) from (fiberSquare f F b).val
    (squarePoint (extendObj (fiber f b) (σ.mapElements.obj y) z) r s))) hn.symm).trans hq
end Homotopy

theorem isoFiberContractible_path_eval {Γ : Context.{u}} {A B : Family Γ}
    (e : A ≅ B) (F : Filling B) (hF : F.Lawful) (b : Term B)
    {x y z : Γ.Elements} (f : x ⟶ y) (g : y ⟶ z)
    (a : (Homotopy.fiber e.hom b).obj x) (r : (interval Γ).obj y) (s : (interval Γ).obj z) :
    (((isoFiberContractible e F hF b).contraction x a).val.val f r).2.val.val
      (extendHom A g (((isoFiberContractible e F hF b).contraction x a).val.val f r).1) s =
    (Homotopy.fiberSquare e.hom F b).val
      (Homotopy.squarePoint (extendObj (Homotopy.fiber e.hom b) z
        ((Homotopy.fiber e.hom b).map (f ≫ g) a)) ((interval Γ).map g r) s) := by
  let S := Homotopy.fiber e.hom b
  let σ := projection S
  let p := Homotopy.fiberPathOver e.hom b σ (generic S)
  let c := Term.reindex (Term.reindex b σ) (projection (interval (total S)))
  let q := NativeSquare.fill (F.reindex σ) true c (pathApp p) c rfl (pathApp_one p).symm
  let d := NativeSquare.slice q false
  let eσ := Functor.isoWhiskerLeft (projection (interval (total S)) ≫ σ).mapElements e
  let v : Term (homogeneousPath (intervalCoefficient (reindex B σ))
      (Term.map eσ.hom (Term.map eσ.inv d)) c) :=
    pathLam q (Term.map_iso_roundtrip eσ.symm d).symm
      (NativeSquare.fill_source (F.reindex σ) (hF.reindex σ)
        true c (pathApp p) c rfl (pathApp_one p).symm)
  have h := Homotopy.fiberIntroOver_path_eval e.hom b
    (projection (interval (total S)) ≫ σ) (Term.map eσ.inv d) v
    (extendHom (interval (total S)) (extendHom S g (S.map f a)) r) s
  exact h.trans (congrArg (fun w => (show B.obj z from q.val
    (Homotopy.squarePoint (extendObj S z w) ((interval Γ).map g r) s)))
      (S.map_comp_apply f g a).symm)
namespace Homotopy
theorem fiber_element_ext {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B} {b : Term B}
    {x : Γ.Elements} {z w : (fiber f b).obj x} (ha : z.1 = w.1)
    (hp : ∀ {y : Γ.Elements} (g : x ⟶ y) (r : (interval Γ).obj y),
      z.2.val.val (extendHom A g z.1) r = w.2.val.val (extendHom A g w.1) r) : z = w := by
  rcases z with ⟨a,p⟩
  rcases w with ⟨a',q⟩
  dsimp at ha
  subst a'
  apply congrArg (Sigma.mk a)
  apply Subtype.ext
  apply PiElement.ext
  intro y g r
  rcases x with @⟨I,γ⟩
  rcases y with @⟨J,y⟩
  rcases g with ⟨g,h⟩
  change I ⟶ J at g
  change totalMap A g ⟨γ,a⟩ = y at h
  subst y
  exact hp (show Γ.elementsMk I γ ⟶ Γ.elementsMk J (Γ.map g γ) from Functor.Elements.homMk g rfl) r
end Homotopy
theorem isoFiberContractible_reindex {Γ Δ : Context.{u}} {A B : Family Γ}
    (e : A ≅ B) (F : Filling B) (hF : F.Lawful) (b : Term B) (σ : Δ ⟶ Γ) :
    Contractible.map (Homotopy.fiberReindexIso e.hom b σ)
      ((isoFiberContractible e F hF b).reindex σ) =
    isoFiberContractible (Functor.isoWhiskerLeft σ.mapElements e)
      (F.reindex σ) (hF.reindex σ) (Term.reindex b σ) := by
  apply Contractible.ext
  · let p : Term (homogeneousPath B (Term.map e.hom (Term.map e.inv b)) b) :=
      pathLam (Term.reindex b (projection (interval Γ)))
        (Term.map_iso_roundtrip e.symm b).symm rfl
    have h := Homotopy.fiberIntroOver_reindex e.hom b (𝟙 Γ) σ (Term.map e.inv b) p
    exact (congrArg (Term.map (Homotopy.fiberReindexIso e.hom b σ).hom) h).trans
      (Homotopy.fiberReindexIso_introOver e.hom b σ (Term.reindex (Term.map e.inv b) σ)
        (homogeneousReindex p σ))
  · intro x a y f r
    apply Homotopy.fiber_element_ext
    · exact congrArg (e.inv.app (σ.mapElements.obj y))
        (Homotopy.fiberSquare_value_reindex e.hom F hF b σ f a r ⟨Cube.endpoint y.obj.unop false⟩)
    · intro z g s
      exact (isoFiberContractible_path_eval e F hF b (σ.mapElements.map f) (σ.mapElements.map g)
        ((Homotopy.fiberReindexIso e.hom b σ).inv.app x a) r s).trans
          ((Homotopy.fiberSquare_value_reindex e.hom F hF b σ (f ≫ g) a ((interval Δ).map g r) s).trans
            (isoFiberContractible_path_eval (Functor.isoWhiskerLeft σ.mapElements e)
              (F.reindex σ) (hF.reindex σ) (Term.reindex b σ) f g a r s).symm)
theorem HomotopyEquivalence.ofIso_reindex {Γ Δ : Context.{u}} {A B : Family Γ}
    (e : A ≅ B) (F : Filling B) (hF : F.Lawful) (σ : Δ ⟶ Γ) :
    (ofIso e F hF).reindex σ = ofIso (Functor.isoWhiskerLeft σ.mapElements e)
      (F.reindex σ) (hF.reindex σ) := by
  apply congrArg HomotopyEquivalence.mk
  exact isoFiberContractible_reindex (Functor.isoWhiskerLeft (projection B).mapElements e)
    (F.reindex (projection B)) (hF.reindex (projection B)) (generic B) (liftSub B σ)

end SquareKit.Cubical.Cartesian
