import SquareKit.Internal.Cubical.Substitution
import SquareKit.Internal.Cubical.IntervalExtension
import SquareKit.Internal.Cubical.IntervalReversal
import SquareKit.Internal.Cubical.IntervalScaling

/-! Homotopy fibers and contraction use native cubical paths. A fiber center
alone, or an inverse on underlying sets, does not supply the contraction. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

/-- Paths in a family which is constant in the added interval coordinate. -/
def homogeneousPath {Γ : Context.{u}} (A : Family Γ) (a b : Term A) : Family Γ :=
  path (reindex A (projection (interval Γ))) a b

/-- The constant native path at a section. -/
def homogeneousRefl {Γ : Context.{u}} {A : Family Γ} (a : Term A) :
    Term (homogeneousPath A a a) :=
  pathLam (a.reindex (projection (interval Γ))) rfl rfl

/-- Reverse a native path using the existing De Morgan reversal provider. -/
def homogeneousReverse {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    (p : Term (homogeneousPath A a b)) : Term (homogeneousPath A b a) :=
  pathLam ((pathApp p).reindex (reverseInterval Γ))
    (by
      apply Term.ext
      intro x
      change (p.val x).val.val (𝟙 x)
        (ULift.up (Cube.comp (Cube.endpoint x.obj.unop false) Cube.reversal)) = b.val x
      exact (congrArg (fun r : Cube.Hom x.obj.unop ⟨1⟩ =>
        (show A.obj x from (p.val x).val.val (𝟙 x)
          (show (interval Γ).obj x from ULift.up r))) (Cube.endpoint_reversal x.obj.unop false)).trans
          ((p.val x).property (𝟙 x)).2)
    (by
      apply Term.ext
      intro x
      change (p.val x).val.val (𝟙 x)
        (ULift.up (Cube.comp (Cube.endpoint x.obj.unop true) Cube.reversal)) = a.val x
      exact (congrArg (fun r : Cube.Hom x.obj.unop ⟨1⟩ =>
        (show A.obj x from (p.val x).val.val (𝟙 x)
          (show (interval Γ).obj x from ULift.up r))) (Cube.endpoint_reversal x.obj.unop true)).trans
          ((p.val x).property (𝟙 x)).1)

def homogeneousReindex {Γ Δ : Context.{u}} {A : Family Γ} {a b : Term A}
    (p : Term (homogeneousPath A a b)) (σ : Δ ⟶ Γ) :
    Term (homogeneousPath (reindex A σ) (a.reindex σ) (b.reindex σ)) :=
  Term.map (pathReindex (reindex A (projection (interval Γ))) a b σ) (p.reindex σ)

/-- The dual connection `¬(r ∧ ¬j)` contracts a path toward its final endpoint. -/
def tailInterval (Γ : Context.{u}) :
    total (interval (total (interval Γ))) ⟶ total (interval Γ) :=
  reverseInterval (total (interval Γ)) ≫ scaleInterval Γ ≫ reverseInterval Γ

theorem tailInterval_zero (Γ : Context.{u}) :
    endpointSub (total (interval Γ)) false ≫ tailInterval Γ = reverseInterval Γ := by
  ext I z
  change (⟨z.1,ULift.up (Cube.comp
    (Cube.meet z.2.down (Cube.comp (Cube.endpoint I.unop false) Cube.reversal)) Cube.reversal)⟩ :
      (total (interval Γ)).obj I) = ⟨z.1,ULift.up (Cube.comp z.2.down Cube.reversal)⟩
  exact congrArg (fun r => (⟨z.1,ULift.up r⟩ : (total (interval Γ)).obj I))
    (congrArg (fun r => Cube.comp r Cube.reversal)
      ((congrArg (Cube.meet z.2.down) (Cube.endpoint_reversal I.unop false)).trans
        (Cube.meet_one z.2.down)))

theorem tailInterval_one (Γ : Context.{u}) :
    endpointSub (total (interval Γ)) true ≫ tailInterval Γ =
      projection (interval Γ) ≫ endpointSub Γ true := by
  ext I z
  change (⟨z.1,ULift.up (Cube.comp
    (Cube.meet z.2.down (Cube.comp (Cube.endpoint I.unop true) Cube.reversal)) Cube.reversal)⟩ :
      (total (interval Γ)).obj I) = ⟨z.1,ULift.up (Cube.endpoint I.unop true)⟩
  exact congrArg (fun r => (⟨z.1,ULift.up r⟩ : (total (interval Γ)).obj I))
    ((congrArg (fun r => Cube.comp r Cube.reversal)
      ((congrArg (Cube.meet z.2.down) (Cube.endpoint_reversal I.unop true)).trans
        (Cube.meet_zero z.2.down))).trans (Cube.endpoint_reversal I.unop false))

theorem tailInterval_start (Γ : Context.{u}) :
    liftSub (interval (total (interval Γ))) (endpointSub Γ false) ≫ tailInterval Γ =
      projection (interval Γ) ≫ endpointSub Γ true := by
  ext I z
  change (⟨z.1,ULift.up (Cube.comp
    (Cube.meet (Cube.endpoint I.unop false) (Cube.comp z.2.down Cube.reversal)) Cube.reversal)⟩ :
      (total (interval Γ)).obj I) = ⟨z.1,ULift.up (Cube.endpoint I.unop true)⟩
  exact congrArg (fun r => (⟨z.1,ULift.up r⟩ : (total (interval Γ)).obj I))
    ((congrArg (fun r => Cube.comp r Cube.reversal)
      (Cube.zero_meet (Cube.comp z.2.down Cube.reversal))).trans
        (Cube.endpoint_reversal I.unop false))

theorem tailInterval_finish (Γ : Context.{u}) :
    liftSub (interval (total (interval Γ))) (endpointSub Γ true) ≫ tailInterval Γ = 𝟙 _ := by
  ext I z
  have hm : Cube.meet (Cube.endpoint I.unop true) (Cube.comp z.2.down Cube.reversal) =
      Cube.comp z.2.down Cube.reversal := by
    refine Quotient.inductionOn (Cube.comp z.2.down Cube.reversal) ?_
    intro r
    exact Quotient.sound (fun i => (Expr.Conv.meet_comm _ _).trans (Expr.Conv.meet_one (r i)))
  change (⟨z.1,ULift.up (Cube.comp
    (Cube.meet (Cube.endpoint I.unop true) (Cube.comp z.2.down Cube.reversal)) Cube.reversal)⟩ :
      (total (interval Γ)).obj I) = z
  rw [hm]
  have he : Cube.comp (Cube.comp z.2.down Cube.reversal) Cube.reversal = z.2.down :=
    (@Category.assoc Cube _ I.unop ⟨1⟩ ⟨1⟩ ⟨1⟩ z.2.down Cube.reversal Cube.reversal).trans
      ((congrArg (fun r => Cube.comp z.2.down r) Cube.reversal_twice).trans
        (@Category.comp_id Cube _ I.unop ⟨1⟩ z.2.down))
  rw [he]
  rcases z with ⟨γ,⟨r⟩⟩
  rfl

theorem tailInterval_natural {Γ Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    tailInterval Δ ≫ liftSub (interval Γ) σ =
      liftSub (interval (total (interval Γ))) (liftSub (interval Γ) σ) ≫ tailInterval Γ := rfl

/-- A chosen center and a coherent path from it to every generalized element. -/
structure HomotopyContractible {Γ : Context.{u}} (A : Family Γ) where
  center : Term A
  contraction : Term (homogeneousPath (reindex A (projection A))
    (center.reindex (projection A)) (generic A))

/-- Substitution retains the chosen center and the whole native contraction. -/
def HomotopyContractible.reindex {Γ Δ : Context.{u}} {A : Family Γ}
    (c : HomotopyContractible A) (σ : Δ ⟶ Γ) :
    HomotopyContractible (Presheaf.reindex A σ) where
  center := c.center.reindex σ
  contraction := Term.map
    (pathReindex (Presheaf.reindex (Presheaf.reindex A (projection A)) (projection (interval (total A))))
      (c.center.reindex (projection A)) (generic A) (liftSub A σ))
    (c.contraction.reindex (liftSub A σ))

/-- Evaluate the contraction at a supplied section. -/
def HomotopyContractible.pathTo {Γ : Context.{u}} {A : Family Γ}
    (c : HomotopyContractible A) (a : Term A) : Term (homogeneousPath A c.center a) :=
  Term.map (pathReindex (Presheaf.reindex (Presheaf.reindex A (projection A)) (projection (interval (total A))))
    (c.center.reindex (projection A)) (generic A) (pair (𝟙 Γ) a))
    (c.contraction.reindex (pair (𝟙 Γ) a))

def homogeneousPathMap {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    {a b : Term A} (p : Term (homogeneousPath A a b)) :
    Term (homogeneousPath B (Term.map f a) (Term.map f b)) :=
  pathLam (Term.map (Functor.whiskerLeft (projection (interval Γ)).mapElements f) (pathApp p))
    (congrArg (Term.map f) (pathApp_zero p)) (congrArg (Term.map f) (pathApp_one p))

/-- Native paths with constant discrete coefficients have equal endpoints. -/
theorem discretePath_endpoints {Γ : Context.{u}} {S : Type u}
    {a b : Term (constantFamily Γ S)} (p : Term (homogeneousPath (constantFamily Γ S) a b)) :
    a = b := by
  apply Term.ext
  intro x
  exact (congrArg (fun t => t.val x) (pathApp_zero p)).symm.trans
    ((constant_section_interval (pathApp p) x ((endpoint Γ false).val x)
      ((endpoint Γ true).val x)).trans (congrArg (fun t => t.val x) (pathApp_one p)))

theorem HomotopyContractible.discrete_observations {Γ : Context.{u}} {A : Family Γ}
    (c : HomotopyContractible A) {S : Type u} (f : A ⟶ constantFamily Γ S) (a b : Term A) :
    Term.map f a = Term.map f b :=
  (discretePath_endpoints (homogeneousPathMap f (c.pathTo a))).symm.trans
    (discretePath_endpoints (homogeneousPathMap f (c.pathTo b)))

/-- The fiber retains a point in the domain and a native path to the target. -/
def homotopyFiber {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (b : Term B) : Family Γ :=
  sigma A (homogeneousPath (reindex B (projection A))
    (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
    (b.reindex (projection A)))

/-- Introduce a fiber point using a native path at the supplied section. -/
def homotopyFiberIntro {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (b : Term B) (a : Term A) (p : Term (homogeneousPath B (Term.map f a) b)) :
    Term (homotopyFiber f b) :=
  sigmaIntro a (Term.map
    (pathReindexIso (reindex (reindex B (projection A)) (projection (interval (total A))))
      (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
      (b.reindex (projection A)) (pair (𝟙 Γ) a)).inv p)

/-- The second projection keeps its native path witness, including all restrictions. -/
def homotopyFiberPath {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (b : Term B) (z : Term (homotopyFiber f b)) :
    Term (homogeneousPath B (Term.map f (sigmaFst z)) b) :=
  Term.map (pathReindexIso
    (reindex (reindex B (projection A)) (projection (interval (total A))))
    (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
    (b.reindex (projection A)) (pair (𝟙 Γ) (sigmaFst z))).hom (sigmaSnd z)

/-- The path family inside the generic-target homotopy fiber. -/
abbrev genericFiberPathFamily {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) :=
  homogeneousPath (reindex (reindex B (projection B)) (projection (reindex A (projection B))))
    (Term.map (Functor.whiskerLeft (projection (reindex A (projection B))).mapElements
      (Functor.whiskerLeft (projection B).mapElements f)) (generic (reindex A (projection B))))
    ((generic B).reindex (projection (reindex A (projection B))))

/-- The path component of a generic fiber at a specified domain section. -/
def genericFiberPathIso {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (σ : Δ ⟶ total B) (a : Term (reindex A (σ ≫ projection B))) :
    reindex (genericFiberPathFamily f) (pair σ a) ≅
      homogeneousPath (reindex B (σ ≫ projection B))
        (Term.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) a)
        ((generic B).reindex σ) :=
  pathReindexIso
    (reindex (reindex (reindex B (projection B)) (projection (reindex A (projection B))))
      (projection (interval (total (reindex A (projection B))))))
    (Term.map (Functor.whiskerLeft (projection (reindex A (projection B))).mapElements
      (Functor.whiskerLeft (projection B).mapElements f)) (generic (reindex A (projection B))))
    ((generic B).reindex (projection (reindex A (projection B)))) (pair σ a)

/-- Introduce a generic-target fiber after an arbitrary context substitution. -/
def genericFiberIntro {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (σ : Δ ⟶ total B) (a : Term (reindex A (σ ≫ projection B)))
    (p : Term (homogeneousPath (reindex B (σ ≫ projection B))
      (Term.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) a)
      ((generic B).reindex σ))) :
    Term (reindex (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f)
      (generic B)) σ) :=
  sigmaIntro (B := reindex (genericFiberPathFamily f) (liftSub (reindex A (projection B)) σ)) a
    (Term.map (genericFiberPathIso f σ a).inv p)

/-- Read the domain component after target substitution. -/
def genericFiberFst {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (σ : Δ ⟶ total B)
    (z : Term (reindex (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f)
      (generic B)) σ)) : Term (reindex A (σ ≫ projection B)) :=
  sigmaFst (B := reindex (genericFiberPathFamily f) (liftSub (reindex A (projection B)) σ)) z

/-- Read the native path component after an arbitrary target substitution. -/
def genericFiberPath {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (σ : Δ ⟶ total B)
    (z : Term (reindex (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f)
      (generic B)) σ)) :
    Term (homogeneousPath (reindex B (σ ≫ projection B))
      (Term.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) (genericFiberFst f σ z))
      ((generic B).reindex σ)) :=
  Term.map (genericFiberPathIso f σ (genericFiberFst f σ z)).hom
    (sigmaSnd (B := reindex (genericFiberPathFamily f) (liftSub (reindex A (projection B)) σ)) z)

theorem genericFiberPathIso_inverse_reindex {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ total B) (a : Term (reindex A (σ ≫ projection B))) (τ : Θ ⟶ Δ) :
    pathReindex (reindex (reindex B (σ ≫ projection B)) (projection (interval Δ)))
      (Term.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) a)
      ((generic B).reindex σ) τ ≫ (genericFiberPathIso f (τ ≫ σ) (a.reindex τ)).inv =
    Functor.whiskerLeft τ.mapElements (genericFiberPathIso f σ a).inv :=
  (Iso.comp_inv_eq (genericFiberPathIso f (τ ≫ σ) (a.reindex τ))).mpr
    ((Iso.eq_inv_comp (Functor.isoWhiskerLeft τ.mapElements (genericFiberPathIso f σ a))).mpr rfl)

theorem genericFiberIntro_reindex {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ total B) (a : Term (reindex A (σ ≫ projection B)))
    (p : Term (homogeneousPath (reindex B (σ ≫ projection B))
      (Term.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) a)
      ((generic B).reindex σ))) (τ : Θ ⟶ Δ) :
    genericFiberIntro f (τ ≫ σ) (a.reindex τ)
      (Term.map (pathReindex (reindex (reindex B (σ ≫ projection B)) (projection (interval Δ)))
        (Term.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) a)
        ((generic B).reindex σ) τ) (p.reindex τ)) =
    (genericFiberIntro f σ a p).reindex τ := by
  apply Term.ext
  intro x
  apply congrArg (Sigma.mk ((a.reindex τ).val x))
  exact congrArg (fun η => η.app x ((p.reindex τ).val x))
    (genericFiberPathIso_inverse_reindex f σ a τ)

theorem genericFiberIntro_congr {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ total B) (a a' : Term (reindex A (σ ≫ projection B)))
    (h : a = a')
    (p : Term (homogeneousPath (reindex B (σ ≫ projection B))
      (Term.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) a) ((generic B).reindex σ)))
    (p' : Term (homogeneousPath (reindex B (σ ≫ projection B))
      (Term.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) a') ((generic B).reindex σ)))
    (hp : HEq p p') : genericFiberIntro f σ a p = genericFiberIntro f σ a' p' := by
  subst a'
  cases hp
  rfl

theorem genericFiberIntro_eta {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ total B)
    (z : Term (reindex (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f)
      (generic B)) σ)) :
    genericFiberIntro f σ (genericFiberFst f σ z) (genericFiberPath f σ z) = z := by
  apply Term.ext
  intro x
  apply congrArg (Sigma.mk ((genericFiberFst f σ z).val x))
  exact congrArg (fun t => t.val x)
    (Term.map_iso_roundtrip (genericFiberPathIso f σ (genericFiberFst f σ z))
      (sigmaSnd (B := reindex (genericFiberPathFamily f) (liftSub (reindex A (projection B)) σ)) z))

/-- Equality of whole path sections also identifies their endpoint-indexed terms. -/
theorem pathTerm_hext {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ b₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ b₁ : Term (reindex B (endpointSub Γ true))}
    (p : Term (path B a₀ a₁)) (q : Term (path B b₀ b₁)) (h : pathApp p = pathApp q) :
    HEq p q := by
  have hzero := (pathApp_zero p).symm.trans
    ((congrArg (fun t => t.reindex (endpointSub Γ false)) h).trans (pathApp_zero q))
  have hone := (pathApp_one p).symm.trans
    ((congrArg (fun t => t.reindex (endpointSub Γ true)) h).trans (pathApp_one q))
  subst b₀
  subst b₁
  exact heq_of_eq (pathApp_injective h)

/-- Contractibility at the generic target quantifies over all targets naturally. -/
structure HomotopyEquivalence {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) where
  fibers : HomotopyContractible
    (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B))

/-- Transport contractibility through a family isomorphism, retaining native paths. -/
def HomotopyContractible.transport {Γ : Context.{u}} {A B : Family Γ}
    (c : HomotopyContractible A) (e : A ≅ B) : HomotopyContractible B where
  center := Term.map e.hom c.center
  contraction := by
    let i := Functor.isoWhiskerLeft (projection B).mapElements e
    let p := homogeneousPathMap i.hom
      ((c.reindex (projection B)).pathTo (Term.map i.inv (generic B)))
    exact pathLam (pathApp p) (pathApp_zero p)
      ((pathApp_one p).trans (Term.map_iso_roundtrip i.symm (generic B)))

/-- Change the second component of a dependent sum by a natural isomorphism. -/
def sigmaSecondMap {Γ : Context.{u}} (A : Family Γ) {B C : Family (total A)}
    (e : B ⟶ C) : sigma A B ⟶ sigma A C where
  app x := TypeCat.ofHom (fun z => ⟨z.1,e.app (extendObj A x z.1) z.2⟩)
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro z
    apply congrArg (Sigma.mk (A.map f z.1))
    exact e.naturality_apply (extendHom A f z.1) z.2

def sigmaSecondIso {Γ : Context.{u}} (A : Family Γ) {B C : Family (total A)}
    (e : B ≅ C) : sigma A B ≅ sigma A C where
  hom := sigmaSecondMap A e.hom
  inv := sigmaSecondMap A e.inv
  hom_inv_id := by
    ext x z
    exact congrArg (Sigma.mk z.1) (congrArg (fun η => η.app (extendObj A x z.1) z.2) e.hom_inv_id)
  inv_hom_id := by
    ext x z
    exact congrArg (Sigma.mk z.1) (congrArg (fun η => η.app (extendObj A x z.1) z.2) e.inv_hom_id)

def genericFiberReindexIso {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (σ : Δ ⟶ Γ) :
    reindex (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B))
      (liftSub B σ) ≅
    homotopyFiber (Functor.whiskerLeft (projection (reindex B σ)).mapElements
      (Functor.whiskerLeft σ.mapElements f)) (generic (reindex B σ)) :=
  sigmaSecondIso _ (pathReindexIso
    (reindex (reindex (reindex B (projection B)) (projection (reindex A (projection B))))
      (projection (interval (total (reindex A (projection B))))))
    (Term.map (Functor.whiskerLeft (projection (reindex A (projection B))).mapElements
      (Functor.whiskerLeft (projection B).mapElements f)) (generic (reindex A (projection B))))
    ((generic B).reindex (projection (reindex A (projection B))))
    (liftSub (reindex A (projection B)) (liftSub B σ)))

/-- A genuine equivalence remains an equivalence after context substitution. -/
def HomotopyEquivalence.reindex {Γ Δ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (E : HomotopyEquivalence f) (σ : Δ ⟶ Γ) :
    HomotopyEquivalence (Functor.whiskerLeft σ.mapElements f) where
  fibers := (E.fibers.reindex (liftSub B σ)).transport (genericFiberReindexIso f σ)

/-- The remaining segment of a path, starting at its reversed outer parameter. -/
def homogeneousTail {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    (p : Term (homogeneousPath A a b)) :
    Term (homogeneousPath (reindex A (projection (interval Γ)))
      ((pathApp p).reindex (reverseInterval Γ)) (b.reindex (projection (interval Γ)))) := by
  have hr (σ τ : total (interval Γ) ⟶ total (interval Γ)) (h : σ = τ) :
      HEq ((pathApp p).reindex σ) ((pathApp p).reindex τ) := by
    cases h
    rfl
  have hzero : ((pathApp p).reindex (tailInterval Γ)).reindex
      (endpointSub (total (interval Γ)) false) = (pathApp p).reindex (reverseInterval Γ) :=
    eq_of_heq (hr _ _ (tailInterval_zero Γ))
  have hone : ((pathApp p).reindex (tailInterval Γ)).reindex
      (endpointSub (total (interval Γ)) true) = b.reindex (projection (interval Γ)) := by
    have he : ((pathApp p).reindex (tailInterval Γ)).reindex
        (endpointSub (total (interval Γ)) true) =
        ((pathApp p).reindex (endpointSub Γ true)).reindex (projection (interval Γ)) :=
      eq_of_heq (hr _ _ (tailInterval_one Γ))
    exact he.trans (congrArg (fun t : Term A => t.reindex (projection (interval Γ))) (pathApp_one p))
  exact pathLam ((pathApp p).reindex (tailInterval Γ)) hzero hone

theorem homogeneousTail_start {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    (p : Term (homogeneousPath A a b)) :
    (pathApp (homogeneousTail p)).reindex
      (liftSub (interval (total (interval Γ))) (endpointSub Γ false)) =
    b.reindex (projection (interval Γ)) := by
  have hr (σ τ : total (interval Γ) ⟶ total (interval Γ)) (h : σ = τ) :
      HEq ((pathApp p).reindex σ) ((pathApp p).reindex τ) := by
    cases h
    rfl
  have he : (pathApp (homogeneousTail p)).reindex
      (liftSub (interval (total (interval Γ))) (endpointSub Γ false)) =
      ((pathApp p).reindex (endpointSub Γ true)).reindex (projection (interval Γ)) :=
    eq_of_heq (hr _ _ (tailInterval_start Γ))
  exact he.trans (congrArg (fun t : Term A => t.reindex (projection (interval Γ))) (pathApp_one p))

theorem homogeneousTail_finish {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    (p : Term (homogeneousPath A a b)) :
    (pathApp (homogeneousTail p)).reindex
      (liftSub (interval (total (interval Γ))) (endpointSub Γ true)) = pathApp p := by
  have hr (σ τ : total (interval Γ) ⟶ total (interval Γ)) (h : σ = τ) :
      HEq ((pathApp p).reindex σ) ((pathApp p).reindex τ) := by
    cases h
    rfl
  exact eq_of_heq (hr _ _ (tailInterval_finish Γ))

/-- The center of an isomorphism's homotopy fiber uses its actual inverse. -/
def isoFiberCenter {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) :
    Term (homotopyFiber (Functor.whiskerLeft (projection B).mapElements e.hom) (generic B)) := by
  let i := Functor.isoWhiskerLeft (projection B).mapElements e
  exact genericFiberIntro e.hom (𝟙 (total B)) (Term.map i.inv (generic B))
    (pathLam ((generic B).reindex (projection (interval (total B))))
      (Term.map_iso_roundtrip i.symm (generic B)).symm rfl)

/-- A whole fiber path is built from the native dual connection. -/
def isoFiberContractionSection {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) :
    let H := homotopyFiber (Functor.whiskerLeft (projection B).mapElements e.hom) (generic B)
    Term (reindex (reindex H (projection H)) (projection (interval (total H)))) := by
  let H := homotopyFiber (Functor.whiskerLeft (projection B).mapElements e.hom) (generic B)
  let π := projection H
  let p := genericFiberPath e.hom π (generic H)
  let q := (pathApp p).reindex (reverseInterval (total H))
  let i := Functor.isoWhiskerLeft
    (projection (interval (total H)) ≫ π ≫ projection B).mapElements e
  let a := Term.map i.inv q
  let t := homogeneousTail p
  exact genericFiberIntro e.hom (projection (interval (total H)) ≫ π) a
    (pathLam (pathApp t)
      ((pathApp_zero t).trans (Term.map_iso_roundtrip i.symm q).symm)
      (pathApp_one t))

theorem isoFiberContractionSection_zero_fst {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) :
    let H := homotopyFiber (Functor.whiskerLeft (projection B).mapElements e.hom) (generic B)
    genericFiberFst e.hom (projection H)
      ((isoFiberContractionSection e).reindex (endpointSub (total H) false)) =
    genericFiberFst e.hom (projection H) ((isoFiberCenter e).reindex (projection H)) := by
  let H := homotopyFiber (Functor.whiskerLeft (projection B).mapElements e.hom) (generic B)
  let p := genericFiberPath e.hom (projection H) (generic H)
  let i := Functor.isoWhiskerLeft (projection H ≫ projection B).mapElements e
  exact congrArg (Term.map i.inv) (pathApp_zero (homogeneousReverse p))

theorem isoFiberContractionSection_one_fst {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) :
    let H := homotopyFiber (Functor.whiskerLeft (projection B).mapElements e.hom) (generic B)
    genericFiberFst e.hom (projection H)
      ((isoFiberContractionSection e).reindex (endpointSub (total H) true)) =
    genericFiberFst e.hom (projection H) (generic H) := by
  let H := homotopyFiber (Functor.whiskerLeft (projection B).mapElements e.hom) (generic B)
  let p := genericFiberPath e.hom (projection H) (generic H)
  let i := Functor.isoWhiskerLeft (projection H ≫ projection B).mapElements e
  exact (congrArg (Term.map i.inv) (pathApp_one (homogeneousReverse p))).trans
    (Term.map_iso_roundtrip i (genericFiberFst e.hom (projection H) (generic H)))

theorem isoFiberContractionSection_zero {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) :
    let H := homotopyFiber (Functor.whiskerLeft (projection B).mapElements e.hom) (generic B)
    (isoFiberContractionSection e).reindex (endpointSub (total H) false) =
      (isoFiberCenter e).reindex (projection H) := by
  let H := homotopyFiber (Functor.whiskerLeft (projection B).mapElements e.hom) (generic B)
  let π := projection H
  let p := genericFiberPath e.hom π (generic H)
  let r := projection (interval (total H)) ≫ π
  let q := (pathApp p).reindex (reverseInterval (total H))
  let i := Functor.isoWhiskerLeft (r ≫ projection B).mapElements e
  let a := Term.map i.inv q
  let t := pathLam (pathApp (homogeneousTail p))
    ((pathApp_zero (homogeneousTail p)).trans (Term.map_iso_roundtrip i.symm q).symm)
    (pathApp_one (homogeneousTail p))
  let ic := Functor.isoWhiskerLeft (projection B).mapElements e
  let ac := Term.map ic.inv (generic B)
  let tc := pathLam ((generic B).reindex (projection (interval (total B))))
    (Term.map_iso_roundtrip ic.symm (generic B)).symm rfl
  let τ := endpointSub (total H) false
  have hp : HEq (homogeneousReindex t τ) (homogeneousReindex tc π) :=
    pathTerm_hext _ _ (homogeneousTail_start p)
  have ha : a.reindex τ = ac.reindex π := isoFiberContractionSection_zero_fst e
  exact (genericFiberIntro_reindex e.hom r a t τ).symm.trans
    ((genericFiberIntro_congr e.hom π _ _ ha _ _ hp).trans
      (genericFiberIntro_reindex e.hom (𝟙 (total B)) ac tc π))

theorem isoFiberContractionSection_one {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) :
    let H := homotopyFiber (Functor.whiskerLeft (projection B).mapElements e.hom) (generic B)
    (isoFiberContractionSection e).reindex (endpointSub (total H) true) = generic H := by
  let H := homotopyFiber (Functor.whiskerLeft (projection B).mapElements e.hom) (generic B)
  let π := projection H
  let p := genericFiberPath e.hom π (generic H)
  let r := projection (interval (total H)) ≫ π
  let q := (pathApp p).reindex (reverseInterval (total H))
  let i := Functor.isoWhiskerLeft (r ≫ projection B).mapElements e
  let a := Term.map i.inv q
  let t := pathLam (pathApp (homogeneousTail p))
    ((pathApp_zero (homogeneousTail p)).trans (Term.map_iso_roundtrip i.symm q).symm)
    (pathApp_one (homogeneousTail p))
  let τ := endpointSub (total H) true
  have hp : HEq (homogeneousReindex t τ) p := pathTerm_hext _ _ (homogeneousTail_finish p)
  have ha : a.reindex τ = genericFiberFst e.hom π (generic H) := isoFiberContractionSection_one_fst e
  exact (genericFiberIntro_reindex e.hom r a t τ).symm.trans
    ((genericFiberIntro_congr e.hom π _ _ ha _ _ hp).trans
      (genericFiberIntro_eta e.hom π (generic H)))

/-- Isomorphisms supply genuine contractible native homotopy fibers. -/
def HomotopyEquivalence.ofIso {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) :
    HomotopyEquivalence e.hom where
  fibers := {
    center := isoFiberCenter e
    contraction := pathLam (isoFiberContractionSection e)
      (isoFiberContractionSection_zero e) (isoFiberContractionSection_one e) }

end SquareKit.Cubical.Presheaf
