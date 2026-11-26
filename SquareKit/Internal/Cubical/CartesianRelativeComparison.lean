import SquareKit.Internal.Cubical.CartesianDiscreteRecords
import SquareKit.Internal.Cubical.HomotopyIsoSubstitution

/-! Relative comparisons through the actual contractible fiber of an equivalence. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u
namespace RelativeComparison

section SquareBody
variable {Γ : Context.{u}} {X : Family Γ} {p q : Term X}
  {H K : Term (homogeneousPath X p q)}
  (Ω : Term (homogeneousPath (homogeneousPath X p q) H K))

/-- The entire two-interval body of an arbitrary native path between paths. -/
noncomputable def squareBody : Term (reindex X
    (projection (interval (total (interval Γ))) ≫ projection (interval Γ))) :=
  pathApp (Term.map (EquivalenceFamilies.homogeneousReindexIso X p q
    (projection (interval Γ))).hom (pathApp Ω))

theorem squareBody_start :
    (squareBody Ω).reindex (endpointSub (total (interval Γ)) false) =
      p.reindex (projection (interval Γ)) := pathApp_zero _

theorem squareBody_finish :
    (squareBody Ω).reindex (endpointSub (total (interval Γ)) true) =
      q.reindex (projection (interval Γ)) := pathApp_one _

theorem squareBody_zero :
    (squareBody Ω).reindex (liftSub (interval (total (interval Γ))) (endpointSub Γ false)) =
      pathApp H := by
  apply Term.ext
  intro x
  let y := (projection (interval Γ)).mapElements.obj x
  exact congrArg (fun t : Term (homogeneousPath X p q) => (t.val y).val.val (𝟙 y) x.val.2)
    (pathApp_zero Ω)

theorem squareBody_one :
    (squareBody Ω).reindex (liftSub (interval (total (interval Γ))) (endpointSub Γ true)) =
      pathApp K := by
  apply Term.ext
  intro x
  let y := (projection (interval Γ)).mapElements.obj x
  exact congrArg (fun t : Term (homogeneousPath X p q) => (t.val y).val.val (𝟙 y) x.val.2)
    (pathApp_one Ω)
end SquareBody

namespace Contractible
variable {Γ : Context.{u}} {A : Family Γ}
  (c : HomotopyContractible A) (F : Filling A) (hF : F.Lawful)
  {a b : Term A} (H K : Term (homogeneousPath A a b))

abbrev P := homogeneousPath A a b
abbrev π := projection (interval Γ)
noncomputable abbrev boundary := endpointBoundary (reindex (P (a := a) (b := b)) (π (Γ := Γ))) H K

noncomputable def line : Term (reindex (P (a := a) (b := b)) (π (Γ := Γ))) :=
  Term.map (EquivalenceFamilies.homogeneousReindexIso A a b (π (Γ := Γ))).inv
    (EquivalenceFamilies.ContractiblePaths.extend (c.reindex (π (Γ := Γ)))
      (F.reindex (π (Γ := Γ))) (hF.reindex _)
      ((boundary H K).map
        (EquivalenceFamilies.homogeneousReindexIso A a b (π (Γ := Γ))).hom))

theorem line_boundary (x : (total (interval Γ)).Elements)
    (hx : ((intervalFace Γ false).join (intervalFace Γ true)).Full x) :
    (line c F hF H K).val x = (boundary H K).val x hx := by
  let e := EquivalenceFamilies.homogeneousReindexIso A a b (π (Γ := Γ))
  have h := EquivalenceFamilies.ContractiblePaths.extend_boundary
    (c.reindex (π (Γ := Γ))) (F.reindex (π (Γ := Γ))) (hF.reindex _)
    ((boundary H K).map e.hom) x hx
  exact (congrArg (e.inv.app x) h).trans
    (congrArg (fun f => f.app x ((boundary H K).val x hx)) e.hom_inv_id)

theorem line_zero : (line c F hF H K).reindex (endpointSub Γ false) = H := by
  apply Term.ext
  intro x
  let y := (endpointSub Γ false).mapElements.obj x
  have hy : (intervalFace Γ false).Full y :=
    (Cofibration.full_endpoint (generic (interval Γ)) false y).mpr rfl
  have hj : ((intervalFace Γ false).join (intervalFace Γ true)).Full y :=
    (Cofibration.full_join _ _ y).mpr (Or.inl hy)
  exact (line_boundary c F hF H K y hj).trans
    ((endpointBoundary_zero (reindex (homogeneousPath A a b) (projection (interval Γ))) H K y hj hy).trans
      (eq_of_heq (endpointSection_val (reindex (homogeneousPath A a b) (projection (interval Γ))) false H y hy)))

theorem line_one : (line c F hF H K).reindex (endpointSub Γ true) = K := by
  apply Term.ext
  intro x
  let y := (endpointSub Γ true).mapElements.obj x
  have hy : (intervalFace Γ true).Full y :=
    (Cofibration.full_endpoint (generic (interval Γ)) true y).mpr rfl
  have hj : ((intervalFace Γ false).join (intervalFace Γ true)).Full y :=
    (Cofibration.full_join _ _ y).mpr (Or.inr hy)
  exact (line_boundary c F hF H K y hj).trans
    ((endpointBoundary_one (reindex (homogeneousPath A a b) (projection (interval Γ))) H K y hj hy).trans
      (eq_of_heq (endpointSection_val (reindex (homogeneousPath A a b) (projection (interval Γ))) true K y hy)))

noncomputable def compare : Term (homogeneousPath (homogeneousPath A a b) H K) :=
  pathLam (line c F hF H K) (line_zero c F hF H K) (line_one c F hF H K)

end Contractible

def homogeneousMap {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (a b : Term A) :
    homogeneousPath A a b ⟶ homogeneousPath B (Term.map f a) (Term.map f b) where
  app _x := TypeCat.ofHom (fun p => ⟨{
    val := fun {y} g r => f.app y (p.val.val g r)
    naturality := fun {_y z} g k r => (f.naturality_apply k _).symm.trans
      (congrArg (f.app z) (p.val.naturality g k r)) },
    fun g => ⟨congrArg (f.app _) (p.property g).1, congrArg (f.app _) (p.property g).2⟩⟩)
  naturality _ _ _ := rfl

namespace Fiber
variable {Γ : Context.{u}} {X D : Family Γ} {S : Type u}
  (f : X ⟶ D) (e : D ≅ constantFamily Γ S) (p : Term X)

abbrev target := Term.map f p
abbrev targetSub := pair (𝟙 Γ) (target f p)
abbrev family := reindex
  (homotopyFiber (Functor.whiskerLeft (projection D).mapElements f) (generic D))
  (targetSub f p)

def projectionMap : family f p ⟶ X where
  app _ := TypeCat.ofHom Sigma.fst
  naturality _ _ _ := rfl

def lift {Δ : Context.{u}} (σ : Δ ⟶ Γ) (z : Term (reindex X σ))
    (h : Term.map (Functor.whiskerLeft σ.mapElements f) z = (target f p).reindex σ) :
    Term (reindex (family f p) σ) :=
  genericFiberIntro f (σ ≫ targetSub f p) z
    (pathLam (((target f p).reindex σ).reindex (Presheaf.projection (interval Δ))) h.symm rfl)

include e in
theorem ext {Δ : Context.{u}} (σ : Δ ⟶ Γ)
    (z w : Term (reindex (family f p) σ))
    (h : Term.map (Functor.whiskerLeft σ.mapElements (projectionMap f p)) z =
      Term.map (Functor.whiskerLeft σ.mapElements (projectionMap f p)) w) : z = w := by
  apply genericFiberTerm_ext f (σ ≫ targetSub f p) z w h
  apply pathTerm_hext
  apply Term.ext
  intro x
  let y := (Presheaf.projection (interval Δ)).mapElements.obj x
  let r := x.val.2
  let P := genericFiberPath f (σ ≫ targetSub f p) z
  let Q := genericFiberPath f (σ ≫ targetSub f p) w
  have hp := DiscreteRecords.presented_path_value
    (Functor.isoWhiskerLeft σ.mapElements e) (P.val y) (𝟙 y) r
  have hq := DiscreteRecords.presented_path_value
    (Functor.isoWhiskerLeft σ.mapElements e) (Q.val y) (𝟙 y) r
  exact hp.trans ((congrArg (fun t => f.app (σ.mapElements.obj y) (t.val y)) h).trans hq.symm)

include e in
theorem path_image {q : Term X} (H : Term (homogeneousPath X p q)) :
    Term.map (Functor.whiskerLeft (Presheaf.projection (interval Γ)).mapElements f) (pathApp H) =
      (target f p).reindex (Presheaf.projection (interval Γ)) := by
  apply Term.ext
  intro x
  let y := (Presheaf.projection (interval Γ)).mapElements.obj x
  exact DiscreteRecords.presented_path_value e ((homogeneousPathMap f H).val y) (𝟙 y) x.val.2

def start : Term (family f p) := lift f p (𝟙 Γ) p rfl

def finish {q : Term X} (H : Term (homogeneousPath X p q)) : Term (family f p) :=
  lift f p (𝟙 Γ) q
    (PathDiscrete.ofIso (constant_pathDiscrete S) e (𝟙 Γ) (homogeneousPathMap f H)).symm


def liftedLine {q : Term X} (H : Term (homogeneousPath X p q)) :
    Term (reindex (family f p) (Presheaf.projection (interval Γ))) :=
  lift f p (Presheaf.projection (interval Γ)) (pathApp H) (path_image f e p H)

theorem liftedLine_zero {q : Term X} (H : Term (homogeneousPath X p q)) :
    (liftedLine f e p H).reindex (endpointSub Γ false) = start f p := by
  apply ext f e p (𝟙 Γ)
  exact pathApp_zero H

theorem liftedLine_one {q : Term X} (H : Term (homogeneousPath X p q)) :
    (liftedLine f e p H).reindex (endpointSub Γ true) = finish f e p H := by
  apply ext f e p (𝟙 Γ)
  exact pathApp_one H

def liftedPath {q : Term X} (H : Term (homogeneousPath X p q)) :
    Term (homogeneousPath (family f p) (start f p) (finish f e p H)) :=
  pathLam (liftedLine f e p H) (liftedLine_zero f e p H) (liftedLine_one f e p H)

theorem liftedPath_projection {q : Term X} (H : Term (homogeneousPath X p q)) :
    Term.map (homogeneousMap (projectionMap f p) (start f p) (finish f e p H))
      (liftedPath f e p H) = H := by
  apply pathApp_injective
  rfl

end Fiber


/-- Reindex both dimensions of a native square, retaining its endpoint paths. -/
def squareReindex {Γ Δ : Context.{u}} {X : Family Γ} {p q : Term X}
    {H K : Term (homogeneousPath X p q)}
    (C : Term (homogeneousPath (homogeneousPath X p q) H K)) (σ : Δ ⟶ Γ) :
    Term (homogeneousPath
      (homogeneousPath (reindex X σ) (p.reindex σ) (q.reindex σ))
      (homogeneousReindex H σ) (homogeneousReindex K σ)) :=
  homogeneousPathMap (EquivalenceFamilies.homogeneousReindexIso X p q σ).hom
    (homogeneousReindex C σ)

theorem squareReindex_comp {Γ Δ Θ : Context.{u}} {X : Family Γ} {p q : Term X}
    {H K : Term (homogeneousPath X p q)}
    (C : Term (homogeneousPath (homogeneousPath X p q) H K))
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    squareReindex (squareReindex C σ) τ = squareReindex C (τ ≫ σ) := rfl

theorem squareReindex_id {Γ : Context.{u}} {X : Family Γ} {p q : Term X}
    {H K : Term (homogeneousPath X p q)}
    (C : Term (homogeneousPath (homogeneousPath X p q) H K)) :
    squareReindex C (𝟙 Γ) = C := by
  apply pathApp_injective
  rfl

/-- The full composition equation, named so concrete witnesses need not be
normalized again merely to elaborate the dependent equality's type. -/
def SquareSubstitutionLaw {Γ Δ Θ : Context.{u}} {X : Family Γ} {p q : Term X}
    {H K : Term (homogeneousPath X p q)}
    (C : Term (homogeneousPath (homogeneousPath X p q) H K))
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) : Prop :=
  squareReindex (squareReindex C σ) τ = squareReindex C (τ ≫ σ)

theorem squareSubstitutionLaw {Γ Δ Θ : Context.{u}} {X : Family Γ} {p q : Term X}
    {H K : Term (homogeneousPath X p q)}
    (C : Term (homogeneousPath (homogeneousPath X p q) H K))
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) : SquareSubstitutionLaw C σ τ :=
  squareReindex_comp C σ τ

/-- The corresponding full identity equation for the same chosen witness. -/
def SquareIdentityLaw {Γ : Context.{u}} {X : Family Γ} {p q : Term X}
    {H K : Term (homogeneousPath X p q)}
    (C : Term (homogeneousPath (homogeneousPath X p q) H K)) : Prop :=
  squareReindex C (𝟙 Γ) = C

theorem squareIdentityLaw {Γ : Context.{u}} {X : Family Γ} {p q : Term X}
    {H K : Term (homogeneousPath X p q)}
    (C : Term (homogeneousPath (homogeneousPath X p q) H K)) : SquareIdentityLaw C :=
  squareReindex_id C

variable {Γ : Context.{u}} {X D : Family Γ} {S : Type u}
  (f : X ⟶ D) (E : HomotopyEquivalence f) (e : D ≅ constantFamily Γ S)
  (FX : Filling X) (hFX : FX.Lawful) (FD : Filling D) (hFD : FD.Lawful)
  {p q : Term X} (H K : Term (homogeneousPath X p q))

noncomputable def fiberComparison :
    Term (homogeneousPath
      (homogeneousPath (Fiber.family f p) (Fiber.start f p) (Fiber.finish f e p H))
      (Fiber.liftedPath f e p H) (Fiber.liftedPath f e p K)) :=
  Contractible.compare (E.fibers.reindex (Fiber.targetSub f p))
    ((genericFiberFilling f FX hFX FD hFD).reindex (Fiber.targetSub f p))
    ((genericFiberFilling_lawful f FX hFX FD hFD).reindex _)
    (Fiber.liftedPath f e p H) (Fiber.liftedPath f e p K)

/-- The prescribed paths are retained as exact faces of a native relative square. -/
noncomputable def compare : Term (homogeneousPath (homogeneousPath X p q) H K) := by
  let P := homogeneousMap (Fiber.projectionMap f p) (Fiber.start f p) (Fiber.finish f e p H)
  let C := homogeneousPathMap P (fiberComparison f E e FX hFX FD hFD H K)
  exact pathLam (pathApp C)
    ((pathApp_zero C).trans (Fiber.liftedPath_projection f e p H))
    ((pathApp_one C).trans (Fiber.liftedPath_projection f e p K))

theorem compare_zero :
    (pathApp (compare f E e FX hFX FD hFD H K)).reindex (endpointSub Γ false) = H :=
  pathApp_zero _

theorem compare_one :
    (pathApp (compare f E e FX hFX FD hFD H K)).reindex (endpointSub Γ true) = K :=
  pathApp_one _


noncomputable def body := squareBody (compare f E e FX hFX FD hFD H K)

theorem body_start :
    (body f E e FX hFX FD hFD H K).reindex (endpointSub (total (interval Γ)) false) =
      p.reindex (projection (interval Γ)) := squareBody_start _

theorem body_finish :
    (body f E e FX hFX FD hFD H K).reindex (endpointSub (total (interval Γ)) true) =
      q.reindex (projection (interval Γ)) := squareBody_finish _

theorem body_zero :
    (body f E e FX hFX FD hFD H K).reindex
      (liftSub (interval (total (interval Γ))) (endpointSub Γ false)) = pathApp H :=
  squareBody_zero _

theorem body_one :
    (body f E e FX hFX FD hFD H K).reindex
      (liftSub (interval (total (interval Γ))) (endpointSub Γ true)) = pathApp K :=
  squareBody_one _

/-- Pull back the fixed chosen comparison rather than rerunning its choices. -/
noncomputable def compareAt {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    Term (homogeneousPath
      (homogeneousPath (reindex X σ) (p.reindex σ) (q.reindex σ))
      (homogeneousReindex H σ) (homogeneousReindex K σ)) :=
  squareReindex (compare f E e FX hFX FD hFD H K) σ

theorem compareAt_zero {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    (pathApp (compareAt f E e FX hFX FD hFD H K σ)).reindex (endpointSub Δ false) =
      homogeneousReindex H σ := pathApp_zero _

theorem compareAt_one {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    (pathApp (compareAt f E e FX hFX FD hFD H K σ)).reindex (endpointSub Δ true) =
      homogeneousReindex K σ := pathApp_one _


theorem compareAt_comp {Δ Θ : Context.{u}} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    squareReindex (compareAt f E e FX hFX FD hFD H K σ) τ =
      compareAt f E e FX hFX FD hFD H K (τ ≫ σ) :=
  squareReindex_comp _ σ τ

theorem compareAt_id :
    compareAt f E e FX hFX FD hFD H K (𝟙 Γ) = compare f E e FX hFX FD hFD H K :=
  squareReindex_id _

noncomputable def finThreeComparison {Γ : Context} {p q : Term (constantFamily Γ (Fin 3))}
    (H K : Term (homogeneousPath (constantFamily Γ (Fin 3)) p q)) :
    Term (homogeneousPath (homogeneousPath (constantFamily Γ (Fin 3)) p q) H K) :=
  compare (𝟙 _) (HomotopyEquivalence.ofIso (Iso.refl _)) (Iso.refl _)
    (DiscreteRecords.constantFilling Γ (Fin 3)) (DiscreteRecords.constantFilling_lawful Γ (Fin 3))
    (DiscreteRecords.constantFilling Γ (Fin 3)) (DiscreteRecords.constantFilling_lawful Γ (Fin 3)) H K

end RelativeComparison
end SquareKit.Cubical.Presheaf
