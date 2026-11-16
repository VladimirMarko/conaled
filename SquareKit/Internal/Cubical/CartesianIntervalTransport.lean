import SquareKit.Internal.Cubical.CartesianEquivalenceComposition

/-! Transport between arbitrary interval sections, with actual contractible native fibers.

Evaluation on dependent interval sections admits relative lifts supplied by the family
filler. A strict section of such an evaluation is an equivalence; composing it with
another evaluation proves transport is an equivalence. The interval itself needs no filler.
-/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u
namespace IntervalTransport
variable {Γ Δ : Context.{u}} {A : Family (total (interval Γ))}

def emptyBox (r : Term (interval Γ)) (a : Term (reindex A (graph r))) :
    OpenBox A Subcontext.bot r where
  tube := ⟨fun _ h => h.elim, fun _ h => h.elim⟩
  base := a
  boundary _ h := h.elim

def line (F : Filling A) (r : Term (interval Γ)) (σ : Δ ⟶ Γ)
    (a : Term (reindex A (σ ≫ graph r))) : Term (reindex A (intervalSub σ)) :=
  F.fill (intervalSub σ) Subcontext.bot (Term.reindex r σ)
    (emptyBox (Term.reindex r σ) a)

theorem line_source (F : Filling A) (hF : F.Lawful) (r : Term (interval Γ)) (σ : Δ ⟶ Γ)
    (a : Term (reindex A (σ ≫ graph r))) :
    Term.reindex (line F r σ a) (graph (Term.reindex r σ)) = a :=
  (hF.fills (intervalSub σ) Subcontext.bot (Term.reindex r σ) (emptyBox (Term.reindex r σ) a)).1

theorem line_reindex (F : Filling A) (hF : F.Lawful) (r : Term (interval Γ)) (σ : Δ ⟶ Γ)
    (a : Term (reindex A (σ ≫ graph r))) {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    line F r (τ ≫ σ) (Term.reindex a τ) = Term.reindex (line F r σ a) (intervalSub τ) :=
  hF.uniform (intervalSub σ) Subcontext.bot (Term.reindex r σ) (emptyBox (Term.reindex r σ) a) τ

def mapOfSection {Ξ : Context.{u}} {B C : Family Ξ} (t : Term (reindex C (projection B))) : B ⟶ C where
  app x := TypeCat.ofHom (fun b => t.val (extendObj B x b))
  naturality _ _ f := by
    apply ConcreteCategory.hom_ext
    intro b
    exact (t.property (extendHom B f b)).symm

def map (F : Filling A) (r s : Term (interval Γ)) : reindex A (graph r) ⟶ reindex A (graph s) :=
  mapOfSection (Term.reindex (line F r (projection (reindex A (graph r))) (generic _))
    (graph (Term.reindex s (projection (reindex A (graph r))))))

theorem map_section (F : Filling A) (hF : F.Lawful) (r s : Term (interval Γ))
    (a : Term (reindex A (graph r))) :
    Term.map (map F r s) a = Term.reindex (line F r (𝟙 Γ) a) (graph s) := by
  have h := line_reindex F hF r (projection (reindex A (graph r))) (generic _) (pair (𝟙 Γ) a)
  exact (congrArg (fun t => Term.reindex t (graph s)) h).symm

theorem map_diagonal (F : Filling A) (hF : F.Lawful) (r : Term (interval Γ)) : map F r r = 𝟙 _ := by
  ext x a
  exact congrArg (fun t => t.val (extendObj (reindex A (graph r)) x a))
    (line_source F hF r (projection (reindex A (graph r))) (generic _))

theorem map_reindex (F : Filling A) (hF : F.Lawful) (r s : Term (interval Γ)) (σ : Δ ⟶ Γ) :
    map (F.reindex (intervalSub σ)) (Term.reindex r σ) (Term.reindex s σ) =
      Functor.whiskerLeft σ.mapElements (map F r s) := by
  have h := line_reindex F hF r (projection (reindex A (graph r))) (generic _) (liftSub (reindex A (graph r)) σ)
  ext x a
  exact congrArg (fun t => t.val ((graph (Term.reindex (Term.reindex s σ)
    (projection (reindex (reindex A (graph r)) σ)))).mapElements.obj
      (extendObj (reindex (reindex A (graph r)) σ) x a))) h
end IntervalTransport
/-- Actual extensions of partial lifts over every changed base. -/
structure MapLifting {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) where
  lift : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Subcontext Δ)
    (a : PartialSection (reindex A σ) φ) (b : Term (reindex B σ)),
    (∀ x hx, f.app (σ.mapElements.obj x) (a.val x hx) = b.val x) → Term (reindex A σ)
  boundary : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Subcontext Δ)
    (a : PartialSection (reindex A σ) φ) (b : Term (reindex B σ)) h x hx,
    (lift σ φ a b h).val x = a.val x hx
  projects : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Subcontext Δ)
    (a : PartialSection (reindex A σ) φ) (b : Term (reindex B σ)) h,
    Term.map (Functor.whiskerLeft σ.mapElements f) (lift σ φ a b h) = b

namespace MapLifting
variable {Γ Δ : Context.{u}} {A B : Family Γ} {f : A ⟶ B} (L : MapLifting f)

theorem liftPath_boundary (σ : Δ ⟶ Γ) (a : Term (reindex A σ)) (b : Term (reindex B σ))
    (p : Term (homogeneousPath (reindex B σ) (Term.map (Functor.whiskerLeft σ.mapElements f) a) b))
    (x : (total (interval Δ)).Elements) (hx : (intervalFace Δ false).holds x) :
    f.app ((projection (interval Δ) ≫ σ).mapElements.obj x)
      ((endpointSection (intervalCoefficient (reindex A σ)) false a).val x hx) = (pathApp p).val x := by
  rcases x with @⟨I,γ,r⟩
  have hr := (intervalFace_iff false _).mp hx
  change r = ⟨Cube.endpoint I.unop false⟩ at hr
  subst r
  exact (congrArg (f.app _) (eq_of_heq (endpointSection_val (intervalCoefficient (reindex A σ))
    false a _ hx))).trans (congrArg (fun t => t.val (Δ.elementsMk I γ)) (pathApp_zero p)).symm

def liftPath (σ : Δ ⟶ Γ) (a : Term (reindex A σ)) (b : Term (reindex B σ))
    (p : Term (homogeneousPath (reindex B σ) (Term.map (Functor.whiskerLeft σ.mapElements f) a) b)) :
    Term (reindex A (projection (interval Δ) ≫ σ)) :=
  L.lift (projection (interval Δ) ≫ σ) (intervalFace Δ false)
    (endpointSection (intervalCoefficient (reindex A σ)) false a) (pathApp p)
    (liftPath_boundary σ a b p)

theorem liftPath_zero (σ : Δ ⟶ Γ) (a : Term (reindex A σ)) (b : Term (reindex B σ))
    (p : Term (homogeneousPath (reindex B σ) (Term.map (Functor.whiskerLeft σ.mapElements f) a) b)) :
    Term.reindex (L.liftPath σ a b p) (endpointSub Δ false) = a := by
  apply Term.ext
  intro x
  have h := L.boundary (projection (interval Δ) ≫ σ) (intervalFace Δ false)
    (endpointSection (intervalCoefficient (reindex A σ)) false a) (pathApp p) (liftPath_boundary σ a b p)
    ((endpointSub Δ false).mapElements.obj x) (by rfl)
  exact h.trans (eq_of_heq (endpointSection_val (intervalCoefficient (reindex A σ)) false a _ (by rfl)))

theorem liftPath_map (σ : Δ ⟶ Γ) (a : Term (reindex A σ)) (b : Term (reindex B σ))
    (p : Term (homogeneousPath (reindex B σ) (Term.map (Functor.whiskerLeft σ.mapElements f) a) b)) :
    Term.map (Functor.whiskerLeft (projection (interval Δ) ≫ σ).mapElements f) (L.liftPath σ a b p) = pathApp p :=
  L.projects _ _ _ _ _
end MapLifting
namespace Homotopy

theorem fiberPathOver_intro {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (b : Term B)
    (σ : Δ ⟶ Γ) (a : Term (reindex A σ))
    (p : Term (homogeneousPath (reindex B σ)
      (Term.map (Functor.whiskerLeft σ.mapElements f) a) (Term.reindex b σ))) :
    fiberPathOver f b σ (fiberIntroOver f b σ a p) = p :=
  Term.map_iso_roundtrip (pathReindexIso (intervalCoefficient (reindex B (projection A)))
    (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
    (Term.reindex b (projection A)) (pair σ a)).symm p

end Homotopy
namespace MapLifting.FiberExtension
variable {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
  (L : MapLifting f) (F : Filling B) (hF : F.Lawful)
  (b : Term B) {φ : Subcontext Γ} (z : PartialSection (Homotopy.fiber f b) φ)

abbrev localA := Homotopy.fiberFstOver f b (restrictInclusion φ) z.toRestricted
abbrev localP := Homotopy.fiberPathOver f b (restrictInclusion φ) z.toRestricted

def targetPartial : PartialSection (Homotopy.fiber (𝟙 B) b) φ :=
  PartialSection.ofRestricted (Homotopy.fiberIntroOver (𝟙 B) b (restrictInclusion φ)
    (Term.map (Functor.whiskerLeft (restrictInclusion φ).mapElements f) (localA b z)) (localP b z))

noncomputable def targetFull : Term (Homotopy.fiber (𝟙 B) b) :=
  (identityFiberContractible F hF b).extend
    (Homotopy.fiberFilling F hF F hF (𝟙 B) b) (targetPartial b z)

noncomputable abbrev fullA := Homotopy.fiberFstOver (𝟙 B) b (𝟙 Γ) (targetFull F hF b z)
noncomputable abbrev fullP := Homotopy.fiberPath (𝟙 B) b (targetFull F hF b z)

theorem targetFull_boundary (x : Γ.Elements) (hx : φ.holds x) :
    (targetFull F hF b z).val x = (targetPartial b z).val x hx :=
  (identityFiberContractible F hF b).extend_boundary
    (Homotopy.fiberFilling F hF F hF (𝟙 B) b)
    (Homotopy.fiberFilling_lawful F hF F hF (𝟙 B) b) _ x hx

theorem fullP_boundary :
    Term.reindex (pathApp (fullP F hF b z)) (intervalSub (restrictInclusion φ)) = pathApp (localP b z) := by
  have hz : Term.reindex (targetFull F hF b z) (restrictInclusion φ) =
      Homotopy.fiberIntroOver (𝟙 B) b (restrictInclusion φ)
        (Term.map (Functor.whiskerLeft (restrictInclusion φ).mapElements f) (localA b z)) (localP b z) := by
    apply Term.ext
    intro x
    exact targetFull_boundary F hF b z ((restrictInclusion φ).mapElements.obj x) x.val.property
  have hp := congrArg (fun t => pathApp (Homotopy.fiberPathOver (𝟙 B) b (restrictInclusion φ) t)) hz
  exact hp.trans (congrArg pathApp (Homotopy.fiberPathOver_intro (𝟙 B) b (restrictInclusion φ)
    (Term.map (Functor.whiskerLeft (restrictInclusion φ).mapElements f) (localA b z)) (localP b z)))

noncomputable def partialLift : PartialSection (intervalCoefficient A) (φ.reindex (projection (interval Γ))) :=
  PartialSection.ofRestricted (Term.reindex
    (L.liftPath (restrictInclusion φ) (localA b z) (Term.reindex b (restrictInclusion φ)) (localP b z))
    (restrictedInterval φ))


theorem partialLift_map (x : (total (interval Γ)).Elements)
    (hx : (φ.reindex (projection (interval Γ))).holds x) :
    f.app ((projection (interval Γ)).mapElements.obj x) ((partialLift L b z).val x hx) =
      (pathApp (fullP F hF b z)).val x := by
  let y := (restrictContext (φ.reindex (projection (interval Γ)))).elementsMk x.obj ⟨x.val,hx⟩
  have h := congrArg (fun t => t.val ((restrictedInterval φ).mapElements.obj y))
    (L.liftPath_map (restrictInclusion φ) (localA b z) (Term.reindex b (restrictInclusion φ)) (localP b z))
  have hp := congrArg (fun t => t.val ((restrictedInterval φ).mapElements.obj y)) (fullP_boundary F hF b z)
  exact h.trans hp.symm

noncomputable def liftFull : Term (intervalCoefficient A) :=
  L.lift (projection (interval Γ)) (φ.reindex (projection (interval Γ)))
    (partialLift L b z) (pathApp (fullP F hF b z)) (partialLift_map L F hF b z)

noncomputable def finalA : Term A := Term.reindex (liftFull L F hF b z) (endpointSub Γ false)

theorem liftFull_map : Term.map (Functor.whiskerLeft (projection (interval Γ)).mapElements f)
    (liftFull L F hF b z) = pathApp (fullP F hF b z) :=
  L.projects _ _ _ _ _

noncomputable def finalP : Term (homogeneousPath B (Term.map f (finalA L F hF b z)) b) :=
  pathLam (pathApp (fullP F hF b z))
    (congrArg (fun t => Term.reindex t (endpointSub Γ false)) (liftFull_map L F hF b z)).symm
    (pathApp_one (fullP F hF b z))

noncomputable def extend : Term (Homotopy.fiber f b) :=
  Homotopy.fiberIntro f b (finalA L F hF b z) (finalP L F hF b z)


theorem finalA_boundary : Term.reindex (finalA L F hF b z) (restrictInclusion φ) = localA b z := by
  apply Term.ext
  intro x
  let y := (endpointSub Γ false).mapElements.obj ((restrictInclusion φ).mapElements.obj x)
  have h := L.boundary (projection (interval Γ)) (φ.reindex (projection (interval Γ)))
    (partialLift L b z) (pathApp (fullP F hF b z)) (partialLift_map L F hF b z) y x.val.property
  exact h.trans (congrArg (fun t => t.val x)
    (L.liftPath_zero (restrictInclusion φ) (localA b z) (Term.reindex b (restrictInclusion φ)) (localP b z)))

theorem extend_restricted : Term.reindex (extend L F hF b z) (restrictInclusion φ) = z.toRestricted := by
  refine (Homotopy.fiberIntroOver_reindex f b (𝟙 Γ) (restrictInclusion φ)
    (finalA L F hF b z) (finalP L F hF b z)).trans ?_
  refine (Homotopy.fiberIntroOver_congr f b (restrictInclusion φ) (Term.reindex (finalA L F hF b z) (restrictInclusion φ)) (localA b z)
    (homogeneousReindex (finalP L F hF b z) (restrictInclusion φ)) (localP b z) (finalA_boundary L F hF b z) (heq_of_eq (fullP_boundary F hF b z))).trans ?_
  exact Homotopy.fiberIntroOver_eta f b (restrictInclusion φ) z.toRestricted

theorem extend_boundary (x : Γ.Elements) (hx : φ.holds x) :
    (extend L F hF b z).val x = z.val x hx :=
  congrArg (fun t => t.val ((restrictContext φ).elementsMk x.obj ⟨x.val,hx⟩)) (extend_restricted L F hF b z)

end MapLifting.FiberExtension

def MapLifting.reindex {Γ Δ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (L : MapLifting f) (σ : Δ ⟶ Γ) : MapLifting (Functor.whiskerLeft σ.mapElements f) where
  lift ρ φ a b h := L.lift (ρ ≫ σ) φ a b h
  boundary ρ φ a b h x hx := L.boundary (ρ ≫ σ) φ a b h x hx
  projects ρ φ a b h := L.projects (ρ ≫ σ) φ a b h

noncomputable def MapLifting.equivalence {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (L : MapLifting f) (F : Filling B) (hF : F.Lawful) : HomotopyEquivalence f where
  fibers := Contractible.ofExtensions
    (fun σ φ z => Term.map
      (Homotopy.fiberReindexIso (Functor.whiskerLeft (projection B).mapElements f) (generic B) σ).inv
      (FiberExtension.extend (L.reindex (σ ≫ projection B))
        (F.reindex (σ ≫ projection B)) (hF.reindex _) (Term.reindex (generic B) σ)
        (z.map (Homotopy.fiberReindexIso (Functor.whiskerLeft (projection B).mapElements f) (generic B) σ).hom)))
    (by
      intro Δ σ φ z x hx
      let i := Homotopy.fiberReindexIso (Functor.whiskerLeft (projection B).mapElements f) (generic B) σ
      exact (congrArg (i.inv.app x) (FiberExtension.extend_boundary (L.reindex (σ ≫ projection B))
        (F.reindex (σ ≫ projection B)) (hF.reindex _) (Term.reindex (generic B) σ)
        (z.map i.hom) x hx)).trans (i.hom_inv_id_app_apply x (z.val x hx)))

namespace MapLifting.SectionExtension
variable {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
  (L : MapLifting f) (j : B ⟶ A) (hj : j ≫ f = 𝟙 B)
  (F : Filling B) (hF : F.Lawful) (a : Term A)
  {φ : Subcontext Γ} (z : PartialSection (Homotopy.fiber j a) φ)

abbrev localB := Homotopy.fiberFstOver j a (restrictInclusion φ) z.toRestricted
abbrev localP := Homotopy.fiberPathOver j a (restrictInclusion φ) z.toRestricted

def mappedPartial : PartialSection (intervalCoefficient B) (φ.reindex (projection (interval Γ))) :=
  PartialSection.ofRestricted (Term.reindex
    (Term.map (Functor.whiskerLeft (projection (interval (restrictContext φ)) ≫ restrictInclusion φ).mapElements f)
      (pathApp (localP j a z))) (restrictedInterval φ))

def targetBox : OpenBox (intervalCoefficient B) φ (endpoint Γ true) where
  tube := mappedPartial (f := f) j a z
  base := Term.map f a
  boundary x hx :=
    congrArg (f.app x) (congrArg (fun t => t.val ((restrictContext φ).elementsMk x.obj ⟨x.val,hx⟩))
      (pathApp_one (localP j a z)))

def targetLine : Term (intervalCoefficient B) := F.fill (projection (interval Γ)) φ (endpoint Γ true) (targetBox (f := f) j a z)
def newB : Term B := Term.reindex (targetLine (f := f) j F a z) (endpointSub Γ false)

include hj hF in
theorem newB_boundary : Term.reindex (newB (f := f) j F a z) (restrictInclusion φ) = localB j a z := by
  apply Term.ext
  intro x
  have ht := (hF.fills (projection (interval Γ)) φ (endpoint Γ true) (targetBox (f := f) j a z)).2
    ((endpointSub Γ false).mapElements.obj ((restrictInclusion φ).mapElements.obj x)) x.val.property
  have hp := congrArg (fun t => f.app ((restrictInclusion φ).mapElements.obj x) (t.val x)) (pathApp_zero (localP j a z))
  exact ht.trans (hp.trans (congrArg (fun g => g.app ((restrictInclusion φ).mapElements.obj x) ((localB j a z).val x)) hj))

noncomputable def localAdjusted : Term (homogeneousPath (Cartesian.reindex A (restrictInclusion φ))
    (Term.reindex (Term.map j (newB (f := f) j F a z)) (restrictInclusion φ)) (Term.reindex a (restrictInclusion φ))) :=
  pathLam (pathApp (localP j a z))
    ((pathApp_zero (localP j a z)).trans
      (congrArg (Term.map (Functor.whiskerLeft (restrictInclusion φ).mapElements j))
        (newB_boundary j hj F hF a z)).symm)
    (pathApp_one (localP j a z))

noncomputable def partialPath : PartialSection (homogeneousPath A (Term.map j (newB (f := f) j F a z)) a) φ :=
  PartialSection.ofRestricted (Term.map (pathReindexIso (intervalCoefficient A)
    (Term.map j (newB (f := f) j F a z)) a (restrictInclusion φ)).inv (localAdjusted j hj F hF a z))

theorem partialPath_body (x : (total (interval Γ)).Elements)
    (hx : (φ.reindex (projection (interval Γ))).holds x) :
    (partialPath j hj F hF a z).pathApp.val x hx =
    (pathApp (localP j a z)).val ((restrictedInterval φ).mapElements.obj
      ((restrictContext (φ.reindex (projection (interval Γ)))).elementsMk x.obj ⟨x.val,hx⟩)) := by
  exact piInverseValue_map (A := interval Γ) (B := intervalCoefficient A) (restrictInclusion φ)
    ((localAdjusted j hj F hF a z).val ((restrictContext φ).elementsMk x.obj ⟨x.val.1,hx⟩)).val
    (𝟙 _) x.val.2

include hj hF in
theorem boundary_map (x : (total (interval Γ)).Elements) (hx : (pathBoundaryFace φ).holds x) :
    f.app ((projection (interval Γ)).mapElements.obj x) ((partialPath j hj F hF a z).pathBoundary.val x hx) =
      (targetLine (f := f) j F a z).val x := by
  rcases hx with hφ | h₀ | h₁
  · have hp := (partialPath j hj F hF a z).pathBoundary_old x (Or.inl hφ) hφ
    have hf := (hF.fills (projection (interval Γ)) φ (endpoint Γ true) (targetBox (f := f) j a z)).2 x hφ
    exact (congrArg (f.app _) (hp.trans (partialPath_body j hj F hF a z x hφ))).trans hf.symm
  · have he := (partialPath j hj F hF a z).pathBoundary_zero x (Or.inr (Or.inl h₀)) h₀
    rcases x with @⟨I,γ,r⟩
    change r = ⟨Cube.endpoint I.unop false⟩ at h₀
    subst r
    exact (congrArg (f.app _) (eq_of_heq he)).trans
      (congrArg (fun g => g.app (Γ.elementsMk I γ) ((newB (f := f) j F a z).val (Γ.elementsMk I γ))) hj)
  · have he := (partialPath j hj F hF a z).pathBoundary_one x (Or.inr (Or.inr h₁)) h₁
    rcases x with @⟨I,γ,r⟩
    change r = ⟨Cube.endpoint I.unop true⟩ at h₁
    subst r
    exact (congrArg (f.app _) (eq_of_heq he)).trans
      (congrArg (fun t => t.val (Γ.elementsMk I γ))
        (hF.fills (projection (interval Γ)) φ (endpoint Γ true) (targetBox (f := f) j a z)).1).symm

noncomputable def body : Term (intervalCoefficient A) :=
  L.lift (projection (interval Γ)) (pathBoundaryFace φ) (partialPath j hj F hF a z).pathBoundary
    (targetLine (f := f) j F a z) (boundary_map j hj F hF a z)

theorem body_zero : Term.reindex (body L j hj F hF a z) (endpointSub Γ false) = Term.map j (newB (f := f) j F a z) := by
  apply Term.ext
  intro x
  have hb := L.boundary (projection (interval Γ)) (pathBoundaryFace φ)
    (partialPath j hj F hF a z).pathBoundary (targetLine (f := f) j F a z)
    (boundary_map j hj F hF a z) ((endpointSub Γ false).mapElements.obj x) (Or.inr (Or.inl rfl))
  exact hb.trans (eq_of_heq ((partialPath j hj F hF a z).pathBoundary_zero _ _ rfl))

theorem body_one : Term.reindex (body L j hj F hF a z) (endpointSub Γ true) = a := by
  apply Term.ext
  intro x
  have hb := L.boundary (projection (interval Γ)) (pathBoundaryFace φ)
    (partialPath j hj F hF a z).pathBoundary (targetLine (f := f) j F a z)
    (boundary_map j hj F hF a z) ((endpointSub Γ true).mapElements.obj x) (Or.inr (Or.inr rfl))
  exact hb.trans (eq_of_heq ((partialPath j hj F hF a z).pathBoundary_one _ _ rfl))

noncomputable def resultPath := pathLam (body L j hj F hF a z)
  (body_zero L j hj F hF a z) (body_one L j hj F hF a z)
noncomputable def extend : Term (Homotopy.fiber j a) :=
  Homotopy.fiberIntro j a (newB (f := f) j F a z) (resultPath L j hj F hF a z)

theorem extend_restricted : Term.reindex (extend L j hj F hF a z) (restrictInclusion φ) = z.toRestricted := by
  refine (Homotopy.fiberIntroOver_reindex j a (𝟙 Γ) (restrictInclusion φ)
    (newB (f := f) j F a z) (resultPath L j hj F hF a z)).trans ?_
  refine (Homotopy.fiberIntroOver_congr j a (restrictInclusion φ)
    (Term.reindex (newB (f := f) j F a z) (restrictInclusion φ)) (localB j a z)
    (homogeneousReindex (resultPath L j hj F hF a z) (restrictInclusion φ)) (localP j a z)
    (newB_boundary j hj F hF a z) ?_).trans (Homotopy.fiberIntroOver_eta j a (restrictInclusion φ) z.toRestricted)
  apply heq_of_eq
  apply Term.ext
  intro x
  have hb := L.boundary (projection (interval Γ)) (pathBoundaryFace φ)
      (partialPath j hj F hF a z).pathBoundary (targetLine (f := f) j F a z)
      (boundary_map j hj F hF a z) ((liftSub (interval Γ) (restrictInclusion φ)).mapElements.obj x)
      (Or.inl x.val.1.property)
  exact hb.trans (((partialPath j hj F hF a z).pathBoundary_old ((liftSub (interval Γ) (restrictInclusion φ)).mapElements.obj x) _ x.val.1.property).trans
      (partialPath_body j hj F hF a z ((liftSub (interval Γ) (restrictInclusion φ)).mapElements.obj x) x.val.1.property))

theorem extend_boundary (x : Γ.Elements) (hx : φ.holds x) :
    (extend L j hj F hF a z).val x = z.val x hx :=
  congrArg (fun t => t.val ((restrictContext φ).elementsMk x.obj ⟨x.val,hx⟩)) (extend_restricted L j hj F hF a z)

end MapLifting.SectionExtension
/-- A strict section of a map with relative lifts has contractible native fibers. -/
noncomputable def MapLifting.sectionEquivalence {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (L : MapLifting f) (j : B ⟶ A) (hj : j ≫ f = 𝟙 B) (F : Filling B) (hF : F.Lawful) : HomotopyEquivalence j where
  fibers := Contractible.ofExtensions
    (fun σ φ z => Term.map
      (Homotopy.fiberReindexIso (Functor.whiskerLeft (projection A).mapElements j) (generic A) σ).inv
      (SectionExtension.extend (L.reindex (σ ≫ projection A))
        (Functor.whiskerLeft (σ ≫ projection A).mapElements j)
        (by ext x b; exact congrArg (fun g => g.app ((σ ≫ projection A).mapElements.obj x) b) hj)
        (F.reindex (σ ≫ projection A)) (hF.reindex _) (Term.reindex (generic A) σ)
        (z.map (Homotopy.fiberReindexIso (Functor.whiskerLeft (projection A).mapElements j) (generic A) σ).hom)))
    (by
      intro Δ σ φ z x hx
      let i := Homotopy.fiberReindexIso (Functor.whiskerLeft (projection A).mapElements j) (generic A) σ
      exact (congrArg (i.inv.app x) (SectionExtension.extend_boundary (L.reindex (σ ≫ projection A))
        (Functor.whiskerLeft (σ ≫ projection A).mapElements j)
        (by ext x b; exact congrArg (fun g => g.app ((σ ≫ projection A).mapElements.obj x) b) hj)
        (F.reindex (σ ≫ projection A)) (hF.reindex _) (Term.reindex (generic A) σ)
        (z.map i.hom) x hx)).trans (i.hom_inv_id_app_apply x (z.val x hx)))

namespace IntervalTransport
variable {Γ Δ : Context.{u}} {A : Family (total (interval Γ))}

def evaluate (r : Term (interval Γ)) : pi (interval Γ) A ⟶ reindex A (graph r) :=
  let P := pi (interval Γ) A
  mapOfSection (Term.reindex
    (app (Term.map (piReindex (interval Γ) A (projection P)) (generic P)))
    (graph (Term.reindex r (projection P))))

theorem evaluate_section (r : Term (interval Γ)) (p : Term (pi (interval Γ) A)) :
    Term.map (evaluate r) p = Term.reindex (app p) (graph r) := rfl

def evaluationBox (r : Term (interval Γ)) (σ : Δ ⟶ Γ) (φ : Subcontext Δ)
    (a : PartialSection (reindex (pi (interval Γ) A) σ) φ)
    (b : Term (reindex (reindex A (graph r)) σ))
    (h : ∀ x hx, (evaluate r).app (σ.mapElements.obj x) (a.val x hx) = b.val x) :
    OpenBox (reindex A (intervalSub σ)) φ (Term.reindex r σ) where
  tube := (a.map (piReindex (interval Γ) A σ)).app
  base := b
  boundary x hx := h x hx

def evaluationLift (F : Filling A) (r : Term (interval Γ)) (σ : Δ ⟶ Γ) (φ : Subcontext Δ)
    (a : PartialSection (reindex (pi (interval Γ) A) σ) φ)
    (b : Term (reindex (reindex A (graph r)) σ))
    (h : ∀ x hx, (evaluate r).app (σ.mapElements.obj x) (a.val x hx) = b.val x) :
    Term (reindex (pi (interval Γ) A) σ) :=
  Term.map (piReindexIso (interval Γ) A σ).inv
    (lam (F.fill (intervalSub σ) φ (Term.reindex r σ) (evaluationBox r σ φ a b h)))

theorem evaluationLift_boundary (F : Filling A) (hF : F.Lawful) (r : Term (interval Γ))
    (σ : Δ ⟶ Γ) (φ : Subcontext Δ)
    (a : PartialSection (reindex (pi (interval Γ) A) σ) φ)
    (b : Term (reindex (reindex A (graph r)) σ))
    (h : ∀ x hx, (evaluate r).app (σ.mapElements.obj x) (a.val x hx) = b.val x)
    (x : Δ.Elements) (hx : φ.holds x) : (evaluationLift F r σ φ a b h).val x = a.val x hx := by
  let e := piReindexIso (interval Γ) A σ
  have hp : e.hom.app x ((evaluationLift F r σ φ a b h).val x) = e.hom.app x (a.val x hx) := by
    refine (e.inv_hom_id_app_apply x _).trans ?_
    apply PiElement.ext
    intro y g s
    refine ((hF.fills (intervalSub σ) φ (Term.reindex r σ) (evaluationBox r σ φ a b h)).2
      (extendObj (interval Δ) y s) (φ.natural g hx)).trans ?_
    have hn := congrArg (fun p => p.val (𝟙 (σ.mapElements.obj y)) s) (a.natural g hx).symm
    change (a.val y (φ.natural g hx)).val (𝟙 _) s =
      (a.val x hx).val (σ.mapElements.map g ≫ 𝟙 _) s at hn
    change (a.val y (φ.natural g hx)).val (σ.mapElements.map (𝟙 y)) s =
      (a.val x hx).val (σ.mapElements.map g) s
    exact (congrArg (fun k => (a.val y (φ.natural g hx)).val k s) (σ.mapElements.map_id y)).trans
      (by simpa only [Category.comp_id] using hn)
  exact (e.hom_inv_id_app_apply x _).symm.trans
    ((congrArg (e.inv.app x) hp).trans (e.hom_inv_id_app_apply x _))

theorem evaluationLift_map (F : Filling A) (hF : F.Lawful) (r : Term (interval Γ))
    (σ : Δ ⟶ Γ) (φ : Subcontext Δ)
    (a : PartialSection (reindex (pi (interval Γ) A) σ) φ)
    (b : Term (reindex (reindex A (graph r)) σ))
    (h : ∀ x hx, (evaluate r).app (σ.mapElements.obj x) (a.val x hx) = b.val x) :
    Term.map (Functor.whiskerLeft σ.mapElements (evaluate r)) (evaluationLift F r σ φ a b h) = b := by
  apply Term.ext
  intro x
  exact (piInverseValue_map (A := interval Γ) (B := A) σ
    ((lam (F.fill (intervalSub σ) φ (Term.reindex r σ) (evaluationBox r σ φ a b h))).val x)
    (𝟙 x) ((Term.reindex r σ).val x)).trans
      (congrArg (fun t => t.val x)
        (hF.fills (intervalSub σ) φ (Term.reindex r σ) (evaluationBox r σ φ a b h)).1)

def evaluationLifting (F : Filling A) (hF : F.Lawful) (r : Term (interval Γ)) :
    MapLifting (evaluate (A := A) r) where
  lift σ φ a b h := evaluationLift F r σ φ a b h
  boundary σ φ a b h x hx := evaluationLift_boundary F hF r σ φ a b h x hx
  projects σ φ a b h := evaluationLift_map F hF r σ φ a b h

noncomputable def evaluationEquivalence (F : Filling A) (hF : F.Lawful) (r : Term (interval Γ)) :
    HomotopyEquivalence (evaluate (A := A) r) :=
  (evaluationLifting F hF r).equivalence (F.reindex (graph r)) (hF.reindex _)
end IntervalTransport
namespace IntervalFunctionFilling
variable {Γ Δ : Context.{u}} {B : Family (total (interval Γ))}
open FunctionFilling
def argument (p : total (interval Δ) ⟶ Γ) :
    Term (reindex (interval Γ) (argumentPath (A := interval Γ) p)) :=
  Term.reindex (generic (reindex (interval Γ) p)) (projection (interval (Args (interval Γ) p)))

theorem argument_target (p : total (interval Δ) ⟶ Γ) :
    Term.reindex (argument p) (graph (target (A := interval Γ) p)) = generic (reindex (interval Γ) p) := rfl

def body (G : Filling B)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (pi (interval Γ) B) p) φ r) : Term (reindex B (liftSub (interval Γ) p)) :=
  bodyAlong G p φ r b (argument p) (argument_target p)

def fill (G : Filling B)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (pi (interval Γ) B) p) φ r) : Term (reindex (pi (interval Γ) B) p) :=
  Term.map (piReindexIso (interval Γ) B p).inv (lam (body G p φ r b))

theorem fill_normalize (G : Filling B)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (pi (interval Γ) B) p) φ r) :
    Term.map (piReindex (interval Γ) B p) (fill G p φ r b) = lam (body G p φ r b) :=
  Term.map_iso_roundtrip (piReindexIso (interval Γ) B p).symm _

theorem body_tube (G : Filling B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (pi (interval Γ) B) p) φ r) (z : (Args (interval Γ) p).Elements)
    (hz : φ.holds ((argumentProjection p).mapElements.obj z)) :
    (body G p φ r b).val z =
      (b.tube.val ((projection (reindex (interval Γ) p)).mapElements.obj z) hz).val (𝟙 _) z.val.2 := by
  have hc := Filling.comp_tube hG (pair (argumentPath p) (argument p))
    (φ.reindex (argumentProjection p)) (Term.reindex r (argumentProjection p)) (target p)
    (b.applyAlong p φ r (argumentProjection p) (argument p)) z hz
  exact hc

theorem body_cap (G : Filling B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (pi (interval Γ) B) p) φ r) (x : Δ.Elements)
    (a : (interval Γ).obj ((graph r ≫ p).mapElements.obj x)) :
    (body G p φ r b).val (extendObj (reindex (interval Γ) p) ((graph r).mapElements.obj x) a) =
      (b.base.val x).val (𝟙 _) a := by
  let z := extendObj (reindex (interval Γ) p) ((graph r).mapElements.obj x) a
  have hc := Filling.comp_diagonal hG (pair (argumentPath p) (argument p))
    (φ.reindex (argumentProjection p)) (Term.reindex r (argumentProjection p)) (target p)
    (b.applyAlong p φ r (argumentProjection p) (argument p)) z rfl
  exact eq_of_heq hc

set_option backward.isDefEq.respectTransparency false in
theorem fill_tube (G : Filling B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (pi (interval Γ) B) p) φ r) (x : (total (interval Δ)).Elements)
    (hx : (φ.reindex (projection (interval Δ))).holds x) :
    (fill G p φ r b).val x = b.tube.val x hx := by
  apply ((piReindexIso (interval Γ) B p).app x).toEquiv.injective
  change (Term.map (piReindex (interval Γ) B p) (fill G p φ r b)).val x = _
  rw [fill_normalize]
  apply PiElement.ext
  intro y f a
  have hy := (φ.reindex (projection (interval Δ))).natural f hx
  have hp := congrArg (fun q => q.val (𝟙 _) a) (b.tube.natural f hx)
  change (b.tube.val x hx).val (p.mapElements.map f ≫ 𝟙 _) a =
    (b.tube.val y hy).val (𝟙 _) a at hp
  change (body G p φ r b).val (extendObj (reindex (interval Γ) p) y a) =
    (b.tube.val x hx).val (p.mapElements.map f) a
  apply (body_tube G hG p φ r b (extendObj (reindex (interval Γ) p) y a) hy).trans
  change (b.tube.val y hy).val (𝟙 _) a = (b.tube.val x hx).val (p.mapElements.map f) a
  simpa only [Category.comp_id] using hp.symm

set_option backward.isDefEq.respectTransparency false in
theorem fill_cap (G : Filling B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (pi (interval Γ) B) p) φ r) :
    Term.reindex (fill G p φ r b) (graph r) = b.base := by
  apply Term.map_injective_of_iso (piReindexIso (interval Γ) B (graph r ≫ p))
  have hn := congrArg (fun s => Term.map
    (piReindex (reindex (interval Γ) p) (reindex B (liftSub (interval Γ) p)) (graph r))
      (Term.reindex s (graph r))) (fill_normalize G p φ r b)
  apply hn.trans
  apply Term.ext
  intro x
  apply PiElement.ext
  intro y f a
  have hp := congrArg (fun q => q.val (𝟙 _) a) (b.base.property f)
  change (b.base.val x).val ((graph r ≫ p).mapElements.map f ≫ 𝟙 _) a =
    (b.base.val y).val (𝟙 _) a at hp
  change (body G p φ r b).val
    (extendObj (reindex (interval Γ) p) ((graph r).mapElements.obj y) a) =
    (b.base.val x).val ((graph r ≫ p).mapElements.map f) a
  exact (body_cap G hG p φ r b y a).trans
    ((by simpa only [Category.comp_id] using hp) : _ = _).symm

theorem argument_uniform     (p : total (interval Δ) ⟶ Γ) {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    argument (intervalSub σ ≫ p) =
      Term.reindex (argument p)
        (intervalSub (liftSub (reindex (interval Γ) p) (intervalSub σ))) := rfl

theorem body_uniform (G : Filling B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (pi (interval Γ) B) p) φ r) {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    body G (intervalSub σ ≫ p) (φ.reindex σ) (Term.reindex r σ) (b.reindex σ) =
      Term.reindex (body G p φ r b) (liftSub (reindex (interval Γ) p) (intervalSub σ)) := by
  let p' := intervalSub σ ≫ p
  let τ := liftSub (reindex (interval Γ) p) (intervalSub σ)
  let k : {v : Term (reindex (interval Γ) (argumentPath (A := interval Γ) p')) //
      Term.reindex v (graph (target p')) = generic (reindex (interval Γ) p')} →
      Term (reindex B (liftSub (interval Γ) p')) :=
    fun v => bodyAlong G p' (φ.reindex σ) (Term.reindex r σ) (b.reindex σ) v.val v.property
  have he : (⟨argument p',argument_target p'⟩ :
      {v : Term (reindex (interval Γ) (argumentPath (A := interval Γ) p')) //
        Term.reindex v (graph (target p')) = generic (reindex (interval Γ) p')}) =
      ⟨Term.reindex (argument p) (intervalSub τ),
        congrArg (fun t => Term.reindex t τ) (argument_target p)⟩ :=
    Subtype.ext (argument_uniform p σ)
  exact (congrArg k he).trans (bodyAlong_uniform G hG p φ r b _ _ σ)

theorem fill_uniform (G : Filling B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (pi (interval Γ) B) p) φ r) {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    fill G (intervalSub σ ≫ p) (φ.reindex σ) (Term.reindex r σ) (b.reindex σ) =
      Term.reindex (fill G p φ r b) (intervalSub σ) := by
  apply Term.map_injective_of_iso (piReindexIso (interval Γ) B (intervalSub σ ≫ p))
  have hn := congrArg (fun s => Term.map
    (piReindex (reindex (interval Γ) p) (reindex B (liftSub (interval Γ) p)) (intervalSub σ))
      (Term.reindex s (intervalSub σ))) (fill_normalize G p φ r b)
  exact (fill_normalize G _ _ _ _).trans
    ((congrArg lam (body_uniform G hG p φ r b σ)).trans hn.symm)

end IntervalFunctionFilling
/-- Fill dependent interval sections pointwise, keeping the argument fixed. -/
def intervalPiFilling {Γ : Context.{u}} {B : Family (total (interval Γ))}
    (G : Filling B) : Filling (pi (interval Γ) B) where
  fill := IntervalFunctionFilling.fill G

theorem intervalPiFilling_lawful {Γ : Context.{u}} {B : Family (total (interval Γ))}
    (G : Filling B) (hG : G.Lawful) :
    (intervalPiFilling G).Lawful where
  fills p φ r b := ⟨IntervalFunctionFilling.fill_cap G hG p φ r b,
    IntervalFunctionFilling.fill_tube G hG p φ r b⟩
  uniform p φ r b σ := IntervalFunctionFilling.fill_uniform G hG p φ r b σ


namespace IntervalTransport
variable {Γ : Context.{u}} {A : Family (total (interval Γ))}
def sectionMap (F : Filling A) (r : Term (interval Γ)) : reindex A (graph r) ⟶ pi (interval Γ) A :=
  mapOfSection (Term.map (piReindexIso (interval Γ) A (projection (reindex A (graph r)))).inv
    (lam (line F r (projection (reindex A (graph r))) (generic _))))

theorem section_evaluate (F : Filling A) (r s : Term (interval Γ)) :
    sectionMap F r ≫ evaluate s = map F r s := by
  ext x a
  exact piInverseValue_map (A := interval Γ) (B := A) (projection (reindex A (graph r)))
    ((lam (line F r (projection (reindex A (graph r))) (generic _))).val (extendObj (reindex A (graph r)) x a))
    (𝟙 _) (s.val x)

noncomputable def sectionEquivalence (F : Filling A) (hF : F.Lawful) (r : Term (interval Γ)) :
    HomotopyEquivalence (sectionMap F r) :=
  (evaluationLifting F hF r).sectionEquivalence (sectionMap F r)
    ((section_evaluate F r r).trans (map_diagonal F hF r))
    (F.reindex (graph r)) (hF.reindex _)

/-- Actual transport equivalence for arbitrary source and target interval terms. -/
noncomputable def equivalence (F : Filling A) (hF : F.Lawful) (r s : Term (interval Γ)) :
    HomotopyEquivalence (map F r s) :=
  (section_evaluate F r s) ▸ (sectionEquivalence F hF r).comp (evaluationEquivalence F hF s)
    (F.reindex (graph r)) (hF.reindex _) (intervalPiFilling F) (intervalPiFilling_lawful F hF)
    (F.reindex (graph s)) (hF.reindex _)

theorem sectionMap_app_eval (F : Filling A) (r : Term (interval Γ))
    (x y : Γ.Elements) (a : (reindex A (graph r)).obj x) (g : x ⟶ y)
    (t : (interval Γ).obj y) :
    ((sectionMap F r).app x a).val g t =
      (line F r (projection (reindex A (graph r))) (generic _)).val
        (extendObj (interval (total (reindex A (graph r))))
          (extendObj (reindex A (graph r)) y ((reindex A (graph r)).map g a)) t) :=
  piInverseValue_map (A := interval Γ) (B := A) (projection (reindex A (graph r)))
    ((lam (line F r (projection (reindex A (graph r))) (generic _))).val
      (extendObj (reindex A (graph r)) x a)) (extendHom (reindex A (graph r)) g a) t

theorem sectionMap_reindex (F : Filling A) (hF : F.Lawful) (r : Term (interval Γ))
    {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    sectionMap (F.reindex (intervalSub σ)) (Term.reindex r σ) =
      Functor.whiskerLeft σ.mapElements (sectionMap F r) ≫ (piReindexIso (interval Γ) A σ).hom := by
  ext x a
  apply PiElement.ext
  intro y g t
  have h := line_reindex F hF r (projection (reindex A (graph r))) (generic _)
    (liftSub (reindex A (graph r)) σ)
  exact (sectionMap_app_eval (F.reindex (intervalSub σ)) (Term.reindex r σ) x y a g t).trans
    ((congrArg (fun q => q.val (extendObj (interval (total (reindex (reindex A (graph r)) σ)))
      (extendObj (reindex (reindex A (graph r)) σ) y ((reindex (reindex A (graph r)) σ).map g a)) t)) h).trans
      (sectionMap_app_eval F r (σ.mapElements.obj x) (σ.mapElements.obj y) a (σ.mapElements.map g) t).symm)
theorem evaluate_reindex (r : Term (interval Γ)) {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    (piReindexIso (interval Γ) A σ).hom ≫ evaluate (Term.reindex r σ) =
      Functor.whiskerLeft σ.mapElements (evaluate (A := A) r) := rfl

end IntervalTransport
/-- Chosen relative lifts commute with further base substitution. -/
def MapLifting.Uniform {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B} (L : MapLifting f) : Prop :=
  ∀ {Δ Θ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Subcontext Δ)
    (a : PartialSection (Cartesian.reindex A σ) φ) (b : Term (Cartesian.reindex B σ))
    (h : ∀ x hx, f.app (σ.mapElements.obj x) (a.val x hx) = b.val x) (τ : Θ ⟶ Δ),
    L.lift (τ ≫ σ) (φ.reindex τ) (a.reindex τ) (Term.reindex b τ)
      (fun x hx => h (τ.mapElements.obj x) hx) = Term.reindex (L.lift σ φ a b h) τ

theorem MapLifting.Uniform.reindex {Γ Δ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    {L : MapLifting f} (hL : L.Uniform) (σ : Δ ⟶ Γ) : (L.reindex σ).Uniform :=
  fun ρ φ a b h τ => hL (ρ ≫ σ) φ a b h τ

theorem MapLifting.liftPath_uniform {Γ Δ Θ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (L : MapLifting f) (hL : L.Uniform) (σ : Δ ⟶ Γ)
    (a : Term (Cartesian.reindex A σ)) (b : Term (Cartesian.reindex B σ))
    (p : Term (homogeneousPath (Cartesian.reindex B σ) (Term.map (Functor.whiskerLeft σ.mapElements f) a) b))
    (τ : Θ ⟶ Δ) :
    L.liftPath (τ ≫ σ) (Term.reindex a τ) (Term.reindex b τ) (homogeneousReindex p τ) =
      Term.reindex (L.liftPath σ a b p) (intervalSub τ) := by
  have he := endpointSection_reindex (intervalCoefficient (Cartesian.reindex A σ)) false a τ
  have hu := hL (projection (interval Δ) ≫ σ) (intervalFace Δ false)
    (endpointSection (intervalCoefficient (Cartesian.reindex A σ)) false a) (pathApp p)
    (MapLifting.liftPath_boundary σ a b p) (intervalSub τ)
  refine Eq.trans ?_ hu
  unfold MapLifting.liftPath
  congr 1

namespace IntervalTransport
variable {Γ Δ Θ : Context.{u}} {A : Family (total (interval Γ))}
theorem evaluationLift_uniform (F : Filling A) (hF : F.Lawful) (r : Term (interval Γ))
    (σ : Δ ⟶ Γ) (φ : Subcontext Δ)
    (a : PartialSection (reindex (pi (interval Γ) A) σ) φ)
    (b : Term (reindex (Cartesian.reindex A (graph r)) σ))
    (h : ∀ x hx, (evaluate r).app (σ.mapElements.obj x) (a.val x hx) = b.val x)
    (τ : Θ ⟶ Δ) :
    evaluationLift F r (τ ≫ σ) (φ.reindex τ) (a.reindex τ) (Term.reindex b τ)
      (fun x hx => h (τ.mapElements.obj x) hx) = Term.reindex (evaluationLift F r σ φ a b h) τ := by
  apply Term.map_injective_of_iso (piReindexIso (interval Γ) A (τ ≫ σ))
  have hn := congrArg (fun s => Term.map
    (piReindex (reindex (interval Γ) σ) (Cartesian.reindex A (liftSub (interval Γ) σ)) τ)
      (Term.reindex s τ))
      (Term.map_iso_roundtrip (piReindexIso (interval Γ) A σ).symm
        (lam (F.fill (intervalSub σ) φ (Term.reindex r σ) (evaluationBox r σ φ a b h))))
  exact (Term.map_iso_roundtrip (piReindexIso (interval Γ) A (τ ≫ σ)).symm _).trans
    ((congrArg lam (hF.uniform (intervalSub σ) φ (Term.reindex r σ)
      (evaluationBox r σ φ a b h) τ)).trans hn.symm)
theorem evaluationLifting_uniform (F : Filling A) (hF : F.Lawful) (r : Term (interval Γ)) :
    (evaluationLifting F hF r).Uniform := evaluationLift_uniform F hF r
theorem evaluationLift_input_reindex (F : Filling A) (r : Term (interval Γ))
    (σ : Δ ⟶ Γ) (ρ : Θ ⟶ Δ) (φ : Subcontext Θ)
    (a : PartialSection (reindex (pi (interval Γ) A) (ρ ≫ σ)) φ)
    (b : Term (reindex (reindex A (graph r)) (ρ ≫ σ)))
    (h : ∀ x hx, (evaluate r).app ((ρ ≫ σ).mapElements.obj x) (a.val x hx) = b.val x) :
    evaluationLift (F.reindex (intervalSub σ)) (Term.reindex r σ) ρ φ
      (a.map (Functor.whiskerLeft ρ.mapElements (piReindexIso (interval Γ) A σ).hom)) b h =
    Term.map (Functor.whiskerLeft ρ.mapElements (piReindexIso (interval Γ) A σ).hom)
      (evaluationLift F r (ρ ≫ σ) φ a b h) := by
  apply Term.map_injective_of_iso (piReindexIso (interval Δ) (reindex A (intervalSub σ)) ρ)
  exact (Term.map_iso_roundtrip (piReindexIso (interval Δ) (reindex A (intervalSub σ)) ρ).symm _).trans
    (Term.map_iso_roundtrip (piReindexIso (interval Γ) A (ρ ≫ σ)).symm _).symm

end IntervalTransport
namespace MapLifting.SectionExtension
variable {Γ Δ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
  (j : B ⟶ A) (hj : j ≫ f = 𝟙 B) (F : Filling B) (hF : F.Lawful)
  (a : Term A) {φ : Subcontext Γ} (z : PartialSection (Homotopy.fiber j a) φ)
  (σ : Δ ⟶ Γ)
def pulled := (z.reindex σ).map (Homotopy.fiberReindexIso j a σ).hom

theorem localP_input_reindex :
    pathApp (localP (Functor.whiskerLeft σ.mapElements j) (Term.reindex a σ) (pulled j a z σ)) =
      Term.reindex (pathApp (localP j a z)) (intervalSub (restrictSubstitution φ σ)) := rfl

theorem mappedPartial_input_reindex :
    mappedPartial (f := Functor.whiskerLeft σ.mapElements f)
      (Functor.whiskerLeft σ.mapElements j) (Term.reindex a σ) (pulled j a z σ) =
      (mappedPartial (f := f) j a z).reindex (intervalSub σ) := rfl

theorem targetBox_input_reindex :
    targetBox (f := Functor.whiskerLeft σ.mapElements f)
      (Functor.whiskerLeft σ.mapElements j) (Term.reindex a σ) (pulled j a z σ) =
      (targetBox (f := f) j a z).reindex σ := rfl

include hF in
theorem targetLine_input_reindex :
    targetLine (f := Functor.whiskerLeft σ.mapElements f)
      (Functor.whiskerLeft σ.mapElements j) (F.reindex σ) (Term.reindex a σ) (pulled j a z σ) =
      Term.reindex (targetLine (f := f) j F a z) (intervalSub σ) :=
  hF.uniform (projection (interval Γ)) φ (endpoint Γ true) (targetBox (f := f) j a z) σ

include hF in
theorem newB_input_reindex :
    newB (f := Functor.whiskerLeft σ.mapElements f)
      (Functor.whiskerLeft σ.mapElements j) (F.reindex σ) (Term.reindex a σ) (pulled j a z σ) =
      Term.reindex (newB (f := f) j F a z) σ :=
  congrArg (fun t => Term.reindex t (endpointSub Δ false)) (targetLine_input_reindex j F hF a z σ)

theorem partialPath_boundary_input_reindex :
    (partialPath (Functor.whiskerLeft σ.mapElements j)
      (show Functor.whiskerLeft σ.mapElements j ≫ Functor.whiskerLeft σ.mapElements f = 𝟙 _ from
        by ext x b; exact congrArg (fun g => g.app (σ.mapElements.obj x) b) hj)
      (F.reindex σ) (hF.reindex _) (Term.reindex a σ) (pulled j a z σ)).pathBoundary =
      (partialPath j hj F hF a z).pathBoundary.reindex (intervalSub σ) := by
  let j' := Functor.whiskerLeft σ.mapElements j
  have hj' : j' ≫ Functor.whiskerLeft σ.mapElements f = 𝟙 _ := by
    ext x b
    exact congrArg (fun g => g.app (σ.mapElements.obj x) b) hj
  let p := partialPath j hj F hF a z
  let q := partialPath j' hj' (F.reindex σ) (hF.reindex _) (Term.reindex a σ) (pulled j a z σ)
  apply PartialSection.ext
  intro x hx
  rcases hx with hφ | h₀ | h₁
  · refine (q.pathBoundary_old x (Or.inl hφ) hφ).trans ?_
    refine (partialPath_body j' hj' (F.reindex σ) (hF.reindex _) (Term.reindex a σ) (pulled j a z σ) x hφ).trans ?_
    exact ((p.pathBoundary_old ((intervalSub σ).mapElements.obj x) (Or.inl hφ) hφ).trans
      (partialPath_body j hj F hF a z ((intervalSub σ).mapElements.obj x) hφ)).symm
  · have hq := q.pathBoundary_zero x (Or.inr (Or.inl h₀)) h₀
    have hp := p.pathBoundary_zero ((intervalSub σ).mapElements.obj x) (Or.inr (Or.inl h₀)) h₀
    rcases x with @⟨I,γ,r⟩
    change r = ⟨Cube.endpoint I.unop false⟩ at h₀
    subst r
    exact (eq_of_heq hq).trans ((congrArg (fun t => j.app (σ.mapElements.obj (Δ.elementsMk I γ))
      (t.val (Δ.elementsMk I γ))) (newB_input_reindex j F hF a z σ)).trans (eq_of_heq hp).symm)
  · have hq := q.pathBoundary_one x (Or.inr (Or.inr h₁)) h₁
    have hp := p.pathBoundary_one ((intervalSub σ).mapElements.obj x) (Or.inr (Or.inr h₁)) h₁
    rcases x with @⟨I,γ,r⟩
    change r = ⟨Cube.endpoint I.unop true⟩ at h₁
    subst r
    exact (eq_of_heq hq).trans (eq_of_heq hp).symm


theorem body_input_reindex (L : MapLifting f) (hL : L.Uniform) :
    body (L.reindex σ) (Functor.whiskerLeft σ.mapElements j)
      (show Functor.whiskerLeft σ.mapElements j ≫ Functor.whiskerLeft σ.mapElements f = 𝟙 _ from
        by ext x b; exact congrArg (fun g => g.app (σ.mapElements.obj x) b) hj)
      (F.reindex σ) (hF.reindex _) (Term.reindex a σ) (pulled j a z σ) =
      Term.reindex (body L j hj F hF a z) (intervalSub σ) := by
  have hp := partialPath_boundary_input_reindex j hj F hF a z σ
  have ht := targetLine_input_reindex (f := f) j F hF a z σ
  have hu := hL (projection (interval Γ)) (pathBoundaryFace φ)
    (partialPath j hj F hF a z).pathBoundary (targetLine (f := f) j F a z)
    (boundary_map j hj F hF a z) (intervalSub σ)
  refine Eq.trans ?_ hu
  dsimp only [body, MapLifting.reindex]
  congr 1


theorem extend_input_reindex (L : MapLifting f) (hL : L.Uniform) :
    Term.map (Homotopy.fiberReindexIso j a σ).hom (Term.reindex (extend L j hj F hF a z) σ) =
      extend (L.reindex σ) (Functor.whiskerLeft σ.mapElements j)
        (show Functor.whiskerLeft σ.mapElements j ≫ Functor.whiskerLeft σ.mapElements f = 𝟙 _ from
          by ext x b; exact congrArg (fun g => g.app (σ.mapElements.obj x) b) hj)
        (F.reindex σ) (hF.reindex _) (Term.reindex a σ) (pulled j a z σ) := by
  let j' := Functor.whiskerLeft σ.mapElements j
  have hj' : j' ≫ Functor.whiskerLeft σ.mapElements f = 𝟙 _ := by
    ext x b
    exact congrArg (fun g => g.app (σ.mapElements.obj x) b) hj
  refine (congrArg (Term.map (Homotopy.fiberReindexIso j a σ).hom)
    (Homotopy.fiberIntroOver_reindex j a (𝟙 Γ) σ
      (newB (f := f) j F a z) (resultPath L j hj F hF a z))).trans ?_
  refine (Homotopy.fiberReindexIso_introOver j a σ _ _).trans ?_
  exact Homotopy.fiberIntroOver_congr j' (Term.reindex a σ) (𝟙 Δ)
    (Term.reindex (newB (f := f) j F a z) σ)
    (newB (f := Functor.whiskerLeft σ.mapElements f) j' (F.reindex σ) (Term.reindex a σ) (pulled j a z σ))
    (homogeneousReindex (resultPath L j hj F hF a z) σ)
    (resultPath (L.reindex σ) j' hj' (F.reindex σ) (hF.reindex _) (Term.reindex a σ) (pulled j a z σ))
    (newB_input_reindex j F hF a z σ).symm
    (heq_of_eq (body_input_reindex j hj F hF a z σ L hL).symm)

end MapLifting.SectionExtension
set_option maxHeartbeats 1600000 in
theorem Homotopy.fiberFilling_reindex {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (b : Term B) (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) (σ : Δ ⟶ Γ) :
    ((fiberFilling F hF G hG f b).reindex σ).transport (fiberReindexIso f b σ) =
    fiberFilling (F.reindex σ) (hF.reindex _) (G.reindex σ) (hG.reindex _)
      (Functor.whiskerLeft σ.mapElements f) (Term.reindex b σ) := by
  let ρ := liftSub A σ
  let a₀ := Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A)
  let a₁ := Term.reindex b (projection A)
  let R := G.reindex (projection (interval (total A)) ≫ projection A)
  have hR : R.Lawful := hG.reindex _
  have hfirst := sigmaFilling_transport_second
    (pathReindexIso (Cartesian.reindex B (projection (interval (total A)) ≫ projection A)) a₀ a₁ ρ)
    (F.reindex σ) (hF.reindex _) ((pathFilling R hR a₀ a₁).reindex ρ)
  exact hfirst.trans (congrArg (sigmaFilling (F.reindex σ) (hF.reindex _))
    (pathFilling_reindex_iso R hR a₀ a₁ ρ))

namespace MapLifting.FiberExtension
variable {Γ Δ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
  (L : MapLifting f) (F : Filling B) (hF : F.Lawful)
  (b : Term B) {φ : Subcontext Γ} (z : PartialSection (Homotopy.fiber f b) φ)
  (σ : Δ ⟶ Γ)
def pulled := (z.reindex σ).map (Homotopy.fiberReindexIso f b σ).hom

theorem localP_input_reindex :
    pathApp (localP (Term.reindex b σ) (pulled b z σ)) =
      Term.reindex (pathApp (localP b z)) (intervalSub (restrictSubstitution φ σ)) := rfl

theorem targetPartial_input_reindex :
    targetPartial (Term.reindex b σ) (pulled b z σ) =
      ((targetPartial b z).reindex σ).map (Homotopy.fiberReindexIso (𝟙 B) b σ).hom := by
  apply PartialSection.ext
  intro x hx
  apply Homotopy.fiber_element_ext
  · rfl
  · intro y g t
    let x' := (restrictContext (φ.reindex σ)).elementsMk x.obj ⟨x.val,hx⟩
    let y' := (restrictContext (φ.reindex σ)).elementsMk y.obj ⟨y.val,(φ.reindex σ).natural g hx⟩
    let g' : x' ⟶ y' := Functor.Elements.homMk g.hom (Subtype.ext g.map_val)
    have hl := Homotopy.fiberIntroOver_path_eval (𝟙 (Cartesian.reindex B σ)) (Term.reindex b σ)
      (restrictInclusion (φ.reindex σ))
      (Term.map (Functor.whiskerLeft (restrictInclusion (φ.reindex σ)).mapElements
        (Functor.whiskerLeft σ.mapElements f)) (localA (Term.reindex b σ) (pulled b z σ)))
      (localP (Term.reindex b σ) (pulled b z σ)) g' t
    have hr := Homotopy.fiberIntroOver_path_eval (𝟙 B) b (restrictInclusion φ)
      (Term.map (Functor.whiskerLeft (restrictInclusion φ).mapElements f) (localA b z))
      (localP b z) ((restrictSubstitution φ σ).mapElements.map g') t
    exact hl.trans hr.symm


theorem targetFull_input_reindex :
    targetFull (F.reindex σ) (hF.reindex _) (Term.reindex b σ) (pulled b z σ) =
      Term.map (Homotopy.fiberReindexIso (𝟙 B) b σ).hom (Term.reindex (targetFull F hF b z) σ) := by
  let e := Homotopy.fiberReindexIso (𝟙 B) b σ
  let c := identityFiberContractible F hF b
  let H := Homotopy.fiberFilling F hF F hF (𝟙 B) b
  have hc : Contractible.map e (c.reindex σ) =
      identityFiberContractible (F.reindex σ) (hF.reindex _) (Term.reindex b σ) :=
    isoFiberContractible_reindex (CategoryTheory.Iso.refl B) F hF b σ
  have hf := Homotopy.fiberFilling_reindex (𝟙 B) b F hF F hF σ
  have hp := targetPartial_input_reindex b z σ
  refine (congrArg₂ (fun cc ff => cc.extend ff (targetPartial (Term.reindex b σ) (pulled b z σ)))
    hc.symm hf.symm).trans ?_
  refine (congrArg ((Contractible.map e (c.reindex σ)).extend ((H.reindex σ).transport e)) hp).trans ?_
  exact ((c.reindex σ).extend_transport e (H.reindex σ) ((targetPartial b z).reindex σ)).trans
    (congrArg (Term.map e.hom) (c.extend_reindex H (Homotopy.fiberFilling_lawful F hF F hF (𝟙 B) b)
      (targetPartial b z) σ))


theorem fullP_input_reindex :
    pathApp (fullP (F.reindex σ) (hF.reindex _) (Term.reindex b σ) (pulled b z σ)) =
      Term.reindex (pathApp (fullP F hF b z)) (intervalSub σ) :=
  congrArg (fun t => pathApp (Homotopy.fiberPath (𝟙 (Cartesian.reindex B σ)) (Term.reindex b σ) t))
    (targetFull_input_reindex F hF b z σ)

theorem partialLift_input_reindex (hL : L.Uniform) :
    partialLift (L.reindex σ) (Term.reindex b σ) (pulled b z σ) =
      (partialLift L b z).reindex (intervalSub σ) := by
  have hu := L.liftPath_uniform hL (restrictInclusion φ) (localA b z) (Term.reindex b (restrictInclusion φ))
    (localP b z) (restrictSubstitution φ σ)
  apply PartialSection.ext
  intro x hx
  exact congrArg (fun t => t.val ((restrictedInterval (φ.reindex σ)).mapElements.obj
    ((restrictContext ((φ.reindex σ).reindex (projection (interval Δ)))).elementsMk x.obj ⟨x.val,hx⟩))) hu

theorem liftFull_input_reindex (hL : L.Uniform) :
    liftFull (L.reindex σ) (F.reindex σ) (hF.reindex _) (Term.reindex b σ) (pulled b z σ) =
      Term.reindex (liftFull L F hF b z) (intervalSub σ) := by
  have hp := partialLift_input_reindex L b z σ hL
  have ht := fullP_input_reindex F hF b z σ
  have hu := hL (projection (interval Γ)) (φ.reindex (projection (interval Γ)))
    (partialLift L b z) (pathApp (fullP F hF b z)) (partialLift_map L F hF b z) (intervalSub σ)
  refine Eq.trans ?_ hu
  dsimp only [liftFull, MapLifting.reindex]
  congr 1

theorem finalA_input_reindex (hL : L.Uniform) :
    finalA (L.reindex σ) (F.reindex σ) (hF.reindex _) (Term.reindex b σ) (pulled b z σ) =
      Term.reindex (finalA L F hF b z) σ :=
  congrArg (fun t => Term.reindex t (endpointSub Δ false)) (liftFull_input_reindex L F hF b z σ hL)

theorem extend_input_reindex (hL : L.Uniform) :
    Term.map (Homotopy.fiberReindexIso f b σ).hom (Term.reindex (extend L F hF b z) σ) =
      extend (L.reindex σ) (F.reindex σ) (hF.reindex _) (Term.reindex b σ) (pulled b z σ) := by
  refine (congrArg (Term.map (Homotopy.fiberReindexIso f b σ).hom)
    (Homotopy.fiberIntroOver_reindex f b (𝟙 Γ) σ (finalA L F hF b z) (finalP L F hF b z))).trans ?_
  refine (Homotopy.fiberReindexIso_introOver f b σ _ _).trans ?_
  exact Homotopy.fiberIntroOver_congr (Functor.whiskerLeft σ.mapElements f) (Term.reindex b σ) (𝟙 Δ)
    (Term.reindex (finalA L F hF b z) σ)
    (finalA (L.reindex σ) (F.reindex σ) (hF.reindex _) (Term.reindex b σ) (pulled b z σ))
    (homogeneousReindex (finalP L F hF b z) σ)
    (finalP (L.reindex σ) (F.reindex σ) (hF.reindex _) (Term.reindex b σ) (pulled b z σ))
    (finalA_input_reindex L F hF b z σ hL).symm
    (heq_of_eq (fullP_input_reindex F hF b z σ).symm)

end MapLifting.FiberExtension
end SquareKit.Cubical.Cartesian
