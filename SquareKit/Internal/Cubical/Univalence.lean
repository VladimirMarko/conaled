import SquareKit.Internal.Cubical.UniverseComposition
import SquareKit.Internal.Cubical.DisjointEquivalences

/-! Exact endpoint code lines for the univalence construction. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u
namespace SmallUniverse

/-- Raising a context commutes with adjoining the interval. -/
def raisedIntervalIso (Γ : Context.{u}) :
    raisedContext (total (interval Γ)) ≅ total (interval (raisedContext Γ)) where
  hom :=
    { app := fun _ => TypeCat.ofHom (fun x => ⟨⟨x.down.1⟩,⟨x.down.2.down⟩⟩)
      naturality := fun _ _ _ => rfl }
  inv :=
    { app := fun _ => TypeCat.ofHom (fun x => ⟨⟨x.1.down,⟨x.2.down⟩⟩⟩)
      naturality := fun _ _ _ => rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

theorem raisedInterval_endpoint (Γ : Context.{u}) (ε : Bool) :
    endpointSub (raisedContext Γ) ε ≫ (raisedIntervalIso Γ).inv =
      raisedSub (endpointSub Γ ε) := rfl

/-- A small-context code line yields a native universe path over the raised
context. This adapter does not assume that the line was constant. -/
def pathOfSmallCode {Γ : Context.{u}}
    (a b : raisedContext Γ ⟶ smallFamilyCodes.{u})
    (p : raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u})
    (h₀ : raisedSub (endpointSub Γ false) ≫ p = a)
    (h₁ : raisedSub (endpointSub Γ true) ≫ p = b) :
    Term (homogeneousPath (family (raisedContext Γ)) (term a) (term b)) :=
  pathOfCode a b ((raisedIntervalIso Γ).inv ≫ p) h₀ h₁

end SmallUniverse
namespace Univalence
variable {Γ : Context.{u}}
  (a b : raisedContext Γ ⟶ smallFamilyCodes.{u})

abbrev face : Cofibration (total (interval Γ)) :=
  (intervalFace Γ false).join (intervalFace Γ true)

abbrev ambient : raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u} :=
  raisedSub (projection (interval Γ)) ≫ b

theorem boundary_left :
    reindex (decode (CodeSystem.boundary a b))
      (CodeSystem.includeLeft (intervalFace Γ false) (intervalFace Γ true)) =
    reindex (decode a) (restrictInclusion (intervalFace Γ false) ≫ projection (interval Γ)) :=
  congrArg decode (CodeSystem.glue_left _ _ (CodeSystem.endpoints_compatible a b))

theorem boundary_right :
    reindex (decode (CodeSystem.boundary a b))
      (CodeSystem.includeRight (intervalFace Γ false) (intervalFace Γ true)) =
    reindex (decode b) (restrictInclusion (intervalFace Γ true) ≫ projection (interval Γ)) :=
  congrArg decode (CodeSystem.glue_right _ _ (CodeSystem.endpoints_compatible a b))

def boundaryLeft (f : decode a ⟶ decode b) :
    reindex (decode (CodeSystem.boundary a b))
      (CodeSystem.includeLeft (intervalFace Γ false) (intervalFace Γ true)) ⟶
    reindex (reindex (decode (ambient b)) (restrictInclusion face))
      (CodeSystem.includeLeft (intervalFace Γ false) (intervalFace Γ true)) :=
  eqToHom (boundary_left a b) ≫
    Functor.whiskerLeft (restrictInclusion (intervalFace Γ false) ≫ projection (interval Γ)).mapElements f

def boundaryRight :
    reindex (decode (CodeSystem.boundary a b))
      (CodeSystem.includeRight (intervalFace Γ false) (intervalFace Γ true)) ⟶
    reindex (reindex (decode (ambient b)) (restrictInclusion face))
      (CodeSystem.includeRight (intervalFace Γ false) (intervalFace Γ true)) :=
  eqToHom (boundary_right a b)

private def castSource {Ξ : Context.{u}} {A B C : Family Ξ}
    (h : A = B) (f : B ⟶ C) (E : HomotopyEquivalence f) :
    HomotopyEquivalence (eqToHom h ≫ f) := by
  subst B
  exact E

def boundaryLeftEquivalence (f : decode a ⟶ decode b) (E : HomotopyEquivalence f) :
    HomotopyEquivalence (boundaryLeft a b f) :=
  castSource (boundary_left a b) _
    (E.reindex (restrictInclusion (intervalFace Γ false) ≫ projection (interval Γ)))

def boundaryRightEquivalence : HomotopyEquivalence (boundaryRight a b) :=
  HomotopyEquivalence.ofIso (eqToIso (boundary_right a b))

variable (e : decode (CodeSystem.boundary a b) ⟶
  reindex (decode (ambient b)) (restrictInclusion (face (Γ := Γ))))
  (E : HomotopyEquivalence e)

/-- Glue extends the endpoint system once its actual equivalence into the
ambient family has been constructed. -/
noncomputable def boundaryLine : raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u} :=
  Glue.code face (ambient b) (CodeSystem.boundary a b) e E

theorem boundaryLine_full :
    raisedSub (restrictInclusion face) ≫ boundaryLine a b e E = CodeSystem.boundary a b :=
  Glue.code_full _ _ _ _ _

theorem boundaryLine_zero :
    raisedSub (endpointSub Γ false) ≫ boundaryLine a b e E = a :=
  (congrArg (fun c => raisedSub (CodeSystem.boundaryZero Γ) ≫ c)
    (boundaryLine_full a b e E)).trans (CodeSystem.boundary_zero a b)

theorem boundaryLine_one :
    raisedSub (endpointSub Γ true) ≫ boundaryLine a b e E = b :=
  (congrArg (fun c => raisedSub (CodeSystem.boundaryOne Γ) ≫ c)
    (boundaryLine_full a b e E)).trans (CodeSystem.boundary_one a b)

noncomputable def boundaryPath :
    Term (homogeneousPath (SmallUniverse.family (raisedContext Γ))
      (SmallUniverse.term a) (SmallUniverse.term b)) :=
  SmallUniverse.pathOfSmallCode a b (boundaryLine a b e E)
    (boundaryLine_zero a b e E) (boundaryLine_one a b e E)


/-- The endpoint system uses the given map at zero and identity at one. -/
def boundaryMap (f : decode a ⟶ decode b) : decode (CodeSystem.boundary a b) ⟶
    reindex (decode (ambient b)) (restrictInclusion face) :=
  CodeSystem.Maps.glue (boundaryLeft a b f) (boundaryRight a b)
    (CodeSystem.Maps.disjointCompatible _ _ intervalFace_disjoint)

private theorem reindex_eqToHom {Ξ Ω : Context.{u}} {A B : Family Ξ}
    (h : A = B) (σ : Ω ⟶ Ξ) :
    Functor.whiskerLeft σ.mapElements (eqToHom h) =
      eqToHom (congrArg (fun X => reindex X σ) h) := by
  cases h
  rfl

theorem boundaryMap_zero (f : decode a ⟶ decode b) :
    Functor.whiskerLeft (CodeSystem.boundaryZero Γ).mapElements (boundaryMap a b f) =
      eqToHom (congrArg decode (CodeSystem.boundary_zero a b)) ≫ f := by
  have h := congrArg (Functor.whiskerLeft (CodeSystem.endpointFace Γ false).mapElements)
    (CodeSystem.Maps.glue_left (boundaryLeft a b f) (boundaryRight a b)
      (CodeSystem.Maps.disjointCompatible _ _ intervalFace_disjoint))
  refine h.trans ?_
  change Functor.whiskerLeft (CodeSystem.endpointFace Γ false).mapElements
    (eqToHom (boundary_left a b)) ≫ f = _
  rw [reindex_eqToHom]
  rfl

theorem boundaryMap_one (f : decode a ⟶ decode b) :
    Functor.whiskerLeft (CodeSystem.boundaryOne Γ).mapElements (boundaryMap a b f) =
      eqToHom (congrArg decode (CodeSystem.boundary_one a b)) := by
  have h := congrArg (Functor.whiskerLeft (CodeSystem.endpointFace Γ true).mapElements)
    (CodeSystem.Maps.glue_right (boundaryLeft a b f) (boundaryRight a b)
      (CodeSystem.Maps.disjointCompatible _ _ intervalFace_disjoint))
  exact h.trans (reindex_eqToHom (boundary_right a b) (CodeSystem.endpointFace Γ true))

noncomputable def boundaryEquivalence (f : decode a ⟶ decode b)
    (H : HomotopyEquivalence f) : HomotopyEquivalence (boundaryMap a b f) :=
  CodeSystem.Maps.disjointEquivalence _ _ intervalFace_disjoint
    (boundaryLeftEquivalence a b f H) (boundaryRightEquivalence a b)

/-- A genuine homotopy equivalence supplies a line with the exact original
endpoint codes, retaining the selected filling data of each endpoint. -/
noncomputable def uaCode (f : decode a ⟶ decode b) (H : HomotopyEquivalence f) :
    raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u} :=
  boundaryLine a b (boundaryMap a b f) (boundaryEquivalence a b f H)

theorem uaCode_zero (f : decode a ⟶ decode b) (H : HomotopyEquivalence f) :
    raisedSub (endpointSub Γ false) ≫ uaCode a b f H = a :=
  boundaryLine_zero _ _ _ _

theorem uaCode_one (f : decode a ⟶ decode b) (H : HomotopyEquivalence f) :
    raisedSub (endpointSub Γ true) ≫ uaCode a b f H = b :=
  boundaryLine_one _ _ _ _

noncomputable def ua (f : decode a ⟶ decode b) (H : HomotopyEquivalence f) :
    Term (homogeneousPath (SmallUniverse.family (raisedContext Γ))
      (SmallUniverse.term a) (SmallUniverse.term b)) :=
  SmallUniverse.pathOfSmallCode a b (uaCode a b f H)
    (uaCode_zero a b f H) (uaCode_one a b f H)

end Univalence
end SquareKit.Cubical.Presheaf
