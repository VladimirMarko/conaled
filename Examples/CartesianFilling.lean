import SquareKit.Internal.Cubical.CartesianSelectedComparison
import Examples.FiniteUniverseLoops
import Examples.CartesianWitnessPreservation

/-! Diagonal and endpoint-union tubes, including variable duplication. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CartesianFilling
open CategoryTheory SquareKit.Cubical.Cartesian

abbrev diagonal : Face 2 := .eq (.var 0) (.var 1)
abbrev boundary : Face 1 := .join (.eq (.var 0) (.endpoint false))
  (.eq (.var 0) (.endpoint true))

theorem diagonal_duplicate : (diagonal.subst (fun _ => Dim.var (0 : Fin 1))).Holds := rfl

theorem diagonal_generic : ¬ diagonal.Holds := by
  intro h
  have h01 : (0 : Fin 2) = 1 := Dim.var.inj h
  exact Fin.zero_ne_one h01

theorem boundary_generic : ¬ boundary.Holds := by
  intro h
  cases h with
  | inl h => cases h
  | inr h => cases h

theorem boundary_vertices (b : Bool) : (boundary.subst (fun _ => (Dim.endpoint b : Dim 0))).Holds := by
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The tube need not contain the generic cube even when it contains every vertex. -/
theorem boundary_all_vertices_not_generic :
    (∀ b : Bool, (boundary.subst (fun _ => (Dim.endpoint b : Dim 0))).Holds) ∧ ¬ boundary.Holds :=
  ⟨boundary_vertices, boundary_generic⟩

def first : Term (interval (representable ⟨2⟩)) where
  val x := ⟨fun _ => x.val.down 0⟩
  property f := by
    apply ULift.ext
    funext i
    exact congrArg (fun h => h.down 0) f.map_val

def second : Term (interval (representable ⟨2⟩)) where
  val x := ⟨fun _ => x.val.down 1⟩
  property f := by
    apply ULift.ext
    funext i
    exact congrArg (fun h => h.down 1) f.map_val

def value : Term (constantFamily (representable ⟨2⟩) Bool) where
  val _ := true
  property _ := rfl

def box : OpenBox (constantFamily (total (interval (representable ⟨2⟩))) Bool)
    diagonal.cofibration.toSubcontext first where
  tube := { val := fun _ _ => true, natural := fun _ _ => rfl }
  base := value
  boundary _ _ := rfl

theorem independent_fill : box.presentedFill (Iso.refl _) =
    Term.reindex value (projection (interval (representable ⟨2⟩))) := rfl

theorem variable_source_tube : box.Fills (box.presentedFill (Iso.refl _)) :=
  box.presentedFill_fills (Iso.refl _)

theorem variable_source_unique (t : Term (constantFamily
    (total (interval (representable ⟨2⟩))) Bool)) (h : Term.reindex t (graph first) = value) :
    t = box.presentedFill (Iso.refl _) := box.presentedFill_unique (Iso.refl _) t h

abbrev finiteBool : FiniteCode := ⟨Bool, inferInstance⟩
def boolNegation : Bool ≃ Bool := ⟨Bool.not, Bool.not, Bool.not_not, Bool.not_not⟩

theorem selected_bool_separation :
    TargetTransport.action finiteBool boolNegation false ≠
      TargetTransport.action finiteBool (Equiv.refl Bool) false := by
  rw [TargetTransport.action_eq, TargetTransport.action_eq]
  decide

example : TargetTransport.action finiteBool boolNegation
    (TargetTransport.action finiteBool boolNegation false) = false := by
  rw [TargetTransport.action_eq, TargetTransport.action_eq]
  rfl

end Examples.CartesianFilling

namespace Examples.CartesianSelectedRecomputation
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open SmallUniverse SmallUniverse.NativeUnivalence
open Examples.CompositionalUnivalence Examples.FiniteUniverseLoops

abbrev finiteThree : Cartesian.FiniteCode := ⟨Fin 3, inferInstance⟩
abbrev sourceCode := Examples.CompositionalUnivalence.code (Fin 3)
noncomputable abbrev sourcePresentation := (Examples.CubicalGlue.constantLocal terminal (Fin 3)).decodeCodeIso

theorem selected_swaps_noncommute :
    Cartesian.TargetTransport.action finiteThree (swap01.trans swap12) 0 ≠
      Cartesian.TargetTransport.action finiteThree (swap12.trans swap01) 0 := by
  rw [Cartesian.TargetTransport.action_eq, Cartesian.TargetTransport.action_eq]
  decide

noncomputable def recomputedLoop : Term (loops (Fin 3)) :=
  Cartesian.RealizedNerve.whiskeredLoop finiteThree sourceCode sourcePresentation (swap01.trans swap12)

noncomputable def recomputedMiddle : Term (homogeneousPath (loops (Fin 3)) recomputedLoop recomputedLoop) :=
  Cartesian.RealizedNerve.whiskeredComposition finiteThree sourceCode sourcePresentation swap01 swap12

theorem recomputedLoop_permutation : loopPermutation recomputedLoop = swap01.trans swap12 := by
  apply Equiv.ext
  intro s
  rw [loopPermutation_apply (S := Fin 3)]
  have h := Cartesian.RealizedNerve.whiskeredTransport finiteThree sourceCode sourcePresentation
    (swap01.trans swap12) s
  change Term.map (pathToMap recomputedLoop) (nativeInput s) = nativeInput ((swap01.trans swap12) s) at h
  exact congrArg (fun t => t.val DiscreteEquivalences.point)
    ((congrArg observe h).trans (observe_input (S := Fin 3) _))

noncomputable def frozenStart : Term (loops (Fin 3)) :=
  ua sourceCode sourceCode (nativeMap swap01 ≫ nativeMap swap12)
    (compositeEquivalence sourceCode sourceCode sourceCode
      (nativeMap swap01) (nativeEquivalence swap01) (nativeMap swap12) (nativeEquivalence swap12))

noncomputable abbrev frozenFinish := forwardLoop

theorem native_ua_permutation
    (f : liftedDecode sourceCode ⟶ liftedDecode sourceCode) (E : HomotopyEquivalence f)
    (e : Fin 3 ≃ Fin 3) (hf : ∀ s, Term.map f (nativeInput s) = nativeInput (e s)) :
    loopPermutation (ua sourceCode sourceCode f E) = e := by
  apply Equiv.ext
  intro s
  rw [loopPermutation_apply (S := Fin 3)]
  have h := observe_path (S := Fin 3) (uaComparison sourceCode sourceCode f E (nativeInput s))
  exact congrArg (fun t => t.val DiscreteEquivalences.point)
    (h.symm.trans ((congrArg observe (hf s)).trans (observe_input (S := Fin 3) _)))

theorem frozenStart_permutation : loopPermutation frozenStart = swap01.trans swap12 :=
  native_ua_permutation _ _ _ (fun s =>
    (congrArg (Term.map (nativeMap swap12)) (nativeInput_action swap01 s)).trans
      (nativeInput_action swap12 (swap01 s)))

@[irreducible] noncomputable def startAlignment : Term (homogeneousPath (loops (Fin 3)) frozenStart recomputedLoop) :=
  samePermutationPath frozenStart recomputedLoop
    (frozenStart_permutation.trans recomputedLoop_permutation.symm)

@[irreducible] noncomputable def finishAlignment : Term (homogeneousPath (loops (Fin 3)) frozenFinish recomputedLoop) :=
  samePermutationPath frozenFinish recomputedLoop
    ((loopPermutation_concat swap01 swap12).trans recomputedLoop_permutation.symm)

@[irreducible] noncomputable def recomputedSquare : Term (homogeneousPath (loops (Fin 3)) frozenStart frozenFinish) :=
  homogeneousConcat (pathsFilling sourceCode sourceCode) (pathsFilling_lawful _ _)
    (homogeneousConcat (pathsFilling sourceCode sourceCode) (pathsFilling_lawful _ _)
      startAlignment recomputedMiddle) (homogeneousReverse finishAlignment)

@[irreducible] noncomputable def relativeThreePath :
    Term (homogeneousPath (homogeneousPath (loops (Fin 3)) frozenStart frozenFinish)
      swapComposition recomputedSquare) :=
  Cartesian.RealizedNerve.relativeComparison finiteThree sourceCode sourcePresentation
    swapComposition recomputedSquare

theorem relativeThreePath_zero :
    (pathApp relativeThreePath).reindex (endpointSub _ false) = swapComposition :=
  pathApp_zero relativeThreePath

theorem relativeThreePath_one :
    (pathApp relativeThreePath).reindex (endpointSub _ true) = recomputedSquare :=
  pathApp_one relativeThreePath

noncomputable def relativeBody : Term (reindex (loops (Fin 3))
    (projection (interval (total (interval (raisedContext terminal)))) ≫
      projection (interval (raisedContext terminal)))) :=
  RelativeComparison.squareBody (Γ := raisedContext terminal) (X := loops (Fin 3)) (p := frozenStart) (q := frozenFinish)
    (H := swapComposition) (K := recomputedSquare) relativeThreePath

theorem relativeBody_start :
    relativeBody.reindex (endpointSub (total (interval (raisedContext terminal))) false) =
      frozenStart.reindex (projection (interval (raisedContext terminal))) :=
  RelativeComparison.squareBody_start (Γ := raisedContext terminal) (X := loops (Fin 3)) (p := frozenStart) (q := frozenFinish)
    (H := swapComposition) (K := recomputedSquare) relativeThreePath

theorem relativeBody_finish :
    relativeBody.reindex (endpointSub (total (interval (raisedContext terminal))) true) =
      frozenFinish.reindex (projection (interval (raisedContext terminal))) :=
  RelativeComparison.squareBody_finish (Γ := raisedContext terminal) (X := loops (Fin 3)) (p := frozenStart) (q := frozenFinish)
    (H := swapComposition) (K := recomputedSquare) relativeThreePath

theorem relativeBody_original :
    relativeBody.reindex (liftSub (interval (total (interval (raisedContext terminal))))
      (endpointSub (raisedContext terminal) false)) = pathApp swapComposition :=
  RelativeComparison.squareBody_zero (Γ := raisedContext terminal) (X := loops (Fin 3)) (p := frozenStart) (q := frozenFinish)
    (H := swapComposition) (K := recomputedSquare) relativeThreePath

theorem relativeBody_recomputed :
    relativeBody.reindex (liftSub (interval (total (interval (raisedContext terminal))))
      (endpointSub (raisedContext terminal) true)) = pathApp recomputedSquare :=
  RelativeComparison.squareBody_one (Γ := raisedContext terminal) (X := loops (Fin 3)) (p := frozenStart) (q := frozenFinish)
    (H := swapComposition) (K := recomputedSquare) relativeThreePath

noncomputable def relativeAt {Δ : Context.{1}} (σ : Δ ⟶ raisedContext terminal) :
    Term (homogeneousPath
      (homogeneousPath (reindex (loops (Fin 3)) σ) (frozenStart.reindex σ) (frozenFinish.reindex σ))
      (homogeneousReindex swapComposition σ) (homogeneousReindex recomputedSquare σ)) :=
  RelativeComparison.squareReindex relativeThreePath σ

theorem relativeAt_comp {Δ Θ : Context.{1}} (σ : Δ ⟶ raisedContext terminal) (τ : Θ ⟶ Δ) :
    RelativeComparison.SquareSubstitutionLaw relativeThreePath σ τ :=
  RelativeComparison.squareSubstitutionLaw relativeThreePath σ τ

theorem relativeAt_id : RelativeComparison.SquareIdentityLaw relativeThreePath :=
  RelativeComparison.squareIdentityLaw relativeThreePath

theorem relativeAt_zero {Δ : Context.{1}} (σ : Δ ⟶ raisedContext terminal) :
    (pathApp (relativeAt σ)).reindex (endpointSub Δ false) =
      homogeneousReindex swapComposition σ := pathApp_zero _

theorem relativeAt_one {Δ : Context.{1}} (σ : Δ ⟶ raisedContext terminal) :
    (pathApp (relativeAt σ)).reindex (endpointSub Δ true) =
      homogeneousReindex recomputedSquare σ := pathApp_one _

example : RelativeComparison.SquareSubstitutionLaw relativeThreePath
    (projection (interval (raisedContext terminal))) (endpointSub (raisedContext terminal) true) :=
  relativeAt_comp _ _

noncomputable def cartesianRelativeThreePath :=
  Cartesian.Term.map (Cartesian.threePathIso (SmallUniverse.family (raisedContext terminal))
    (term sourceCode) (term sourceCode) frozenStart frozenFinish swapComposition recomputedSquare).hom
      (Cartesian.restrictTerm relativeThreePath)

noncomputable def cartesianRelativeAt {Δ : Cartesian.Context.{1}}
    (σ : Δ ⟶ Cartesian.restrict (raisedContext terminal)) :=
  Cartesian.Term.reindex cartesianRelativeThreePath σ

theorem cartesianRelativeAt_comp {Δ Θ : Cartesian.Context.{1}}
    (σ : Δ ⟶ Cartesian.restrict (raisedContext terminal)) (τ : Θ ⟶ Δ) :
    Cartesian.Term.reindex (cartesianRelativeAt σ) τ = cartesianRelativeAt (τ ≫ σ) := rfl

theorem cartesianRelativeAt_id :
    cartesianRelativeAt (𝟙 _) = cartesianRelativeThreePath := rfl

theorem cartesianRelativeThreePath_retains_native :
    Cartesian.Term.map (Cartesian.threePathIso (SmallUniverse.family (raisedContext terminal))
      (term sourceCode) (term sourceCode) frozenStart frozenFinish swapComposition recomputedSquare).inv
      cartesianRelativeThreePath = Cartesian.restrictTerm relativeThreePath := by
  apply Cartesian.Term.ext
  intro x
  exact (Cartesian.threePathIso (SmallUniverse.family (raisedContext terminal))
    (term sourceCode) (term sourceCode) frozenStart frozenFinish swapComposition recomputedSquare).hom_inv_id_app_apply _ _

abbrev twoIntervalProjection :=
  projection (interval (total (interval (raisedContext terminal)))) ≫
    projection (interval (raisedContext terminal))

noncomputable def universeBody := pathApp (Term.map
  (EquivalenceFamilies.homogeneousReindexIso (SmallUniverse.family (raisedContext terminal))
    (term sourceCode) (term sourceCode) twoIntervalProjection).hom relativeBody)

theorem universeBody_zero :
    universeBody.reindex (endpointSub _ false) = (term sourceCode).reindex twoIntervalProjection :=
  pathApp_zero _

theorem universeBody_one :
    universeBody.reindex (endpointSub _ true) = (term sourceCode).reindex twoIntervalProjection :=
  pathApp_one _

end Examples.CartesianSelectedRecomputation
