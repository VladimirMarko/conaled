import Examples.CubicalFrozenHigherObservation

/-! An assignment through both original substitutions retains the higher
identity and the dependent q/u tail in their actual final display. -/
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
namespace Examples.CubicalSharedAssignment
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open SquareKit.Cubical.CategoryCocycles
open Examples.CubicalCocycleAssignment Examples.FrozenMemoStages

abbrev display := (tauData cocycleModel cocycleBase cocycleRootedFamily).display

abbrev s0 := (CM.lift twoPoints.family (duplicate cocycleModel cocycleBase cocycleRootedFamily)).down
abbrev t0 := (CM.sectionSub (CM.subTy twoPoints.family (duplicate cocycleModel cocycleBase cocycleRootedFamily))
   (deltaX cocycleModel cocycleBase cocycleRootedFamily)).down
abbrev baseMap := t0 ≫ s0
abbrev pFamily := (points.path.reindex s0).reindex t0

theorem p_at_assignment : reindex pFamily.family assignX = FirstIdentityFamily terminal.{0} := by
  exact normalizedIdentity_reindex points.family.family points.x.down points.y.down (assignX ≫ baseMap)

def assignedP : Term (reindex pFamily.family assignX) :=
 (normalizedIdentityRefl (zeroTerm terminal)).convert p_at_assignment.symm

def assignP : terminal.{0} ⟶ total pFamily.family := pair assignX assignedP
abbrev s1 := liftSub points.path.family s0
abbrev t1 := liftSub (reindex points.path.family s0) t0
abbrev pMap := t1 ≫ s1
abbrev ppFamily := (onePath.path.reindex s1).reindex t1

theorem pp_at_assignment : reindex ppFamily.family assignP = FirstIdentityFamily terminal.{0} := by
 exact normalizedIdentity_reindex onePath.family.family onePath.x.down onePath.y.down (assignP ≫ pMap)

def assignedPP : Term (reindex ppFamily.family assignP) :=
 (normalizedIdentityRefl (zeroTerm terminal)).convert pp_at_assignment.symm

def assignPP : terminal.{0} ⟶ total ppFamily.family := pair assignP assignedPP
abbrev s2 := liftSub onePath.path.family s1
abbrev t2 := liftSub (reindex onePath.path.family s1) t1
abbrev ppMap := t2 ≫ s2
abbrev hFamily := (parallelPoints.identity.reindex s2).reindex t2

theorem prefix_eq : assignPP ≫ ppMap = Examples.CubicalCocycleAssignment.assignParallel := rfl

theorem h_at_assignment : reindex hFamily.family assignPP = SecondIdentityFamily terminal.{0} :=
  (congrArg (reindex parallelPoints.identity.family) prefix_eq).trans homotopy_at_assignment

def assignedH : Term (reindex hFamily.family assignPP) :=
 (secondIdentity terminal).convert h_at_assignment.symm

def assignH : terminal.{0} ⟶ total hFamily.family := pair assignPP assignedH
abbrev s3 := liftSub parallelPoints.identity.family s2
abbrev t3 := liftSub (reindex parallelPoints.identity.family s2) t2
abbrev hMap := t3 ≫ s3
abbrev qFamily := ((Examples.FrozenMemoStages.qFamily CM cocycleBase cocycleRootedFamily).reindex s3).reindex t3

theorem pair_heq {Γ Δ : Context.{0}} {A : Family Γ} {σ τ : Δ ⟶ Γ}
 (h : σ = τ) {a : Term (reindex A σ)} {b : Term (reindex A τ)} (hv : HEq a b) :
 pair σ a = pair τ b := by cases h; cases hv; rfl

theorem pair_lift {Γ Δ Θ : Context.{0}} (A : Family Γ) (σ : Δ ⟶ Γ)
 (τ : Θ ⟶ Δ) (t : Term (reindex (reindex A σ) τ)) :
 pair τ t ≫ liftSub A σ = pair (A := A) (τ ≫ σ) t := rfl

theorem h_prefix_eq : assignH ≫ hMap = assignHomotopy :=
 (pair_lift parallelPoints.identity.family ppMap assignPP assignedH).trans
 (pair_heq (A := parallelPoints.identity.family) (a := assignedH) (b := assignedHomotopy) prefix_eq ((Term.convert_heq h_at_assignment.symm (secondIdentity terminal)).trans
    (Term.convert_heq homotopy_at_assignment.symm (secondIdentity terminal)).symm))

theorem q_at_assignment : reindex qFamily.family assignH = FirstIdentityFamily terminal.{0} :=
 (congrArg (reindex (Examples.FrozenMemoStages.qFamily CM cocycleBase cocycleRootedFamily).family) h_prefix_eq).trans
 Examples.CubicalCocycleAssignment.q_at_assignment

def assignedQ : Term (reindex qFamily.family assignH) :=
 (normalizedIdentityRefl (zeroTerm terminal)).convert q_at_assignment.symm

def assignQ : terminal.{0} ⟶ total qFamily.family := pair assignH assignedQ
abbrev s4 := liftSub (Examples.FrozenMemoStages.qFamily CM cocycleBase cocycleRootedFamily).family s3
abbrev t4 := liftSub (reindex (Examples.FrozenMemoStages.qFamily CM cocycleBase cocycleRootedFamily).family s3) t3
abbrev qMap := t4 ≫ s4
abbrev uFamily := ((Examples.FrozenMemoStages.uFamily CM cocycleBase cocycleRootedFamily).reindex s4).reindex t4

theorem q_prefix_eq : assignQ ≫ qMap = Examples.CubicalCocycleAssignment.assignQ :=
 (pair_lift (Examples.FrozenMemoStages.qFamily CM cocycleBase cocycleRootedFamily).family hMap assignH assignedQ).trans
 (pair_heq (A := (Examples.FrozenMemoStages.qFamily CM cocycleBase cocycleRootedFamily).family)
 (a := assignedQ) (b := Examples.CubicalCocycleAssignment.assignedQ) h_prefix_eq
 ((Term.convert_heq q_at_assignment.symm _).trans
 (Term.convert_heq Examples.CubicalCocycleAssignment.q_at_assignment.symm _).symm))

theorem u_at_assignment : reindex uFamily.family assignQ = FirstIdentityFamily terminal.{0} :=
 (congrArg (reindex (Examples.FrozenMemoStages.uFamily CM cocycleBase cocycleRootedFamily).family) q_prefix_eq).trans
 Examples.CubicalCocycleAssignment.u_at_assignment

def assignedU : Term (reindex uFamily.family assignQ) :=
 (normalizedIdentityRefl (zeroTerm terminal)).convert u_at_assignment.symm

set_option maxHeartbeats 4000000 in
def assignFinal : terminal.{0} ⟶ display.total := pair assignQ assignedU

set_option maxHeartbeats 4000000 in
theorem retainedTauHomotopy :
 HEq ((tauHomotopy cocycleModel cocycleBase cocycleRootedFamily).value.down.reindex assignFinal)
 (secondIdentity terminal.{0}) :=
 Term.convert_heq h_at_assignment.symm (secondIdentity terminal)

/-- Normalize only the proved family equality; retain the interpreted selected value. -/
def normalizedTauHomotopy : Term (SecondIdentityFamily terminal.{0}) :=
 cast (type_eq_of_heq retainedTauHomotopy)
  ((tauHomotopy cocycleModel cocycleBase cocycleRootedFamily).value.down.reindex assignFinal)

theorem normalizedTauHomotopy_eq : normalizedTauHomotopy = secondIdentity terminal.{0} :=
 eq_of_heq ((cast_heq _ _).trans retainedTauHomotopy)

theorem tauObservation_one : secondObservation normalizedTauHomotopy = 1 :=
 (congrArg secondObservation normalizedTauHomotopy_eq).trans secondObservation_selected

theorem tauObservation_no_erasure : normalizedTauHomotopy ≠ secondZero terminal.{0} := by
 intro h
 have e := (congrArg secondObservation h).trans secondObservation_zero
 exact Int.one_ne_zero (tauObservation_one.symm.trans e)

/-- The later dependent tail retains the same rooted-family section. -/
theorem retainedU : HEq assignedU Examples.CubicalCocycleAssignment.assignedU :=
 (Term.convert_heq u_at_assignment.symm (normalizedIdentityRefl (zeroTerm terminal))).trans
 (Term.convert_heq Examples.CubicalCocycleAssignment.u_at_assignment.symm
   (normalizedIdentityRefl (zeroTerm terminal))).symm

example : secondObservation normalizedTauHomotopy = 1 ∧
 secondObservation (secondZero terminal.{0}) = 0 :=
 ⟨tauObservation_one, secondObservation_zero⟩

end Examples.CubicalSharedAssignment
