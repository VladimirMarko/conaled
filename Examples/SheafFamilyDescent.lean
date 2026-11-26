import SquareKit.SheafFamilyDescent
import SquareKit.SmoothClutchingScaling
import Examples.ActionQuotientStack
import Examples.SheafFamilyCover

/-! Family descent over the two charts of the nontrivial quarter-turn torsor. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace Examples.SheafFamilyDescent
open CategoryTheory Limits Opposite SquareKit
open SmoothTorsors Orbifolds.QuarterTurn
open SquareKit.SheafFamilyDescent

abbrev charts := SmoothClutching.Represented.chart

theorem charts_joint : SheafFamilyCover.JointlyLocallySurjective charts :=
  SmoothClutching.Represented.atlas.covering

/-- Each chart trivializes the torsor, so a surjective chart would contradict
its independently proved global nontriviality. -/
theorem chart_not_surjective (b : Bool) :
    ¬ Presheaf.IsLocallySurjective SmoothOpenSite.topology (charts b).hom := by
  intro h
  have : Mono (charts b) := by
    cases b
    · exact SmoothClutching.left_mono
    · exact SmoothClutching.right_mono
  have : Epi (charts b) := Sheaf.epi_of_isLocallySurjective _
  have := isIso_of_mono_of_epi (charts b)
  apply nontrivialTorsor_not_trivializable
  have t := (SmoothClutching.Represented.localTrivialization C4 quarterTurn b).reindex
    (inv (charts b))
  change SheafTorsor.Arrow (SheafTorsor.trivial group SmoothClutching.base)
    (SheafTorsor.reindex (SheafTorsor.reindex nontrivialTorsor (charts b)) (inv (charts b))) at t
  rw [SheafTorsor.reindex_comp, IsIso.inv_hom_id, SheafTorsor.reindex_id] at t
  exact ⟨t⟩

example : Sieve.ofArrows (fun _ : Bool => SmoothClutching.lineSheaf) charts ∈
    SquareKit.SheafFamilyCover.topology SmoothClutching.base :=
  SheafFamilyCover.covering charts_joint

/-- This family is a genuine two-chart cover with neither chart covering alone. -/
theorem charts_proper :
    Sieve.ofArrows (fun _ : Bool => SmoothClutching.lineSheaf) charts ≠ ⊤ := by
  intro h
  have hi : Sieve.ofArrows (fun _ : Bool => SmoothClutching.lineSheaf) charts
      (𝟙 SmoothClutching.base) := by rw [h]; trivial
  obtain ⟨b,k,hk⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hi
  exact chart_not_surjective b (Presheaf.isLocallySurjective_of_isLocallySurjective_fac
    SmoothOpenSite.topology (congrArg (fun f => f.hom) hk.symm))

/-- The family topology contains genuinely new covers: no locally surjective
singleton lies in the sieve of the two disjoint points. -/
theorem inclusion_not_singleton_cover :
    Sieve.ofArrows (fun _ : Bool => SheafFamilyCover.constant PUnit)
      SheafFamilyCover.inclusion ∉
        SquareKit.SheafCover.topology (SheafFamilyCover.constant Bool) := by
  rintro ⟨Y,f,hf,hR⟩
  obtain ⟨b,k,hk⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hR
  exact SheafFamilyCover.member_not_surjective b
    (Presheaf.isLocallySurjective_of_isLocallySurjective_fac
      SheafFamilyCover.topology (congrArg (fun t => t.hom) hk.symm))

example : Sieve.ofArrows (fun _ : Bool => SheafFamilyCover.constant PUnit)
    SheafFamilyCover.inclusion ∈
      SquareKit.SheafFamilyCover.topology (SheafFamilyCover.constant Bool) :=
  SquareKit.SheafFamilyCover.covering SheafFamilyCover.inclusion_jointlyLocallySurjective

def baseLoop (g : C4) :
    SheafTorsor.trivial group SmoothClutching.base ⟶
      SheafTorsor.trivial group SmoothClutching.base :=
  SheafTorsor.regularArrow (SmoothOpenSite.constantSection SmoothClutching.base g)

theorem baseLoop_injective : Function.Injective baseLoop := by
  intro g h he
  have hs := SheafTorsor.regularArrow_injective he
  let z : EuclideanOpen.Points SmoothClutching.line := ⟨fun _ => 0, one_ne_zero⟩
  have ht := congrArg (fun f => SmoothClutching.labelAt C4 (SmoothClutching.left ≫ f) z) hs
  change SmoothClutching.labelAt C4 (SmoothOpenSite.constantSection _ g) z =
    SmoothClutching.labelAt C4 (SmoothOpenSite.constantSection _ h) z at ht
  simpa only [SmoothClutching.labelAt_constant] using ht

/-- An ineffective action on a genuine sheaf target retains the C4 arrows. -/
def ineffectiveBase : SheafActionQuotient.Action group SmoothClutching.base where
  act _ _ x := x
  one_act _ _ := rfl
  mul_act _ _ _ _ := rfl
  natural _ _ _ := rfl

abbrev regularBase := SheafActionQuotient.chart ineffectiveBase (𝟙 SmoothClutching.base)

def baseStabilizer (g : C4) : regularBase ⟶ regularBase where
  torsorArrow := baseLoop g
  preserves _ _ := rfl

theorem baseStabilizer_quarterTurn_ne_one : baseStabilizer quarterTurn ≠ baseStabilizer 1 := by
  intro h
  exact quarterTurn_ne_one (baseLoop_injective (congrArg SheafActionQuotient.Arrow.torsorArrow h))

abbrev scale2 := SmoothClutching.baseScale 2 (by norm_num)
abbrev scale3 := SmoothClutching.baseScale 3 (by norm_num)

example : scale2 ≠ 𝟙 SmoothClutching.base :=
  SmoothClutching.baseScale_ne_identity 2 (by norm_num) (by norm_num)

example : scale3 ≠ 𝟙 SmoothClutching.base :=
  SmoothClutching.baseScale_ne_identity 3 (by norm_num) (by norm_num)

abbrev swappedCharts := fun b => charts (!b)

theorem swappedCharts_joint : SquareKit.SheafFamilyCover.JointlyLocallySurjective swappedCharts := by
  apply SquareKit.SheafFamilyCover.of_refinement _ charts Bool.not (fun _ => 𝟙 _) _ charts_joint
  intro b
  cases b <;> simp [swappedCharts]

/-- A nontrivial group on the one-stage bottom-topology site. -/
def finiteGroup : Sheaf SheafFamilyCover.topology GrpCat :=
  ⟨(Functor.const SheafFamilyCover.Siteᵒᵖ).obj (GrpCat.of C4), Presheaf.isSheaf_bot _⟩

def finiteAction : SquareKit.SheafActionQuotient.Action finiteGroup
    (SheafFamilyCover.constant Bool) where
  act _ _ x := x
  one_act _ _ := rfl
  mul_act _ _ _ _ := rfl
  natural _ _ _ := rfl

theorem emptyTargetFamily_jointlyLocallySurjective : SquareKit.SheafFamilyCover.JointlyLocallySurjective
    SheafFamilyCover.emptyTargetFamily := by
  rw [SquareKit.SheafFamilyCover.empty_iff]
  intro U x
  exact x.elim


abbrev torsorE := torsorEquivalence group charts charts_joint
abbrev torsorData := torsorE.functor.obj nontrivialTorsor
abbrev gluedTorsor := torsorE.inverse.obj torsorData

def torsorRecovery : gluedTorsor ≅ nontrivialTorsor := (torsorE.unitIso.app _).symm

theorem glued_not_trivializable :
    ¬ Nonempty (SheafTorsor.Arrow (SheafTorsor.trivial group SmoothClutching.base) gluedTorsor) := by
  rintro ⟨h⟩
  exact nontrivialTorsor_not_trivializable ⟨h.comp torsorRecovery.hom⟩

example : torsorE.functor.obj gluedTorsor ≅ torsorData := torsorE.counitIso.app _

/-- All compatible maps survive the family recovery round trip. -/
example {P Q : SheafTorsor.Torsor group SmoothClutching.base} (h : P ⟶ Q) :
    torsorE.inverse.map (torsorE.functor.map h) ≫ (torsorE.unitIso.app Q).inv =
      (torsorE.unitIso.app P).inv ≫ h := torsorE.unitIso.inv.naturality h

theorem descended_loops_distinct :
    torsorE.inverse.map (torsorE.functor.map (baseLoop quarterTurn)) ≠
      torsorE.inverse.map (torsorE.functor.map (baseLoop 1)) := by
  intro h
  exact quarterTurn_ne_one (baseLoop_injective
    (torsorE.functor.map_injective (torsorE.inverse.map_injective h)))

abbrev quotientE := quotientEquivalence ActionQuotientStack.targetAction charts charts_joint
abbrev quotientData := quotientE.functor.obj ActionQuotientStack.genuine
abbrev gluedQuotient := quotientE.inverse.obj quotientData

def quotientRecovery : gluedQuotient ≅ ActionQuotientStack.genuine :=
  (quotientE.unitIso.app _).symm

theorem quotient_glued_not_trivializable :
    ¬ Nonempty (SheafTorsor.Arrow (SheafTorsor.trivial group SmoothClutching.base)
      gluedQuotient.torsor) := by
  rintro ⟨h⟩
  exact nontrivialTorsor_not_trivializable ⟨h.comp quotientRecovery.hom.torsorArrow⟩

/-- Recovery retains the section-valued target of the clutching torsor. -/
theorem quotient_recovery_target (x : SmoothClutching.base.obj.Elements)
    (p : gluedQuotient.torsor.family.family.obj x) :
    (quotientRecovery.hom.torsorArrow.iso.hom.app x p).val = gluedQuotient.value x p :=
  quotientRecovery.hom.preserves x p

example : quotientE.functor.obj gluedQuotient ≅ quotientData := quotientE.counitIso.app _

abbrev stabilizerE := quotientEquivalence ineffectiveBase charts charts_joint

theorem descended_stabilizers_distinct :
    stabilizerE.inverse.map (stabilizerE.functor.map (baseStabilizer quarterTurn)) ≠
      stabilizerE.inverse.map (stabilizerE.functor.map (baseStabilizer 1)) := by
  intro h
  exact baseStabilizer_quarterTurn_ne_one
    (stabilizerE.functor.map_injective (stabilizerE.inverse.map_injective h))

example : (SheafTorsor.Stack.pseudofunctor group).IsStack
    (SquareKit.SheafFamilyCover.topology (J := SmoothOpenSite.topology)) := inferInstance

example : (SheafActionQuotient.Stack.pseudofunctor ActionQuotientStack.targetAction).IsStack
    (SquareKit.SheafFamilyCover.topology (J := SmoothOpenSite.topology)) := inferInstance

/-- Empty-family effectiveness uses the exact coverage condition, even with a
nontrivial group and a nonterminal target. -/
example : SheafTorsor.Torsor finiteGroup (SheafFamilyCover.constant Empty) ≌
    (SheafTorsor.Stack.pseudofunctor finiteGroup).DescentData SheafFamilyCover.emptyTargetFamily :=
  torsorEquivalence finiteGroup _ emptyTargetFamily_jointlyLocallySurjective

example : SheafActionQuotient.Object finiteAction (SheafFamilyCover.constant Empty) ≌
    (SheafActionQuotient.Stack.pseudofunctor finiteAction).DescentData
      SheafFamilyCover.emptyTargetFamily := quotientEquivalence finiteAction _ emptyTargetFamily_jointlyLocallySurjective

/-- Without coverage, the empty family loses the previously distinct arrows. -/
example : ¬ ((SheafTorsor.Stack.pseudofunctor group).toDescentData
    TorsorStack.emptyFamily).Faithful := TorsorStack.empty_descent_not_faithful

example : ¬ ((SheafActionQuotient.Stack.pseudofunctor ActionQuotientStack.ineffective).toDescentData
    TorsorStack.emptyFamily).Faithful := ActionQuotientStack.empty_descent_not_faithful


universe u' v'
variable (F : Pseudofunctor
  (LocallyDiscrete (Sheaf SmoothOpenSite.topology Type)ᵒᵖ) Cat.{v',u'})

def scalingPull (r : ℝ) (hr : r ≠ 0) :=
  Pseudofunctor.DescentData.pullFunctor F
    (f := charts) (f' := charts) (α := id)
    (p := SmoothClutching.baseScale r hr)
    (p' := fun _ => EuclideanOpen.embedding.map (SmoothClutching.lineScale r))
    (SmoothClutching.scalingAtlasMap r hr).commutes

/-- The checked recovery comparison applies to a nonidentity map of contexts. -/
def scalingRecovery [(F.toDescentData charts).IsEquivalence] (r : ℝ) (hr : r ≠ 0) :
    scalingPull F r hr ⋙ (F.toDescentData charts).asEquivalence.inverse ≅
      (F.toDescentData charts).asEquivalence.inverse ⋙
        (F.map (SmoothClutching.baseScale r hr).op.toLoc).toFunctor :=
  recoveryNaturality F (f := charts) (g := charts) id _ _ (SmoothClutching.scalingAtlasMap r hr).commutes

/-- Two successive nonidentity substitutions compare the actual recovered objects. -/
def repeatedRecovery [(F.toDescentData charts).IsEquivalence] (D : F.DescentData charts) :
    (F.toDescentData charts).asEquivalence.inverse.obj
      ((scalingPull F 3 (by norm_num)).obj ((scalingPull F 2 (by norm_num)).obj D)) ≅
    (F.map scale3.op.toLoc).toFunctor.obj ((F.map scale2.op.toLoc).toFunctor.obj
      ((F.toDescentData charts).asEquivalence.inverse.obj D)) :=
  (scalingRecovery F 3 (by norm_num)).app _ ≪≫
    (F.map scale3.op.toLoc).toFunctor.mapIso ((scalingRecovery F 2 (by norm_num)).app D)

def swapPull := Pseudofunctor.DescentData.pullFunctor F
  (f := charts) (f' := swappedCharts) (α := Bool.not) (p := 𝟙 SmoothClutching.base)
  (p' := fun _ => 𝟙 _) (by intro b; simp [swappedCharts])

/-- Family refinement commutes with effective recovery on all compatible arrows. -/
def swapRecovery [(F.toDescentData charts).IsEquivalence]
    [(F.toDescentData swappedCharts).IsEquivalence] :
    swapPull F ⋙ (F.toDescentData swappedCharts).asEquivalence.inverse ≅
      (F.toDescentData charts).asEquivalence.inverse :=
  recoveryNaturality F Bool.not (𝟙 _) (fun _ => 𝟙 _) (by intro b; simp [swappedCharts]) ≪≫
    Functor.isoWhiskerLeft _ (Cat.Hom.toNatIso (F.mapId _)) ≪≫ Functor.rightUnitor _

variable {F}

local instance : ((SheafTorsor.Stack.pseudofunctor group).toDescentData charts).IsEquivalence :=
  torsorE.isEquivalence_functor

local instance : ((SheafActionQuotient.Stack.pseudofunctor
    ActionQuotientStack.targetAction).toDescentData charts).IsEquivalence :=
  quotientE.isEquivalence_functor

/-- The two-step comparison on the nontrivial torsor's actual family data. -/
def torsorRepeatedRecovery := repeatedRecovery (SheafTorsor.Stack.pseudofunctor group) torsorData

/-- The same two-step comparison retains the genuine equivariant target map. -/
def quotientRepeatedRecovery := repeatedRecovery
  (SheafActionQuotient.Stack.pseudofunctor ActionQuotientStack.targetAction) quotientData

/-- The pseudofunctor's two successive maps are the established composite substitution. -/
example (P : SheafTorsor.Torsor group SmoothClutching.base) :
    ((SheafTorsor.Stack.pseudofunctor group).map scale3.op.toLoc).toFunctor.obj
      (((SheafTorsor.Stack.pseudofunctor group).map scale2.op.toLoc).toFunctor.obj P) =
    SheafTorsor.reindex P (scale3 ≫ scale2) :=
  SheafTorsor.reindex_comp P scale2 scale3

example (P : SheafActionQuotient.Object ActionQuotientStack.targetAction SmoothClutching.base) :
    ((SheafActionQuotient.Stack.pseudofunctor ActionQuotientStack.targetAction).map
      scale3.op.toLoc).toFunctor.obj
      (((SheafActionQuotient.Stack.pseudofunctor ActionQuotientStack.targetAction).map
        scale2.op.toLoc).toFunctor.obj P) =
    SheafActionQuotient.reindex P (scale3 ≫ scale2) :=
  SheafActionQuotient.reindex_comp P scale2 scale3

example : swapPull (SheafTorsor.Stack.pseudofunctor group) ⋙
    (torsorEquivalence group swappedCharts swappedCharts_joint).inverse ≅ torsorE.inverse := by
  have : ((SheafTorsor.Stack.pseudofunctor group).toDescentData charts).IsEquivalence := torsorE.isEquivalence_functor
  have : ((SheafTorsor.Stack.pseudofunctor group).toDescentData swappedCharts).IsEquivalence :=
    (torsorEquivalence group swappedCharts swappedCharts_joint).isEquivalence_functor
  exact swapRecovery _

example : swapPull (SheafActionQuotient.Stack.pseudofunctor ActionQuotientStack.targetAction) ⋙
    (quotientEquivalence ActionQuotientStack.targetAction swappedCharts swappedCharts_joint).inverse ≅
      quotientE.inverse := by
  have : ((SheafActionQuotient.Stack.pseudofunctor ActionQuotientStack.targetAction).toDescentData charts).IsEquivalence := quotientE.isEquivalence_functor
  have : ((SheafActionQuotient.Stack.pseudofunctor ActionQuotientStack.targetAction).toDescentData swappedCharts).IsEquivalence :=
    (quotientEquivalence ActionQuotientStack.targetAction swappedCharts swappedCharts_joint).isEquivalence_functor
  exact swapRecovery _

abbrev torsorAggregateE := aggregateEquivalence (SheafTorsor.Stack.pseudofunctor group)
  (torsor_effectiveCoproducts group) charts

example : torsorAggregateE.functor.obj (torsorAggregateE.inverse.obj torsorData) ≅ torsorData :=
  torsorAggregateE.counitIso.app _

abbrev quotientAggregateE := aggregateEquivalence
  (SheafActionQuotient.Stack.pseudofunctor ActionQuotientStack.targetAction)
  (quotient_effectiveCoproducts ActionQuotientStack.targetAction) charts

example : quotientAggregateE.functor.obj (quotientAggregateE.inverse.obj quotientData) ≅ quotientData :=
  quotientAggregateE.counitIso.app _

end Examples.SheafFamilyDescent
