import SquareKit.SmoothDualSheaf
import Applications.Orbifolds.QuarterTurn
import SquareKit.SheafTorsor
import SquareKit.SmoothConstantRigidity
import SquareKit.SmoothTorsorEquivalence
import SquareKit.SheafTorsorDescent
import SquareKit.SmoothClutchingPrincipal

/-! C4 torsors with disconnected labels, nonidentity infinitesimal restriction,
and a nontrivial clutching torsor recovered by effective descent. -/
noncomputable section
namespace Examples.SmoothTorsors
open CategoryTheory Opposite SquareKit SquareKit.SmoothOpenSite
open SquareKit.SmoothPresentationSite SquareKit.SmoothGeometricKL SquareKit.SheafTorsor
open Orbifolds.QuarterTurn

abbrev group := locallyConstantGroup C4
abbrev point := representable (J := SquareKit.SmoothOpenSite.topology) (free 0)

def loop (g : C4) : Arrow (trivial group point) (trivial group point) :=
  regularArrow (constantSection point g)

/-- All four labels survive as automorphisms of the regular sheaf torsor. -/
theorem loop_injective : Function.Injective loop := by
  intro g h he
  have hs := regularArrow_injective he
  have hv := congrArg (fun k : point ⟶ locallyConstantGroupSheaf C4 =>
    k.hom.app (atStage (free 0)) (𝟙 (op (free 0)))) hs
  exact constantLabel_injective C4 (free 0) (𝟙 _) hv

theorem quarterTurn_ne_one : quarterTurn ≠ (1 : C4) := by
  intro he
  have hi := congrArg (fun g : C4 => ((g.val : ℂ)).im) he
  norm_num [quarterTurn] at hi

theorem nonidentity_loop : loop quarterTurn ≠ loop 1 :=
  fun h => quarterTurn_ne_one (loop_injective h)

abbrev disconnected := Limits.coprod point point

/-- A label over a disconnected parameter has independent values on its pieces. -/
def varyingLabel : disconnected ⟶ locallyConstantGroupSheaf C4 :=
  Limits.coprod.desc (constantSection point 1) (constantSection point quarterTurn)

theorem varyingLabel_left : Limits.coprod.inl ≫ varyingLabel = constantSection point 1 :=
  Limits.coprod.inl_desc _ _

theorem varyingLabel_right : Limits.coprod.inr ≫ varyingLabel = constantSection point quarterTurn :=
  Limits.coprod.inr_desc _ _

/-- The label is not a single constant on the disconnected base. -/
theorem varyingLabel_not_constant (g : C4) : varyingLabel ≠ constantSection disconnected g := by
  intro he
  have hl := congrArg (fun k : disconnected ⟶ locallyConstantGroupSheaf C4 =>
    (Limits.coprod.inl : point ⟶ disconnected) ≫ k) he
  have hr := congrArg (fun k : disconnected ⟶ locallyConstantGroupSheaf C4 =>
    (Limits.coprod.inr : point ⟶ disconnected) ≫ k) he
  rw [varyingLabel_left] at hl
  rw [varyingLabel_right] at hr
  have hleft : (1 : C4) = g := constantLabel_injective C4 (free 0) (𝟙 _)
    (congrArg (fun k : point ⟶ locallyConstantGroupSheaf C4 =>
      k.hom.app (atStage (free 0)) (𝟙 (op (free 0)))) hl)
  have hright : quarterTurn = g := constantLabel_injective C4 (free 0) (𝟙 _)
    (congrArg (fun k : point ⟶ locallyConstantGroupSheaf C4 =>
      k.hom.app (atStage (free 0)) (𝟙 (op (free 0)))) hr)
  exact quarterTurn_ne_one (hright.trans hleft.symm)

/-- Zero and infinitesimal pullback are inverse on labels at every stage. -/
example (A : Code) (g : (locallyConstantGroupSheaf C4).obj.obj (atStage (dual A))) :
    constantGroupDualEquiv C4 A ((constantGroupDualEquiv C4 A).symm g) = g :=
  (constantGroupDualEquiv C4 A).apply_symm_apply g

/-- This stage restriction really changes the infinitesimal coordinate. -/
def killEps : dual (free 0) ⟶ dual (free 0) := dualZero (free 0) ≫ inl (free 0)

theorem killEps_value : smoothMap killEps (eps (free 0)).val = 0 := by
  change smoothMap (inl (free 0)) (smoothMap (dualZero (free 0)) (eps (free 0)).val) = 0
  rw [dualZero, dualLift_eps]
  exact (smoothMap (inl (free 0))).toAlgHom.map_zero

theorem killEps_nonidentity : killEps ≠ 𝟙 (dual (free 0)) := by
  intro he
  have hz := killEps_value
  rw [he] at hz
  change (eps (free 0)).val = 0 at hz
  have hd := congrArg (fun z => (dualToActual (free 0) z).snd) hz
  change (SmoothAlgebra.Presentation.toDual _ (SmoothAlgebra.Presentation.dualEps _)).snd = _ at hd
  rw [SmoothAlgebra.Presentation.toDual_eps] at hd
  have hz₀ : dualToActual (free 0) 0 = 0 := (dualToActual (free 0)).toAlgHom.map_zero
  rw [hz₀] at hd
  have hr := congrArg realEvaluation hd
  change realEvaluation 1 = realEvaluation 0 at hr
  have h₁ : realEvaluation 1 = 1 := realEvaluation.toAlgHom.map_one
  have h₀ : realEvaluation 0 = 0 := realEvaluation.toAlgHom.map_zero
  rw [h₁, h₀] at hr
  exact one_ne_zero hr

/-- Restriction along that nonidentity map preserves the nonidentity C4 label. -/
theorem killEps_label :
    Arrow.reindex (regularArrow (constantSection
      (representable (J := SquareKit.SmoothOpenSite.topology) (dual (free 0))) quarterTurn))
      (representableMap killEps) =
    regularArrow (constantSection
      (representable (J := SquareKit.SmoothOpenSite.topology) (dual (free 0))) quarterTurn) := rfl

theorem nonidentity_dual_label :
    regularArrow (constantSection
      (representable (J := SquareKit.SmoothOpenSite.topology) (dual (free 0))) quarterTurn) ≠
    regularArrow (constantSection
      (representable (J := SquareKit.SmoothOpenSite.topology) (dual (free 0))) (1 : C4)) := by
  intro he
  have hs := regularArrow_injective he
  have hv := congrArg (fun k =>
    k.hom.app (atStage (dual (free 0))) (𝟙 (op (dual (free 0))))) hs
  exact quarterTurn_ne_one
    (constantLabel_injective C4 (dual (free 0)) (dualZero (free 0)).op hv)

/-- Naturality of the torsor equivalence also holds for this nonidentity
infinitesimal restriction, not only for ordinary real-stage maps. -/
example :
    restriction (representableMap killEps) ⋙
        (torsorProjectionEquivalence (H := C4) (dual (free 0))).functor =
      (torsorProjectionEquivalence (H := C4) (dual (free 0))).functor ⋙
        restriction (representableMap (dualMap killEps)) :=
  torsorProjection_baseChange killEps

/-- All locally trivial C4 torsors, including ones without sections, are covered
by the theorem. No trivialization argument is an input to this equivalence. -/
example (A : Code) :
    Torsor group (representable (J := SquareKit.SmoothOpenSite.topology) A) ≌
      Torsor group (SheafRelation.product
        (PresentationGeometry.infinitesimal SquareKit.SmoothOpenSite.topology)
        (representable (J := SquareKit.SmoothOpenSite.topology) A)) :=
  infinitesimalTorsorEquivalence A

/-- Localizing at zero is an actual empty stage of the same site. -/
abbrev emptyStage : Code := localization (free 0) 0

theorem emptyStage_no_real (r : SmoothAlgebra.Hom (Carrier emptyStage) ℝ) : False := by
  have hu : IsUnit (r (smoothMap (localizationBase (free 0) 0) 0)) :=
    (SmoothAlgebra.PresentedLocalization.atBase_isUnit (free 0).equations 0).map r.toAlgHom
  have hz : smoothMap (localizationBase (free 0) 0) 0 = 0 :=
    (smoothMap (localizationBase (free 0) 0)).toAlgHom.map_zero
  have hr : r 0 = 0 := r.toAlgHom.map_zero
  rw [hz, hr] at hu
  exact not_isUnit_zero hu

example : Nonempty (Unique ((locallyConstantGroupSheaf C4).obj.obj (atStage emptyStage))) :=
  empty_stage_unique (locallyConstantGroupSheaf C4) emptyStage emptyStage_no_real

/-- Every torsor is trivial on its own locally surjective total-space cover.
This supplies a checked input to effective descent without choosing a global
section of the original torsor. -/
example {X : Sheaf SquareKit.SmoothOpenSite.topology Type} (P : Torsor group X) :
    Arrow (trivial group (SplitSheaf.Ext P.family))
      (reindex P (SplitSheaf.p P.family)) :=
  ofSection _ (SplitSheaf.q P.family)

example {X : Sheaf SquareKit.SmoothOpenSite.topology Type} (P : Torsor group X) :
    Arrow (Descent.torsor (Descent.canonicalDatum P.family P)) P :=
  Descent.canonicalRecovery P.family P

/-- This object is obtained by gluing actual sheaves and has no global
trivialization. Its transition uses the positive quarter-turn. -/
abbrev nontrivialTorsor := SmoothClutching.torsor C4 quarterTurn

theorem nontrivialTorsor_no_section :
    ¬ Nonempty (SplitSheaf.Tm nontrivialTorsor.family) :=
  SmoothClutching.no_global_section C4 quarterTurn quarterTurn_ne_one

theorem nontrivialTorsor_not_trivializable :
    ¬ Nonempty (Arrow (trivial group SmoothClutching.base) nontrivialTorsor) :=
  SmoothClutching.not_trivializable C4 quarterTurn quarterTurn_ne_one

/-- The generic effective-descent construction recovers this nontrivial object
from a cover on which its torsor is explicitly trivial. -/
def nontrivialCoverTrivialization :
    Arrow (trivial group (SplitSheaf.Ext nontrivialTorsor.family))
      (reindex nontrivialTorsor (SplitSheaf.p nontrivialTorsor.family)) :=
  ofSection _ (SplitSheaf.q nontrivialTorsor.family)

def recoveredNontrivial :=
  Descent.torsor (Descent.canonicalDatum nontrivialTorsor.family nontrivialTorsor)

theorem recoveredNontrivial_not_trivializable :
    ¬ Nonempty (Arrow (trivial group SmoothClutching.base) recoveredNontrivial) := by
  rintro ⟨f⟩
  exact nontrivialTorsor_not_trivializable
    ⟨f.comp (Descent.canonicalRecovery nontrivialTorsor.family nontrivialTorsor)⟩

/-- Infinitesimal rigidity also applies to this genuinely nontrivial torsor,
using the arbitrary-base comparison underlying the represented theorem. -/
example : Arrow (dualTorsor nontrivialTorsor)
    (reindex nontrivialTorsor (dualSheafZero SmoothClutching.base)) :=
  dualTorsorZero nontrivialTorsor

end Examples.SmoothTorsors
