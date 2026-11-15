import SquareKit.SmoothCechRecovery
import SquareKit.SmoothClutchingAtlas
import SquareKit.SmoothQuarterTurnArcs

/-! Checked specializations of represented smooth Čech descent. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Manifold ContDiff
namespace Examples.SmoothCechDescent
open SquareKit SquareKit.EuclideanOpen SquareKit.SmoothOpenSite
open SquareKit.SmoothRepresentedCover SquareKit.SmoothCech
open SquareKit.SmoothManifoldAction SquareKit.ManifoldRealization

/-- The identity chart is an admitted cover with actual represented intersections. -/
def identityAtlas (U : Domain) : Atlas (embedding.obj U) Unit where
  domain _ := U
  chart _ := 𝟙 _
  covering V x := by
    apply topology.superset_covering _ (topology.top_mem V)
    intro W r hr
    exact ⟨(), (embedding.obj U).obj.map r.op x, rfl⟩
  pair _ _ := U
  left _ _ := 𝟙 _
  right _ _ := 𝟙 _
  square _ _ := by simpa using (IsPullback.of_id_snd (f := 𝟙 (embedding.obj U)))
  triple _ _ _ := U
  firstSecond _ _ _ := 𝟙 _
  third _ _ _ := 𝟙 _
  tripleSquare _ _ _ := by simpa using (IsPullback.of_id_snd (f := 𝟙 (embedding.obj U)))

variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (Model d) ∞ M]

def identityDatum (U : Domain) (m : External.SmoothMap U d M) :
    Datum (d := d) (G := G) (M := M) (identityAtlas U) where
  localMap _ := m
  transition _ _ := ⟨1, fun x => one_smul G (m.val x)⟩
  diagonal _ _ := rfl
  cocycle _ _ _ _ := (one_mul 1).symm

example (U : Domain) (m : External.SmoothMap U d M)
    (smoothAction : ∀ g : G, ContMDiff (Model d) (Model d) ∞ (fun x : M => g • x)) :
    SheafActionQuotient.Object (representation smoothAction).action (embedding.obj U) :=
  (identityDatum (G := G) U m).interpreted smoothAction

example (U : Domain) (m : External.SmoothMap U d M) :
    (Hom.ident (identityDatum (G := G) U m)).inverse.comp
      (Hom.ident (identityDatum (G := G) U m)) = Hom.ident (identityDatum (G := G) U m) :=
  Hom.inverse_comp _

namespace Clutching
open SquareKit.SmoothClutching
open scoped Orbifolds.FiniteActionPresentation
local instance trivialAction (G : Type) [Group G] : MulAction G (Space 1) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem smooth (G : Type) [Group G] (g : G) : ContMDiff (Model 1) (Model 1) ∞
    (fun x : Space 1 => g • x) := contMDiff_id

def zeroMap : base ⟶ object 1 (Space 1) :=
  pushout.desc (hat (fun _ : Points line => (0 : Space 1)) contMDiff_const)
    (hat (fun _ : Points line => (0 : Space 1)) contMDiff_const) rfl

theorem trivial_act (G : Type) [Group G] (U : SmoothPresentationSite.Siteᵒᵖ)
    (g : (locallyConstantGroup G).obj.obj U) (m : (object 1 (Space 1)).obj.obj U) :
    (representation (smooth G)).action.act U g m = m := by
  let r := representation (smooth G)
  let S := Presheaf.imageSieve (constantLabel G) g
  have hS : S ∈ topology U.unop := Presheaf.imageSieve_mem topology (constantLabel G) g
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp (object 1 (Space 1)).property) S hS).isSeparatedFor.ext
  intro V f hf
  obtain ⟨k,hk⟩ := hf
  change (object 1 (Space 1)).obj.map f.op (r.act U g m) = _
  rw [r.act_natural, ← hk, r.act_constant]
  change ((ManifoldRealization.map id contMDiff_id).hom.app _ _) = _
  rw [ManifoldRealization.map_id]
  rfl

def quotient (G : Type) [Group G] (c : G) :
    SheafActionQuotient.Object (representation (smooth G)).action base :=
  SheafActionQuotient.invariantObject (torsor G c) zeroMap
    (fun x g => trivial_act G x.obj g _)

def admitted (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G] (c : G) :
    TrivializedOn Represented.atlas (smooth G) (quotient G c) where
  trivialization := Represented.localTrivialization G c

theorem interpreted_no_section (G : Type) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (c : G) (hc : c ≠ 1) :
    ¬ Nonempty (SplitSheaf.Tm ((admitted G c).extractedDatum.interpreted (smooth G)).torsor.family) := by
  rintro ⟨s⟩
  exact no_global_section G c hc ⟨SheafTorsor.sectionOfArrow
    ((SheafTorsor.ofSection _ s).comp (admitted G c).extractedRecovery.torsorArrow)⟩

open Orbifolds.QuarterTurn
local instance : TopologicalSpace C4 := ⊥
local instance : DiscreteTopology C4 := ⟨rfl⟩

def quarterTurnDatum := (admitted C4 quarterTurn).extractedDatum

theorem quarterTurn_no_section :
    ¬ Nonempty (SplitSheaf.Tm (quarterTurnDatum.interpreted (smooth C4)).torsor.family) :=
  interpreted_no_section C4 quarterTurn SquareKit.SmoothQuarterTurnArcs.quarterTurn_ne_one

end Clutching
end Examples.SmoothCechDescent
