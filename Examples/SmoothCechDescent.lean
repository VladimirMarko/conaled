import SquareKit.SmoothCechComparison

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

end Examples.SmoothCechDescent
