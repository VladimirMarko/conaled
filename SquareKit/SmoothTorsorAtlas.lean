import SquareKit.SmoothPrincipalAtlas
import SquareKit.SmoothAtlasSubdivision
import SquareKit.SmoothManifoldRepresentedAtlas
import SquareKit.SmoothOrdinaryCoverLifting

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-! Principal section covers derived from local surjectivity, and the resulting
represented trivializing atlases for torsors over ordinary Euclidean opens. -/
noncomputable section
namespace SquareKit.EuclideanOpen
open CategoryTheory Opposite SmoothAlgebra SmoothOpenSite

theorem locallySurjective_principal {E X : Sheaf topology Type} (p : E ⟶ X)
    [Presheaf.IsLocallySurjective topology p.hom] (U : Domain)
    (k : embedding.obj U ⟶ X) (x : Points U) :
    ∃ q : freeAlgebra U.dimension, q.val x.val ≠ 0 ∧
      ∃ l : embedding.obj (subdomain U q) ⟶ E,
        l ≫ p = embedding.map (subInclusion U q) ≫ k := by
  let a := topology.yonedaEquiv k
  let S := Presheaf.imageSieve p.hom a
  have hs : S ∈ topology (toSite.obj U) := Presheaf.imageSieve_mem topology p.hom a
  obtain ⟨q,u,hu,⟨y,hy⟩,hz⟩ := covering_local_inclusion S hs U (𝟙 _) x
  have hz' : S (toSite.map u) := by simpa only [Category.comp_id] using hz
  obtain ⟨z,hz⟩ := hz'
  let l : embedding.obj (⟨U.dimension,q⟩ : Domain) ⟶ E := topology.yonedaEquiv.symm z
  have hl : l ≫ p = embedding.map u ≫ k := by
    apply topology.yonedaEquiv.injective
    change p.hom.app _ (topology.yonedaEquiv l) = _
    rw [show topology.yonedaEquiv l = z from topology.yonedaEquiv.apply_symm_apply z]
    exact hz.trans (topology.yonedaEquiv_naturality k (toSite.map u))
  have hq : q.val x.val ≠ 0 := by
    have he : y.val = x.val := (hu y).symm.trans (congrArg Subtype.val hy)
    exact he ▸ y.property
  let v : subdomain U q ⟶ (⟨U.dimension,q⟩ : Domain) :=
    domainInclusion _ _ (fun _ h => right_ne_zero_of_mul h)
  have hv : v ≫ u = subInclusion U q := OpenFunctions.Map.ext (fun z => Subtype.ext (hu _))
  refine ⟨q,hq,embedding.map v ≫ l,?_⟩
  rw [Category.assoc,hl,← Category.assoc,← embedding.map_comp,hv]

/-- An actual local lift, chosen from the proved local-surjectivity argument. -/
structure PrincipalLift {E X : Sheaf topology Type} (p : E ⟶ X)
    (U : Domain) (k : embedding.obj U ⟶ X) (x : Points U) where
  defining : freeAlgebra U.dimension
  at_point : defining.val x.val ≠ 0
  lift : embedding.obj (subdomain U defining) ⟶ E
  equation : lift ≫ p = embedding.map (subInclusion U defining) ≫ k

def principalLift {E X : Sheaf topology Type} (p : E ⟶ X)
    [Presheaf.IsLocallySurjective topology p.hom] (U : Domain)
    (k : embedding.obj U ⟶ X) (x : Points U) : PrincipalLift p U k x :=
  Classical.choice (by
    obtain ⟨q,hq,l,hl⟩ := locallySurjective_principal p U k x
    exact ⟨⟨q,hq,l,hl⟩⟩)

theorem principalLift_covers {E X : Sheaf topology Type} (p : E ⟶ X)
    [Presheaf.IsLocallySurjective topology p.hom] (U : Domain) (k : embedding.obj U ⟶ X) :
    Covers U (fun x => (principalLift p U k x).defining) :=
  fun x => ⟨x,(principalLift p U k x).at_point⟩
end SquareKit.EuclideanOpen

namespace SquareKit.EuclideanOpen.TorsorAtlas
open CategoryTheory SmoothOpenSite
variable (U : Domain) {G : Sheaf topology GrpCat} (P : SheafTorsor.Torsor G (embedding.obj U))

def defining (x : Points U) : SmoothAlgebra.freeAlgebra U.dimension :=
  (principalLift (SplitSheaf.p P.family) U (𝟙 _) x).defining
theorem covers : Covers U (defining U P) :=
  principalLift_covers (SplitSheaf.p P.family) U (𝟙 _)

/-- The section cover and all represented overlap geometry are outputs. -/
def atlas : SmoothRepresentedCover.Atlas (embedding.obj U) (Points U) :=
  PrincipalAtlas.atlas U (defining U P) (covers U P)

def localSection (x : Points U) : SplitSheaf.Tm (SheafTorsor.reindex P ((atlas U P).chart x)).family :=
  SplitSheaf.readTerm P.family (principalLift (SplitSheaf.p P.family) U (𝟙 _) x).lift (by
    simpa only [atlas, defining, PrincipalAtlas.atlas, Category.comp_id] using (principalLift (SplitSheaf.p P.family) U (𝟙 _) x).equation)

def trivialization (x : Points U) : SheafTorsor.Arrow
    (SheafTorsor.trivial G (embedding.obj ((atlas U P).domain x)))
    (SheafTorsor.reindex P ((atlas U P).chart x)) :=
  SheafTorsor.ofSection _ (localSection U P x)

end SquareKit.EuclideanOpen.TorsorAtlas
namespace SquareKit.SmoothCech
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothManifoldAction ManifoldRealization
open scoped Manifold ContDiff
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))

/-- Every quotient object over a represented open receives derived local data. -/
def trivializedOnOpen (U : Domain)
    (P : SheafActionQuotient.Object (representation smoothAction).action (embedding.obj U)) :
    TrivializedOn (TorsorAtlas.atlas U P.torsor) smoothAction P where
  trivialization := TorsorAtlas.trivialization U P.torsor

end SquareKit.SmoothCech

namespace SquareKit.ManifoldRealization.ChartFamily.TorsorAtlas
open CategoryTheory EuclideanOpen SmoothOpenSite
open scoped Manifold ContDiff
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Space n) M]
variable (A : ChartFamily n M) {G : Sheaf topology GrpCat} (P : SheafTorsor.Torsor G A.realization)

def defining (i : A.Index) (x : Points (A.charts.domain i)) : SmoothAlgebra.freeAlgebra n :=
  (principalLift (SplitSheaf.p P.family) (A.charts.domain i) (A.charts.chart i) x).defining
theorem covers (i : A.Index) : Covers (A.charts.domain i) (defining A P i) :=
  principalLift_covers (SplitSheaf.p P.family) (A.charts.domain i) (A.charts.chart i)
def charts : ChartFamily n M := A.subdivision (fun i => Points (A.charts.domain i))
  (defining A P) (covers A P)

/-- Every sheaf torsor over this manifold realization has a derived section atlas. -/
def atlas : SmoothRepresentedCover.Atlas A.realization (charts A P).Index :=
  (charts A P).representedAtlas.transport ((charts A P).comparison A)

def localLift (p : (charts A P).Index) :
    embedding.obj ((atlas A P).domain p) ⟶ SplitSheaf.extension P.family :=
  embedding.map (restrictChartDomainIso (A.chart p.1) (defining A P p.1 p.2)).hom ≫
    (principalLift (SplitSheaf.p P.family) (A.charts.domain p.1) (A.charts.chart p.1) p.2).lift

theorem localLift_projection (p : (charts A P).Index) :
    localLift A P p ≫ SplitSheaf.p P.family = (atlas A P).chart p := by
  rcases p with ⟨i,x⟩
  rw [localLift, Category.assoc, PrincipalLift.equation]
  have h := A.subdivision_chart (fun i => Points (A.charts.domain i))
    (defining A P) (covers A P) ⟨i,x⟩
  simpa only [atlas, charts, defining, SmoothRepresentedCover.Atlas.transport,
    ChartFamily.representedAtlas, ChartFamily.subdivisionMap, Functor.map_comp, Category.assoc] using h.symm

def localSection (p : (charts A P).Index) :
    SplitSheaf.Tm (SheafTorsor.reindex P ((atlas A P).chart p)).family :=
  SplitSheaf.readTerm P.family (localLift A P p) (localLift_projection A P p)

def trivialization (p : (charts A P).Index) : SheafTorsor.Arrow
    (SheafTorsor.trivial G (embedding.obj ((atlas A P).domain p)))
    (SheafTorsor.reindex P ((atlas A P).chart p)) :=
  SheafTorsor.ofSection _ (localSection A P p)
end SquareKit.ManifoldRealization.ChartFamily.TorsorAtlas

namespace SquareKit.SmoothCech
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothManifoldAction ManifoldRealization
open scoped Manifold ContDiff
variable {d n : ℕ} {G M N : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
  [TopologicalSpace N] [ChartedSpace (Space n) N]
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))

/-- All quotient objects over an actual manifold chart realization are admitted;
the target action need not be effective and no global section is chosen. -/
def trivializedOnManifold (A : ChartFamily n N)
    (P : SheafActionQuotient.Object (representation smoothAction).action A.realization) :
    TrivializedOn (ChartFamily.TorsorAtlas.atlas A P.torsor) smoothAction P where
  trivialization := ChartFamily.TorsorAtlas.trivialization A P.torsor
end SquareKit.SmoothCech

namespace SquareKit.SmoothCech.TrivializedOn
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothManifoldAction SmoothRepresentedCover
open ManifoldRealization
open scoped Manifold ContDiff
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
variable {X Y : Sheaf topology Type} {I J : Type} {A : Atlas X I} {B : Atlas Y J}
variable {smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x)}
variable {P : SheafActionQuotient.Object (representation smoothAction).action X}

/-- Restriction retains the explicit endpoint equality supplied by the atlas map. -/
def restrict (t : TrivializedOn A smoothAction P) {f : Y ⟶ X} (r : AtlasMap A B f) :
    TrivializedOn B smoothAction (SheafActionQuotient.reindex P f) where
  trivialization j := by
    have e := (t.trivialization (r.index j)).reindex (embedding.map (r.chart j))
    change SheafTorsor.Arrow (SheafTorsor.trivial _ (embedding.obj (B.domain j)))
      (SheafTorsor.reindex P.torsor (embedding.map (r.chart j) ≫ A.chart (r.index j))) at e
    rw [r.commutes j] at e
    exact e
end SquareKit.SmoothCech.TrivializedOn

namespace SquareKit.ManifoldRealization.ChartFamily.JointTorsorAtlas
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothAlgebra
open scoped Manifold ContDiff
variable {n : ℕ} {M J : Type} [TopologicalSpace M] [ChartedSpace (Space n) M] [Fintype J]
variable (A : ChartFamily n M) {G : Sheaf topology GrpCat}
  (P : J → SheafTorsor.Torsor G A.realization)

def defining (i : A.Index) (z : J → Points (A.charts.domain i)) : freeAlgebra n :=
  ∏ j, TorsorAtlas.defining A (P j) i (z j)

theorem covers (i : A.Index) : Covers (A.charts.domain i) (defining A P i) := by
  intro x
  refine ⟨fun _ => x, ?_⟩
  change (evaluate x.val).toAlgHom (∏ j, TorsorAtlas.defining A (P j) i x) ≠ 0
  rw [map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact (principalLift (SplitSheaf.p (P j).family) (A.charts.domain i) (A.charts.chart i) x).at_point

def atlas := A.subdivisionAtlas (fun i => J → Points (A.charts.domain i)) (defining A P) (covers A P)

def restriction (i : A.Index) (z : J → Points (A.charts.domain i)) (j : J) :
    subdomain (A.charts.domain i) (defining A P i z) ⟶
      subdomain (A.charts.domain i) (TorsorAtlas.defining A (P j) i (z j)) :=
  domainInclusion _ _ (by
    intro x hx
    apply mul_ne_zero (left_ne_zero_of_mul hx)
    have h := right_ne_zero_of_mul hx
    change (evaluate x).toAlgHom (∏ k, TorsorAtlas.defining A (P k) i (z k)) ≠ 0 at h
    rw [map_prod] at h
    exact Finset.prod_ne_zero_iff.mp h j (Finset.mem_univ j))

def localLift (j : J) (p : Σ i, J → Points (A.charts.domain i)) :
    embedding.obj ((atlas A P).domain p) ⟶ SplitSheaf.extension (P j).family :=
  embedding.map ((restrictChartDomainIso (A.chart p.1) (defining A P p.1 p.2)).hom ≫
    restriction A P p.1 p.2 j) ≫
      (principalLift (SplitSheaf.p (P j).family) (A.charts.domain p.1)
        (A.charts.chart p.1) (p.2 j)).lift

theorem localLift_projection (j : J) (p : Σ i, J → Points (A.charts.domain i)) :
    localLift A P j p ≫ SplitSheaf.p (P j).family = (atlas A P).chart p := by
  rw [localLift, Category.assoc, PrincipalLift.equation]
  have he : restriction A P p.1 p.2 j ≫
      subInclusion (A.charts.domain p.1) (TorsorAtlas.defining A (P j) p.1 (p.2 j)) =
      subInclusion (A.charts.domain p.1) (defining A P p.1 p.2) :=
    OpenFunctions.Map.ext (fun _ => rfl)
  dsimp only [TorsorAtlas.defining] at he
  rw [← Category.assoc, ← embedding.map_comp, Category.assoc, he]
  exact (A.subdivision_chart (fun i => J → Points (A.charts.domain i))
    (defining A P) (covers A P) p).symm

def trivialization (j : J) (p : Σ i, J → Points (A.charts.domain i)) : SheafTorsor.Arrow
    (SheafTorsor.trivial G (embedding.obj ((atlas A P).domain p)))
    (SheafTorsor.reindex (P j) ((atlas A P).chart p)) :=
  SheafTorsor.ofSection _ (SplitSheaf.readTerm (P j).family (localLift A P j p) (localLift_projection A P j p))
end SquareKit.ManifoldRealization.ChartFamily.JointTorsorAtlas
