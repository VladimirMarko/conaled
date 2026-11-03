import SquareKit.SmoothAtlasSubdivision
import SquareKit.SmoothOrdinaryCoverLifting
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! Local chart lifts of arbitrary arrows into a chart realization. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace SquareKit.EuclideanOpen.Charts
open SmoothOpenSite SmoothAlgebra
variable {M : Type} (A : Charts M)

abbrev rawDiagram := A.diagram.multispan ⋙ sheafToPresheaf topology Type
abbrev rawRealization := colimit A.rawDiagram

def sheafifiedIso : (presheafToSheaf topology Type).obj A.rawRealization ≅ A.realization :=
  (Sheaf.isColimitSheafifyCocone (colimit.cocone A.rawDiagram)
    (colimit.isColimit A.rawDiagram)).coconePointUniqueUpToIso
      (colimit.isColimit A.diagram.multispan)

def rawMap : A.rawRealization ⟶ A.realization.obj :=
  toSheafify topology A.rawRealization ≫ A.sheafifiedIso.hom.hom

instance : Presheaf.IsLocallySurjective topology A.rawMap := by
  dsimp only [rawMap]
  infer_instance

theorem rawMap_ι (j : WalkingMultispan A.shape) :
    colimit.ι A.rawDiagram j ≫ A.rawMap =
      (colimit.ι A.diagram.multispan j).hom := by
  have h := (Sheaf.isColimitSheafifyCocone (colimit.cocone A.rawDiagram)
    (colimit.isColimit A.rawDiagram)).comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit A.diagram.multispan) j
  have hh := congrArg (fun f => (sheafToPresheaf topology Type).map f) h
  change ((Sheaf.sheafifyCocone (colimit.cocone A.rawDiagram)).ι.app j).hom ≫
    A.sheafifiedIso.hom.hom = _ at hh
  rw [Sheaf.sheafifyCocone_ι_app_val] at hh
  exact (Category.assoc (colimit.ι A.rawDiagram j)
    (toSheafify topology A.rawRealization) A.sheafifiedIso.hom.hom).symm.trans hh

/-- Every section of the presheaf colimit maps to a single chart section.
Sheafification subsequently makes this description local. -/
theorem rawMap_chart {X : SmoothPresentationSite.Site}
    (a : A.rawRealization.obj (op X)) :
    ∃ i, ∃ b : (embedding.obj (A.domain i)).obj.obj (op X),
      A.rawMap.app (op X) a = (A.chart i).hom.app (op X) b := by
  obtain ⟨j, b, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj (op X)) (colimit.isColimit A.rawDiagram)) a
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (A.rawMap_ι j) (op X)) b
  cases j with
  | right i => exact ⟨i, b, h⟩
  | left r =>
    refine ⟨r.first, (embedding.map r.left).hom.app (op X) b, h.trans ?_⟩
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg (fun f => (sheafToPresheaf topology Type).map f)
        (colimit.w A.diagram.multispan (WalkingMultispan.Hom.fst r))) (op X)) b).symm

/-- Around every ordinary source point an arbitrary sheaf arrow factors through
a target chart, with an ordinary coordinate inclusion as its source restriction. -/
theorem local_chart (U : Domain) (h : embedding.obj U ⟶ A.realization) (x : Points U) :
    ∃ q : SmoothAlgebra.Free U.dimension,
      ∃ u : (⟨U.dimension, q⟩ : Domain) ⟶ U,
      (∀ y, ((show EuclideanOpen.Map _ _ from u) y).val = y.val) ∧
      (∃ y, (show EuclideanOpen.Map _ _ from u) y = x) ∧
      ∃ i, ∃ b : (⟨U.dimension, q⟩ : Domain) ⟶ A.domain i,
        embedding.map u ≫ h = embedding.map b ≫ A.chart i := by
  let a := topology.yonedaEquiv h
  let S := Presheaf.imageSieve A.rawMap a
  have hs : S ∈ topology (toSite.obj U) := Presheaf.imageSieve_mem topology A.rawMap a
  obtain ⟨q, u, hu, hx, hz⟩ := covering_local_inclusion S hs U (𝟙 _) x
  have hz' : S (toSite.map u) := by simpa only [Category.comp_id] using hz
  obtain ⟨z, hz⟩ := hz'
  obtain ⟨i, b, hb⟩ := A.rawMap_chart z
  let t : (⟨U.dimension, q⟩ : Domain) ⟶ A.domain i :=
    toSiteFullyFaithful.preimage b
  refine ⟨q, u, hu, hx, i, t, ?_⟩
  apply topology.yonedaEquiv.injective
  refine (topology.yonedaEquiv_naturality h (toSite.map u)).symm.trans
    (hz.symm.trans (hb.trans ?_))
  change (A.chart i).hom.app _ b =
    (A.chart i).hom.app _ ((𝟙 _) ≫ toSite.map t)
  rw [Category.id_comp]
  exact congrArg ((A.chart i).hom.app _) (toSiteFullyFaithful.map_preimage b).symm

theorem local_chart_principal (U : Domain) (h : embedding.obj U ⟶ A.realization) (x : Points U) :
    ∃ q : SmoothAlgebra.Free U.dimension, q.val x.val ≠ 0 ∧
      ∃ i, ∃ b : subdomain U q ⟶ A.domain i,
        embedding.map (subInclusion U q) ≫ h = embedding.map b ≫ A.chart i := by
  obtain ⟨q, u, hu, ⟨y, hy⟩, i, b, hb⟩ := A.local_chart U h x
  have hq : q.val x.val ≠ 0 := by
    have he : y.val = x.val := (hu y).symm.trans (congrArg Subtype.val hy)
    exact he ▸ y.property
  let v : subdomain U q ⟶ (⟨U.dimension, q⟩ : Domain) :=
    domainInclusion _ _ (fun _ hz => right_ne_zero_of_mul hz)
  have hv : v ≫ u = subInclusion U q := OpenFunctions.Map.ext (fun z => Subtype.ext (hu _))
  refine ⟨q, hq, i, v ≫ b, ?_⟩
  rw [← hv, embedding.map_comp, Category.assoc, hb, embedding.map_comp, Category.assoc]

/-- A chart lift near one specified ordinary source point. -/
structure LocalLift (U : Domain) (h : embedding.obj U ⟶ A.realization) (x : Points U) where
  defining : SmoothAlgebra.Free U.dimension
  atPoint : defining.val x.val ≠ 0
  index : A.Index
  coordinate : subdomain U defining ⟶ A.domain index
  factorization : embedding.map (subInclusion U defining) ≫ h =
    embedding.map coordinate ≫ A.chart index

def localLift (U : Domain) (h : embedding.obj U ⟶ A.realization) (x : Points U) :
    A.LocalLift U h x :=
  Classical.choice (by
    obtain ⟨q, hq, i, b, hb⟩ := A.local_chart_principal U h x
    exact ⟨⟨q, hq, i, b, hb⟩⟩)

end SquareKit.EuclideanOpen.Charts
