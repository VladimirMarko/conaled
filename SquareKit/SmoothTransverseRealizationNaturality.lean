import SquareKit.SmoothTransverseStageCover
import SquareKit.SmoothManifoldRepresentedAtlas
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! Stagewise descent tests for manifold realizations. -/
noncomputable section
namespace SquareKit.ManifoldRealization.ChartFamily
open CategoryTheory Opposite EuclideanOpen SmoothOpenSite
open SmoothPresentationSite (Site)
variable {m n : ℕ} {M N : Type} [TopologicalSpace M] [ChartedSpace (Space m) M]
  [TopologicalSpace N] [ChartedSpace (Space n) N]
  (A : ChartFamily m M) (B : ChartFamily n N)

/-- A full-stage cancellation test on chart sections extends by separatedness. -/
theorem chartwise_injective {X : Sheaf topology Type} (c : A.realization ⟶ X)
    (hc : ∀ (V : Site) (i j : A.Index)
      (a : (embedding.obj (A.charts.domain i)).obj.obj (op V))
      (b : (embedding.obj (A.charts.domain j)).obj.obj (op V)),
      c.hom.app (op V) ((A.charts.chart i).hom.app (op V) a) =
        c.hom.app (op V) ((A.charts.chart j).hom.app (op V) b) →
      (A.charts.chart i).hom.app (op V) a = (A.charts.chart j).hom.app (op V) b)
    (V : Site) : Function.Injective (c.hom.app (op V)) := by
  intro x y h
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp A.realization.property)
    (SheafCoproductLocal.liftSieve _ A.charts.chart x ⊓
      SheafCoproductLocal.liftSieve _ A.charts.chart y)
    (topology.intersection_covering (A.chart_covering V x) (A.chart_covering V y))).isSeparatedFor.ext
  intro W r hr
  obtain ⟨⟨i,a,ha⟩,⟨j,b,hb⟩⟩ := hr
  rw [← ha, ← hb]
  apply hc
  rw [ha, hb, NatTrans.naturality_apply, NatTrans.naturality_apply, h]

/-- Two independent manifold chart covers suffice to test local existence of
preimages. The local condition still concerns the complete target section. -/
theorem chartwise_locallySurjective {E T : Sheaf topology Type} (c : E ⟶ T)
    (first : T ⟶ A.realization) (second : T ⟶ B.realization)
    (hc : ∀ (V : Site) (z : T.obj.obj (op V)) (i : A.Index) (j : B.Index)
      (a : (embedding.obj (A.charts.domain i)).obj.obj (op V))
      (b : (embedding.obj (B.charts.domain j)).obj.obj (op V)),
      (A.charts.chart i).hom.app (op V) a = first.hom.app (op V) z →
      (B.charts.chart j).hom.app (op V) b = second.hom.app (op V) z →
      Presheaf.imageSieve c.hom z ∈ topology V) :
    Presheaf.IsLocallySurjective topology c.hom where
  imageSieve_mem {V} z := by
    apply topology.transitive
      (topology.intersection_covering
        (A.chart_covering V (first.hom.app (op V) z))
        (B.chart_covering V (second.hom.app (op V) z)))
    intro W r hr
    obtain ⟨⟨i,a,ha⟩,⟨j,b,hb⟩⟩ := hr
    rw [Presheaf.pullback_imageSieve]
    apply hc W (T.obj.map r.op z) i j a b
    · exact ha.trans (NatTrans.naturality_apply first.hom r.op z).symm
    · exact hb.trans (NatTrans.naturality_apply second.hom r.op z).symm

end SquareKit.ManifoldRealization.ChartFamily

namespace SquareKit.EuclideanOpen
open CategoryTheory Opposite SmoothAlgebra SmoothAlgebra.Localization
open SmoothPresentationSite

/-- A principal support for an arbitrary relatively open part of an ordinary domain. -/
def relativeSupport (U : Domain) (O : Set (Points U)) (hO : IsOpen O) : Free U.dimension :=
  openDefining (Subtype.val '' O) ((domain_open U).isOpenMap_subtype_val O hO)

theorem relativeSupport_iff (U : Domain) (O : Set (Points U)) (hO : IsOpen O)
    (x : Points U) : (relativeSupport U O hO).val x.val ≠ 0 ↔ x ∈ O := by
  change x.val ∈ locus (openDefining _ _) ↔ _
  rw [openDefining_locus]
  constructor
  · rintro ⟨y, hy, he⟩
    exact (Subtype.ext he : y = x) ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

/-- Localizing at the support forces every real reduction into the chosen open,
while retaining the entire generalized section. -/
theorem relativeSupport_local_real (U : Domain) (O : Set (Points U)) (hO : IsOpen O)
    (B : Code) (a : Hom (Principal U.defining) (Carrier B))
    (h : Hom (Carrier (localization B (a (principalBase U.defining
      (relativeSupport U O hO))))) ℝ) :
    realPoints U.defining
      (h.comp ((localizationBase B (a (principalBase U.defining
        (relativeSupport U O hO)))).comp a)) ∈ O := by
  apply (relativeSupport_iff U O hO _).mp
  rw [← point_base]
  exact isUnit_iff_ne_zero.mp
    ((PresentedLocalization.atBase_isUnit B.equations
      (a (principalBase U.defining (relativeSupport U O hO)))).map h.toAlgHom)

end SquareKit.EuclideanOpen

namespace SquareKit.SmoothOpenSite
open CategoryTheory Opposite SmoothAlgebra SmoothPresentationSite

theorem imageSieve_of_principal_lifts {E T : Sheaf SmoothOpenSite.topology Type}
    (c : E ⟶ T) (B : Code) (z : T.obj.obj (op (op B)))
    {I : Type} (s : I → Carrier B) (hs : OpenCover.Covers s)
    (hl : ∀ i, ∃ x : E.obj.obj (op (op (localization B (s i)))),
      c.hom.app _ x = T.obj.map (localizationBase B (s i)).op.op z) :
    Presheaf.imageSieve c.hom z ∈ SmoothOpenSite.topology (op B) := by
  apply SmoothOpenSite.topology.superset_covering _ (SmoothOpenSite.principal_covering B s hs)
  apply (Sieve.generate_le_iff _ _).mpr
  intro V r hr
  obtain ⟨i⟩ := hr
  exact hl i

end SquareKit.SmoothOpenSite
