import SquareKit.ElementSiteLocalEquivalence
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

/-! A fully faithful dense site comparison remains dense over every presheaf of parameters. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.ElementSite
open CategoryTheory Opposite
universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u)

/-- Change the base object while retaining its parameter section. -/
abbrev comparison : Site (F.op ⋙ P) ⥤ Site P := (Functor.Elements.precomp F.op P).op

instance comparison_faithful [F.Faithful] : (comparison F P).Faithful where
  map_injective {X Y} {f g} h := by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    apply F.op.map_injective
    exact congrArg (fun k => k.unop.hom) h

instance comparison_full [F.Full] [F.Faithful] : (comparison F P).Full where
  map_surjective {X Y} f := by
    let g : Y.unop.obj ⟶ X.unop.obj := F.op.preimage f.unop.hom
    have hg : (F.op ⋙ P).map g Y.unop.val = X.unop.val := by
      change P.map (F.op.map g) Y.unop.val = X.unop.val
      rw [F.op.map_preimage]
      exact f.unop.map_val
    refine ⟨(Functor.Elements.homMk g hg).op, ?_⟩
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    exact F.op.map_preimage f.unop.hom

/-- Projection of a generated sieve commutes with the base change functor. -/
theorem down_comparison_pushforward {X : Site (F.op ⋙ P)} (S : Sieve X) :
    down P (S.functorPushforward (comparison F P)) =
      (down (F.op ⋙ P) S).functorPushforward F := by
  ext V f
  constructor
  · rintro ⟨y, hy, Z, g, t, hg, hfac⟩
    refine ⟨Z.unop.obj.unop, g.unop.hom.unop, t.unop.hom.unop,
      ⟨Z.unop.val, g.unop.map_val, hg⟩, ?_⟩
    exact congrArg (fun k => (projection P).map k) hfac
  · rintro ⟨Z, g, t, ⟨z, hz, hg⟩, rfl⟩
    let q : point (F.op ⋙ P) Z z ⟶ X := (Functor.Elements.homMk g.op hz).op
    let k := arrow P t z
    refine ⟨P.map t.op z, ?_, ?_⟩
    · change P.map (t ≫ F.map g).op X.unop.val = P.map t.op z
      rw [op_comp, P.map_comp]
      exact congrArg (P.map t.op) hz
    · refine ⟨point (F.op ⋙ P) Z z, q, k, hg, ?_⟩
      apply Quiver.Hom.unop_inj
      apply Functor.Elements.hom_ext
      rfl

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

instance comparison_isCoverDense [F.IsCoverDense K] :
    (comparison F P).IsCoverDense (topology P K) where
  is_cover X := by
    apply K.superset_covering ?_ (F.is_cover_of_isCoverDense K X.unop.obj.unop)
    rintro V f ⟨⟨Z, t, g, rfl⟩⟩
    let z := P.map g.op X.unop.val
    let q : (comparison F P).obj (point (F.op ⋙ P) Z z) ⟶ X := arrow P g X.unop.val
    let k := arrow P t z
    refine ⟨P.map t.op z, ?_, ?_⟩
    · change P.map (t ≫ g).op X.unop.val = _
      rw [op_comp, P.map_comp]
      rfl
    · exact ⟨⟨point (F.op ⋙ P) Z z, k, q, rfl⟩⟩

/-- Dense restriction remains a site comparison over arbitrary parameter sections. -/
instance comparison_isDenseSubsite [F.Full] [F.Faithful] [F.IsDenseSubsite J K] :
    (comparison F P).IsDenseSubsite (topology (F.op ⋙ P) J) (topology P K) := by
  let := Functor.IsDenseSubsite.isCoverDense J K F
  exact
    { functorPushforward_mem_iff := by
        intro X S
        change down P _ ∈ K _ ↔ down (F.op ⋙ P) S ∈ J _
        rw [down_comparison_pushforward]
        exact F.functorPushforward_mem_iff J K }

/-- The source element topology is exactly the induced topology, not an extra assumption. -/
theorem comparison_inducedTopology [F.Full] [F.Faithful] [F.IsDenseSubsite J K] :
    (comparison F P).inducedTopology (topology P K) = topology (F.op ⋙ P) J := by
  let := Functor.IsDenseSubsite.isCoverDense J K F
  ext X S
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense]
  exact (comparison F P).functorPushforward_mem_iff _ _

/-- Parameter substitution commutes strictly with changing the base site. -/
theorem comparison_mapSite {Q : Dᵒᵖ ⥤ Type u} (η : P ⟶ Q) :
    mapSite (Functor.whiskerLeft F.op η) ⋙ comparison F Q =
      comparison F P ⋙ mapSite η := by
  rfl

end SquareKit.ElementSite
