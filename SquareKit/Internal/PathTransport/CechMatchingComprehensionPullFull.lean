import SquareKit.Internal.PathTransport.CechMatchingComprehensionPullFaithful
import SquareKit.Internal.PathTransport.CechMatchingComprehensionFiberFull
import SquareKit.Internal.PathTransport.CechMatchingMapSquare

/-! Every vertical target matching arrow lifts through relative reindexing. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension.Pull
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {D E : StrictDiagram.{u,u}} (S : StrictMap D E) (A : FamilyData E)
variable (h : A.Coherence) (hp : (data S A).Coherence) (d : Datum D.toDiagram)

theorem raw_lift (x y : Fiber (data S A) hp d)
    (q : (raw S A h hp d).obj x ⟶ (raw S A h hp d).obj y)
    (hq : (A.projection h).functor.map q ≫
      eqToHom (Functor.congr_obj (fiberMap_projection S (totalMap S A h hp) (projection S A h hp) d) y) =
      eqToHom (Functor.congr_obj (fiberMap_projection S (totalMap S A h hp) (projection S A h hp) d) x)) :
    ∃ f : x ⟶ y, (raw S A h hp d).map f = q := by
  have hv : q.localArrow.base = S.localMap.map (𝟙 d.localObject) := by
    have hh := congrArg Datum.Hom.localArrow hq
    simp only [Datum.comp_localArrow, Datum.eqToHom_localArrow] at hh
    change q.localArrow.base ≫ (𝟙 (S.localMap.obj d.localObject)) = 𝟙 _ at hh
    exact ((Category.comp_id _).symm.trans hh).trans (S.localMap.map_id _).symm
  let l := GrothendieckPreFiber.lift (A.localFamily ⋙ Grpd.forgetToCat) S.localMap
    (𝟙 d.localObject) q.localArrow hv
  have hl : l.base = 𝟙 d.localObject := GrothendieckPreFiber.lift_base _ _ _ _ _
  have hm : (Grothendieck.pre (A.localFamily ⋙ Grpd.forgetToCat) S.localMap).map l =
      q.localArrow := GrothendieckPreFiber.map_lift _ _ _ _ _
  have hc : (data S A).firstMap.map l ≫ y.overlap.hom =
      x.overlap.hom ≫ (data S A).secondMap.map l := by
    apply GrothendieckPreFiber.map_injective_of_base
      (A.doubleFamily ⋙ Grpd.forgetToCat) S.doubleMap
    · change D.first.map l.base ≫ y.overlap.hom.base = x.overlap.hom.base ≫ D.second.map l.base
      rw [hl, y.base_overlap, x.base_overlap]
      change D.first.map (𝟙 d.localObject) ≫ d.overlap.hom =
        d.overlap.hom ≫ D.second.map (𝟙 d.localObject)
      rw [D.first.map_id, D.second.map_id]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
    · apply ((totalMap S A h hp).square_iff l).mp
      change A.firstMap.map ((Grothendieck.pre _ S.localMap).map l) ≫ _ =
        _ ≫ A.secondMap.map ((Grothendieck.pre _ S.localMap).map l)
      rw [hm]
      exact q.commutes
  refine ⟨⟨⟨l,hc⟩,hl⟩, ?_⟩
  apply Datum.Hom.ext
  exact hm

instance : (toFiber S A h hp d).Full :=
  fixedBaseFunctor_full A h (raw S A h hp d) (S.functor.obj d)
    (fiberMap_projection S (totalMap S A h hp) (projection S A h hp) d)
    (raw_lift S A h hp d)

end SquareKit.Internal.PathTransport.CechMatching.Comprehension.Pull

namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem fiberMap_full_of_pull {D E : StrictDiagram.{u,u}} (S : StrictMap D E)
    (A : FamilyData E) (B : FamilyData D) (h : A.Coherence) (hb : B.Coherence)
    (q : B = Pull.data S A) (F : StrictMap (B.total hb) (A.total h))
    (sq : F.comp (A.projection h) = (B.projection hb).comp S)
    (hl : HEq F.localMap (Grothendieck.pre (A.localFamily ⋙ Grpd.forgetToCat) S.localMap))
    (hd : HEq F.doubleMap (Grothendieck.pre (A.doubleFamily ⋙ Grpd.forgetToCat) S.doubleMap))
    (ht : HEq F.tripleMap (Grothendieck.pre (A.tripleFamily ⋙ Grpd.forgetToCat) S.tripleMap))
    (d : Datum D.toDiagram) : (fiberMap S F sq d).Full ∧ (fiberMap S F sq d).Faithful := by
  subst B
  have hf : F = Pull.totalMap S A h hb :=
    StrictMap.ext _ _ (eq_of_heq hl) (eq_of_heq hd) (eq_of_heq ht)
  subst F
  exact ⟨inferInstanceAs ((Pull.toFiber S A h hb d).Full),
    inferInstanceAs ((Pull.toFiber S A h hb d).Faithful)⟩
end SquareKit.Internal.PathTransport.CechMatching.Comprehension
