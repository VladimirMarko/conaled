import SquareKit.Internal.PathTransport.CechMatchingComprehensionFiberMap

/-! Fixed-base extraction respects composition of strict relative maps. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
variable {D E : StrictDiagram.{u,u}} {A : FamilyData D} {B : FamilyData E}
variable {hA : A.Coherence} {hB : B.Coherence}
variable (S : StrictMap D E) (F : StrictMap (A.total hA) (B.total hB))
variable (sq : F.comp (B.projection hB) = (A.projection hA).comp S)
variable {Z : Type v} [Category.{u} Z] (R : Z ⥤ Datum (A.total hA).toDiagram)
variable (d : Datum D.toDiagram) (hr : R ⋙ (A.projection hA).functor = (Functor.const Z).obj d)
variable (hs : (R ⋙ F.functor) ⋙ (B.projection hB).functor = (Functor.const Z).obj (S.functor.obj d))

theorem Fiber.comp_matchingArrow {d : Datum D.toDiagram} {x y z : Fiber A hA d}
    (f : x ⟶ y) (g : y ⟶ z) : (f ≫ g).matchingArrow = f.matchingArrow ≫ g.matchingArrow := rfl

theorem Fiber.eqToHom_arrow {d : Datum D.toDiagram} {x y : Fiber A hA d}
    (q : x = y) : (eqToHom q).matchingArrow = eqToHom (congrArg Fiber.datum q) := by
  subst y
  rfl

theorem fixedBaseFunctor_comp :
    fixedBaseFunctor A hA R d hr ⋙ fiberMap S F sq d =
      fixedBaseFunctor B hB (R ⋙ F.functor) (S.functor.obj d) hs := by
  apply CategoryTheory.Functor.ext
  · intro x y f
    apply Fiber.Hom.ext
    simp only [Fiber.comp_matchingArrow, Fiber.eqToHom_arrow]
    change (eqToHom _ ≫ F.functor.map
      (eqToHom _ ≫ R.map f ≫ eqToHom _) ≫ eqToHom _) =
      (eqToHom _ ≫ (eqToHom _ ≫ F.functor.map (R.map f) ≫ eqToHom _) ≫ eqToHom _)
    simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc,
      eqToHom_trans]
  · intro x
    apply Fiber.datum_injective
    change (Fiber.ofDatum _ _).datum = (Fiber.ofDatum _ _).datum
    rw [Fiber.datum_ofDatum, Fiber.datum_ofDatum]
    exact congrArg F.functor.obj (Fiber.datum_ofDatum _ _)

theorem fixedBaseFunctor_isEquivalence_of_comp
    (T : Z ⥤ Datum (B.total hB).toDiagram) (e : Datum E.toDiagram)
    (ht : T ⋙ (B.projection hB).functor = (Functor.const Z).obj e)
    (hb : S.functor.obj d = e) (he : R ⋙ F.functor = T)
    [(fiberMap S F sq d).Full] [(fiberMap S F sq d).Faithful]
    [(fixedBaseFunctor B hB T e ht).IsEquivalence] :
    (fixedBaseFunctor A hA R d hr).IsEquivalence := by
  subst e
  subst T
  let V := fixedBaseFunctor A hA R d hr
  let Q := fiberMap S F sq d
  have : (V ⋙ Q).IsEquivalence := by
    change (fixedBaseFunctor A hA R d hr ⋙ fiberMap S F sq d).IsEquivalence
    rw [fixedBaseFunctor_comp S F sq R d hr ht]
    infer_instance
  have : Q.EssSurj := ⟨fun y => by
    obtain ⟨z, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (V ⋙ Q) y
    exact ⟨V.obj z, ⟨i⟩⟩⟩
  have : Q.IsEquivalence := { }
  exact Functor.isEquivalence_of_comp_right V Q

end SquareKit.Internal.PathTransport.CechMatching.Comprehension
