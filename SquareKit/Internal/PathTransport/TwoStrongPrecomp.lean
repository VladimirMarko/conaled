import SquareKit.Internal.PathTransport.TwoStrongTransport
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w' u'' v'' w''
variable {A : Type u} [Bicategory.{w,v} A] [Bicategory.Strict A]
variable {B : Type u'} [Bicategory.{w',v'} B] [Bicategory.Strict B]
variable {C : Type u''} [Bicategory.{w'',v''} C] [Bicategory.Strict C]
variable {F G : StrictPseudofunctor B C}
variable (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
variable (H : StrictPseudofunctor A B)
omit [Strict B] [Strict C] in
private theorem naturality_id_at (a : B) (q : a ⟶ a) (e : q = 𝟙 a)
    (eF : F.map q = 𝟙 (F.obj a)) (eG : G.map q = 𝟙 (G.obj a)) :
    (η.naturality q).hom ≫ η.app a ◁ eqToHom eG =
      eqToHom eF ▷ η.app a ≫ (λ_ (η.app a)).hom ≫ (ρ_ (η.app a)).inv := by
  cases e
  simpa only [F.mapId_eq_eqToIso, G.mapId_eq_eqToIso, eqToIso.hom] using η.naturality_id a
omit [Strict B] [Strict C] in
private theorem naturality_comp_at {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
    (q : a ⟶ c) (e : q = f ≫ g)
    (eF : F.map q = F.map f ≫ F.map g) (eG : G.map q = G.map f ≫ G.map g) :
    (η.naturality q).hom ≫ η.app a ◁ eqToHom eG =
      eqToHom eF ▷ η.app c ≫ (α_ (F.map f) (F.map g) (η.app c)).hom ≫
      F.map f ◁ (η.naturality g).hom ≫ (α_ (F.map f) (η.app b) (G.map g)).inv ≫
      (η.naturality f).hom ▷ G.map g ≫ (α_ (η.app a) (G.map f) (G.map g)).hom := by
  cases e
  simpa only [F.mapComp_eq_eqToIso, G.mapComp_eq_eqToIso, eqToIso.hom] using η.naturality_comp f g
/-- Reindex a coherent transformation along a strict higher substitution. -/
def strongPrecomp :
    Pseudofunctor.StrongTrans (H.comp F).toPseudofunctor (H.comp G).toPseudofunctor where
  app x := η.app (H.obj x)
  naturality f := η.naturality (H.map f)
  naturality_naturality α := η.naturality_naturality (H.map₂ α)
  naturality_id x := by
    simpa only [(H.comp F).mapId_eq_eqToIso, (H.comp G).mapId_eq_eqToIso, eqToIso.hom, StrictPseudofunctor.comp_map, StrictPseudofunctor.comp_obj] using
      naturality_id_at η (H.obj x) (H.map (𝟙 x)) (H.map_id x)
        (by rw [H.map_id, F.map_id]) (by rw [H.map_id, G.map_id])
  naturality_comp f g := by
    simpa only [(H.comp F).mapComp_eq_eqToIso, (H.comp G).mapComp_eq_eqToIso, eqToIso.hom, StrictPseudofunctor.comp_map, StrictPseudofunctor.comp_obj] using
      naturality_comp_at η (H.map f) (H.map g) (H.map (f ≫ g)) (H.map_comp f g)
        (by rw [H.map_comp, F.map_comp]) (by rw [H.map_comp, G.map_comp])
end SquareKit.Internal.PathTransport
