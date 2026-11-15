import SquareKit.Internal.PathTransport.FamilyMapSquares

/-! An external selected comparison of strict contraction squares respects
their selected counits. No new contraction or counit is chosen. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.EquivalenceSquare
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
variable {e : D ≌ C} {e' : D' ≌ C'} {K K' : C' ⥤ C} {L L' : D' ⥤ D}

theorem selectedCounit_square (s : Square e e' K L) (t : Square e e' K' L')
    (η : K ≅ K') (θ : L ≅ L')
    (h : isoWhiskerLeft e'.functor η ≪≫ eqToIso t.forward =
      eqToIso s.forward ≪≫ isoWhiskerRight θ e.functor) :
    whiskerLeft K e.counitInv ≫ eqToHom (congrArg (· ⋙ e.functor) s.inverse) ≫
        whiskerLeft e'.inverse (whiskerRight θ.hom e.functor) =
      η.hom ≫ whiskerLeft K' e.counitInv ≫
        eqToHom (congrArg (· ⋙ e.functor) t.inverse) := by
  rw [← Category.assoc, ← s.counitInv]
  rw [← t.counitInv]
  apply NatTrans.ext
  funext x
  have hh := congrArg (fun i => i.hom.app (e'.inverse.obj x)) h
  have hn := η.hom.naturality (e'.counitInv.app x)
  dsimp only [Functor.comp_obj, Functor.id_obj] at hn
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, eqToIso.hom,
    eqToHom_app] at hh
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    eqToHom_app, Category.assoc]
  rw [← hh]
  rw [← Category.assoc, hn]
  simp [Category.assoc]

end SquareKit.Internal.PathTransport.GroupoidModel.EquivalenceSquare
