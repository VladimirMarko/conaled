import SquareKit.Internal.PathTransport.PathContext

/-! Identity transport is equivalent to the square of actual section lifts. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C : Grpd.{u,u}} (A : C ⥤ Grpd.{u,u}) (x y : Section A)
variable {a b : C} (f : a ⟶ b) (p : x.obj a ⟶ y.obj a) (q : x.obj b ⟶ y.obj b)

theorem identity_transport_square (hq : (directIdentity A x y).map f p = q) :
    x.lift.map f ≫ (Grothendieck.ι (A ⋙ Grpd.forgetToCat) b).map q =
      (Grothendieck.ι (A ⋙ Grpd.forgetToCat) a).map p ≫ y.lift.map f := by
  let aa : PathComparison.PathCtx A x := ⟨y.lift.obj a, Discrete.mk p⟩
  let bb : PathComparison.PathCtx A x := ⟨y.lift.obj b, Discrete.mk q⟩
  let ff : aa ⟶ bb := ⟨y.lift.map f, Discrete.eqToHom hq⟩
  exact PathComparison.arrow_natural A x ff

theorem identity_transport_iff_square :
    (directIdentity A x y).map f p = q ↔
      x.lift.map f ≫ (Grothendieck.ι (A ⋙ Grpd.forgetToCat) b).map q =
        (Grothendieck.ι (A ⋙ Grpd.forgetToCat) a).map p ≫ y.lift.map f := by
  constructor
  · exact identity_transport_square A x y f p q
  · intro hs
    have ht := identity_transport_square A x y f p ((directIdentity A x y).map f p) rfl
    apply (Grothendieck.ι (A ⋙ Grpd.forgetToCat) b).map_injective
    exact (cancel_epi (x.lift.map f)).mp (ht.trans hs.symm)

end SquareKit.Internal.PathTransport.GroupoidModel
