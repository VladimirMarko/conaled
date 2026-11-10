import SquareKit.Internal.PathTransport.CechMatching

namespace SquareKit.Internal.PathTransport.CechMatching
open CategoryTheory
universe u v
variable {D : Diagram.{u,v}} {a b c d : Datum D}

theorem Datum.Hom.eq_conjugate (p : a ⟶ b) (q : c ⟶ d)
    (hx : c = a) (hy : d = b)
    (hp : p.localArrow = eqToHom (congrArg Datum.localObject hx.symm) ≫ q.localArrow ≫
      eqToHom (congrArg Datum.localObject hy)) :
    p = eqToHom hx.symm ≫ q ≫ eqToHom hy := by
  apply Datum.Hom.ext
  simpa only [Datum.comp_localArrow, Datum.eqToHom_localArrow] using hp

end SquareKit.Internal.PathTransport.CechMatching
