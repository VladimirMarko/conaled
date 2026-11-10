import SquareKit.Internal.PathTransport.CechMatchingComprehensionProducts
import SquareKit.Internal.PathTransport.CechMatchingComprehensionRebase
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Algebra.Group.Int.Defs

noncomputable section
namespace Examples.CechMatchingComprehension
open CategoryTheory SquareKit.Internal.PathTransport.CechMatching
universe u v

/-- Both supplied local arrows survive product matching, including base action. -/
theorem product_arrows {D E : Diagram.{u,v}} {d d' : Datum D} {e e' : Datum E}
    (f : d ⟶ d') (g : e ⟶ e') :
    ((productEquivalence D E).functor.map (X := (d,e)) (Y := (d',e')) (f,g)).localArrow =
      (f.localArrow,g.localArrow) := rfl

abbrev Loops := SingleObj (Multiplicative ℤ)
abbrev star := SingleObj.star (Multiplicative ℤ)
abbrev loop : star ⟶ star := Multiplicative.ofAdd 1

theorem vertical_loop_survives (D : Diagram.{0,0}) (d : Datum D) :
    (constantProductEquivalence D (Grpd.of Loops)).functor.map (X := (d,star)) (Y := (d,star)) (𝟙 d, loop) ≠
      (constantProductEquivalence D (Grpd.of Loops)).functor.map (X := (d,star)) (Y := (d,star)) (𝟙 d, 𝟙 star) := by
  intro h
  have hh := (constantProductEquivalence D (Grpd.of Loops)).functor.map_injective h
  have hb := congrArg (fun f => f.2) hh
  change (1 : ℤ) = 0 at hb
  exact (by decide : (1 : ℤ) ≠ 0) hb

theorem rebase_keeps_selected_arrow {D : Diagram.{u,v}} (d : Datum D)
    {y : D.localCategory} (i : d.localObject ≅ y) :
    (Datum.rebaseIso d i).hom.localArrow = i.hom := Datum.rebaseIso_local d i

end Examples.CechMatchingComprehension
