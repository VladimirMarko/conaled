import SquareKit.SplitSheaf

/-! Double and triple overlaps of a split sheaf display. -/
namespace SquareKit.SplitSheaf.Cech
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {X : Sheaf J (Type w)} (A : Ty X)

abbrev double := extension (tySub A (p A))
abbrev first : double A ⟶ extension A := p (tySub A (p A))
abbrev second : double A ⟶ extension A := lift A (p A)

def diagonal : extension A ⟶ double A := pair (tySub A (p A)) (𝟙 _) (q A)

abbrev triple := extension (tySub A (first A ≫ p A))
abbrev firstSecond : triple A ⟶ double A := p (tySub A (first A ≫ p A))
abbrev firstThird : triple A ⟶ double A := lift (tySub A (p A)) (first A)
abbrev secondThird : triple A ⟶ double A := lift (tySub A (p A)) (second A)

@[simp] theorem diagonal_first : diagonal A ≫ first A = 𝟙 _ := rfl
@[simp] theorem diagonal_second : diagonal A ≫ second A = 𝟙 _ := rfl

theorem firstSecond_first : firstSecond A ≫ first A = firstThird A ≫ first A := rfl
theorem firstSecond_second : firstSecond A ≫ second A = secondThird A ≫ first A := rfl
theorem firstThird_second : firstThird A ≫ second A = secondThird A ≫ second A := rfl

end SquareKit.SplitSheaf.Cech
