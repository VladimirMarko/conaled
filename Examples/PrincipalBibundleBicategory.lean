import SquareKit.SheafGroupoidBibundleEquivalence

/-! The constructed tensor and coherence operations through Mathlib notation. -/
open CategoryTheory SquareKit.SheafGroupoid
open scoped CategoryTheory.Bicategory
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H K L : SquareKit.SheafGroupoid J}
variable (P : G ⟶ H) (Q : H ⟶ K) (R : K ⟶ L)
example : P ≫ Q = Bibundle.tensor P Q := rfl
example : (𝟙 G : G ⟶ G) = Bibundle.identity G.toOperations := rfl
example : P ◁ (𝟙 Q) = 𝟙 (P ≫ Q) := Bicategory.whiskerLeft_id P Q
example : (α_ P Q R).hom = (Bibundle.associator P Q R).hom := rfl
example : (λ_ P).hom = (Bibundle.leftUnitor P).hom := rfl
example : (ρ_ P).hom = (Bibundle.rightUnitor P).hom := rfl
example (f : P ⟶ P) (g : Q ⟶ Q) :
    P ◁ g ≫ f ▷ Q = f ▷ Q ≫ P ◁ g := Bicategory.whisker_exchange f g
