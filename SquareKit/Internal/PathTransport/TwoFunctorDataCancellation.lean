import SquareKit.Internal.PathTransport.TwoFunctorData
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
variable {A B C : Type*}
variable [Quiver A] [∀ x y : A, Quiver (x ⟶ y)]
variable [Quiver B] [∀ x y : B, Quiver (x ⟶ y)]
variable [Quiver C] [∀ x y : C, Quiver (x ⟶ y)]

theorem rawPostcomp_injective (P : PrelaxFunctorStruct A B)
    (ho : Function.Injective P.obj)
    (hm : ∀ {x y : A}, Function.Injective (P.map (X := x) (Y := y)))
    (hc : ∀ {x y : A} {p q : x ⟶ y}, Function.Injective (P.map₂ (f := p) (g := q))) :
    Function.Injective (fun D : PrelaxFunctorStruct C A => D.comp P) := by
  intro D E h
  rcases D with ⟨⟨Do,Dm⟩,Dc⟩
  rcases E with ⟨⟨Eo,Em⟩,Ec⟩
  have hO : Do = Eo := by
    funext x
    apply ho
    exact congrArg (fun G => G.obj x) h
  subst Eo
  have hM : @Dm = @Em := by
    funext x y p
    apply hm
    exact eq_of_heq (congr_arg_heq (fun G => G.map p) h)
  subst Em
  have hC : @Dc = @Ec := by
    funext x y p q α
    apply hc
    exact eq_of_heq (congr_arg_heq (fun G => G.map₂ α) h)
  subst Ec
  rfl

theorem raw_left_inverse_of_right (P : PrelaxFunctorStruct A B) (D : PrelaxFunctorStruct B A)
    (ho : Function.Injective P.obj)
    (hm : ∀ {x y : A}, Function.Injective (P.map (X := x) (Y := y)))
    (hc : ∀ {x y : A} {p q : x ⟶ y}, Function.Injective (P.map₂ (f := p) (g := q)))
    (hR : D.comp P = PrelaxFunctorStruct.id B) :
    P.comp D = PrelaxFunctorStruct.id A := by
  apply rawPostcomp_injective P ho @hm @hc
  change P.comp (D.comp P) = P
  rw [hR]
  rfl
end SquareKit.Internal.PathTransport
