import SquareKit.Category

/-! Comparison with Mathlib's quotient when the input already has equality laws. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SquareKit
namespace LawfulQuotient
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] (r : HomRel C) [Congruence r]

def equiv : HomEquiv (ofCategory C) where
  homSetoid a b := ⟨@r a b, Congruence.equivalence⟩

theorem congruence : CategoryCongr (ofCategory C) (equiv r) where
  comp := by
    intro a b c g g' f f' hg hf
    exact (Congruence.equivalence (r := r)).trans
      (HomRel.comp_left f hg) (HomRel.comp_right g' hf)

theorem laws : CategoryLaws (ofCategory C) (equiv r) where
  id_comp f := by change r (f ≫ 𝟙 _) f; rw [Category.comp_id]; exact (Congruence.equivalence (r := r)).refl f
  comp_id f := by change r (𝟙 _ ≫ f) f; rw [Category.id_comp]; exact (Congruence.equivalence (r := r)).refl f
  assoc h g f := by
    change r (f ≫ g ≫ h) ((f ≫ g) ≫ h)
    rw [Category.assoc]; exact (Congruence.equivalence (r := r)).refl (f ≫ g ≫ h)

/-- Both constructions identify exactly the given congruence, not a larger relation. -/
def homEquiv (a b : C) :
    HomQuotient.Hom (⟨a⟩ : HomQuotient (ofCategory C) (equiv r)) ⟨b⟩ ≃
      ((Quotient.functor r).obj a ⟶ (Quotient.functor r).obj b) where
  toFun q := _root_.Quotient.liftOn q (fun f => (Quotient.functor r).map f)
    (fun _ _ h => CategoryTheory.Quotient.sound r h)
  invFun q := Quot.liftOn q (fun f => HomQuotient.classOf (E := equiv r) f)
    (fun f g h => _root_.Quotient.sound ((HomRel.compClosure_iff_self r f g).mp h))
  left_inv q := _root_.Quotient.inductionOn q (fun _ => rfl)
  right_inv q := Quot.inductionOn q (fun _ => rfl)

@[simp] theorem homEquiv_classOf {a b : C} (f : a ⟶ b) :
    homEquiv r a b (HomQuotient.classOf f) = (Quotient.functor r).map f := rfl

/-- The hom equivalences preserve identity and composition as a Mathlib functor. -/
def comparison :
    letI := HomQuotient.category (congruence r) (laws r)
    HomQuotient (ofCategory C) (equiv r) ⥤ Quotient r := by
  letI := HomQuotient.category (congruence r) (laws r)
  exact {
    obj := fun a => (Quotient.functor r).obj a.as
    map := fun {a b} f => homEquiv r a.as b.as f
    map_id := fun _ => rfl
    map_comp := fun f g => _root_.Quotient.inductionOn₂ f g (fun _ _ => rfl) }
end LawfulQuotient
end SquareKit
