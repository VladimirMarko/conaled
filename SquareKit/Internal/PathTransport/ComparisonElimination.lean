import SquareKit.Internal.PathTransport.ComparisonProjections

/-! Normalized elimination in the comparison model consumes the common
family-map theorem. Coherence will be constructed for the path root and tails. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor ContextualElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Normalized contractions in both contexts with their counit coherence. -/
structure Contraction (Δ Γ : Context.{u}) where
  left : NormalizedEquivalence (Cat.of Δ.left) (Cat.of Γ.left)
  right : NormalizedEquivalence (Cat.of Δ.right) (Cat.of Γ.right)
  square : EquivalenceSquare.Square right.equiv left.equiv Γ.map Δ.map

namespace Contraction
variable {Γ Δ : Context.{u}}

def forward (e : Contraction Δ Γ) : Substitution Δ Γ :=
  ⟨e.left.equiv.functor, e.right.equiv.functor, e.square.forward⟩

/-- The section comparison is a theorem from the contraction square and
branch comparison, not a field of the model. -/
def eliminate (e : Contraction Δ Γ) (A : Family Γ) (d : Section (A.reindex e.forward)) : Section A where
  left := eliminateSection e.left A.left d.left
  right := eliminateSection e.right A.right d.right
  commutes := by
    apply pair_injective Γ.map
    change ((eliminateSection e.left A.left d.left).familyImage A.map).lift ⋙
      Grothendieck.pre (A.right ⋙ Grpd.forgetToCat) Γ.map =
        Γ.map ⋙ (eliminateSection e.right A.right d.right).lift
    rw [GroupoidModel.Section.familyImage_lift]
    simp only [eliminateSection, GroupoidModel.Section.ofOver_lift]
    exact EquivalenceSquare.eliminate_familyMap e.right e.left Γ.map Δ.map e.square
      (A.right ⋙ Grpd.forgetToCat) (A.left ⋙ Grpd.forgetToCat)
      (whiskerRight A.map Grpd.forgetToCat)
      (GroupoidModel.pair A.right e.right.equiv.functor d.right) rfl
      (GroupoidModel.pair A.left e.left.equiv.functor d.left) rfl
      (A.pair e.forward d).commutes

/-- Dependent extension constructs the next contraction square using the same
arbitrary family map that defines comparison comprehension. -/
def extend (e : Contraction Δ Γ) (A : Family Γ) :
    Contraction (A.reindex e.forward).extend A.extend where
  left := e.left.extend (A.left ⋙ Grpd.forgetToCat)
  right := e.right.extend (A.right ⋙ Grpd.forgetToCat)
  square := by
    have h := EquivalenceSquare.liftChangingSquare e.right.equiv e.left.equiv
      Γ.map Δ.map e.square (A.right ⋙ Grpd.forgetToCat)
      (A.left ⋙ Grpd.forgetToCat) (whiskerRight A.map Grpd.forgetToCat)
    have hb : (A.reindex e.forward).extend.map =
        Grothendieck.map (whiskerLeft e.left.equiv.functor (whiskerRight A.map Grpd.forgetToCat)) ⋙
          EquivalenceSquare.branchMap e.right.equiv e.left.equiv Γ.map Δ.map e.square
            (A.right ⋙ Grpd.forgetToCat) := by
      dsimp [Family.extend, Family.reindex, forward, EquivalenceSquare.branchMap]
      rw [whiskerRight_comp, Grothendieck.map_comp_eq, whisker_eq]
      rfl
    change EquivalenceSquare.Square
      (Grothendieck.preEquivalence (A.right ⋙ Grpd.forgetToCat) e.right.equiv)
      (Grothendieck.preEquivalence (A.left ⋙ Grpd.forgetToCat) e.left.equiv)
      A.extend.map (A.reindex e.forward).extend.map
    rw [hb]
    exact h

/-- Replace only the forward functor by a proved equal substitution. -/
def changeForward (e : Contraction Δ Γ) (σ : Substitution Δ Γ) (h : e.forward = σ) :
    Contraction Δ Γ where
  left := e.left.changeFunctor σ.left (congrArg Substitution.left h)
  right := e.right.changeFunctor σ.right (congrArg Substitution.right h)
  square := EquivalenceSquare.changeFunctorSquare _ _ _ _ e.square _ _
    (congrArg Substitution.right h) (congrArg Substitution.left h)

@[simp] theorem changeForward_forward (e : Contraction Δ Γ) (σ : Substitution Δ Γ)
    (h : e.forward = σ) : (e.changeForward σ h).forward = σ := by ext <;> rfl

end Contraction
end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
