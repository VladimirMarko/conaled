import SquareKit.Lawvere.Tensor
import SquareKit.Lawvere.Concrete

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SquareKit.Lawvere
open UnaryInteraction
namespace Presentation
variable {S T : Type} (P : UnaryInteraction.Presentation S) (Q : UnaryInteraction.Presentation T)

theorem leftTerm_word (w : List S) :
    leftTerm (unaryPresentation P) (unaryPresentation Q) (UnaryInteraction.term w) ≍
      UnaryInteraction.term (w.map (Sum.inl : S → S ⊕ T)) := by
  induction w with
  | nil =>
    change FinitaryTerm.leaf (arity := sumArity (unaryPresentation P) (unaryPresentation Q)) (0 : Fin 1) ≍
      FinitaryTerm.leaf (arity := fun _ : S ⊕ T => 1) (0 : Fin 1)
    congr 1
    funext s; cases s <;> rfl
  | cons s w ih =>
    change FinitaryTerm.node (Sum.inl s) (fun _ => leftTerm (unaryPresentation P) (unaryPresentation Q) (UnaryInteraction.term w)) ≍
      FinitaryTerm.node (Sum.inl s) (fun _ => UnaryInteraction.term (w.map (Sum.inl : S → S ⊕ T)))
    congr 1
    · funext s; cases s <;> rfl
    · exact Function.hfunext rfl (fun _ _ _ => ih)
theorem rightTerm_word (w : List T) :
    rightTerm (unaryPresentation P) (unaryPresentation Q) (UnaryInteraction.term w) ≍
      UnaryInteraction.term (w.map (Sum.inr : T → S ⊕ T)) := by
  induction w with
  | nil =>
    change FinitaryTerm.leaf (arity := sumArity (unaryPresentation P) (unaryPresentation Q)) (0 : Fin 1) ≍
      FinitaryTerm.leaf (arity := fun _ : S ⊕ T => 1) (0 : Fin 1)
    congr 1
    funext s; cases s <;> rfl
  | cons s w ih =>
    change FinitaryTerm.node (Sum.inr s) (fun _ => rightTerm (unaryPresentation P) (unaryPresentation Q) (UnaryInteraction.term w)) ≍
      FinitaryTerm.node (Sum.inr s) (fun _ => UnaryInteraction.term (w.map (Sum.inr : T → S ⊕ T)))
    congr 1
    · funext s; cases s <;> rfl
    · exact Function.hfunext rfl (fun _ _ _ => ih)

end Presentation
end SquareKit.Lawvere

namespace SquareKit.Lawvere
namespace Presentation
open UnaryInteraction
variable {S T : Type} (P : UnaryInteraction.Presentation S) (Q : UnaryInteraction.Presentation T)

theorem unary_sum : sum (unaryPresentation P) (unaryPresentation Q) =
    unaryPresentation (UnaryInteraction.union P Q) := by
  unfold sum unaryPresentation UnaryInteraction.union
  congr 1
  · funext s; cases s <;> rfl
  · funext e; cases e <;> rfl
  · apply Function.hfunext rfl
    intro e e' h
    cases eq_of_heq h
    cases e with
    | inl e => exact leftTerm_word P Q (P.lhs e)
    | inr e => exact rightTerm_word P Q (Q.lhs e)
  · apply Function.hfunext rfl
    intro e e' h
    cases eq_of_heq h
    cases e with
    | inl e => exact leftTerm_word P Q (P.rhs e)
    | inr e => exact rightTerm_word P Q (Q.rhs e)
end Presentation
end SquareKit.Lawvere

namespace SquareKit.Lawvere.Presentation
variable {S T : Type} (P : UnaryInteraction.Presentation S) (Q : UnaryInteraction.Presentation T)
theorem unary_crossLeft (s : S) (t : T) :
    crossLeft (unaryPresentation P) (unaryPresentation Q) s t ≍
      UnaryInteraction.term [Sum.inl s, Sum.inr t] := by
  unfold crossLeft UnaryInteraction.term
  congr 1
  · funext s; cases s <;> rfl
  · apply Function.hfunext rfl
    intro i i' h
    congr 1
    · funext s; cases s <;> rfl
    · apply Function.hfunext rfl
      intro j j' h
      congr 1
      · funext s; cases s <;> rfl
      · change (finProdFinEquiv (m := 1) (n := 1) (i,j) : Fin 1) = (0 : Fin 1)
        exact @Subsingleton.elim (Fin 1) _ _ _
theorem unary_crossRight (s : S) (t : T) :
    crossRight (unaryPresentation P) (unaryPresentation Q) s t ≍
      UnaryInteraction.term [Sum.inr t, Sum.inl s] := by
  unfold crossRight UnaryInteraction.term
  congr 1
  · funext s; cases s <;> rfl
  · apply Function.hfunext rfl
    intro i i' h
    congr 1
    · funext s; cases s <;> rfl
    · apply Function.hfunext rfl
      intro j j' h
      congr 1
      · funext s; cases s <;> rfl
      · change (finProdFinEquiv (m := 1) (n := 1) (j,i) : Fin 1) = (0 : Fin 1)
        exact @Subsingleton.elim (Fin 1) _ _ _
end SquareKit.Lawvere.Presentation

namespace SquareKit.Lawvere.Presentation
variable {S T : Type} (P : UnaryInteraction.Presentation S) (Q : UnaryInteraction.Presentation T)
theorem unary_tensor : tensor (unaryPresentation P) (unaryPresentation Q) =
    unaryPresentation (UnaryInteraction.tensor P Q) := by
  unfold tensor sum unaryPresentation UnaryInteraction.tensor UnaryInteraction.union
  congr 1
  · funext s; cases s <;> rfl
  · funext e; cases e with
    | inl e => cases e <;> rfl
    | inr st => rfl
  · apply Function.hfunext rfl
    intro e e' h
    cases eq_of_heq h
    cases e with
    | inl e => cases e with
      | inl e => exact leftTerm_word P Q (P.lhs e)
      | inr e => exact rightTerm_word P Q (Q.lhs e)
    | inr st => exact unary_crossLeft P Q st.1 st.2
  · apply Function.hfunext rfl
    intro e e' h
    cases eq_of_heq h
    cases e with
    | inl e => cases e with
      | inl e => exact leftTerm_word P Q (P.rhs e)
      | inr e => exact rightTerm_word P Q (Q.rhs e)
    | inr st => exact unary_crossRight P Q st.1 st.2
end SquareKit.Lawvere.Presentation

namespace SquareKit.Lawvere.Presentation
open CategoryTheory UnaryInteraction
variable {S T X : Type} (P : UnaryInteraction.Presentation S) (Q : UnaryInteraction.Presentation T)
/-- Exact equation-scheme recovery supplies explicit comparison maps in both directions. -/
def unarySumIso : (sum (unaryPresentation P) (unaryPresentation Q)).operations ≅
    (unaryPresentation (UnaryInteraction.union P Q)).operations :=
  eqToIso (congrArg Presentation.operations (unary_sum P Q))

def unaryTensorIso : (tensor (unaryPresentation P) (unaryPresentation Q)).operations ≅
    (unaryPresentation (UnaryInteraction.tensor P Q)).operations :=
  eqToIso (congrArg Presentation.operations (unary_tensor P Q))

theorem unary_laws_iff (op : S → X → X) :
    (∀ e (x : Fin 1 → X),
      FinitaryTerm.fold (fun s xs => op s (xs (0 : Fin 1))) x ((unaryPresentation P).lhs e) =
      FinitaryTerm.fold (fun s xs => op s (xs (0 : Fin 1))) x ((unaryPresentation P).rhs e)) ↔
      UnaryInteraction.Valid P op := by
  change (∀ e (x : Fin 1 → X),
    (UnaryInteraction.term (P.lhs e)).eval (UnaryInteraction.algebra op) x =
    (UnaryInteraction.term (P.rhs e)).eval (UnaryInteraction.algebra op) x) ↔ _
  simp only [UnaryInteraction.eval_term]
  constructor
  · intro h e x; exact h e (fun _ => x)
  · intro h e x; exact h e (x 0)

/-- The recovered equation models impose exactly the existing valid-model and interchange laws. -/
theorem unary_tensor_laws_iff (l : S → X → X) (r : T → X → X) :
    (∀ e (x : Fin 1 → X),
      FinitaryTerm.fold (fun s xs => (Sum.elim l r) s (xs (0 : Fin 1))) x
        ((unaryPresentation (UnaryInteraction.tensor P Q)).lhs e) =
      FinitaryTerm.fold (fun s xs => (Sum.elim l r) s (xs (0 : Fin 1))) x
        ((unaryPresentation (UnaryInteraction.tensor P Q)).rhs e)) ↔
      UnaryInteraction.Valid P l ∧ UnaryInteraction.Valid Q r ∧ CommutingOperations.Interchange l r :=
  (unary_laws_iff _ _).trans (UnaryInteraction.tensor_valid_iff P Q l r)
end SquareKit.Lawvere.Presentation

namespace SquareKit.Lawvere.Presentation
open CategoryTheory
variable {S T : Type} (P : UnaryInteraction.Presentation S) (Q : UnaryInteraction.Presentation T)
/-- The comparison also recovers categorical models and their homomorphisms. -/
def unaryTensorModelEquivalence :
    (tensor (unaryPresentation P) (unaryPresentation Q)).EquationModel ≌
      Model (unaryPresentation (UnaryInteraction.tensor P Q)).operations.theory (Type) := by
  rw [unary_tensor]
  exact (unaryPresentation (UnaryInteraction.tensor P Q)).equationModelEquivalence

def unarySumModelEquivalence :
    (sum (unaryPresentation P) (unaryPresentation Q)).EquationModel ≌
      Model (unaryPresentation (UnaryInteraction.union P Q)).operations.theory (Type) := by
  rw [unary_sum]
  exact (unaryPresentation (UnaryInteraction.union P Q)).equationModelEquivalence
end SquareKit.Lawvere.Presentation
