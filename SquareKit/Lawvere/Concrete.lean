import SquareKit.Lawvere.Presentations
import SquareKit.UnaryInteraction
import SquareKit.SmoothAlgebra
import SquareKit.Internal.Cubical.DimensionModels

/-! Existing smooth and De Morgan mathematics as Lawvere-theory instances. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.Lawvere
open CategoryTheory
universe u

/-- Smooth operations with their existing simultaneous composition. -/
def smoothOperations : Operations where
  Op := SmoothAlgebra.Operation
  var := SmoothAlgebra.projection
  subst := SmoothAlgebra.substitute
  var_subst _ _ := rfl
  subst_var _ := rfl
  subst_assoc _ _ _ := rfl

/-- Every existing smooth algebra supplies a categorical model. -/
def smoothAlgebra (A : Type*) [CommRing A] [Algebra ℝ A] [SmoothAlgebra.Structure A] :
    smoothOperations.Algebra where
  Carrier := A
  act := SmoothAlgebra.act
  var_act := SmoothAlgebra.Structure.projection
  subst_act := SmoothAlgebra.Structure.substitute

/-- Smooth homomorphisms act coordinatewise as natural transformations. -/
def smoothHom {A B : Type u} [CommRing A] [Algebra ℝ A] [SmoothAlgebra.Structure A]
    [CommRing B] [Algebra ℝ B] [SmoothAlgebra.Structure B] (h : SmoothAlgebra.Hom A B) :
    (smoothAlgebra A).toFunctor ⟶ (smoothAlgebra B).toFunctor where
  app _ := TypeCat.ofHom (fun x i => h (x i))
  naturality _ _ f := by ext x; funext i; exact h.map_act (f i) x

/-- Existing unary presentations, including their union and tensor equation schemes,
enter the general finite-arity presentation construction unchanged. -/
def unaryPresentation {S : Type} (P : UnaryInteraction.Presentation S) : Presentation where
  Symbol := S
  arity _ := 1
  Equation := P.Law
  variableCount _ := 1
  lhs e := UnaryInteraction.term (P.lhs e)
  rhs e := UnaryInteraction.term (P.rhs e)

/-- Recover an existing unary model as a model of the general presentation. -/
def unaryModel {S X : Type} (P : UnaryInteraction.Presentation S) (op : S → X → X)
    (h : UnaryInteraction.Valid P op) : GuardedTheory.Model (unaryPresentation P).guarded where
  Carrier := X
  operation s xs := op s (xs (0 : Fin 1))
  Predicate p := PEmpty.elim p
  rules e ρ _ := by
    change (UnaryInteraction.term (P.lhs e)).eval (UnaryInteraction.algebra op) ρ =
      (UnaryInteraction.term (P.rhs e)).eval (UnaryInteraction.algebra op) ρ
    rw [UnaryInteraction.eval_term, UnaryInteraction.eval_term]
    exact h e (ρ (0 : Fin 1))

namespace DeMorgan
open Cubical
abbrev termSetoid (n : Nat) : Setoid (Expr (Fin n)) :=
  ⟨Expr.Conv, ⟨Expr.Conv.refl, Expr.Conv.symm, Expr.Conv.trans⟩⟩

noncomputable def operations : Operations where
  Op n := Quotient (termSetoid n)
  var i := Quotient.mk _ (.var i)
  subst t σ := Quotient.liftOn t
    (fun t => Quotient.mk _ (t.subst (fun i => (σ i).out)))
    (fun _ _ h => Quotient.sound (h.subst _))
  var_subst i σ := Quotient.out_eq (σ i)
  subst_var t := by
    refine Quotient.inductionOn t ?_
    intro t
    apply Quotient.sound
    change Expr.Conv _ _
    have h := Expr.subst_congr (fun i => (Quotient.mk (termSetoid _) (.var i)).out)
      Expr.var (fun i => Quotient.exact (Quotient.out_eq (Quotient.mk (termSetoid _) (.var i)))) t
    simpa only [Expr.subst_var] using h
  subst_assoc t σ τ := by
    refine Quotient.inductionOn t ?_
    intro t
    apply Quotient.sound
    rw [Expr.subst_subst]
    apply Expr.subst_congr
    intro i
    have he : (σ i).liftOn (fun s => Quotient.mk (termSetoid _) (s.subst (fun j => (τ j).out)))
        (fun _ _ h => Quotient.sound (h.subst _)) =
        Quotient.mk (termSetoid _) ((σ i).out.subst (fun j => (τ j).out)) := by
      conv_lhs => rw [← Quotient.out_eq (σ i)]
      rfl
    dsimp only
    rw [he]
    exact Expr.Conv.symm (Quotient.exact (Quotient.out_eq
      (Quotient.mk (termSetoid _) ((σ i).out.subst (fun j => (τ j).out)))))

/-- The separating four-element algebra is a model of the shared theory. -/
noncomputable def four : operations.Algebra where
  Carrier := Four.Carrier
  act t ρ := Quotient.liftOn t (Four.eval ρ) (fun _ _ h => Four.sound ρ h)
  var_act _ _ := rfl
  subst_act t σ ρ := by
    refine Quotient.inductionOn t ?_
    intro t
    change Four.eval ρ (Expr.subst _ t) = _
    rw [Four.eval_subst]
    congr 1
    funext i
    exact congrArg (fun q => Quotient.liftOn q (Four.eval ρ)
      (fun _ _ h => Four.sound ρ h)) (Quotient.out_eq (σ i))

/-- Convert an existing cube substitution to its tuple of quotient operations. -/
def fromCube {a b : Cube} (f : a ⟶ b) : Fin b.dimension → operations.Op a.dimension :=
  fun i => Quotient.liftOn f (fun σ => Quotient.mk _ (σ i))
    (fun _ _ h => Quotient.sound (h i))

/-- Reassemble the tuple into the existing cube representation. -/
noncomputable def toCube {a b : Cube} (f : Fin b.dimension → operations.Op a.dimension) : a ⟶ b :=
  Cube.ofRaw (fun i => (f i).out)

@[simp] theorem from_to {a b : Cube} (f : Fin b.dimension → operations.Op a.dimension) :
    fromCube (toCube f) = f := funext (fun i => Quotient.out_eq (f i))

@[simp] theorem to_from {a b : Cube} (f : a ⟶ b) : toCube (fromCube f) = f := by
  refine Quotient.inductionOn f ?_
  intro σ
  apply Quotient.sound
  intro i
  exact Quotient.exact (Quotient.out_eq (Quotient.mk (termSetoid _) (σ i)))

/-- Recovery of the existing cube hom sets, not merely agreement on closed terms. -/
noncomputable def cubeHomEquiv (a b : Cube) :
    (a ⟶ b) ≃ ((⟨a.dimension⟩ : operations.Context) ⟶ ⟨b.dimension⟩) :=
  ⟨fromCube, toCube, to_from, from_to⟩

noncomputable def cubeFunctor : operations.Context ⥤ Cube where
  obj a := ⟨a.size⟩
  map {X Y} f := toCube (a := ⟨X.size⟩) (b := ⟨Y.size⟩) f
  map_id a := by
    apply Quotient.sound
    intro i
    exact Quotient.exact (Quotient.out_eq (Quotient.mk (termSetoid _) (.var i)))
  map_comp f g := by
    apply Quotient.sound
    intro i
    change Expr.Conv _ (Expr.subst (fun j => (f j).out) (g i).out)
    have he : operations.subst (g i) f = Quotient.mk (termSetoid _)
        (Expr.subst (fun j => (f j).out) (g i).out) := by
      conv_lhs => rw [← Quotient.out_eq (g i)]
      rfl
    change Expr.Conv (operations.subst (g i) f).out _
    rw [he]
    exact Quotient.exact (Quotient.out_eq (Quotient.mk (termSetoid _) (Expr.subst (fun j => (f j).out) (g i).out)))

/-- Passing to the common interface does not impose Boolean complements. -/
theorem not_boolean :
    (Quotient.mk (termSetoid 1) (.meet (.var 0) (.neg (.var 0)))) ≠
      Quotient.mk (termSetoid 1) .zero := by
  intro h
  have bad := Four.sound (fun _ => (true, false)) (Quotient.exact h)
  cases bad
end DeMorgan
end SquareKit.Lawvere
