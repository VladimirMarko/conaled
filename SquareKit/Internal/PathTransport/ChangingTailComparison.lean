import SquareKit.Internal.PathTransport.FamilyMapSquares

/-! Finite sequences of changing dependent families and their induced
contraction squares. These data are categorical, independent of source syntax
or a model of comparison judgments. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel
open CategoryTheory CategoryTheory.Functor ContextualElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Each step compares independently specified families over the complete
preceding contexts. Transformations need not be invertible or faithful. -/
inductive ChangingTail {C C' : Cat.{u,u}} (K : C' ⥤ C) :
    {E E' : Cat.{u,u}} → (E' ⥤ E) → Type (u+1) where
  | empty : ChangingTail K K
  | extend {E E' : Cat.{u,u}} {R : E' ⥤ E} (previous : ChangingTail K R)
      (A : E ⥤ Cat.{u,u}) (B : E' ⥤ Cat.{u,u}) (α : B ⟶ R ⋙ A) :
      ChangingTail K (E := Cat.of (Grothendieck A)) (E' := Cat.of (Grothendieck B))
        (Grothendieck.map α ⋙ Grothendieck.pre A R)

namespace ChangingTail
variable {C C' : Cat.{u,u}} {K : C' ⥤ C}

def target {E E' : Cat.{u,u}} {R : E' ⥤ E} (T : ChangingTail K R) : Telescope C E :=
  match T with
  | .empty => .empty C
  | .extend previous A _ _ => .ext previous.target A
termination_by structural T

def source {E E' : Cat.{u,u}} {R : E' ⥤ E} (T : ChangingTail K R) : Telescope C' E' :=
  match T with
  | .empty => .empty C'
  | .extend previous _ B _ => .ext previous.source B
termination_by structural T

/-- The branch comparison and its contraction coherence are constructed at
every extension. No final square is assumed. -/
def propagate {E E' : Cat.{u,u}} {R : E' ⥤ E} (T : ChangingTail K R) {D D' : Cat.{u,u}}
    (e : NormalizedEquivalence D C) (e' : NormalizedEquivalence D' C')
    (L : D' ⥤ D) (sq : EquivalenceSquare.Square e.equiv e'.equiv K L) :
    { S : (T.source.reindex e').1 ⥤ (T.target.reindex e).1 //
      EquivalenceSquare.Square (T.target.reindex e).2.2.equiv
        (T.source.reindex e').2.2.equiv R S } :=
  match T with
  | .empty => ⟨L,sq⟩
  | .extend previous A B α =>
    let p := previous.propagate e e' L sq
    ⟨Grothendieck.map (whiskerLeft (previous.source.reindex e').2.2.equiv.functor α) ⋙
        EquivalenceSquare.branchMap (previous.target.reindex e).2.2.equiv
          (previous.source.reindex e').2.2.equiv _ p.val p.property A,
      EquivalenceSquare.liftChangingSquare (previous.target.reindex e).2.2.equiv
        (previous.source.reindex e').2.2.equiv _ p.val p.property A B α⟩
termination_by structural T

/-- Elimination comparison after arbitrary finite changing tails consumes the
constructed square. The only section assumption is the mapped branch equation. -/
theorem eliminate {E E' : Cat.{u,u}} {R : E' ⥤ E} {D D' : Cat.{u,u}} (T : ChangingTail K R)
    (e : NormalizedEquivalence D C) (e' : NormalizedEquivalence D' C')
    (L : D' ⥤ D) (sq : EquivalenceSquare.Square e.equiv e'.equiv K L)
    (A : E ⥤ Cat.{u,u}) (B : E' ⥤ Cat.{u,u}) (α : B ⟶ R ⋙ A)
    (s : (T.target.reindex e).1 ⥤ Grothendieck A)
    (hs : s ⋙ Grothendieck.forget A = (T.target.reindex e).2.2.equiv.functor)
    (s' : (T.source.reindex e').1 ⥤ Grothendieck B)
    (hs' : s' ⋙ Grothendieck.forget B = (T.source.reindex e').2.2.equiv.functor)
    (hb : s' ⋙ Grothendieck.map α ⋙ Grothendieck.pre A R =
      (T.propagate e e' L sq).val ⋙ s) :
    (T.source.reindex e').2.2.eliminate s' hs' ⋙ Grothendieck.map α ⋙ Grothendieck.pre A R =
      R ⋙ (T.target.reindex e).2.2.eliminate s hs :=
  EquivalenceSquare.eliminate_familyMap _ _ R _ (T.propagate e e' L sq).property A B α s hs s' hs' hb

end ChangingTail
end SquareKit.Internal.PathTransport.GroupoidModel

namespace SquareKit.Internal.PathTransport.GroupoidModel.PathComparison
open CategoryTheory CategoryTheory.Functor ContextualElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- The normalized categorical path contraction used by contextual J. -/
def normalized {Γ : Type u} [Category.{u} Γ] [IsGroupoid Γ]
    (A : Γ ⥤ Grpd.{u,u}) (x : Section A) :
    NormalizedEquivalence (Cat.of Γ) (Cat.of (PathCtx A x)) where
  equiv := pathEquivalence A x
  unit_obj _ := rfl
  unit_hom _ := rfl

/-- This is the same normalized root used by the existing contextual model. -/
theorem normalized_eq_instance (C : Type u) [Groupoid.{u} C] (F : C ⥤ Type u)
    {Γ : Grpd.{u,u}} (A : Γ ⥤ Grpd.{u,u}) (x : Section A) :
    normalized A x = Instance.pathEquivalence C F A x := rfl

/-- The root square and every dependent-extension square are constructed from
the base/family data. Only the ordinary mapped-branch equation remains an input. -/
theorem eliminateChangingTail {Γ Δ : Type u} [Category.{u} Γ] [IsGroupoid Γ]
    [Category.{u} Δ] [IsGroupoid Δ]
    (A : Γ ⥤ Grpd.{u,u}) (B : Δ ⥤ Grpd.{u,u}) (K : Δ ⥤ Γ)
    (α : B ⟶ K ⋙ A) (x : Section A) (y : Section B)
    (h : y.familyImage α = x.reindex K)
    {E E' : Cat.{u,u}} {R : E' ⥤ E}
    (T : ChangingTail (C := Cat.of (PathCtx A x)) (C' := Cat.of (PathCtx B y))
      (familyMapTo α y (x.reindex K) h ⋙ substitution A x K) R)
    (P : E ⥤ Cat.{u,u}) (Q : E' ⥤ Cat.{u,u}) (β : Q ⟶ R ⋙ P)
    (s : (T.target.reindex (normalized A x)).1 ⥤ Grothendieck P)
    (hs : s ⋙ Grothendieck.forget P = (T.target.reindex (normalized A x)).2.2.equiv.functor)
    (s' : (T.source.reindex (normalized B y)).1 ⥤ Grothendieck Q)
    (hs' : s' ⋙ Grothendieck.forget Q = (T.source.reindex (normalized B y)).2.2.equiv.functor)
    (hb : s' ⋙ Grothendieck.map β ⋙ Grothendieck.pre P R =
      (T.propagate (normalized A x) (normalized B y) K (baseFamilySquare A B K α x y h)).val ⋙ s) :
    (T.source.reindex (normalized B y)).2.2.eliminate s' hs' ⋙ Grothendieck.map β ⋙
      Grothendieck.pre P R = R ⋙ (T.target.reindex (normalized A x)).2.2.eliminate s hs :=
  T.eliminate (normalized A x) (normalized B y) K (baseFamilySquare A B K α x y h)
    P Q β s hs s' hs' hb

end SquareKit.Internal.PathTransport.GroupoidModel.PathComparison
