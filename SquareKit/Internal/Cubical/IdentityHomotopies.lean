import SquareKit.Internal.Cubical.IdentityEvaluation

/-! A section over a display is a natural fiber map; its identity section is a natural homotopy. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

variable {Γ : Context.{u}} {A : Family Γ}

def sectionMap (t : Term (reindex A (projection A))) : A ⟶ A where
  app x := TypeCat.ofHom (fun a => t.val (extendObj A x a))
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (t.property (extendHom A f a)).symm

noncomputable def sectionHomotopyValue {t : Term (reindex A (projection A))}
    (β : Term (normalizedIdentity (reindex A (projection A)) t (generic A)))
    (x : Γ.Elements) (a : A.obj x) (r : (interval Γ).obj x) : A.obj x :=
  (β.val (extendObj A x a)).eval r

theorem sectionHomotopyValue_map {t : Term (reindex A (projection A))}
    (β : Term (normalizedIdentity (reindex A (projection A)) t (generic A)))
    {x y : Γ.Elements} (f : x ⟶ y) (a : A.obj x) (r : (interval Γ).obj x) :
    A.map f (sectionHomotopyValue β x a r) =
      sectionHomotopyValue β y (A.map f a) ((interval Γ).map f r) := by
  have e := LocalIdentity.eval_map (extendHom A f a) (β.val (extendObj A x a)) r
  have q := congrArg (fun p : (normalizedIdentity (reindex A (projection A)) t (generic A)).obj
      (extendObj A y (A.map f a)) => p.eval ((interval Γ).map f r))
    (β.property (extendHom A f a))
  exact e.trans q

theorem sectionHomotopyValue_zero {t : Term (reindex A (projection A))}
    (β : Term (normalizedIdentity (reindex A (projection A)) t (generic A)))
    (x : Γ.Elements) (a : A.obj x) :
    sectionHomotopyValue β x a ((endpoint Γ false).val x) = (sectionMap t).app x a :=
  (β.val (extendObj A x a)).eval_zero

theorem sectionHomotopyValue_one {t : Term (reindex A (projection A))}
    (β : Term (normalizedIdentity (reindex A (projection A)) t (generic A)))
    (x : Γ.Elements) (a : A.obj x) :
    sectionHomotopyValue β x a ((endpoint Γ true).val x) = a :=
  (β.val (extendObj A x a)).eval_one

end SquareKit.Cubical.Presheaf
