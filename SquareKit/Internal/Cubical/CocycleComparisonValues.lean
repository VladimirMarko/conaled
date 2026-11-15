import SquareKit.Internal.Cubical.CocycleIdentityRestriction
import SquareKit.Internal.Cubical.IdentityHomotopies

/-! Evaluate a specified endpoint comparison along a selected second identity. -/
noncomputable section
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf

variable {Γ : Context.{0}}
variable {t : Term (reindex (FirstIdentityFamily Γ) (projection (FirstIdentityFamily Γ)))}
variable (β : Term (normalizedIdentity (reindex (FirstIdentityFamily Γ) (projection (FirstIdentityFamily Γ)))
  t (generic (FirstIdentityFamily Γ))))

def comparisonValue (h : Term (SecondIdentityFamily Γ)) (x : Γ.Elements)
    (r s v : (interval Γ).obj x) : CubeCocycle x.obj.unop :=
  (sectionHomotopyValue β x ((h.val x).eval r) s).eval v

def actionValue (h : Term (SecondIdentityFamily Γ)) (x : Γ.Elements)
    (r v : (interval Γ).obj x) : CubeCocycle x.obj.unop :=
  ((sectionMap t).app x ((h.val x).eval r)).eval v

theorem comparisonValue_map (h : Term (SecondIdentityFamily Γ)) {x y : Γ.Elements}
    (f : x ⟶ y) (r s v : (interval Γ).obj x) :
    cocycles.map f.hom (comparisonValue β h x r s v) =
      comparisonValue β h y ((interval Γ).map f r) ((interval Γ).map f s) ((interval Γ).map f v) := by
  have eh := (LocalIdentity.eval_map f (h.val x) r).trans
    (congrArg (fun p : (SecondIdentityFamily Γ).obj y => p.eval ((interval Γ).map f r)) (h.property f))
  have eb := (sectionHomotopyValue_map β f ((h.val x).eval r) s).trans
    (congrArg (fun p => sectionHomotopyValue β y p ((interval Γ).map f s)) eh)
  exact (LocalIdentity.eval_map f (sectionHomotopyValue β x ((h.val x).eval r) s) v).trans
    (congrArg (fun p : (FirstIdentityFamily Γ).obj y => p.eval ((interval Γ).map f v)) eb)

theorem comparisonValue_start (h : Term (SecondIdentityFamily Γ)) (x : Γ.Elements)
    (r v : (interval Γ).obj x) :
    comparisonValue β h x r ((endpoint Γ false).val x) v = actionValue (t := t) h x r v :=
  congrArg (fun p : (FirstIdentityFamily Γ).obj x => p.eval v)
    (sectionHomotopyValue_zero β x ((h.val x).eval r))

theorem comparisonValue_finish (h : Term (SecondIdentityFamily Γ)) (x : Γ.Elements)
    (r v : (interval Γ).obj x) :
    comparisonValue β h x r ((endpoint Γ true).val x) v = secondValue h x r v :=
  congrArg (fun p : (FirstIdentityFamily Γ).obj x => p.eval v)
    (sectionHomotopyValue_one β x ((h.val x).eval r))

def comparisonRootValue (x : Γ.Elements) (s v : (interval Γ).obj x) : CubeCocycle x.obj.unop :=
  (sectionHomotopyValue β x ((normalizedIdentityRefl (zeroTerm Γ)).val x) s).eval v

theorem comparisonValue_root (h : Term (SecondIdentityFamily Γ)) (x : Γ.Elements)
    (s v : (interval Γ).obj x) (e : Bool) :
    comparisonValue β h x ((endpoint Γ e).val x) s v = comparisonRootValue β x s v := by
  cases e
  · exact congrArg (fun p => (sectionHomotopyValue β x p s).eval v) (h.val x).eval_zero
  · exact congrArg (fun p => (sectionHomotopyValue β x p s).eval v) (h.val x).eval_one

theorem comparisonValue_side (h : Term (SecondIdentityFamily Γ)) (x : Γ.Elements)
    (r s : (interval Γ).obj x) (e : Bool) :
    comparisonValue β h x r s ((endpoint Γ e).val x) = zeroCocycle (Over x.obj.unop) := by
  cases e
  · exact (sectionHomotopyValue β x ((h.val x).eval r) s).eval_zero
  · exact (sectionHomotopyValue β x ((h.val x).eval r) s).eval_one

end SquareKit.Cubical.CategoryCocycles
