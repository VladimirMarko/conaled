import SquareKit.Internal.Cubical.HomotopyEquivalences

/-! Native fiber contractions induce actual bijections on sections of constant
families. The conclusion uses derived discrete-path rigidity. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.DiscreteEquivalences
open CategoryTheory
universe u

private def firstMap {Γ : Context.{u}} (A : Family Γ) (B : Family (total A)) :
    sigma A B ⟶ A where
  app _ := TypeCat.ofHom Sigma.fst
  naturality _ _ _ := rfl

variable {Γ : Context.{u}} {S T : Type u}
  (f : constantFamily Γ S ⟶ constantFamily Γ T) (E : HomotopyEquivalence f)

noncomputable def inverseSection (b : Term (constantFamily Γ T)) : Term (constantFamily Γ S) :=
  genericFiberFst f (pair (𝟙 Γ) b) (E.fibers.center.reindex (pair (𝟙 Γ) b))

theorem rightInverse (b : Term (constantFamily Γ T)) :
    Term.map f (inverseSection f E b) = b :=
  discretePath_endpoints (genericFiberPath f (pair (𝟙 Γ) b)
    (E.fibers.center.reindex (pair (𝟙 Γ) b)))

theorem leftInverse (a : Term (constantFamily Γ S)) :
    inverseSection f E (Term.map f a) = a := by
  let τ := pair (A := constantFamily Γ T) (𝟙 Γ) (Term.map f a)
  let c := E.fibers.reindex τ
  let z := genericFiberIntro f τ a (homogeneousRefl (Term.map f a))
  exact discretePath_endpoints (homogeneousPathMap
    (firstMap (constantFamily Γ S)
      (reindex (genericFiberPathFamily f) (liftSub (reindex (constantFamily Γ S)
        (projection (constantFamily Γ T))) τ))) (c.pathTo z))

noncomputable def sectionsEquiv : Term (constantFamily Γ S) ≃ Term (constantFamily Γ T) where
  toFun := Term.map f
  invFun := inverseSection f E
  left_inv := leftInverse f E
  right_inv := rightInverse f E

def constant (s : S) : Term (constantFamily Γ S) where
  val _ := s
  property _ := rfl

def point : terminal.{u}.Elements := terminal.elementsMk (Opposite.op ⟨0⟩) PUnit.unit

theorem closedSection_eq (t : Term (constantFamily terminal S)) : t = constant (t.val point) := by
  apply Term.ext
  intro x
  let k : point ⟶ x := Functor.Elements.homMk
    (@Quiver.Hom.op Cube _ _ _ (Cube.ofRaw (fun i : Fin 0 => Fin.elim0 i))) (by
      change (PUnit.unit : PUnit) = x.val
      exact Subsingleton.elim _ _)
  exact (t.property k).symm

/-- Closed sections are determined by their zero-dimensional value. -/
def closedSections : Term (constantFamily terminal S) ≃ S where
  toFun t := t.val point
  invFun := constant
  left_inv t := (closedSection_eq t).symm
  right_inv _ := rfl

/-- This classifies section observations, not native equivalence witnesses. -/
noncomputable def closedEquiv
    (f : constantFamily terminal S ⟶ constantFamily terminal T) (E : HomotopyEquivalence f) : S ≃ T :=
  closedSections.symm.trans ((sectionsEquiv f E).trans closedSections)

theorem closedEquiv_app
    (f : constantFamily terminal S ⟶ constantFamily terminal T) (E : HomotopyEquivalence f)
    (x : terminal.Elements) (s : S) : f.app x s = closedEquiv f E s :=
  congrArg (fun t => t.val x) (closedSection_eq (Term.map f (constant s)))

end SquareKit.Cubical.Presheaf.DiscreteEquivalences
