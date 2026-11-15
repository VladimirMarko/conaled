import SquareKit.Internal.Cubical.EquivalencePaths
import Examples.CubicalContractibleTotals

/-! Coordinate interchange on a contractible native carrier lifts to a path of equivalences. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalEquivalencePaths
open CategoryTheory SquareKit.Cubical.Presheaf
universe u
variable {Γ : Context.{u}} {D : Family Γ}

abbrev square (D : Family Γ) := sigma D (reindex D (projection D))

def swapIso : square D ≅ square D where
  hom := {
    app := fun _ => TypeCat.ofHom (fun z => ⟨z.2, z.1⟩)
    naturality := by intros; rfl }
  inv := {
    app := fun _ => TypeCat.ofHom (fun z => ⟨z.2, z.1⟩)
    naturality := by intros; rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

noncomputable def squareFilling (F : Filling D) (hF : F.Lawful) : Filling (square D) :=
  sigmaFilling F hF (F.reindex (projection D))

theorem squareFilling_lawful (F : Filling D) (hF : F.Lawful) : (squareFilling F hF).Lawful :=
  sigmaFilling_lawful F hF _ (hF.reindex _)

def first : Term (reindex D (projection (square D))) where
  val x := x.val.2.1
  property h := congrArg Sigma.fst ((generic (square D)).property h)

def second : Term (reindex D (projection (square D))) where
  val x := x.val.2.2
  property {_x y} h := congrArg (fun z : (square D).obj ((projection (square D)).mapElements.obj y) =>
    (show D.obj ((projection (square D)).mapElements.obj y) from z.2))
    ((generic (square D)).property h)

noncomputable def crossPath (c : HomotopyContractible D) (F : Filling D) (hF : F.Lawful) :
    Term (homogeneousPath (reindex D (projection (square D))) first second) :=
  homogeneousConcat (F.reindex (projection (square D))) (hF.reindex _)
    (homogeneousReverse ((c.reindex (projection (square D))).pathTo first))
    ((c.reindex (projection (square D))).pathTo second)

noncomputable def swapHomotopy (c : HomotopyContractible D) (F : Filling D) (hF : F.Lawful) :
    Term (homogeneousPath (reindex (square D) (projection (square D)))
      (Term.map (Functor.whiskerLeft (projection (square D)).mapElements (𝟙 (square D))) (generic (square D)))
      (Term.map (Functor.whiskerLeft (projection (square D)).mapElements (swapIso (D := D)).hom) (generic (square D)))) := by
  let p := crossPath c F hF
  let q := homogeneousReverse p
  let body : Term (reindex (square D) (projection (interval (total (square D))) ≫ projection (square D))) :=
    sigmaIntro (B := reindex (reindex D (projection D))
      (liftSub D (projection (interval (total (square D))) ≫ projection (square D))))
      (pathApp p) (pathApp q)
  refine pathLam body ?_ ?_
  · apply Term.ext
    intro x
    apply Sigma.ext (congrArg (fun t => t.val x) (pathApp_zero p))
    exact heq_of_eq (congrArg (fun t => t.val x) (pathApp_zero q))
  · apply Term.ext
    intro x
    apply Sigma.ext (congrArg (fun t => t.val x) (pathApp_one p))
    exact heq_of_eq (congrArg (fun t => t.val x) (pathApp_one q))

/-- The input maps are coordinate identity and coordinate swap; the output retains
both chosen generic-fiber contractions. -/
noncomputable def swapEquivalencePath (c : HomotopyContractible D) (F : Filling D) (hF : F.Lawful) :=
  EquivalencePaths.ofHomotopy (𝟙 (square D)) (swapIso (D := D)).hom (swapHomotopy c F hF)
    (squareFilling F hF) (squareFilling_lawful F hF)
    (squareFilling F hF) (squareFilling_lawful F hF)
    (HomotopyEquivalence.ofIso (Iso.refl (square D))) (HomotopyEquivalence.ofIso swapIso)

section BooleanSingleton
open CubicalContractibleTotals CubicalEquivalenceFamilies
variable {Ξ : Context.{0}}

/-- A closed specialization uses the actual native based-path singleton on true,
with its derived sigma/path filling and contraction. -/
noncomputable def booleanSingletonSwap :=
  swapEquivalencePath (forwardTotal (Γ := Ξ))
    (sigmaFilling boolFilling boolFilling_lawful forwardFilling)
    (sigmaFilling_lawful _ boolFilling_lawful _ forwardFilling_lawful)

end BooleanSingleton
end Examples.CubicalEquivalencePaths
