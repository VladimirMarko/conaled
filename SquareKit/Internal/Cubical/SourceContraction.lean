import SquareKit.Internal.Cubical.CubeContraction
import SquareKit.Internal.Cubical.Naturals

/-! Interpretation of the archived recursive contraction through the constructed
Nat eliminator and interval function operations. X is a fixed presheaf parameter;
this does not interpret the source's universe-polymorphic binder internally. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

abbrev ContractionMethod (X : Context.{u}) (n : ℕ) :=
  total (interval (cubes X n)) ⟶ cubes X n

/-- The source successor body: contract n (c (i meet j)) j. -/
def sourceStepBody (X : Context.{u}) (n : ℕ) (k : ContractionMethod X n) :
    total (interval (total (interval (cubes X (n+1))))) ⟶ cubes X n where
  app I := TypeCat.ofHom (fun z => k.app I
    ⟨z.1.1.apply (Cube.meet z.2.down z.1.2.down), z.1.2⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨c,j⟩,i⟩
    change CubeElement X (n+1) I at c
    change ULift (Cube.Hom I.unop ⟨1⟩) at j i
    have hk := k.naturality_apply f
      ⟨c.apply (Cube.meet i.down j.down), j⟩
    change k.app J ⟨(c.apply (Cube.meet i.down j.down)).restrict f,
      ⟨Cube.comp f.unop j.down⟩⟩ =
        (k.app I ⟨c.apply (Cube.meet i.down j.down),j⟩).restrict f at hk
    change k.app J ⟨(c.restrict f).apply
      (Cube.meet (Cube.comp f.unop i.down) (Cube.comp f.unop j.down)),
      ⟨Cube.comp f.unop j.down⟩⟩ = _
    rw [CubeElement.apply_restrict, Cube.comp_meet] at hk
    exact hk

/-- Abstract i, then use the proved successor-cube isomorphism. -/
def sourceStep (X : Context.{u}) (n : ℕ) (k : ContractionMethod X n) :
    ContractionMethod X (n+1) := cubeLam (sourceStepBody X n k) ≫ cubeUncurry X n

/-- The coordinate construction obeys exactly the source successor body. -/
theorem sourceStepBody_contract (X : Context.{u}) (n : ℕ) :
    sourceStepBody X n (contractCube X n) =
      cubeApp (contractCube X (n+1) ≫ cubeCurry X n) := by
  ext I z
  rcases z with ⟨⟨c,j⟩,i⟩
  change CubeElement X (n+1) I at c
  change ULift (Cube.Hom I.unop ⟨1⟩) at j i
  change (contractCube X n).app I ⟨c.apply (Cube.meet i.down j.down),j⟩ =
    (((contractCube X (n+1)).app I ⟨c,j⟩).restrict (𝟙 I)).apply i.down
  have hi (p : CubeElement X (n+1) I) : p.restrict (𝟙 I) = p := by
    apply CubeElement.ext
    intro J f r
    exact congrArg (fun g => p.val g r) (Category.id_comp f)
  exact (contractCube_apply X n c j.down i.down).symm.trans
    (congrArg (fun p => p.apply i.down) (hi _).symm)

theorem sourceStep_contract (X : Context.{u}) (n : ℕ) :
    sourceStep X n (contractCube X n) = contractCube X (n+1) := by
  unfold sourceStep
  rw [sourceStepBody_contract, cubeLam_app, Category.assoc, cubeCurry_uncurry, Category.comp_id]

/-- The zero source body is reflexivity, interpreted as projection off j. -/
theorem sourceZero_contract (X : Context.{u}) :
    projection (interval (cubes X 0)) = contractCube X 0 := by
  ext I z
  exact (contractCube_dimension_zero X z.1 z.2.down).symm

/-- The recursion motive consists of natural contraction operations at n.
It is a family of global semantic operations; realization applies the resulting
operation at each cube, to its c and j arguments. -/
abbrev methodFamily (X : Context.{u}) : Family (total (natFamily terminal.{u})) where
  obj e := ContractionMethod X e.val.2.down
  map {_x y} f := TypeCat.ofHom (cast (congrArg (ContractionMethod X)
    (congrArg (fun z : (total (natFamily terminal.{u})).obj y.obj => z.2.down) f.map_val)))
  map_id _ := rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro k
    exact (cast_cast _ _ k).symm

def sourceZero (X : Context.{u}) :
    Term (reindex (methodFamily X) (pair (𝟙 terminal) (natZero terminal))) where
  val _ := projection (interval (cubes X 0))
  property _ := rfl

def sourceSuccessor (X : Context.{u}) : NatStep (methodFamily X) where
  val _ n k := sourceStep X n k
  naturality _ _ _ := rfl

/-- The selected source recursion uses the constructed dependent eliminator. -/
def sourceRecursion (X : Context.{u}) : Term (methodFamily X) :=
  natElim (sourceZero X) (sourceSuccessor X)

/-- Realize the closed natural-number argument in the global operation family. -/
def interpretedContraction (X : Context.{u}) (n : ℕ) : ContractionMethod X n :=
  (sourceRecursion X).val ((total (natFamily terminal.{u})).elementsMk
    (Opposite.op ⟨0⟩) ⟨PUnit.unit, ⟨n⟩⟩)

theorem interpretedContraction_zero (X : Context.{u}) :
    interpretedContraction X 0 = projection (interval (cubes X 0)) := by
  have h := congrArg (fun t : Term (reindex (methodFamily X)
    (pair (𝟙 terminal) (natZero terminal))) =>
      t.val (terminal.elementsMk (Opposite.op ⟨0⟩) PUnit.unit))
      (natElim_zero (sourceZero X) (sourceSuccessor X))
  exact h

theorem interpretedContraction_successor (X : Context.{u}) (n : ℕ) :
    interpretedContraction X (n+1) = sourceStep X n (interpretedContraction X n) :=
  natElim_succ (sourceZero X) (sourceSuccessor X)
    (terminal.elementsMk (Opposite.op ⟨0⟩) PUnit.unit) n

/-- The interpreted recursion is the coordinate contraction, by its actual
zero/successor computation rules and the checked source binding equation. -/
theorem interpretedContraction_eq (X : Context.{u}) (n : ℕ) :
    interpretedContraction X n = contractCube X n := by
  induction n with
  | zero => exact (interpretedContraction_zero X).trans (sourceZero_contract X)
  | succ n ih =>
    rw [interpretedContraction_successor, ih]
    exact sourceStep_contract X n

/-- Path abstraction realizes the result of the interpreted source recursion. -/
def interpretedContractionPath (X : Context.{u}) (n : ℕ) :
    Term (path (Functor.Elements.π (total (interval (cubes X n))) ⋙ cubes X n)
      (transformationTerm (cubeOrigin X n ≫ constantCube X n))
      (transformationTerm (𝟙 (cubes X n)))) :=
  pathLam (transformationTerm (interpretedContraction X n))
    (by rw [interpretedContraction_eq]; exact congrArg transformationTerm (contractCube_zero X n))
    (by rw [interpretedContraction_eq]; exact congrArg transformationTerm (contractCube_one X n))

theorem interpretedContractionPath_eq (X : Context.{u}) (n : ℕ) :
    interpretedContractionPath X n = cubeContraction X n := by
  apply Term.ext
  intro x
  apply Subtype.ext
  apply PiElement.ext
  intro y f a
  exact congrArg (fun k : ContractionMethod X n => k.app y.obj ⟨y.val,a⟩)
    (interpretedContraction_eq X n)

/-- The global-operation recursion can be realized at any base cube. -/
theorem sourceRecursion_at (X : Context.{u}) (n : ℕ) (x : terminal.{u}.Elements) :
    (sourceRecursion X).val (extendObj (natFamily terminal) x ⟨n⟩) =
      interpretedContraction X n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (sourceStep X n) ih

end SquareKit.Cubical.Presheaf
