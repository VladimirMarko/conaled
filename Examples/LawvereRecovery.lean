import Examples.LawvereEncoding
import SquareKit.Lawvere.ConcreteRecovery

/-! Checked recovery of operations, morphisms, and nonliteral finite powers. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Examples.LawvereRecovery
open SquareKit SquareKit.Lawvere SquareKit.Lawvere.Operations CategoryTheory CategoryTheory.Limits
open Examples.Lawvere Examples.LawvereEncoding

example : (Recovery.algebra realAction.algebra.model).act negOp (fun _ _ => (3 : ℝ)) 0 = (-3 : ℝ) := by
  rw [Algebra.recovered_act]
  rfl
example : (Recovery.algebra realAction.algebra.model).act zeroOp Fin.elim0 0 = (0 : ℝ) := by
  rw [Algebra.recovered_act]
  rfl
example : (Recovery.algebra boolAction.algebra.model).act
    (Quotient.mk ((unaryPresentation unaryInvolution).setoid 1)
      (UnaryInteraction.term [()])) (fun _ _ => true) 0 = false := by
  rw [Algebra.recovered_act]
  rfl

example {A : Type u} [CommRing A] [Algebra ℝ A] [SmoothAlgebra.Structure A]
    {n} (t : SmoothAlgebra.Operation n) (x : Fin n → A) :
    (Recovery.algebra (smoothAlgebra A).model).act t (fun i _ => x i) 0 = SmoothAlgebra.act t x :=
  Algebra.recovered_act _ _ _

/-- A natural transformation recovers exactly the original smooth homomorphism. -/
example (h : SmoothAlgebra.Hom ℝ ℝ) :
    Algebra.homOfNatTrans (smoothHom h) = smoothAlgebraHom h := by
  apply Algebra.Hom.ext
  rfl

/-- Wrap each whole context, so the model's powers are not literally function types. -/
def wrappedFunctor (A : smoothOperations.Algebra) : smoothOperations.Context ⥤ Type where
  obj n := ULift (Fin n.size → A.Carrier)
  map f := TypeCat.ofHom (fun x => ⟨fun i => A.act (f i) x.down⟩)
  map_id n := by ext x i; exact A.var_act i x.down
  map_comp f g := by ext x i; exact A.subst_act (g i) f x.down

def unwrapIso (A : smoothOperations.Algebra) : wrappedFunctor A ≅ A.toFunctor :=
  NatIso.ofComponents (fun _ => (Equiv.ulift).toIso) (by intro m n f; rfl)

instance (A : smoothOperations.Algebra) : PreservesFiniteProducts (wrappedFunctor A) where
  preserves _ := preservesLimitsOfShape_of_natIso (unwrapIso A).symm

def wrappedModel (A : smoothOperations.Algebra) : Model smoothOperations.theory (Type) :=
  ⟨wrappedFunctor A, (inferInstance : PreservesFiniteProducts (wrappedFunctor A))⟩

/-- Recovery evaluates the original smooth operation through the wrapper. -/
example : ((Recovery.algebra (wrappedModel (smoothAlgebra ℝ))).act
    (smoothOperations.subst (double 0) increment) (fun _ => ⟨fun _ => (3 : ℝ)⟩)).down 0 = (8 : ℝ) := by
  let M := wrappedModel (smoothAlgebra ℝ)
  let x : Fin 1 → Recovery.carrier M := fun _ => ⟨fun _ => (3 : ℝ)⟩
  have h := congrArg (fun y => y.down 0) (Recovery.coordinates_inv_apply M x 0)
  change ((Recovery.coordinates M 1).inv x).down 0 = (3 : ℝ) at h
  let y : ℝ := ((Recovery.coordinates M 1).inv x).down 0
  have hy : y = 3 := h
  change (2 : ℝ) * (y + 1) = 8
  rw [hy]
  norm_num

/-- A constant also survives recovery from the wrapped empty context. -/
example : ((Recovery.algebra (wrappedModel (smoothAlgebra ℝ))).act
    (SmoothAlgebra.constant 0 7) Fin.elim0).down 0 = (7 : ℝ) := rfl

example (M : Model smoothOperations.theory (Type u)) :
    (Recovery.algebra M).model ≅ M := Recovery.modelIso M

/-- The general theorem does not require natural-number objects or literal powers. -/
example (T : Theory.{u,v}) : T.operations.Algebra.{v,w} ≌ Model T (Type w) :=
  T.algebraModelEquivalence
example (T : Theory.{u,v}) (M : Model T (Type w)) :
    T.algebraModelEquivalence.functor.obj M.algebra ≅ M := M.algebraModelIso
example (T : Theory.{u,v}) (M : Model T (Type w)) :
    M.algebra.Carrier = M.toFunctor.obj T.generator := M.algebra_carrier

/-- Two differently tagged copies of every arity give a genuinely nonskeletal theory. -/
abbrev Tagged := InducedCategory smoothOperations.Context
  (Prod.fst : smoothOperations.Context × Bool → smoothOperations.Context)
abbrev forgetTag : Tagged ⥤ smoothOperations.Context := inducedFunctor Prod.fst
instance : forgetTag.IsEquivalence where
  essSurj := ⟨fun n => ⟨(n, false), ⟨Iso.refl _⟩⟩⟩
instance : HasFiniteProducts Tagged where
  out _ := Adjunction.hasLimitsOfShape_of_equivalence forgetTag

def taggedTheory : Theory where
  Obj := Tagged
  category := inferInstance
  products := inferInstance
  generator := (⟨1⟩, false)
  generated X := by
    refine ⟨X.1.size, ⟨forgetTag.preimageIso ?_⟩⟩
    exact (smoothOperations.powerLimit X.1.size).conePointUniqueUpToIso (limit.isLimit _) ≪≫
      (PreservesProduct.iso forgetTag (fun _ : Fin X.1.size => (⟨1⟩, false))).symm

example : ((⟨1⟩, false) : Tagged) ≠ (⟨1⟩, true) := by
  intro h
  have := congrArg Prod.snd h
  cases this
example : @Iso Tagged inferInstance (⟨1⟩, false) (⟨1⟩, true) := forgetTag.preimageIso (X := (⟨1⟩, false)) (Y := (⟨1⟩, true)) (Iso.refl _)
example : taggedTheory.operations.Algebra ≌ Model taggedTheory (Type) :=
  taggedTheory.algebraModelEquivalence
example (M : Model taggedTheory (Type)) :
    taggedTheory.algebraModelEquivalence.functor.obj M.algebra ≅ M := M.algebraModelIso

example : DeMorgan.operations.Context ≌ Cubical.Cube := DeMorgan.cubeEquivalence
example {a b : Cubical.Cube} (f : a ⟶ b) :
    DeMorgan.cubeFunctor.map (X := ⟨a.dimension⟩) (Y := ⟨b.dimension⟩) (DeMorgan.fromCube f) = f := DeMorgan.to_from f
example : Quotient.mk (DeMorgan.termSetoid 1) (.meet (.var 0) (.neg (.var 0))) ≠
    Quotient.mk (DeMorgan.termSetoid 1) .zero := DeMorgan.not_boolean
end Examples.LawvereRecovery
