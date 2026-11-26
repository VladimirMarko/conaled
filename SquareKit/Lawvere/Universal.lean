import SquareKit.Lawvere.Presentations
import SquareKit.Lawvere.Comparison

/-! # Universal properties of unconditional equational presentations

Symbol assignments extend uniquely to maps of operations. Models and their
homomorphisms correspond to categorical models through algebra recovery.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SquareKit.Lawvere
open CategoryTheory
universe u v w z
namespace Presentation
variable (P : Presentation.{u})
def symbol (s : P.Symbol) : P.operations.Op (P.arity s) :=
  Quotient.mk _ (.node s FinitaryTerm.leaf)

theorem mk_bind {m n} (t : P.Term n) (σ : Fin n → P.Term m) :
    (Quotient.mk (P.setoid m) (t.bind σ)) =
      P.operations.subst (Quotient.mk _ t) (fun i => Quotient.mk _ (σ i)) := by
  apply Quotient.sound
  exact P.bind_congr t _ _ (fun i => .symm (Quotient.exact (Quotient.out_eq (Quotient.mk (P.setoid m) (σ i)))))

theorem mk_node {n} (s : P.Symbol) (ts : Fin (P.arity s) → P.Term n) :
    (Quotient.mk (P.setoid n) (.node s ts)) =
      P.operations.subst (P.symbol s) (fun i => Quotient.mk _ (ts i)) :=
  P.mk_bind (.node s FinitaryTerm.leaf) ts

structure Assignment (O : Operations.{v}) where
  op : (s : P.Symbol) → O.Op (P.arity s)
  laws : ∀ e, P.evaluate op (P.lhs e) = P.evaluate op (P.rhs e)

namespace Assignment
@[ext] theorem ext {O : Operations.{v}} {a b : P.Assignment O} (h : a.op = b.op) : a = b := by
  cases a; cases b; cases h; rfl
end Assignment

theorem map_mk {O : Operations.{v}} (F : P.operations.Map O) {n} (t : P.Term n) :
    F.map (Quotient.mk _ t) = P.evaluate (fun s => F.map (P.symbol s)) t := by
  induction t with
  | leaf i => exact F.map_var i
  | node s ts ih =>
    rw [P.mk_node, F.map_subst]
    exact congrArg (O.subst (F.map (P.symbol s))) (funext ih)

def assignment {O : Operations.{v}} (F : P.operations.Map O) : P.Assignment O where
  op s := F.map (P.symbol s)
  laws e := by
    rw [← P.map_mk F, ← P.map_mk F]
    exact congrArg F.map (Quotient.sound (.equation e))

@[simp] theorem interpretation_symbol {O : Operations.{v}} (a : P.Assignment O) (s : P.Symbol) :
    (P.interpretation a.op a.laws).map (P.symbol s) = a.op s := O.subst_var _

def assignmentEquiv (O : Operations.{v}) : P.Assignment O ≃ P.operations.Map O where
  toFun a := P.interpretation a.op a.laws
  invFun := P.assignment
  left_inv a := by
    apply Assignment.ext
    funext s
    exact P.interpretation_symbol a s
  right_inv F := by
    apply Operations.Map.ext
    intro n t
    refine Quotient.inductionOn t ?_
    intro t
    exact (P.map_mk F t).symm

theorem interpretation_unique {O : Operations.{v}} (a : P.Assignment O)
    (F : P.operations.Map O) (h : ∀ s, F.map (P.symbol s) = a.op s) :
    F = P.interpretation a.op a.laws := by
  apply (P.assignmentEquiv O).symm.injective
  apply Assignment.ext
  funext s
  exact (h s).trans (P.interpretation_symbol a s).symm

/-- A carrier with primitive operations satisfying the unconditional equations. -/
structure EquationModel where
  Carrier : Type w
  operation : (s : P.Symbol) → (Fin (P.arity s) → Carrier) → Carrier
  laws : ∀ e (x : Fin (P.variableCount e) → Carrier),
    FinitaryTerm.fold operation x (P.lhs e) = FinitaryTerm.fold operation x (P.rhs e)

namespace EquationModel
variable {P}
structure Hom (A B : P.EquationModel.{u,w}) where
  toFun : A.Carrier → B.Carrier
  operation : ∀ s x, toFun (A.operation s x) = B.operation s (fun i => toFun (x i))

@[ext] theorem Hom.ext {A B : P.EquationModel.{u,w}} {f g : Hom A B}
    (h : f.toFun = g.toFun) : f = g := by cases f; cases g; cases h; rfl

instance : Category P.EquationModel.{u,w} where
  Hom := Hom
  id _ := ⟨id, fun _ _ => rfl⟩
  comp f g := ⟨g.toFun ∘ f.toFun, fun s x => by
    change g.toFun (f.toFun (EquationModel.operation _ s x)) = _
    rw [f.operation, g.operation]
    rfl⟩

def toGuarded (A : P.EquationModel.{u,w}) : GuardedTheory.Model P.guarded where
  Carrier := A.Carrier
  operation := A.operation
  Predicate := fun p => nomatch p
  rules e x _ := A.laws e x

def toAlgebra (A : P.EquationModel.{u,w}) : P.operations.Algebra := P.algebra A.toGuarded

theorem Hom.fold {A B : P.EquationModel.{u,w}} (h : A ⟶ B) {n} (t : P.Term n)
    (x : Fin n → A.Carrier) :
    h.toFun (FinitaryTerm.fold A.operation x t) =
      FinitaryTerm.fold B.operation (fun i => h.toFun (x i)) t := by
  induction t with
  | leaf => rfl
  | node s ts ih =>
    change h.toFun (A.operation s _) = _
    rw [h.operation]
    exact congrArg (B.operation s) (funext ih)

def algebraFunctor : P.EquationModel.{u,w} ⥤ P.operations.Algebra.{u,w} where
  obj := toAlgebra
  map h := ⟨h.toFun, fun t x => by
    refine Quotient.inductionOn t ?_
    intro t
    exact h.fold t x⟩

end EquationModel

theorem act_mk (A : P.operations.Algebra.{u,w}) {n} (t : P.Term n)
    (x : Fin n → A.Carrier) :
    A.act (Quotient.mk _ t) x =
      FinitaryTerm.fold (fun s => A.act (P.symbol s)) x t := by
  induction t with
  | leaf i => exact A.var_act i x
  | node s ts ih =>
    rw [P.mk_node, A.subst_act]
    exact congrArg (A.act (P.symbol s)) (funext ih)

def equationModel (A : P.operations.Algebra.{u,w}) : P.EquationModel.{u,w} where
  Carrier := A.Carrier
  operation s := A.act (P.symbol s)
  laws e x := by
    rw [← P.act_mk, ← P.act_mk]
    exact congrArg (fun t => A.act t x) (Quotient.sound (.equation e))

def equationModelFunctor : P.operations.Algebra.{u,w} ⥤ P.EquationModel.{u,w} where
  obj := P.equationModel
  map h := ⟨h.toFun, fun s x => h.map_act (P.symbol s) x⟩

/-- The primitive-operation round trip retains the carrier and every homomorphism. -/
def equationUnitIso : 𝟭 P.EquationModel.{u,w} ≅
    EquationModel.algebraFunctor ⋙ P.equationModelFunctor :=
  NatIso.ofComponents (fun A =>
    { hom := ⟨id, fun _ _ => rfl⟩
      inv := ⟨id, fun _ _ => rfl⟩
      hom_inv_id := by rfl
      inv_hom_id := by rfl }) (by intro A B h; rfl)

def equationCounitIso : P.equationModelFunctor ⋙ EquationModel.algebraFunctor ≅
    𝟭 P.operations.Algebra.{u,w} :=
  NatIso.ofComponents (fun A =>
    { hom := ⟨id, fun t x => by
        refine Quotient.inductionOn t ?_
        intro t
        exact (P.act_mk A t x).symm⟩
      inv := ⟨id, fun t x => by
        refine Quotient.inductionOn t ?_
        intro t
        exact P.act_mk A t x⟩
      hom_inv_id := by rfl
      inv_hom_id := by rfl }) (by intro A B h; rfl)

def equationAlgebraEquivalence : P.EquationModel.{u,w} ≌ P.operations.Algebra.{u,w} :=
  CategoryTheory.Equivalence.mk EquationModel.algebraFunctor P.equationModelFunctor
    P.equationUnitIso P.equationCounitIso

/-- Models of the equations correspond to categorical models, including their maps. -/
def equationModelEquivalence : P.EquationModel.{u,w} ≌ Model P.operations.theory (Type w) :=
  P.equationAlgebraEquivalence.trans Operations.Algebra.modelEquivalence

/-- Interpret into a possibly nonskeletal theory using its chosen finite powers. -/
def categoricalInterpretation {T : Theory.{v,z}} (a : P.Assignment T.operations) :
    Hom P.operations.theory T :=
  Hom.comp (P.interpretation a.op a.laws).theoryHom T.skeletonHom

def categoricalAssignment {T : Theory.{v,z}} (F : Hom P.operations.theory T) :
    P.Assignment T.operations := P.assignment (Operations.operationMap F)

@[simp] theorem categorical_recovery {T : Theory.{v,z}} (a : P.Assignment T.operations) :
    P.categoricalAssignment (P.categoricalInterpretation a) = a := by
  unfold categoricalAssignment categoricalInterpretation
  rw [Operations.operationMap_canonical]
  exact (P.assignmentEquiv T.operations).left_inv a

/-- Uniqueness in a nonskeletal target is a natural isomorphism of interpretations. -/
def categoricalUniqueness {T : Theory.{v,z}} (a : P.Assignment T.operations)
    (F : Hom P.operations.theory T) (h : P.categoricalAssignment F = a) :
    F.toFunctor ≅ (P.categoricalInterpretation a).toFunctor := by
  have hf : Operations.operationMap F = P.interpretation a.op a.laws := by
    apply P.interpretation_unique
    intro s
    exact congrArg (fun b : P.Assignment T.operations => b.op s) h
  exact Operations.normalizationIso F ≪≫
    eqToIso (congrArg (fun φ : P.operations.Map T.operations => φ.toFunctor ⋙ T.skeletonFunctor) hf)

/-- The uniqueness comparison also preserves the specified generator isomorphism. -/
theorem categoricalUniqueness_generator {T : Theory.{v,z}} (a : P.Assignment T.operations)
    (F : Hom P.operations.theory T) (h : P.categoricalAssignment F = a) :
    (P.categoricalUniqueness a F h).hom.app ⟨1⟩ ≫
      (P.categoricalInterpretation a).generatorIso.hom = F.generatorIso.hom := by
  simp only [categoricalUniqueness, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app, Category.assoc]
  simpa only [categoricalInterpretation, Operations.canonical_generator,
    eqToHom_refl, Category.id_comp] using Operations.normalization_generator F

/-- Any equivalent categorical presentation has the same model category. -/
def equationModelEquivalenceOfEquivalence (T : Theory.{v,z})
    (e : P.operations.Context ≌ T.Obj) : P.EquationModel.{u,w} ≌ Model T (Type w) :=
  P.equationModelEquivalence.trans (Model.precomposeEquivalence e).symm

end Presentation
end SquareKit.Lawvere
