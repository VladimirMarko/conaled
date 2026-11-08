import Examples.AbstractFIFO
import Applications.Intervals.Arithmetic

/-! #374 compares direct certificates with existing typed registration routes.
No universal annotation engine is introduced. Both clients retain their chosen
implementation result, and the controls distinguish that contract from merely
producing another related result. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Examples.RelationalTransfer
open Relational

/-- Ordinary equality elimination transports any chosen relation witness.
This does not upgrade the representation relation itself to equality. -/
theorem transport_equalities {A B : Type} (R : A → B → Prop)
    {a a' : A} {b b' : B} (ha : a = a') (hb : b = b') (h : R a b) : R a' b' := by
  cases ha
  cases hb
  exact h

/-- The existing witness construction retains the actual implementation value. -/
theorem selected_witness {A B : RelRep} (f : RelSquare A B)
    (x : (witness A).R) : ((witnessSquare f).impl x).val.1 = f.impl x.val.1 := rfl

/-- Certificate composition retains both chosen maps, not an existentially
chosen output. This is a specialization of the existing witness functor law. -/
theorem selected_composition {A B C : RelRep} (f : RelSquare A B) (g : RelSquare B C)
    (x : (witness A).R) :
    (witnessSquare (compose g f)).impl x =
      (witnessSquare g).impl ((witnessSquare f).impl x) := by
  exact congrArg (fun s : Squares.Square (witness A) (witness C) => s.impl x)
    (witness_compose g f)

namespace FIFO
open Sequences.AbstractFIFO Sequences.Symmetric

abbrev Rel := (representation Nat).Rel
abbrev Output (cs : List (Command Nat)) (xs : List Nat) :=
  {q : SymList Nat // Rel q (run (lists Nat) cs xs)}

/-- Direct frozen certificate: exactly the four local operation obligations
from the paper, without using the generic word theorem as a primitive. -/
def direct (q : SymList Nat) (xs : List Nat) (h : Rel q xs) :
    Output Examples.AbstractFIFO.edits xs :=
  ⟨run (symmetric Nat) Examples.AbstractFIFO.edits q, by
    have h1 := (symmetric_correct Nat).snoc 1 _ _ h
    have h2 := (symmetric_correct Nat).snoc 2 _ _ h1
    have h3 := (symmetric_correct Nat).tail _ _ h2
    exact (symmetric_correct Nat).snoc 3 _ _ h3⟩

theorem direct_head (q : SymList Nat) (xs : List Nat) (h : Rel q xs) :
    headSL (direct q xs h).val = (run (lists Nat) Examples.AbstractFIFO.edits xs).head? :=
  (symmetric_correct Nat).head _ _ (direct q xs h).property

/-- Existing primitive registration and source recursion produce the selected
runtime state and a kernel-checked witness for every command word. -/
def registered (cs : List (Command Nat)) (q : SymList Nat) (xs : List Nat)
    (h : Rel q xs) : Output cs xs :=
  ⟨(CategoricalCompiler.compile
      (STLCRelations.target _ (Syntax.primitives (symmetric Nat) Rel (symmetric_correct Nat)))
      (Syntax.program cs)).impl ((), q), by
    have hr := Syntax.compile_preserves (symmetric Nat) Rel (symmetric_correct Nat)
      (Syntax.program cs) (r := ((),q)) (s := ((),xs)) (show True ∧ Rel q xs from ⟨trivial,h⟩)
    have he : CategoricalCompiler.eval (Syntax.meaning (lists Nat)) (Syntax.program cs)
        ((),xs) = run (lists Nat) cs xs := Syntax.eval_plug (lists Nat) cs _ _
    exact transport_equalities Rel rfl he hr⟩

theorem registered_selected (cs : List (Command Nat)) (q : SymList Nat) (xs : List Nat)
    (h : Rel q xs) : (registered cs q xs h).val = run (symmetric Nat) cs q :=
  Syntax.program_runs (symmetric Nat) Rel (symmetric_correct Nat) cs q

theorem direct_registered (q : SymList Nat) (xs : List Nat) (h : Rel q xs) :
    direct q xs h = registered Examples.AbstractFIFO.edits q xs h := by
  apply Subtype.ext
  exact (registered_selected _ _ _ _).symm

/-- The public Option observation uses equality, independently of raw layout. -/
theorem registered_head (cs : List (Command Nat)) (q : SymList Nat) (xs : List Nat)
    (h : Rel q xs) : headSL (registered cs q xs h).val = (run (lists Nat) cs xs).head? :=
  (symmetric_correct Nat).head _ _ (registered cs q xs h).property

/-- Arrow type translation quantifies over related inputs. This actual lambda
exercises abstraction/application rather than treating a whole client theorem
as a registered constant. The word recursor remains Syntax.plug. -/
def functionTerm (cs : List (Command Nat)) :
    CategoricalCompiler.Term (Syntax.Prim Nat) [] (.arr .base .base) :=
  .lam (Syntax.program cs)

theorem registered_function (cs : List (Command Nat)) {q : SymList Nat} {xs : List Nat}
    (h : Rel q xs) :
    Rel (((CategoricalCompiler.compile
      (STLCRelations.target _ (Syntax.primitives (symmetric Nat) Rel (symmetric_correct Nat)))
      (functionTerm cs)).impl ()) q) (run (lists Nat) cs xs) := by
  have hr := STLCRelations.compile_apply_preserves
    (representation Nat) (Syntax.primitives (symmetric Nat) Rel (symmetric_correct Nat))
    (functionTerm cs) (r := ()) (s := ()) trivial h
  have he : CategoricalCompiler.eval (Syntax.meaning (lists Nat)) (Syntax.program cs)
      ((),xs) = run (lists Nat) cs xs := Syntax.eval_plug (lists Nat) cs _ _
  exact transport_equalities Rel rfl he hr

/-- Word composition preserves the exact chosen intermediate state. -/
theorem registered_append (cs ds : List (Command Nat)) (q : SymList Nat) (xs : List Nat)
    (h : Rel q xs) :
    (registered (cs ++ ds) q xs h).val =
      (registered ds (registered cs q xs h).val (run (lists Nat) cs xs)
        (registered cs q xs h).property).val := by
  simp only [registered_selected, run_append]

/-- The middle list is retained as data when composing representation routes;
its value is fixed by execution, not selected from a propositional existence. -/
def routeWitness (cs : List (Command Nat)) (q q' : SymList Nat) (xs : List Nat)
    (h : Rel q xs) (h' : Rel q' xs) :
    {middle : List Nat // Rel (registered cs q xs h).val middle ∧
      Rel (registered cs q' xs h').val middle} :=
  ⟨run (lists Nat) cs xs, (registered cs q xs h).property, (registered cs q' xs h').property⟩

theorem route_middle (cs : List (Command Nat)) (q q' : SymList Nat) (xs : List Nat)
    (h : Rel q xs) (h' : Rel q' xs) :
    (routeWitness cs q q' xs h h').val = run (lists Nat) cs xs := rfl

theorem route_observation (cs : List (Command Nat)) (q q' : SymList Nat) (xs : List Nat)
    (h : Rel q xs) (h' : Rel q' xs) :
    headSL (registered cs q xs h).val = headSL (registered cs q' xs h').val :=
  (registered_head cs q xs h).trans (registered_head cs q' xs h').symm

/-- Pasting the existing word certificates preserves their chosen data. -/
theorem witness_append (cs ds : List (Command Nat))
    (w : (witness (Simulation.representation Rel)).R) :
    (witnessSquare ((symmetric_correct Nat).runSquare (cs ++ ds))).impl w =
      (witnessSquare ((symmetric_correct Nat).runSquare ds)).impl
        ((witnessSquare ((symmetric_correct Nat).runSquare cs)).impl w) := by
  rw [Simulation.runSquare_append]
  exact selected_composition _ _ w

example : headSL (registered Examples.AbstractFIFO.edits Examples.AbstractFIFO.leftLayout
      [1,2,3] Examples.AbstractFIFO.left_related).val =
    headSL (registered Examples.AbstractFIFO.edits Examples.AbstractFIFO.rightLayout
      [1,2,3] Examples.AbstractFIFO.right_related).val :=
  route_observation _ _ _ _ Examples.AbstractFIFO.left_related Examples.AbstractFIFO.right_related

/-- The existing source-substitution recursion remains available after
registration; no new per-word substitution proof is required. -/
example {Γ Δ} (s : CategoricalCompiler.Term.Sub (Syntax.Prim Nat) Γ Δ)
    (cs : List (Command Nat)) (t : CategoricalCompiler.Term (Syntax.Prim Nat) Γ .base) :
    CategoricalCompiler.Term.subst s (Syntax.plug cs t) =
      Syntax.plug cs (CategoricalCompiler.Term.subst s t) := Syntax.subst_plug s cs t

example : (registered Examples.AbstractFIFO.edits nilSL [] ⟨inv_nilSL,rfl⟩).val =
    run (symmetric Nat) Examples.AbstractFIFO.edits nilSL := registered_selected _ _ _ _

example : headSL (registered Examples.AbstractFIFO.edits nilSL [] ⟨inv_nilSL,rfl⟩).val = some 2 :=
  (registered_head _ _ _ _).trans rfl

/-- Relation transport does not supply a total inverse or permit normalization
of every selected raw state. The empty-word client already refutes that claim. -/
theorem no_selected_reset : ¬ ∃ encode : List Nat → SymList Nat,
    ∀ q xs (h : Rel q xs), encode xs = (registered [] q xs h).val := by
  rintro ⟨encode, h⟩
  have hl := h _ _ Examples.AbstractFIFO.left_related
  have hr := h _ _ Examples.AbstractFIFO.right_related
  simp only [registered_selected, run] at hl hr
  exact Examples.AbstractFIFO.hidden_front_length (congrArg (fun q : SymList Nat => q.1.length)
    (hl.symm.trans hr))

/-- Removing the valid-domain condition breaks the unchanged public head. -/
theorem invalid_domain :
    fromSL (([],[1,2]) : SymList Nat) = [2,1] ∧
    headSL (([],[1,2]) : SymList Nat) ≠ ([2,1] : List Nat).head? ∧
    ¬ Inv (([],[1,2]) : SymList Nat) := by
  simp [fromSL, headSL, Sequences.Symmetric.Inv]

/-- Hidden layout observation cannot be registered with equality on Nat. -/
theorem no_layout_registration : ¬ ∃ get : List Nat → Nat,
    ∀ q xs, Rel q xs → q.1.length = get xs := by
  rintro ⟨get, h⟩
  exact Examples.AbstractFIFO.hidden_front_length
    ((h _ _ Examples.AbstractFIFO.left_related).trans
      (h _ _ Examples.AbstractFIFO.right_related).symm)
end FIFO

namespace Interval
open IntervalAnalysis

abbrev Output (x y : ℚ) := {I : Interval // Contains I ((x*y)*(x*y)+x)}

/-- Direct proof of the same shared arithmetic term as the registered route.
The shared product's proof is reused at both occurrences. -/
def direct (I J : Interval) (x y : ℚ) (hx : Contains I x) (hy : Contains J y) : Output x y :=
  ⟨add (mul (mul I J) (mul I J)) I,
    by
      have hxy := mul_contains hx hy
      exact add_contains (mul_contains hxy hxy) hx⟩

def registered (I J : Interval) (x y : ℚ) (hx : Contains I x) (hy : Contains J y) : Output x y :=
  ⟨(IntervalAnalysis.compile Arithmetic.shared).impl ((),(I,J)), shared_contains I J x y hx hy⟩

/-- Unit/product type interpretation and let-sharing preserve the exact interval
chosen by the existing compiler, in addition to point enclosure. -/
theorem direct_registered (I J : Interval) (x y : ℚ) (hx : Contains I x) (hy : Contains J y) :
    direct I J x y hx hy = registered I J x y hx hy := rfl

/-- Composition consumes the same representation relation at the middle type. -/
def negated := compose negSquare (IntervalAnalysis.compile Arithmetic.shared)

theorem negated_contains (I J : Interval) (x y : ℚ) (hx : Contains I x) (hy : Contains J y) :
    Contains (negated.impl ((),(I,J))) (-((x*y)*(x*y)+x)) :=
  negated.preserves (r := ((),(I,J))) (s := ((),(x,y))) ⟨trivial, hx, hy⟩

theorem negated_selected (I J : Interval) (x y : ℚ) (hx : Contains I x) (hy : Contains J y) :
    negated.impl ((),(I,J)) = neg (registered I J x y hx hy).val := rfl

/-- The same generic witness composition used by FIFO works for enclosure,
without introducing a chosen decoder or equality on interval representations. -/
theorem witness_negated
    (w : (witness (FirstOrderRelations.object representation
      (FirstOrderCompiler.context [.prod .base .base]))).R) :
    (witnessSquare negated).impl w =
      (witnessSquare negSquare).impl
        ((witnessSquare (IntervalAnalysis.compile Arithmetic.shared)).impl w) :=
  selected_composition _ _ w

example (I J : Interval) (x y : ℚ) (hx : Contains I x) (hy : Contains J y) :
    ((witnessSquare negated).impl
      ⟨(((),(I,J)),((),(x,y))), ⟨trivial,hx,hy⟩⟩).val.1 = negated.impl ((),(I,J)) :=
  selected_witness _ _

/-- Many points may share one representation, unlike FIFO's functional decode. -/
theorem nonfunctional : Contains unitBox (-1) ∧ Contains unitBox 1 ∧ (-1 : ℚ) ≠ 1 := by
  norm_num [Contains, unitBox]

theorem no_decoder : ¬ ∃ decode : Interval → ℚ,
    ∀ I x, Contains I x → decode I = x := by
  rintro ⟨decode,h⟩
  have he := (h unitBox (-1) nonfunctional.1).symm.trans
    (h unitBox 1 nonfunctional.2.1)
  exact nonfunctional.2.2 he

theorem partial_domain : ¬ ∃ x, Contains (⟨1,0⟩ : Interval) x := by
  rintro ⟨x, h⟩
  obtain ⟨hlo,hhi⟩ := h
  norm_num at hlo hhi
  linarith

/-- An endpoint is not an observation of the represented point. -/
theorem no_endpoint_registration : ¬ ∃ get : ℚ → ℚ,
    ∀ I x, Contains I x → I.lo = get x := by
  rintro ⟨get,h⟩
  have h0 := h (singleton 0) 0 (singleton_contains 0)
  have h1 := h unitBox 0 (by norm_num [Contains,unitBox])
  norm_num [IntervalAnalysis.singleton,unitBox] at h0 h1
  linarith

/-- Resetting to a singleton retains the relation at zero but loses the exact
chosen interval; no output-selection principle follows from Contains alone. -/
theorem selected_reset_fails :
    let out := registered unitBox unitBox 0 0 (by norm_num [Contains,unitBox])
      (by norm_num [Contains,unitBox])
    Contains (singleton 0) ((0*0)*(0*0)+(0 : ℚ)) ∧ out.val ≠ singleton 0 := by
  constructor
  · norm_num [Contains, IntervalAnalysis.singleton]
  · intro h
    have hlo := congrArg Interval.lo h
    rw [← direct_registered] at hlo
    norm_num [direct, add, mul, unitBox, IntervalAnalysis.singleton] at hlo

/-- Semantic equality may be eliminated in a relation witness, but interval
representation equality does not follow from pointwise arithmetic equality. -/
example (x : ℚ) : Contains (singleton (x + -x)) 0 :=
  transport_equalities Contains rfl (point_cancellation x) (singleton_contains (x + -x))

example : add unitBox (neg unitBox) ≠ singleton 0 := interval_cancellation_is_wider.2
end Interval
end Examples.RelationalTransfer
