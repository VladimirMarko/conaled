import Applications.Sequences.AbstractFIFOSyntax
import SquareKit.STLCSignature

/-! A public FIFO operation extends the existing signature. The old client
contract is recovered without a new syntax induction or stronger invariant. -/
namespace Sequences.AbstractFIFO.Extension
open CategoricalCompiler SquareKit
variable {α Q R : Type}

/-- Move the first element to the back; an empty queue is unchanged. -/
def rotate (ops : Ops α Q) (q : Q) : Q :=
  match ops.head q with
  | none => q
  | some x => ops.snoc x (ops.tail q)

theorem rotate_related {a : Ops α Q} {b : Ops α R} {rel : Q → R → Prop}
    (h : Simulation a b rel) {q r} (hr : rel q r) :
    rel (rotate a q) (rotate b r) := by
  unfold rotate
  rw [h.head q r hr]
  cases b.head r with
  | none => exact hr
  | some x => exact h.snoc x _ _ (h.tail q r hr)

inductive New : Ty → Ty → Type where
  | rotate : New .base .base

abbrev Prim (α : Type) := STLCSignature.Add (Syntax.Prim α) New

def meaning (ops : Ops α Q) : {a b : Ty} → Prim α a b → Val Q a → Val Q b
  | _, _, .inl p => Syntax.meaning ops p
  | _, _, .inr .rotate => rotate ops

def primitives (ops : Ops α Q) (rel : Q → List α → Prop)
    (h : Simulation ops (lists α) rel) :
    STLCRelations.Primitives ⟨Q,List α,rel⟩ (Prim α) (meaning (lists α)) where
  impl p := match p with
    | .inl p => (Syntax.primitives ops rel h).impl p
    | .inr .rotate => rotate ops
  correct p := by
    cases p with
    | inl p => exact (Syntax.primitives ops rel h).correct p
    | inr p => cases p; exact rotate_related h

/-- Restriction recovers the original target, not only its final observation. -/
theorem old_target (ops : Ops α Q) (rel : Q → List α → Prop)
    (h : Simulation ops (lists α) rel) :
    STLCSignature.restrictTarget Sum.inl (STLCRelations.target _ (primitives ops rel h)) =
      STLCRelations.target _ (Syntax.primitives ops rel h) := rfl

/-- Every old term retains its compiled representation. -/
theorem old_compile (ops : Ops α Q) (rel : Q → List α → Prop)
    (h : Simulation ops (lists α) rel) (t : Term (Syntax.Prim α) Γ a) :
    compile (STLCRelations.target _ (primitives ops rel h)) (STLCSignature.map Sum.inl t) =
      compile (STLCRelations.target _ (Syntax.primitives ops rel h)) t := by
  exact STLCSignature.compile_target Sum.inl _ t

/-- Recover the established old client theorem under exactly its old premises. -/
theorem old_observe (ops : Ops α Q) (rel : Q → List α → Prop)
    (h : Simulation ops (lists α) rel) (cs : List (Command α)) {q xs}
    (related : rel q xs) :
    ops.head ((compile (STLCRelations.target _ (primitives ops rel h))
      (STLCSignature.map Sum.inl (Syntax.program cs))).impl ((),q)) =
      client (lists α) cs xs := by
  rw [old_compile]
  exact Syntax.observe_program ops rel h cs related

/-- A new client uses rotate on a bound input, then the old word client. -/
def program (cs : List (Command α)) : Term (Prim α) [.base] .base :=
  .letE (.prim (.inr .rotate) (.var .here))
    (STLCSignature.map Sum.inl (Syntax.plug cs (.var .here)))

theorem eval_program (cs : List (Command α)) (xs : List α) :
    eval (meaning (lists α)) (program cs) ((),xs) =
      run (lists α) cs (rotate (lists α) xs) := by
  unfold program eval
  rw [STLCSignature.eval_map]
  exact Syntax.eval_plug (lists α) cs (.var .here) _

/-- The existing fundamental theorem proves the extended client's observation. -/
theorem observe (ops : Ops α Q) (rel : Q → List α → Prop)
    (h : Simulation ops (lists α) rel) (cs : List (Command α)) {q xs}
    (related : rel q xs) :
    ops.head ((compile (STLCRelations.target _ (primitives ops rel h)) (program cs)).impl ((),q)) =
      client (lists α) cs (rotate (lists α) xs) := by
  apply h.head
  have hp := STLCRelations.compile_preserves _ (primitives ops rel h) (program cs)
    (r := ((),q)) (s := ((),xs)) (show True ∧ rel q xs from ⟨trivial, related⟩)
  change rel _ (eval (meaning (lists α)) (program cs) ((),xs)) at hp
  rw [eval_program] at hp
  exact hp

/-- Shared observations survive the extension for two representations of one list. -/
theorem representation_independent (ops : Ops α Q) (rel : Q → List α → Prop)
    (h : Simulation ops (lists α) rel) (cs : List (Command α)) {q q' xs}
    (hq : rel q xs) (hq' : rel q' xs) :
    ops.head ((compile (STLCRelations.target _ (primitives ops rel h)) (program cs)).impl ((),q)) =
    ops.head ((compile (STLCRelations.target _ (primitives ops rel h)) (program cs)).impl ((),q')) :=
  (observe ops rel h cs hq).trans (observe ops rel h cs hq').symm

/-- The generic extension theorem discharges all unchanged structural fields. -/
theorem interpretation_preserves (ops : Ops α Q) (rel : Q → List α → Prop)
    (h : Simulation ops (lists α) rel) :
    STLCNaturality.Preserves (STLCRelations.interpretation _ (primitives ops rel h))
      (equality _)
      (STLCNaturality.ofTarget (STLCRelations.target _ (primitives ops rel h)))
      (STLCNaturality.semantics (List α) (meaning (lists α))) := by
  have hext := STLCSignature.preserves_extend
    (STLCRelations.interpretation_preserves _ (Syntax.primitives ops rel h))
    (fun p => (STLCRelations.target _ (primitives ops rel h)).primitive (.inr p))
    (fun p => meaning (lists α) (.inr p))
    (by intro a b p; cases p; rfl)
  refine { hext with primitive := ?_ }
  intro a b p
  cases p with
  | inl p => exact hext.primitive (.inl p)
  | inr p => exact hext.primitive (.inr p)

/-- Extension followed by the existing inclusion and semantic projection agrees
with direct evaluation. Composition uses the shared naturality theorem. -/
theorem composed_interpretation (ops : Ops α Q) (rel : Q → List α → Prop)
    (h : Simulation ops (lists α) rel) (t : Term (Prim α) Γ a) :
    RelationalCategory.semantics.map
      ((STLCRelations.inclusion _ (primitives ops rel h)).map
        (compile (STLCRelations.target _ (primitives ops rel h)) t)) =
      eval (meaning (lists α)) t := by
  apply funext
  intro ρ
  have ht := STLCNaturality.naturality
    (STLCRelations.interpretation_laws _ (primitives ops rel h)) (equalityCongr _)
    (show STLCNaturality.ModelCongr (equality _)
      (STLCNaturality.semantics (List α) (meaning (lists α))) from
      ⟨by intros; subst_vars; rfl, by intros; subst_vars; rfl, by intros; subst_vars; rfl⟩)
    (interpretation_preserves ops rel h) t
  have hp := congrFun ht ρ
  rw [STLCNaturality.compile_ofTarget] at hp
  exact hp.trans (STLCNaturality.semantics_compile (List α) (meaning (lists α)) t ρ)

end Sequences.AbstractFIFO.Extension
