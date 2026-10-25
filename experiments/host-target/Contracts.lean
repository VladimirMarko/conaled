import SquareKit.Internal.GraphEmissionContract
import SquareKit.Internal.GraphEmissionTyping
import Squares

/-!
Experimental contracts for the six-constructor graph core sublanguage.
`Annotated` models the old ConLeche binder shape restricted to `pw = .never`;
`CoreSyntax.Expr` models its metadata-free shape. Names and levels still use
host Lean data. These local interpretations do not assert upstream typing,
annotation validity, set denotation, or checker acceptance. See the research note.
-/
namespace HostTarget
open SquareKit.Internal
open GraphEmissionPure
abbrev Core := CoreSyntax.Expr

/-- The selected old annotation, not Lean's display `BinderInfo`. -/
inductive Never where
  | never
  deriving DecidableEq

inductive Annotated where
  | bvar : Nat → Annotated
  | sort : Lean.Level → Annotated
  | const : Lean.Name → List Lean.Level → Annotated
  | app : Annotated → Annotated → Annotated
  | lam : Annotated → Annotated → Never → Annotated
  | all : Annotated → Annotated → Never → Annotated

def erase : Annotated → Core
  | .bvar n => .bvar n
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f x => .app (erase f) (erase x)
  | .lam a b _ => .lam (erase a) (erase b)
  | .all a b _ => .all (erase a) (erase b)

def annotate : Core → Annotated
  | .bvar n => .bvar n
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f x => .app (annotate f) (annotate x)
  | .lam a b => .lam (annotate a) (annotate b) .never
  | .all a b => .all (annotate a) (annotate b) .never

@[simp] theorem erase_annotate (e : Core) : erase (annotate e) = e := by
  induction e <;> simp_all [annotate, erase]

@[simp] theorem annotate_erase (e : Annotated) : annotate (erase e) = e := by
  induction e with
  | lam a b m ha hb | all a b m ha hb => cases m; simp_all [annotate, erase]
  | _ => simp_all [annotate, erase]

/-- Observation is supplied by the client; equality of syntax alone is not a model. -/
def annotatedRep {α : Type} (observe : Core → α) : Squares.Rep where
  R := Annotated
  S := α
  decode e := observe (erase e)

def coreRep {α : Type} (observe : Core → α) : Squares.Rep where
  R := Core
  S := α
  decode := observe

def erasureSquare {α : Type} (observe : Core → α) :
    Squares.Square (annotatedRep observe) (coreRep observe) where
  impl := erase
  spec := id
  commutes _ := rfl

/-- Reuse any downstream square without imposing its observation on other clients. -/
def throughErasure {α : Type} {B : Squares.Rep}
    (observe : Core → α) (next : Squares.Square (coreRep observe) B) :=
  Squares.compose next (erasureSquare observe)

/-- Capture-avoiding substitution comes from the existing binder implementation. -/
def contractOld (body arg : Annotated) : Annotated :=
  annotate (CoreSyntax.instantiate (erase body) (erase arg))

def contractNew := CoreSyntax.instantiate

/-- The `.never` beta branch shares this reduct after erasure. This does not
model the old alternative beta rule with an argument-typing certificate. -/
theorem beta_reduct (body arg : Annotated) :
    erase (contractOld body arg) = contractNew (erase body) (erase arg) := by
  simp [contractOld, contractNew]

/-- A binder-sensitive case: substituting the outer argument beneath a lambda
must keep its formerly free variable free, now at index one. -/
example : erase (contractOld
    (.lam (.sort .zero) (.bvar 1) .never) (.bvar 0)) =
    .lam (.sort .zero) (.bvar 1) := by
  rw [beta_reduct]
  rfl

/-- Distinct universe data survives the two conversions. -/
example : erase (annotate (.sort (.succ .zero))) ≠
    erase (annotate (.sort .zero)) := by
  simp

/-- Compose the erasure square with the existing exact conversion to Lean.Expr. -/
def leanRep : Squares.Rep where
  R := Lean.Expr
  S := Core
  decode e := (CoreSyntax.Expr.ofLean e).getD (.bvar 0)

def leanSquare : Squares.Square (coreRep id) leanRep where
  impl := CoreSyntax.Expr.toLean
  spec := id
  commutes e := by
    change Core at e
    change (CoreSyntax.Expr.ofLean (CoreSyntax.Expr.toLean e)).getD (.bvar 0) = e
    rw [CoreSyntax.Expr.ofLean_toLean]
    rfl

example (e : Annotated) :
    leanRep.decode ((throughErasure id leanSquare).impl e) = erase e :=
  (throughErasure id leanSquare).commutes e

/-- The same local graph meaning and typing can be reused for the old-shaped
encoding. These are the repository's contracts, not ConLeche's judgments. -/
theorem graph_contract (d : GraphTarget.Declaration) :
    CoreSyntax.HasType [] (erase (annotate (emitCore d).2))
      (erase (annotate (emitCore d).1)) ∧
    ClosedDenotes.{0} (erase (annotate (emitCore d).1))
      (erase (annotate (emitCore d).2)) (GraphTarget.Declaration.denote.{0} d) := by
  simp only [erase_annotate]
  exact ⟨emitCore_typed d, emitCore_denotes.{0} d⟩

/-- Retain the actual forward graph consumer; there is no upstream-acceptance premise. -/
example : CoreSyntax.HasType []
    (erase (annotate (emitCore GraphTarget.forwardDeclaration).2))
    (erase (annotate (emitCore GraphTarget.forwardDeclaration).1)) :=
  (graph_contract GraphTarget.forwardDeclaration).1

example : GraphTarget.Declaration.denote.{0} GraphTarget.forwardDeclaration :=
  (graph_contract GraphTarget.forwardDeclaration).2.sound

end HostTarget
