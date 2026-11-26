import Applications.Resources.RotationCertificate.MoveApplyMachine
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.IntervalCases

/-!
# Connected clients of the physical move-parser and positioned-rotation join

These expectations were fixed before implementation. They distinguish the
internal parser result, the paid dispatch, the first whole live result, and
later caller activations. Both protected alphabets, dirty stores, original
registers at time zero, source observations, and actual physical cells remain
visible in the client contracts.

The fixture literals are retained independently of the producer's proof-side
endpoint evaluator. Actual compilation and audit evidence is recorded separately
from these fixed contracts.
-/

namespace Examples.RotationCertificateMoveApplyMachine

open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)

open Resources.RotationCertificate.MoveApplyMachine

def AuthorAlphabet : Fin 2 → Type := Fin.cases Tag (fun _ => Unit)
def IndependentAlphabet : Fin 2 → Type := Fin.cases Bool (fun _ => Tag)

instance authorAlphabetFintype (k : Fin 2) : Fintype (AuthorAlphabet k) :=
  Fin.cases (motive := fun k : Fin 2 => Fintype (AuthorAlphabet k))
    (inferInstance : Fintype Tag) (fun _ => (inferInstance : Fintype Unit)) k

instance independentAlphabetFintype (k : Fin 2) : Fintype (IndependentAlphabet k) :=
  Fin.cases (motive := fun k : Fin 2 => Fintype (IndependentAlphabet k))
    (inferInstance : Fintype Bool) (fun _ => (inferInstance : Fintype Tag)) k

def authorWords (tags : Word) (units : List Unit) :
    ∀ k, List (AuthorAlphabet k) := Fin.cases tags (fun _ => units)
def independentWords (bits : List Bool) (tags : Word) :
    ∀ k, List (IndependentAlphabet k) := Fin.cases bits (fun _ => tags)

def authorContext : ∀ k, List (AuthorAlphabet k) :=
  authorWords [15, 2, 7, 10, 3] [(), ()]
def independentContext : ∀ k, List (IndependentAlphabet k) :=
  independentWords [true, false, true] [11, 15]

def stale (flag : Bool) : Registers Bool :=
  ((some .right, (some (15 : Tag), some ())), flag)
def clean (flag : Bool) : Registers Bool := ((none, (none, none)), flag)

abbrev ExampleCfg := Cfg IndependentAlphabet Unit Bool
abbrev ExampleCaller := External Unit → Statement IndependentAlphabet Unit Bool
abbrev AuthorCfg := Cfg AuthorAlphabet Unit Bool
abbrev AuthorCaller := External Unit → Statement AuthorAlphabet Unit Bool

def parseFailure : FinalResult := .inl ()
def rotationFailure : FinalResult := .inr .failure
def rotationSuccess : FinalResult := .inr .success

def movePhase (q : MoveParserMachine.Phase) : Phase := .inl q
def dispatchPhase (r : MoveParserMachine.Result) : Phase := .inr (.inl r)
def positionPhase (q : PositionedRotationMachine.Phase) : Phase := .inr (.inr q)

def data (C : Word) (B O : List Branch) (X F S : Word)
    (Hd : List Unit) : LocalData :=
  { certificate := C, moveReverse := B, path := O,
    source := X, saved := F, scratch := S, pending := Hd }

def atPhase (q : Phase) (flag : Bool) (D : LocalData) : ExampleCfg :=
  cfg (some (phaseLabel q)) (stale flag) D independentContext
def atResult (r : FinalResult) (flag : Bool) (D : LocalData) : ExampleCfg :=
  cfg (some (resultLabel r)) (clean flag) D independentContext

def nilTree : BinaryTree Unit := .nil
def oneTree : BinaryTree Unit := .node () nilTree nilTree
def rightTwo : BinaryTree Unit := .node () nilTree oneTree
def leftTwo : BinaryTree Unit := .node () oneTree nilTree
def leftContext : BinaryTree Unit := .node () rightTwo nilTree
def twoRightTwos : BinaryTree Unit := .node () rightTwo rightTwo
def nestedRight : BinaryTree Unit := .node () (.node () nilTree rightTwo) nilTree
def nestedLeft : BinaryTree Unit := .node () (.node () nilTree leftTwo) nilTree

def Runs {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (start : Cfg Γ Λ R)
    (ticks : Nat) (finish : Cfg Γ Λ R) : Prop :=
  (next caller)^[ticks] (some start) = some finish

def FirstRun {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (start : Cfg Γ Λ R)
    (ticks : Nat) (finish : Cfg Γ Λ R) : Prop :=
  Runs caller start ticks finish ∧ ¬ Owned finish.l ∧
    ∀ n, n < ticks → ∃ reached, Runs caller start n reached ∧ Owned reached.l

def FirstResult {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (start : Cfg Γ Λ R)
    (r : FinalResult) : Prop :=
  ∃ ticks finish, FirstRun caller start ticks finish ∧
    finish.l = some (resultLabel r)

structure RunFixture where
  phase : Phase
  before : LocalData
  result : FinalResult
  after : LocalData
  ticks : Nat

def RunFixture.Expected (c : RunFixture) (caller : ExampleCaller)
    (flag : Bool) : Prop :=
  FirstRun caller (atPhase c.phase flag c.before) c.ticks
    (atResult c.result flag c.after)

inductive RegisterStage
  | original | parser | complete

def RegisterStage.apply {R : Type} (stage : RegisterStage)
    (regs : Registers R) : Registers R :=
  match stage with
  | .original => regs
  | .parser => resetMove regs
  | .complete => reset regs

structure Boundary where
  tick : Nat
  control : Phase ⊕ FinalResult
  stores : LocalData
  stage : RegisterStage
  cells : Nat
  creditCells : Nat

def boundaryLabel {Λ : Type} (control : Phase ⊕ FinalResult) : Label Λ :=
  match control with
  | .inl q => phaseLabel q
  | .inr r => resultLabel r

def leftBoundaries : List Boundary :=
  [ ⟨0, .inl (movePhase .start), data [6,10,15] [] [] [1,0,1,15] [] [] [], .original, 7, 11⟩,
    ⟨1, .inl (movePhase (.scan .left)), data [10,15] [] [] [1,0,1,15] [] [] [], .parser, 6, 11⟩,
    ⟨2, .inl (movePhase (.emit .left)), data [15] [] [] [1,0,1,15] [] [] [], .parser, 5, 11⟩,
    ⟨3, .inl (dispatchPhase (.success .left)), data [15] [] [] [1,0,1,15] [] [] [], .parser, 5, 11⟩,
    ⟨4, .inl (positionPhase (.seek .left)), data [15] [] [] [1,0,1,15] [] [] [], .complete, 5, 9⟩,
    ⟨5, .inl (positionPhase (.start .left)), data [15] [] [] [1,0,1,15] [] [] [], .complete, 5, 9⟩,
    ⟨6, .inl (positionPhase (.scanScratch .left)), data [15] [] [] [0,1,15] [] [] [()], .complete, 5, 9⟩,
    ⟨7, .inl (positionPhase .checkRight), data [15] [] [] [1,15] [] [0] [], .complete, 4, 7⟩,
    ⟨8, .inl (positionPhase (.restoreScratch .successLeft)), data [15] [] [] [15] [] [0] [], .complete, 3, 5⟩,
    ⟨9, .inl (positionPhase (.restoreScratch .successLeft)), data [15] [] [] [0,15] [] [] [], .complete, 3, 5⟩,
    ⟨10, .inl (positionPhase (.restorePrefix .success)), data [15] [] [] [1,1,0,15] [] [] [], .complete, 5, 5⟩,
    ⟨11, .inr rotationSuccess, data [15] [] [] [1,1,0,15] [] [] [], .complete, 5, 5⟩ ]

def rightBoundaries : List Boundary :=
  [ ⟨0, .inl (movePhase .start), data [7,10,15] [] [] [1,1,0,15] [] [] [], .original, 7, 11⟩,
    ⟨1, .inl (movePhase (.scan .right)), data [10,15] [] [] [1,1,0,15] [] [] [], .parser, 6, 11⟩,
    ⟨2, .inl (movePhase (.emit .right)), data [15] [] [] [1,1,0,15] [] [] [], .parser, 5, 11⟩,
    ⟨3, .inl (dispatchPhase (.success .right)), data [15] [] [] [1,1,0,15] [] [] [], .parser, 5, 11⟩,
    ⟨4, .inl (positionPhase (.seek .right)), data [15] [] [] [1,1,0,15] [] [] [], .complete, 5, 9⟩,
    ⟨5, .inl (positionPhase (.start .right)), data [15] [] [] [1,1,0,15] [] [] [], .complete, 5, 9⟩,
    ⟨6, .inl (positionPhase (.scanScratch .right)), data [15] [] [] [0,15] [] [] [()], .complete, 4, 8⟩,
    ⟨7, .inl (positionPhase (.restoreScratch .successRight)), data [15] [] [] [1,15] [] [0] [], .complete, 4, 5⟩,
    ⟨8, .inl (positionPhase (.restoreScratch .successRight)), data [15] [] [] [0,1,15] [] [] [], .complete, 4, 5⟩,
    ⟨9, .inl (positionPhase (.restorePrefix .success)), data [15] [] [] [1,0,1,15] [] [] [], .complete, 5, 5⟩,
    ⟨10, .inr rotationSuccess, data [15] [] [] [1,0,1,15] [] [] [], .complete, 5, 5⟩ ]

def failureData (C : Word) (B : List Branch) : LocalData :=
  data C B [.right,.left] [1,15] [12,3] [14] [(),()]

def parseFailureBoundaries : List Boundary :=
  [ ⟨0, .inl (movePhase .start), failureData [6,8,9] [], .original, 12, 14⟩,
    ⟨1, .inl (movePhase (.scan .left)), failureData [8,9] [], .parser, 11, 14⟩,
    ⟨2, .inl (movePhase (.scan .left)), failureData [9] [.left], .parser, 11, 14⟩,
    ⟨3, .inl (movePhase (.scan .left)), failureData [] [.right,.left], .parser, 11, 14⟩,
    ⟨4, .inl (movePhase (.undo .left)), failureData [] [.right,.left], .parser, 11, 14⟩,
    ⟨5, .inl (movePhase (.undo .left)), failureData [9] [.left], .parser, 11, 14⟩,
    ⟨6, .inl (movePhase (.undo .left)), failureData [8,9] [], .parser, 11, 14⟩,
    ⟨7, .inl (dispatchPhase .failure), failureData [6,8,9] [], .parser, 12, 14⟩,
    ⟨8, .inr parseFailure, failureData [6,8,9] [], .complete, 12, 12⟩ ]


/- Proof-independent literal fixture additions for the released client. -/

def fixedRuns : List RunFixture :=
  [ ⟨movePhase .start, data [6,10] [] [] (treeCode rightTwo) [] [] [],
      rotationSuccess, data [] [] [] (treeCode leftTwo) [] [] [], 11⟩,
    ⟨movePhase .start, data [7,10] [] [] (treeCode leftTwo) [] [] [],
      rotationSuccess, data [] [] [] (treeCode rightTwo) [] [] [], 10⟩,
    ⟨movePhase .start, data [6,8,9,10] [] [] (treeCode nestedRight) [] [] [],
      rotationSuccess, data [] [] [] (treeCode nestedLeft) [] [] [], 21⟩,
    ⟨movePhase .start, data [6,9,8,10] [] [] (treeCode nestedRight) [] [] [],
      rotationFailure, data [] [] [] (treeCode nestedRight) [] [] [], 27⟩,
    ⟨movePhase .start, data [6,8,10,15,2] [] [.right] (treeCode nestedRight) [] [] [],
      rotationSuccess, data [15,2] [] [] (treeCode nestedLeft) [] [] [], 19⟩,
    ⟨movePhase .start, data [6,8,10,15] [.right,.left] [.right] [] [] [] [],
      rotationFailure, data [15] [] [.right,.left,.right] [] [] [] [], 11⟩,
    ⟨movePhase .start, data [15] [.right,.left] [.right] [] [] [] [],
      parseFailure, data [15] [.right,.left] [.right] [] [] [] [], 2⟩,
    ⟨movePhase .start, data [] [.right,.left] [.right] [] [] [] [],
      parseFailure, data [] [.right,.left] [.right] [] [] [] [], 2⟩,
    ⟨movePhase .start, data [6,8,15] [.right,.left] [.right] [] [] [] [],
      parseFailure, data [6,8,9,8,15] [] [.right] [] [] [] [], 8⟩,
    ⟨movePhase .start, failureData [15] [], parseFailure, failureData [15] [], 2⟩,
    ⟨movePhase .start, failureData [] [], parseFailure, failureData [] [], 2⟩,
    ⟨movePhase .start, failureData [6,8,9,15,10] [],
      parseFailure, failureData [6,8,9,15,10] [], 8⟩,
    ⟨movePhase .start, failureData [7,9,8,15,10] [],
      parseFailure, failureData [7,9,8,15,10] [], 8⟩,
    ⟨movePhase .start, data [6,10,15] [] [] (treeCode oneTree) [] [] [],
      rotationFailure, data [15] [] [] (treeCode oneTree) [] [] [], 12⟩,
    ⟨movePhase .start, data [6,15] [] [] (treeCode oneTree) [] [] [],
      parseFailure, data [6,15] [] [] (treeCode oneTree) [] [] [], 4⟩,
    ⟨movePhase .start, data [6,10] [] [] (treeCode rightTwo) [] [] [()],
      rotationFailure, data [] [] [] (treeCode rightTwo) [] [] [], 18⟩,
    ⟨movePhase .start, data [6,10,15] [] [] [1,0,1,15] [] [] [],
      rotationSuccess, data [15] [] [] [1,1,0,15] [] [] [], 11⟩,
    ⟨movePhase .start, data [7,10,15] [] [] [1,1,0,15] [] [] [],
      rotationSuccess, data [15] [] [] [1,0,1,15] [] [] [], 10⟩,
    ⟨movePhase .start, data [6,10] [] [] (treeCode leftContext) [] [] [],
      rotationFailure, data [] [] [] (treeCode leftContext) [] [] [], 20⟩,
    ⟨movePhase .start, data [6,10] [] [.left] (treeCode leftContext) [] [] [],
      rotationSuccess, data [] [] [] (treeCode (.node () leftTwo nilTree)) [] [] [], 13⟩,
    ⟨movePhase .start, data [6,10,15,2,7] [] [] (treeCode rightTwo ++ [14,5]) [12,3] [] [],
      rotationSuccess, data [15,2,7] [] [] [3,12,1,1,0,0,0,14,5] [] [] [], 13⟩,
    ⟨movePhase .start, data [6,10,15] [] [] (treeCode rightTwo ++ [15,2]) [12,3] [] [],
      rotationSuccess, data [15] [] [] [3,12,1,1,0,0,0,15,2] [] [] [], 13⟩,
    ⟨movePhase .start, data [7,10,15] [] [] (treeCode leftTwo ++ [15,2]) [12,3] [] [],
      rotationSuccess, data [15] [] [] [3,12,1,0,1,0,0,15,2] [] [] [], 12⟩,
    ⟨movePhase .start, data [6,8,10] [] [] (treeCode twoRightTwos) [] [] [],
      rotationSuccess, data [] [] [] (treeCode (.node () leftTwo rightTwo)) [] [] [], 15⟩,
    ⟨movePhase .start, data [6,9,10] [] [] (treeCode twoRightTwos) [] [] [],
      rotationSuccess, data [] [] [] (treeCode (.node () rightTwo leftTwo)) [] [] [], 25⟩,
    ⟨movePhase .start, data [7,8,9,8,10] [] [] (treeCode oneTree) [] [] [],
      rotationFailure, data [] [] [.left] (treeCode oneTree) [] [] [], 15⟩,
    ⟨movePhase .start, data [6,10,15] [] [] [0] [] [] [],
      rotationFailure, data [15] [] [] [0] [] [] [], 8⟩,
    ⟨movePhase .start, data [6,8,10,15] [] [.right,.left] [0] [] [] [],
      rotationFailure, data [15] [] [.right,.left] [0] [] [] [], 9⟩,
    ⟨positionPhase (.restoreScratch .successLeft),
      data [15,6] [.right,.left] [.right] [15] [12,3] [14,0] [(),()],
      rotationSuccess, data [15,6] [.right,.left] [.right] [3,12,1,1,0,14,15] [] [] [(),()], 6⟩,
    ⟨movePhase .start, data [6,10] [] [] [1,0,1,15] [] [14] [],
      rotationSuccess, data [] [] [] [1,1,14,0,15] [] [] [], 12⟩ ]

structure RepresentedFixture where
  parsed : RotationMove
  oldPath : List Branch
  tree : BinaryTree Unit
  value : Option (BinaryTree Unit)
  parserWork : Nat
  applicationWork : Nat
  positionTicks : Nat
  wholeTicks : Nat
  remaining : List Branch

def representedFixtures : List RepresentedFixture :=
  [ ⟨⟨.left, []⟩, [], rightTwo, some leftTwo, 4, 5, 7, 11, []⟩,
    ⟨⟨.right, []⟩, [], leftTwo, some rightTwo, 4, 5, 6, 10, []⟩,
    ⟨⟨.left, [.left,.right]⟩, [], nestedRight, some nestedLeft, 10, 11, 13, 21, []⟩,
    ⟨⟨.left, [.right,.left]⟩, [], nestedRight, none, 10, 4, 19, 27, []⟩,
    ⟨⟨.left, [.left]⟩, [.right], nestedRight, some nestedLeft, 7, 11, 13, 19, []⟩,
    ⟨⟨.left, [.left]⟩, [], nestedRight,
      some (.node () (.node () oneTree oneTree) nilTree), 7, 8, 9, 15, []⟩,
    ⟨⟨.left, []⟩, [], leftContext, none, 4, 3, 16, 20, []⟩,
    ⟨⟨.left, []⟩, [.left], leftContext, some (.node () leftTwo nilTree), 4, 8, 9, 13, []⟩,
    ⟨⟨.left, [.left]⟩, [], twoRightTwos, some (.node () leftTwo rightTwo), 7, 8, 9, 15, []⟩,
    ⟨⟨.left, [.right]⟩, [], twoRightTwos, some (.node () rightTwo leftTwo), 7, 8, 19, 25, []⟩,
    ⟨⟨.right, [.left,.right,.left]⟩, [], oneTree, none, 13, 4, 5, 15, [.left]⟩,
    ⟨⟨.left, []⟩, [], nilTree, none, 4, 3, 4, 8, []⟩,
    ⟨⟨.left, [.left]⟩, [.right,.left], nilTree, none, 7, 2, 3, 9, [.right,.left]⟩ ]

def RepresentedFixture.Expected {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (c : RepresentedFixture) (caller : External Λ → Statement Γ Λ R)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (rest F z : Word) : Prop :=
  (parseMoveRun (moveCode c.parsed ++ rest)).2 = c.parserWork ∧
  applyMoveRun ⟨c.parsed.direction, c.parsed.position ++ c.oldPath⟩ c.tree =
    (c.value, c.applicationWork) ∧
  PositionedRotationMachine.representedClock c.parsed.direction
    (c.parsed.position ++ c.oldPath) c.tree = c.positionTicks ∧
  PositionedRotationMachine.remainingPath (c.parsed.position ++ c.oldPath) c.tree =
    c.remaining ∧
  FirstRun caller
    (cfg (some (moveLabel .start)) regs
      (data (moveCode c.parsed ++ rest) [] c.oldPath (treeCode c.tree ++ z) F [] []) ctx)
    (c.wholeTicks + F.length)
    (cfg (some (resultLabel (if c.value.isSome then rotationSuccess else rotationFailure)))
      (reset regs)
      (data rest [] c.remaining (F.reverse ++ treeCode (c.value.getD c.tree) ++ z) [] [] []) ctx)

structure InitFixture where
  input : Word
  result : FinalResult
  certificate : Word
  path : List Branch
  ticks : Nat
  peak : Nat

def initFixtures : List InitFixture :=
  [ ⟨[], parseFailure, [], [], 2, 0⟩,
    ⟨[15], parseFailure, [15], [], 2, 1⟩,
    ⟨[6,10], rotationFailure, [], [], 8, 2⟩,
    ⟨[6,8,10], rotationFailure, [], [], 9, 3⟩,
    ⟨[7,9,8,10,15], rotationFailure, [15], [.left], 11, 5⟩ ]

/- Explicit expected contracts, prior to their connection proofs. -/

def Boundary.cfg {K Λ R : Type} {Γ : K → Type}
    (b : Boundary) (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  MoveApplyMachine.cfg (some (boundaryLabel b.control)) (b.stage.apply regs) b.stores ctx

def Boundary.Expected {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (b : Boundary) (caller : External Λ → Statement Γ Λ R)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (start : LocalData) (total : Nat) : Prop :=
  Runs caller (MoveApplyMachine.cfg (some (moveLabel .start)) regs start ctx) b.tick (b.cfg regs ctx) ∧
  remainingSteps (b.cfg (Λ := Λ) regs ctx) = total - b.tick ∧
  (b.tick < total ↔ Owned (b.cfg (Λ := Λ) regs ctx).l) ∧
  (b.cfg (Λ := Λ) regs ctx).var = b.stage.apply regs ∧
  (∀ k, (b.cfg (Λ := Λ) regs ctx).stk (.inr k) = ctx k) ∧
  stackCells (b.cfg (Λ := Λ) regs ctx) = b.cells + contextCells ctx ∧
  potential (b.cfg (Λ := Λ) regs ctx) = b.creditCells + contextCells ctx

def DispatchExpected {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (r : MoveParserMachine.Result)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  step caller (cfg (some (dispatchLabel r)) regs D ctx) =
    some (cfg (some (match r with
      | .failure => resultLabel parseFailure
      | .success d => positionLabel (.seek d))) (reset regs) D ctx)

def DirtyPhaseExpected {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (q : Phase)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  FirstRun caller (cfg (some (phaseLabel q)) regs D ctx) (phaseSteps q D)
    (phaseResult q regs D ctx) ∧
  ∃ r out, phaseResult (Λ := Λ) q regs D ctx = cfg (some (resultLabel r)) (reset regs) out ctx

def PrefixExpected {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (start : Cfg Γ Λ R) (n : Nat) : Prop :=
  n ≤ remainingSteps start → ∃ reached,
    Runs caller start n reached ∧
    remainingSteps reached = remainingSteps start - n ∧
    Relation.ReflTransGen (LocalStep caller) start reached ∧
    (n < remainingSteps start ↔ Owned reached.l) ∧
    (n = 0 → reached = start) ∧
    reached.var = registersAt start n ∧
    (∀ k, reached.stk (.inr k) = start.stk (.inr k))

def PrefixSpaceExpected {K Λ R : Type} {Γ : K → Type}
    [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (start : Cfg Γ Λ R) (n : Nat) : Prop :=
  n ≤ remainingSteps start → ∃ reached,
    Runs caller start n reached ∧
    remainingSteps reached = remainingSteps start - n ∧
    Relation.ReflTransGen (LocalStep caller) start reached ∧
    (n < remainingSteps start ↔ Owned reached.l) ∧
    (n = 0 → reached = start) ∧
    reached.var = registersAt start n ∧
    (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧
    stackCells reached ≤ potential reached ∧ potential reached ≤ potential start

def ParserFailureExpected {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (C : Word) (O : List Branch) (X F S : Word)
    (Hd : List Unit) : Prop :=
  (parseMoveRun C).1 = none →
    let D := data C [] O X F S Hd
    Runs caller (cfg (some (moveLabel .start)) regs D ctx) (MoveParserMachine.fullSteps C)
      (cfg (some (dispatchLabel .failure)) (resetMove regs) D ctx) ∧
    FirstRun caller (cfg (some (moveLabel .start)) regs D ctx)
      (MoveParserMachine.fullSteps C + 1)
      (cfg (some (resultLabel parseFailure)) (reset regs) D ctx) ∧
    (parseMoveRun C).2 = MoveParserMachine.fullSteps C + 1

def ParserSuccessExpected {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (C rest : Word) (mv : RotationMove)
    (O : List Branch) (X F S : Word) (Hd : List Unit) : Prop :=
  (parseMoveRun C).1 = some (mv, rest) →
    let before := data C [] O X F S Hd
    let joined := data rest [] (mv.position ++ O) X F S Hd
    let positionData : PositionedRotationMachine.LocalData :=
      { source := X, saved := F, scratch := S, pending := Hd, path := mv.position ++ O }
    MoveParserMachine.fullSteps C = 2 * mv.position.length + 3 ∧
    Runs caller (cfg (some (moveLabel .start)) regs before ctx)
      (2 * mv.position.length + 3)
      (cfg (some (dispatchLabel (.success mv.direction))) (resetMove regs) joined ctx) ∧
    Runs caller (cfg (some (moveLabel .start)) regs before ctx)
      (2 * mv.position.length + 4)
      (cfg (some (positionLabel (.seek mv.direction))) (reset regs) joined ctx) ∧
    FirstRun caller (cfg (some (moveLabel .start)) regs before ctx)
      (2 * mv.position.length + 4 +
        PositionedRotationMachine.phaseSteps (.seek mv.direction) positionData)
      (phaseResult (positionPhase (.seek mv.direction)) (reset regs) joined ctx)

def RawExpected {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (mv : RotationMove) (rest X : Word)
    (O : List Branch) : Prop :=
  let before := data (moveCode mv ++ rest) [] O X [] [] []
  ∃ (r : PositionedRotationMachine.Result) (Y : Word) (remaining : List Branch),
    FirstRun caller (cfg (some (moveLabel .start)) regs before ctx)
      (phaseSteps (movePhase .start) before)
      (cfg (some (resultLabel (.inr r))) (reset regs)
        (data rest [] remaining Y [] [] []) ctx) ∧
    Y.length = X.length ∧ remaining.IsSuffix (mv.position ++ O) ∧
    (r = .failure → Y = X) ∧ (r = .success → remaining = [])

def RepresentedExpected {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (mv : RotationMove) (rest : Word)
    (O : List Branch) (s : BinaryTree Unit) (F z : Word) : Prop :=
  let q := mv.position ++ O
  let value := (applyMoveRun ⟨mv.direction, q⟩ s).1
  let before := data (moveCode mv ++ rest) [] O (treeCode s ++ z) F [] []
  let after := data rest [] (PositionedRotationMachine.remainingPath q s)
    (F.reverse ++ treeCode (value.getD s) ++ z) [] [] []
  FirstRun caller (cfg (some (moveLabel .start)) regs before ctx)
    (2 * mv.position.length + 4 + PositionedRotationMachine.representedClock mv.direction q s + F.length)
    (cfg (some (resultLabel (if value.isSome then rotationSuccess else rotationFailure)))
      (reset regs) after ctx) ∧
  after.source.length = F.length + 2 * s.numNodes + 1 + z.length

def RootIffExpected {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (rest X F : Word) : Prop :=
  (FirstResult caller (cfg (some (moveLabel .start)) regs
      (data ([6,10] ++ rest) [] [] X F [] []) ctx) rotationSuccess ↔
    ∃ (A : BinaryTree Unit) (z : Word), X = [1] ++ treeCode A ++ [1] ++ z) ∧
  (FirstResult caller (cfg (some (moveLabel .start)) regs
      (data ([7,10] ++ rest) [] [] X F [] []) ctx) rotationSuccess ↔
    ∃ (A : BinaryTree Unit) (z : Word), X = [1,1] ++ treeCode A ++ z)

def RootPatternsExpected {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (rest F z : Word) (A : BinaryTree Unit) : Prop :=
  FirstRun caller (cfg (some (moveLabel .start)) regs
      (data ([6,10] ++ rest) [] [] ([1] ++ treeCode A ++ [1] ++ z) F [] []) ctx)
    (2 * (treeCode A).length + 9 + F.length)
    (cfg (some (resultLabel rotationSuccess)) (reset regs)
      (data rest [] [] (F.reverse ++ [1,1] ++ treeCode A ++ z) [] [] []) ctx) ∧
  FirstRun caller (cfg (some (moveLabel .start)) regs
      (data ([7,10] ++ rest) [] [] ([1,1] ++ treeCode A ++ z) F [] []) ctx)
    (2 * (treeCode A).length + 8 + F.length)
    (cfg (some (resultLabel rotationSuccess)) (reset regs)
      (data rest [] [] (F.reverse ++ [1] ++ treeCode A ++ [1] ++ z) [] [] []) ctx)

def HasExactPeak {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (start : Cfg Γ Λ R)
    (ticks peak : Nat) : Prop :=
  (∀ n, n ≤ ticks → ∃ reached, Runs caller start n reached ∧ stackCells reached ≤ peak) ∧
    ∃ n, n ≤ ticks ∧ ∃ reached, Runs caller start n reached ∧ stackCells reached = peak

def LeftNodesExpected {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (rest : Word) : Prop :=
  let raw : Word := List.replicate n nodeTag
  let start := cfg (some (moveLabel .start)) regs (data ([6,10] ++ rest) [] [] raw [] [] []) ctx
  let drop := cfg (some (positionLabel .dropPending)) (reset regs)
    (data rest [] [] raw [] [] (List.replicate n ())) ctx
  FirstRun caller start (3 * n + 8)
      (cfg (some (resultLabel rotationFailure)) (reset regs) (data rest [] [] raw [] [] []) ctx) ∧
    Runs caller start (2 * n + 6) drop ∧ remainingSteps drop = n + 2 ∧
    stackCells drop = rest.length + 2 * n + contextCells ctx ∧
    HasExactPeak caller start (3 * n + 8)
      (max (n + 2) (2 * n) + rest.length + contextCells ctx)

def RightNodesExpected {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (m : Nat) (rest : Word) : Prop :=
  let raw : Word := List.replicate (m + 2) nodeTag
  let start := cfg (some (moveLabel .start)) regs (data ([7,10] ++ rest) [] [] raw [] [] []) ctx
  let drop := cfg (some (positionLabel .dropPending)) (reset regs)
    (data rest [] [] raw [] [] (List.replicate (m + 1) ())) ctx
  FirstRun caller start (3 * m + 11)
      (cfg (some (resultLabel rotationFailure)) (reset regs) (data rest [] [] raw [] [] []) ctx) ∧
    Runs caller start (2 * m + 8) drop ∧ remainingSteps drop = m + 3 ∧
    stackCells drop = rest.length + 2 * m + 3 + contextCells ctx ∧
    HasExactPeak caller start (3 * m + 11)
      (max (m + 4) (2 * m + 3) + rest.length + contextCells ctx)

def ParserNodesExpected {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (k : Nat) (O : List Branch) (X F S : Word)
    (Hd : List Unit) : Prop :=
  let C : Word := [6] ++ List.replicate k pathLeftTag
  let D := data C [] O X F S Hd
  let start := cfg (some (moveLabel .start)) regs D ctx
  FirstRun caller start (2 * k + 4)
      (cfg (some (resultLabel parseFailure)) (reset regs) D ctx) ∧
    HasExactPeak caller start (2 * k + 4)
      (C.length + O.length + X.length + F.length + S.length + Hd.length + contextCells ctx)

/- Small independent source observations, connected to actual public source code. -/

theorem literal_tree_codes :
    treeCode nilTree = [0] ∧ treeCode oneTree = [1,0,0] ∧
    treeCode rightTwo = [1,0,1,0,0] ∧ treeCode leftTwo = [1,1,0,0,0] ∧
    treeCode nestedRight = [1,1,0,1,0,1,0,0,0] ∧
    treeCode nestedLeft = [1,1,0,1,1,0,0,0,0] := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem represented_fixture_source_observations (c : RepresentedFixture)
    (member : c ∈ representedFixtures) :
    applyMoveRun ⟨c.parsed.direction, c.parsed.position ++ c.oldPath⟩ c.tree =
        (c.value, c.applicationWork) ∧
      PositionedRotationMachine.representedClock c.parsed.direction
        (c.parsed.position ++ c.oldPath) c.tree = c.positionTicks ∧
      PositionedRotationMachine.remainingPath (c.parsed.position ++ c.oldPath) c.tree =
        c.remaining ∧
      3 * c.parsed.position.length + 4 = c.parserWork ∧
      2 * c.parsed.position.length + 4 + c.positionTicks = c.wholeTicks := by
  simp only [representedFixtures, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem arbitrary_certificate_suffix_has_the_same_source_parse_cost
    (c : RepresentedFixture) (member : c ∈ representedFixtures) (rest : Word) :
    (parseMoveRun (moveCode c.parsed ++ rest)).2 = c.parserWork := by
  rw [parseMoveRun_code]
  exact (represented_fixture_source_observations c member).2.2.2.1

theorem parsed_path_then_old_path_is_not_reversal_or_discard :
    applyMoveRun ⟨.left, [.left,.right]⟩ nestedRight = (some nestedLeft, 11) ∧
      applyMoveRun ⟨.left, [.right,.left]⟩ nestedRight = (none, 4) ∧
      applyMoveRun ⟨.left, [.left]⟩ nestedRight =
        (some (.node () (.node () oneTree oneTree) nilTree), 8) ∧
      PositionedRotationMachine.representedClock .left [.left,.right] nestedRight = 13 ∧
      PositionedRotationMachine.representedClock .left [.right,.left] nestedRight = 19 ∧
      PositionedRotationMachine.representedClock .left [.left] nestedRight = 9 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem source_tariffs_do_not_determine_the_physical_clock :
    (parseMoveRun [6,8,10]).2 = 7 ∧ (parseMoveRun [6,9,10]).2 = 7 ∧
      applyMoveRun ⟨.left, [.left]⟩ twoRightTwos =
        (some (.node () leftTwo rightTwo), 8) ∧
      applyMoveRun ⟨.left, [.right]⟩ twoRightTwos =
        (some (.node () rightTwo leftTwo), 8) ∧
      PositionedRotationMachine.representedClock .left [.left] twoRightTwos = 9 ∧
      PositionedRotationMachine.representedClock .left [.right] twoRightTwos = 19 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem source_missing_cursor_differs_from_the_consumed_physical_path :
    applyMoveRun ⟨.right, [.left,.right,.left]⟩ oneTree = (none, 4) ∧
      PositionedRotationMachine.remainingPath [.left,.right,.left] oneTree = [.left] ∧
      PositionedRotationMachine.representedClock .right [.left,.right,.left] oneTree = 5 ∧
      (parseMoveRun [7,8,9,8,10]).2 = 13 := ⟨rfl, rfl, rfl, rfl⟩

theorem both_raw_mirrors_fail_whole_tree_recognition :
    (parseTreeRun [1,0,1,15]).1 = none ∧
      (parseTreeRun [1,1,0,15]).1 = none := ⟨rfl, rfl⟩

theorem all_three_temporaries_are_distinct_from_the_parser_reset (flag : Bool) :
    resetMove (stale flag) = ((some .right, (none, some ())), flag) ∧
      reset (stale flag) = clean flag ∧
      resetMove (stale flag) ≠ reset (stale flag) := by
  refine ⟨rfl, rfl, ?_⟩
  intro equal
  have branch := congrArg (fun r : Registers Bool => r.1.1) equal
  contradiction

theorem every_temporary_tuple_has_the_staged_reset (temps : Temporaries) (flag : Bool) :
    resetMove (temps, flag) = ((temps.1, (none, temps.2.2)), flag) ∧
      reset (temps, flag) = ((none, (none, none)), flag) := ⟨rfl, rfl⟩

theorem context_words_remain_two_different_alphabets :
    authorContext 0 = ([15,2,7,10,3] : Word) ∧
      authorContext 1 = [(),()] ∧
      independentContext 0 = [true,false,true] ∧
      independentContext 1 = ([11,15] : Word) := ⟨rfl, rfl, rfl, rfl⟩

theorem fixture_counts : leftBoundaries.length = 12 ∧ rightBoundaries.length = 11 ∧
    parseFailureBoundaries.length = 9 ∧ fixedRuns.length = 30 ∧
    representedFixtures.length = 13 ∧ initFixtures.length = 5 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/- Connected uses of the actual published carrier and transport foundation. -/

theorem actual_small_carriers_and_both_label_specializations :
    Fintype.card LocalStack = 7 ∧ Fintype.card Phase = 26 ∧
      Fintype.card FinalResult = 3 ∧ Fintype.card Temporaries = 102 ∧
      Fintype.card (StackId (Fin 2)) = 9 ∧
      Fintype.card (Label Unit) = 30 ∧ Fintype.card (Label (Fin 2)) = 31 ∧
      Fintype.card (Registers Bool) = 204 := by
  refine ⟨card_localStack, card_phase, card_finalResult, card_temporaries, ?_, ?_, ?_, ?_⟩
  · simpa using (card_stackId (K := Fin 2))
  · simpa using (card_label (Λ := Unit))
  · simpa using (card_label (Λ := Fin 2))
  · simpa using (card_registers (R := Bool))

theorem owned_control_stays_finite_for_nat_callers :
    Fintype.card (OwnedLabel Nat) = 26 := card_ownedLabel

theorem every_independent_stack_alphabet_is_finite (k : StackId (Fin 2)) :
    Nonempty (Fintype (Alphabet IndependentAlphabet k)) := ⟨inferInstance⟩

theorem every_author_stack_alphabet_is_finite (k : StackId (Fin 2)) :
    Nonempty (Fintype (Alphabet AuthorAlphabet k)) := ⟨inferInstance⟩

theorem move_view_maps_every_local_physical_store {K : Type} :
    moveStackEquiv (K := K) (.inl .raw) = .inl .certificate ∧
      moveStackEquiv (K := K) (.inl .reverse) = .inl .moveReverse ∧
      moveStackEquiv (K := K) (.inl .path) = .inl .path ∧
      moveStackEquiv (K := K) (.inr (.inl .source)) = .inl .source ∧
      moveStackEquiv (K := K) (.inr (.inl .saved)) = .inl .saved ∧
      moveStackEquiv (K := K) (.inr (.inl .scratch)) = .inl .scratch ∧
      moveStackEquiv (K := K) (.inr (.inl .pending)) = .inl .pending :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem position_view_maps_every_local_physical_store {K : Type} :
    positionStackEquiv (K := K) (.inl .source) = .inl .source ∧
      positionStackEquiv (K := K) (.inl .saved) = .inl .saved ∧
      positionStackEquiv (K := K) (.inl .scratch) = .inl .scratch ∧
      positionStackEquiv (K := K) (.inl .pending) = .inl .pending ∧
      positionStackEquiv (K := K) (.inl .path) = .inl .path ∧
      positionStackEquiv (K := K) (.inr (.inl .certificate)) = .inl .certificate ∧
      positionStackEquiv (K := K) (.inr (.inl .moveReverse)) = .inl .moveReverse :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem both_component_views_keep_external_indices_and_share_one_path {K : Type} (k : K) :
    moveStackEquiv (.inr (.inr k)) = .inr k ∧
      positionStackEquiv (.inr (.inr k)) = .inr k ∧
      moveStackEquiv (K := K) (.inl .path) = positionStackEquiv (K := K) (.inl .path) :=
  ⟨rfl, rfl, rfl⟩

theorem complete_register_permutation_and_its_inverse {R : Type}
    (a : Option Tag) (b : Option Branch) (u : Option Unit) (r : R) :
    moveRegisterEquiv (a, ((b, u), r)) = ((b, (a, u)), r) ∧
      moveRegisterEquiv.symm ((b, (a, u)), r) = (a, ((b, u), r)) ∧
      moveRegisterEquiv (MoveParserMachine.reset (a, ((b, u), r))) =
        ((b, (none, u)), r) := ⟨rfl, rfl, rfl⟩

theorem complete_label_maps_distinguish_all_three_results {Λ : Type}
    (q : MoveParserMachine.Phase) (p : PositionedRotationMachine.Phase)
    (r : MoveParserMachine.Result) (s : PositionedRotationMachine.Result) :
    moveLabelEquiv (MoveParserMachine.phaseLabel q) = moveLabel (Λ := Λ) q ∧
      moveLabelEquiv (MoveParserMachine.resultLabel r) = dispatchLabel (Λ := Λ) r ∧
      positionLabelEquiv (PositionedRotationMachine.phaseLabel p) = positionLabel (Λ := Λ) p ∧
      positionLabelEquiv (PositionedRotationMachine.resultLabel s) = resultLabel (Λ := Λ) (.inr s) ∧
      resultLabel (Λ := Λ) parseFailure ≠ resultLabel rotationFailure ∧
      resultLabel (Λ := Λ) parseFailure ≠ resultLabel rotationSuccess ∧
      resultLabel (Λ := Λ) rotationFailure ≠ resultLabel rotationSuccess := by
  refine ⟨moveLabelEquiv_phase q, moveLabelEquiv_result r,
    positionLabelEquiv_phase p, positionLabelEquiv_result s, ?_, ?_, ?_⟩ <;>
    intro impossible <;> cases impossible

section CompleteViews
variable {K Λ R : Type} {Γ : K → Type}

theorem whole_move_view_retains_all_dirty_physical_data
    (label : Option (MoveParserMachine.Label (MoveCallerLabel Λ)))
    (a : Option Tag) (b : Option Branch) (u : Option Unit) (r : R)
    (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    moveCfg (moveView label (a, ((b, u), r)) D ctx) =
      cfg (label.map moveLabelEquiv) ((b, (a, u)), r) D ctx :=
  moveCfg_view label (a, ((b, u), r)) D ctx

theorem whole_position_view_retains_dirty_certificate_and_reverse
    (label : Option (PositionedRotationMachine.Label (PositionCallerLabel Λ)))
    (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    positionCfg (positionView label regs D ctx) =
      cfg (label.map positionLabelEquiv) regs D ctx := positionCfg_view label regs D ctx

theorem the_two_views_are_injective_on_complete_configurations :
    Function.Injective (moveCfg (Γ := Γ) (Λ := Λ) (R := R)) ∧
      Function.Injective (positionCfg (Γ := Γ) (Λ := Λ) (R := R)) := by
  constructor
  · exact FrontEndMachine.Transport.cfg_injective moveStackEquiv moveSymbolEquiv
      moveRegisterEquiv moveLabelEquiv moveLabelEquiv.injective
  · exact FrontEndMachine.Transport.cfg_injective positionStackEquiv positionSymbolEquiv
      (Equiv.refl _) positionLabelEquiv positionLabelEquiv.injective

end CompleteViews

section Dispatch
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

theorem every_dispatch_is_exactly_one_full_reset_and_no_stack_change
    (r : MoveParserMachine.Result) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : DispatchExpected caller r D regs ctx :=
  dispatch_step caller r D regs ctx

def dispatchInActualTime (r : MoveParserMachine.Result) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (dispatchLabel r)) regs D ctx)
      (some (cfg (some (dispatchTarget r)) (reset regs) D ctx)) 1 where
  steps := 1
  evals_in_steps := by
    change step caller (cfg (some (dispatchLabel r)) regs D ctx) = _
    exact dispatch_step caller r D regs ctx
  steps_le_m := Nat.le_refl _

theorem dispatch_timed_data_keeps_one_actual_step
    (r : MoveParserMachine.Result) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : (dispatchInActualTime caller r D regs ctx).steps = 1 := rfl

end Dispatch

/- Literal caller activations remain outside the first whole owned return. -/

def haltCaller : ExampleCaller := fun _ => .halt

def sentinelHaltCaller (marker : Tag) : AuthorCaller
  | .inl _ => .push (.inr (0 : Fin 2)) (fun _ => marker) .halt
  | .inr _ => .halt

def allocatingCaller : ExampleCaller
  | .inl _ => .push (.inr (0 : Fin 2)) (fun _ => true)
      (.load (fun regs => (regs.1, !regs.2)) (.goto (fun _ => callerLabel ())))
  | .inr _ => .halt

def misleadingCaller : ExampleCaller
  | .inl (.inl _) => .goto (fun _ => resultLabel rotationSuccess)
  | .inl (.inr _) => .halt
  | .inr _ => .halt

def reentryCaller : ExampleCaller
  | .inl (.inr .success) => .goto (fun _ => moveLabel .start)
  | .inl _ => .halt
  | .inr _ => .halt

def badDispatchProgram (caller : ExampleCaller) : Label Unit → Statement IndependentAlphabet Unit Bool
  | .inr (.inl (.success .left)) => .halt
  | label => program caller label

theorem firstRun_unique {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (start left right : Cfg Γ Λ R)
    (m n : Nat) (first : FirstRun caller start m left)
    (second : FirstRun caller start n right) : m = n ∧ left = right := by
  have notLt : ¬ m < n := by
    intro smaller
    obtain ⟨reached, run, owned⟩ := second.2.2 m smaller
    have equal : reached = left := Option.some.inj (run.symm.trans first.1)
    exact first.2.1 (equal ▸ owned)
  have notGt : ¬ n < m := by
    intro smaller
    obtain ⟨reached, run, owned⟩ := first.2.2 n smaller
    have equal : reached = right := Option.some.inj (run.symm.trans second.1)
    exact second.2.1 (equal ▸ owned)
  have same : m = n := by omega
  subst n
  exact ⟨rfl, Option.some.inj (first.1.symm.trans second.1)⟩

theorem runs_trans {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (start middle finish : Cfg Γ Λ R)
    (m n : Nat) (first : Runs caller start m middle) (second : Runs caller middle n finish) :
    Runs caller start (m + n) finish := by
  unfold Runs at *
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

theorem append_actual_step {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (start finish : Cfg Γ Λ R) (n : Nat)
    (run : Runs caller start n finish) (out : Option (Cfg Γ Λ R))
    (last : step caller finish = out) :
    (next caller)^[n + 1] (some start) = out := by
  rw [Function.iterate_succ_apply', run, next_some, last]

def oneActualStepTime {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (start : Cfg Γ Λ R)
    (out : Option (Cfg Γ Λ R)) (executed : step caller start = out) :
    StateTransition.EvalsToInTime (step caller) start out 1 where
  steps := 1
  evals_in_steps := by
    change step caller start = out
    exact executed
  steps_le_m := Nat.le_refl _

def appendTimed {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (start middle : Cfg Γ Λ R)
    (finish : Option (Cfg Γ Λ R)) (m n : Nat)
    (first : StateTransition.EvalsToInTime (step caller) start (some middle) m)
    (second : StateTransition.EvalsToInTime (step caller) middle finish n) :
    StateTransition.EvalsToInTime (step caller) start finish (n + m) :=
  StateTransition.EvalsToInTime.trans (step caller) m n start middle finish first second

theorem halt_is_one_paid_activation_before_outer_none (r : FinalResult)
    (regs : Registers Bool) (D : LocalData) (ctx : ∀ k, List (IndependentAlphabet k)) :
    step haltCaller (cfg (some (resultLabel r)) regs D ctx) = some (cfg none regs D ctx) ∧
      step haltCaller (cfg none regs D ctx) = none := ⟨rfl, rfl⟩

theorem sentinel_push_and_halt_are_one_actual_activation (marker : Tag) (r : FinalResult)
    (regs : Registers Bool) (D : LocalData) (tags : Word) (units : List Unit) :
    step (sentinelHaltCaller marker)
      (cfg (some (resultLabel r)) regs D (authorWords tags units)) =
      some (cfg none regs D (authorWords (marker :: tags) units)) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k =>
      fin_cases k <;> rfl

theorem allocating_caller_changes_the_actual_protected_data_and_caller_register
    (r : FinalResult) (regs : Registers Bool) (D : LocalData)
    (bits : List Bool) (tags : Word) :
    step allocatingCaller (cfg (some (resultLabel r)) regs D (independentWords bits tags)) =
      some (cfg (some (callerLabel ())) (regs.1, !regs.2) D
        (independentWords (true :: bits) tags)) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k =>
      fin_cases k <;> rfl

theorem misleading_success_is_a_later_paid_caller_step (regs : Registers Bool)
    (D : LocalData) (ctx : ∀ k, List (IndependentAlphabet k)) :
    step misleadingCaller (cfg (some (resultLabel parseFailure)) regs D ctx) =
      some (cfg (some (resultLabel rotationSuccess)) regs D ctx) := rfl

theorem reentry_jump_preserves_every_actual_store (regs : Registers Bool)
    (D : LocalData) (ctx : ∀ k, List (IndependentAlphabet k)) :
    step reentryCaller (cfg (some (resultLabel rotationSuccess)) regs D ctx) =
      some (cfg (some (moveLabel .start)) regs D ctx) := rfl

theorem agreeing_on_twenty_three_imported_phases_omits_the_dispatch
    (caller : ExampleCaller) :
    (∀ q : MoveParserMachine.Phase, badDispatchProgram caller (moveLabel q) = moveBlock q) ∧
      (∀ q : PositionedRotationMachine.Phase,
        badDispatchProgram caller (positionLabel q) = positionBlock q) := ⟨fun _ => rfl, fun _ => rfl⟩

theorem altered_dispatch_gives_a_present_halt (caller : ExampleCaller)
    (regs : Registers Bool) (D : LocalData) :
    Turing.TM2.step (badDispatchProgram caller)
      (cfg (some (dispatchLabel (.success .left))) regs D independentContext) =
      some (cfg none regs D independentContext) := rfl

theorem imported_block_agreement_does_not_prove_the_paid_join (caller : ExampleCaller)
    (regs : Registers Bool) (D : LocalData) :
    Turing.TM2.step (badDispatchProgram caller)
      (cfg (some (dispatchLabel (.success .left))) regs D independentContext) ≠
      some (cfg (some (positionLabel (.seek .left))) (reset regs) D independentContext) := by
  rw [altered_dispatch_gives_a_present_halt]
  intro equal
  have labels := congrArg (fun c : ExampleCfg => c.l) (Option.some.inj equal)
  cases labels


section ActualExecution
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

theorem every_dirty_phase_has_its_exact_first_live_result
    (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    DirtyPhaseExpected caller q D regs ctx := by
  refine ⟨⟨phase_iterate caller q D regs ctx,
    (phase_first_return caller q D regs ctx).1,
    (phase_first_return caller q D regs ctx).2⟩, ?_⟩
  exact ⟨(evaluate q D).result, (evaluate q D).data, rfl⟩

theorem local_run_gives_an_actual_first_return {n : Nat} {before after : Cfg Γ Λ R}
    (run : LocalRun caller n before after) (returned : ¬ Owned after.l) :
    FirstRun caller before n after :=
  ⟨LocalRun.iterate caller run, returned, LocalRun.owned_prefix caller run⟩

def localRunInActualTime {n : Nat} {before after : Cfg Γ Λ R}
    (run : LocalRun caller n before after) :
    StateTransition.EvalsToInTime (step caller) before (some after) n where
  steps := n
  evals_in_steps := LocalRun.iterate caller run
  steps_le_m := Nat.le_refl _

def arbitraryDirtyPhaseInActualTime (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel q)) regs D ctx)
      (some (phaseResult q regs D ctx)) (phaseSteps q D) :=
  localRunInActualTime caller (phase_localRun caller q D regs ctx)

theorem dirty_timing_keeps_the_actual_phase_steps (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (arbitraryDirtyPhaseInActualTime caller q D regs ctx).steps = phaseSteps q D := rfl

def arbitraryConfigurationInActualTime (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (step caller) start (some (finalCfg start))
      (remainingSteps start) := localRunInActualTime caller (cfg_localRun caller start)

theorem initially_nonowned_has_only_its_unchanged_zero_prefix
    (start : Cfg Γ Λ R) (notOwned : ¬ Owned start.l) (n : Nat)
    (bound : n ≤ remainingSteps start) :
    n = 0 ∧ Runs caller start n start ∧ finalCfg start = start := by
  have zero := nonowned_remaining start notOwned
  have nzero : n = 0 := by omega
  subst n
  exact ⟨rfl, rfl, nonowned_finalCfg start notOwned⟩

omit [DecidableEq K] in
theorem exact_rank_is_positive_precisely_at_actual_owned_labels (start : Cfg Γ Λ R) :
    0 < remainingSteps start ↔ Owned start.l := remainingSteps_pos_iff start

theorem every_owned_transition_has_the_exact_drop_and_identical_future_endpoint
    (before after : Cfg Γ Λ R) (owned : Owned before.l)
    (executed : step caller before = some after) :
    remainingSteps before = remainingSteps after + 1 ∧ finalCfg before = finalCfg after :=
  ⟨local_step_remaining caller ⟨owned, executed⟩, finalCfg_step caller ⟨owned, executed⟩⟩

theorem every_first_return_has_the_exact_rank_and_complete_endpoint
    (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (finish : Cfg Γ Λ R)
    (first : FirstRun caller (cfg (some (phaseLabel q)) regs D ctx) n finish) :
    n = phaseSteps q D ∧ finish = phaseResult q regs D ctx := by
  exact firstRun_unique caller _ finish (phaseResult q regs D ctx) n (phaseSteps q D)
    first (every_dirty_phase_has_its_exact_first_live_result caller q D regs ctx).1

theorem fixture_firstRun_of_checked_evaluation (c : RunFixture)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (checked : evaluate c.phase c.before = ⟨c.result, c.after, c.ticks⟩) :
    FirstRun caller (cfg (some (phaseLabel c.phase)) regs c.before ctx) c.ticks
      (cfg (some (resultLabel c.result)) (reset regs) c.after ctx) := by
  simpa only [phaseSteps, phaseResult, checked] using
    (every_dirty_phase_has_its_exact_first_live_result caller c.phase c.before regs ctx).1

def fixtureInActualTime (c : RunFixture) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (checked : evaluate c.phase c.before = ⟨c.result, c.after, c.ticks⟩) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel c.phase)) regs c.before ctx)
      (some (cfg (some (resultLabel c.result)) (reset regs) c.after ctx)) c.ticks where
  steps := c.ticks
  evals_in_steps := (fixture_firstRun_of_checked_evaluation caller c regs ctx checked).1
  steps_le_m := Nat.le_refl _

end ActualExecution

/- Each independent literal endpoint is connected below through actual phase execution. -/

theorem root_left_evaluation :
    evaluate (movePhase .start) (data [6,10] [] [] (treeCode rightTwo) [] [] []) =
      ⟨rotationSuccess, data [] [] [] (treeCode leftTwo) [] [] [], 11⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, rightTwo, nilTree, oneTree,
    treeCode, nodeTag, emptyTag, List.cons_append, List.nil_append, rotateLeftTag, ↓reduceIte, moveScanFinish,
    parsePathRun, endMoveTag, List.reverse_nil, List.append_nil, evaluatePosition, positionData,
    PositionedRotationMachine.evaluate_phase, PositionedRotationMachine.advance, Fin.zero_eq_one_iff,
    OfNat.ofNat_ne_one, List.tail_cons, PositionedRotationMachine.modeResult, PositionedRotationMachine.markerWord,
    PositionedRotationMachine.evaluate_result, zero_add, Nat.reduceAdd, setPositionData, MoveParserMachine.phaseSteps,
    MoveParserMachine.startSteps, rotateRightTag, Fin.reduceEq, or_false, MoveParserMachine.branchCount, pathLeftTag,
    pathRightTag, or_self, mul_zero, List.length_nil, add_zero, rotationSuccess, leftTwo]

theorem root_right_evaluation :
    evaluate (movePhase .start) (data [7,10] [] [] (treeCode leftTwo) [] [] []) =
      ⟨rotationSuccess, data [] [] [] (treeCode rightTwo) [] [] [], 10⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, leftTwo, oneTree, nilTree,
    treeCode, nodeTag, emptyTag, List.cons_append, List.nil_append, rotateLeftTag, Fin.reduceEq, ↓reduceIte,
    rotateRightTag, moveScanFinish, parsePathRun, endMoveTag, List.reverse_nil, List.append_nil, evaluatePosition,
    positionData, PositionedRotationMachine.evaluate_phase, PositionedRotationMachine.advance, and_self,
    Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, List.tail_cons, PositionedRotationMachine.modeResult,
    PositionedRotationMachine.markerWord, PositionedRotationMachine.evaluate_result, zero_add, Nat.reduceAdd,
    setPositionData, MoveParserMachine.phaseSteps, MoveParserMachine.startSteps, or_true, MoveParserMachine.branchCount,
    pathLeftTag, pathRightTag, or_self, mul_zero, List.length_nil, add_zero, rotationSuccess, rightTwo]

theorem two_parsed_branches_evaluation :
    evaluate (movePhase .start) (data [6,8,9,10] [] [] (treeCode nestedRight) [] [] []) =
      ⟨rotationSuccess, data [] [] [] (treeCode nestedLeft) [] [] [], 21⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, nestedRight, nilTree,
    rightTwo, oneTree, treeCode, nodeTag, emptyTag, List.cons_append, List.nil_append, rotateLeftTag, ↓reduceIte,
    moveScanFinish, parsePathRun, endMoveTag, Fin.reduceEq, pathLeftTag, Resources.bind, pathRightTag, Nat.reduceAdd,
    List.reverse_nil, List.append_nil, evaluatePosition, positionData, PositionedRotationMachine.evaluate_phase,
    PositionedRotationMachine.advance, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, List.tail_cons,
    PositionedRotationMachine.modeResult, PositionedRotationMachine.markerWord,
    PositionedRotationMachine.evaluate_result, zero_add, setPositionData, MoveParserMachine.phaseSteps,
    MoveParserMachine.startSteps, rotateRightTag, or_false, MoveParserMachine.branchCount, or_true, or_self,
    Nat.reduceMul, List.length_nil, add_zero, rotationSuccess, nestedLeft, leftTwo]

theorem reversed_parsed_branches_evaluation :
    evaluate (movePhase .start) (data [6,9,8,10] [] [] (treeCode nestedRight) [] [] []) =
      ⟨rotationFailure, data [] [] [] (treeCode nestedRight) [] [] [], 27⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, nestedRight, nilTree,
    rightTwo, oneTree, treeCode, nodeTag, emptyTag, List.cons_append, List.nil_append, rotateLeftTag, ↓reduceIte,
    moveScanFinish, parsePathRun, endMoveTag, Fin.reduceEq, pathLeftTag, pathRightTag, Resources.bind, Nat.reduceAdd,
    List.reverse_nil, List.append_nil, evaluatePosition, positionData, PositionedRotationMachine.evaluate_phase,
    PositionedRotationMachine.advance, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, List.tail_cons, List.cons_ne_self,
    PositionedRotationMachine.evaluate_result, zero_add, setPositionData, MoveParserMachine.phaseSteps,
    MoveParserMachine.startSteps, rotateRightTag, or_false, MoveParserMachine.branchCount, or_true, or_self,
    Nat.reduceMul, List.length_nil, add_zero, rotationFailure]

theorem parsed_before_old_path_evaluation :
    evaluate (movePhase .start) (data [6,8,10,15,2] [] [.right] (treeCode nestedRight) [] [] []) =
      ⟨rotationSuccess, data [15,2] [] [] (treeCode nestedLeft) [] [] [], 19⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, nestedRight, nilTree,
    rightTwo, oneTree, treeCode, nodeTag, emptyTag, List.cons_append, List.nil_append, rotateLeftTag, ↓reduceIte,
    moveScanFinish, parsePathRun, endMoveTag, Fin.reduceEq, pathLeftTag, Resources.bind, Nat.reduceAdd,
    List.reverse_nil, evaluatePosition, positionData, PositionedRotationMachine.evaluate_phase,
    PositionedRotationMachine.advance, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, List.tail_cons,
    PositionedRotationMachine.modeResult, PositionedRotationMachine.markerWord,
    PositionedRotationMachine.evaluate_result, zero_add, setPositionData, MoveParserMachine.phaseSteps,
    MoveParserMachine.startSteps, rotateRightTag, or_false, MoveParserMachine.branchCount, pathRightTag, or_self,
    mul_one, List.length_nil, add_zero, rotationSuccess, nestedLeft, leftTwo]

theorem dirty_reverse_then_empty_source_evaluation :
    evaluate (movePhase .start) (data [6,8,10,15] [.right,.left] [.right] [] [] [] []) =
      ⟨rotationFailure, data [15] [] [.right,.left,.right] [] [] [] [], 11⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, rotateLeftTag, ↓reduceIte,
    moveScanFinish, parsePathRun, endMoveTag, Fin.reduceEq, pathLeftTag, Resources.bind, Nat.reduceAdd,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, evaluatePosition, positionData,
    PositionedRotationMachine.evaluate_phase, PositionedRotationMachine.advance,
    PositionedRotationMachine.evaluate_result, zero_add, setPositionData, MoveParserMachine.phaseSteps,
    MoveParserMachine.startSteps, rotateRightTag, or_false, MoveParserMachine.branchCount, pathRightTag, or_self,
    mul_one, List.length_cons, List.length_nil, rotationFailure]

theorem dirty_immediate_foreign_evaluation :
    evaluate (movePhase .start) (data [15] [.right,.left] [.right] [] [] [] []) =
      ⟨parseFailure, data [15] [.right,.left] [.right] [] [] [] [], 2⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, rotateLeftTag, Fin.reduceEq,
    ↓reduceIte, rotateRightTag, MoveParserMachine.phaseSteps, MoveParserMachine.startSteps, or_self, Nat.reduceAdd,
    parseFailure, Evaluation.mk.injEq, and_self, and_true]
  rfl

theorem dirty_immediate_eof_evaluation :
    evaluate (movePhase .start) (data [] [.right,.left] [.right] [] [] [] []) =
      ⟨parseFailure, data [] [.right,.left] [.right] [] [] [] [], 2⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, MoveParserMachine.phaseSteps,
    MoveParserMachine.startSteps, Nat.reduceAdd, parseFailure, Evaluation.mk.injEq, and_self, and_true]
  rfl

theorem dirty_accepted_direction_failure_evaluation :
    evaluate (movePhase .start) (data [6,8,15] [.right,.left] [.right] [] [] [] []) =
      ⟨parseFailure, data [6,8,9,8,15] [] [.right] [] [] [] [], 8⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, rotateLeftTag, ↓reduceIte,
    moveScanFinish, parsePathRun, endMoveTag, Fin.reduceEq, pathLeftTag, Resources.bind, pathRightTag, Nat.reduceAdd,
    pathTags, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.map_cons, branchTag,
    List.map_nil, MoveParserMachine.phaseSteps, MoveParserMachine.startSteps, rotateRightTag, or_false,
    MoveParserMachine.branchCount, or_self, zero_add, mul_one, List.length_cons, List.length_nil, parseFailure,
    Evaluation.mk.injEq, LocalData.mk.injEq, List.cons.injEq, and_true, and_self]
  exact ⟨rfl, rfl⟩

theorem foreign_with_dirty_tree_evaluation :
    evaluate (movePhase .start) (failureData [15] []) =
      ⟨parseFailure, failureData [15] [], 2⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, failureData, data, Fin.isValue, rotateLeftTag,
    Fin.reduceEq, ↓reduceIte, rotateRightTag, MoveParserMachine.phaseSteps, MoveParserMachine.startSteps, or_self,
    Nat.reduceAdd, parseFailure, Evaluation.mk.injEq, and_self, and_true]
  rfl

theorem eof_with_dirty_tree_evaluation :
    evaluate (movePhase .start) (failureData [] []) =
      ⟨parseFailure, failureData [] [], 2⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, failureData, data, Fin.isValue,
    MoveParserMachine.phaseSteps, MoveParserMachine.startSteps, Nat.reduceAdd, parseFailure, Evaluation.mk.injEq,
    and_self, and_true]
  rfl

theorem left_foreign_suffix_evaluation :
    evaluate (movePhase .start) (failureData [6,8,9,15,10] []) =
      ⟨parseFailure, failureData [6,8,9,15,10] [], 8⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, failureData, data, Fin.isValue, rotateLeftTag,
    ↓reduceIte, moveScanFinish, parsePathRun, endMoveTag, Fin.reduceEq, pathLeftTag, Resources.bind, pathRightTag,
    Nat.reduceAdd, pathTags, List.reverse_nil, List.map_nil, List.nil_append, MoveParserMachine.phaseSteps,
    MoveParserMachine.startSteps, rotateRightTag, or_false, MoveParserMachine.branchCount, or_true, or_self, zero_add,
    Nat.reduceMul, List.length_nil, add_zero, parseFailure, Evaluation.mk.injEq, LocalData.mk.injEq, List.cons.injEq,
    and_true, and_self]
  exact ⟨rfl, rfl⟩

theorem right_foreign_suffix_evaluation :
    evaluate (movePhase .start) (failureData [7,9,8,15,10] []) =
      ⟨parseFailure, failureData [7,9,8,15,10] [], 8⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, failureData, data, Fin.isValue, rotateLeftTag,
    Fin.reduceEq, ↓reduceIte, rotateRightTag, moveScanFinish, parsePathRun, endMoveTag, pathLeftTag, pathRightTag,
    Resources.bind, Nat.reduceAdd, pathTags, List.reverse_nil, List.map_nil, List.nil_append,
    MoveParserMachine.phaseSteps, MoveParserMachine.startSteps, or_true, MoveParserMachine.branchCount, or_false,
    or_self, zero_add, Nat.reduceMul, List.length_nil, add_zero, parseFailure, Evaluation.mk.injEq, LocalData.mk.injEq,
    List.cons.injEq, and_true, and_self]
  exact ⟨rfl, rfl⟩

theorem rotation_failure_after_consumption_evaluation :
    evaluate (movePhase .start) (data [6,10,15] [] [] (treeCode oneTree) [] [] []) =
      ⟨rotationFailure, data [15] [] [] (treeCode oneTree) [] [] [], 12⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, oneTree, nilTree, treeCode,
    nodeTag, emptyTag, List.cons_append, List.nil_append, rotateLeftTag, ↓reduceIte, moveScanFinish, parsePathRun,
    endMoveTag, List.reverse_nil, List.append_nil, evaluatePosition, positionData,
    PositionedRotationMachine.evaluate_phase, PositionedRotationMachine.advance, Fin.zero_eq_one_iff,
    OfNat.ofNat_ne_one, List.tail_cons, PositionedRotationMachine.modeResult, reduceCtorEq,
    PositionedRotationMachine.markerWord, PositionedRotationMachine.evaluate_result, zero_add, Nat.reduceAdd,
    setPositionData, MoveParserMachine.phaseSteps, MoveParserMachine.startSteps, rotateRightTag, Fin.reduceEq, or_false,
    MoveParserMachine.branchCount, pathLeftTag, pathRightTag, or_self, mul_zero, List.length_nil, add_zero,
    rotationFailure]

theorem parser_failure_before_consumption_evaluation :
    evaluate (movePhase .start) (data [6,15] [] [] (treeCode oneTree) [] [] []) =
      ⟨parseFailure, data [6,15] [] [] (treeCode oneTree) [] [] [], 4⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, oneTree, nilTree, treeCode,
    nodeTag, emptyTag, List.cons_append, List.nil_append, rotateLeftTag, ↓reduceIte, moveScanFinish, parsePathRun,
    endMoveTag, Fin.reduceEq, pathLeftTag, pathRightTag, pathTags, List.reverse_nil, List.map_nil,
    MoveParserMachine.phaseSteps, MoveParserMachine.startSteps, rotateRightTag, or_false, MoveParserMachine.branchCount,
    or_self, mul_zero, List.length_nil, add_zero, zero_add, Nat.reduceAdd, parseFailure, Evaluation.mk.injEq,
    LocalData.mk.injEq, List.cons.injEq, and_true, and_self]
  exact ⟨rfl, rfl⟩

theorem old_pending_changes_outcome_evaluation :
    evaluate (movePhase .start) (data [6,10] [] [] (treeCode rightTwo) [] [] [()]) =
      ⟨rotationFailure, data [] [] [] (treeCode rightTwo) [] [] [], 18⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, rightTwo, nilTree, oneTree,
    treeCode, nodeTag, emptyTag, List.cons_append, List.nil_append, rotateLeftTag, ↓reduceIte, moveScanFinish,
    parsePathRun, endMoveTag, List.reverse_nil, List.append_nil, evaluatePosition, positionData,
    PositionedRotationMachine.evaluate_phase, PositionedRotationMachine.advance, Fin.zero_eq_one_iff,
    OfNat.ofNat_ne_one, List.tail_cons, List.cons_ne_self, PositionedRotationMachine.modeResult, reduceCtorEq,
    PositionedRotationMachine.markerWord, PositionedRotationMachine.evaluate_result, zero_add, Nat.reduceAdd,
    setPositionData, MoveParserMachine.phaseSteps, MoveParserMachine.startSteps, rotateRightTag, Fin.reduceEq, or_false,
    MoveParserMachine.branchCount, pathLeftTag, pathRightTag, or_self, mul_zero, List.length_nil, add_zero,
    rotationFailure]

theorem malformed_left_evaluation :
    evaluate (movePhase .start) (data [6,10,15] [] [] [1,0,1,15] [] [] []) =
      ⟨rotationSuccess, data [15] [] [] [1,1,0,15] [] [] [], 11⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, rotateLeftTag, ↓reduceIte,
    moveScanFinish, parsePathRun, endMoveTag, List.reverse_nil, List.append_nil, evaluatePosition, positionData,
    PositionedRotationMachine.evaluate_phase, PositionedRotationMachine.advance, nodeTag, Fin.zero_eq_one_iff,
    OfNat.ofNat_ne_one, emptyTag, List.tail_cons, PositionedRotationMachine.modeResult,
    PositionedRotationMachine.markerWord, List.cons_append, List.nil_append, PositionedRotationMachine.evaluate_result,
    zero_add, Nat.reduceAdd, setPositionData, MoveParserMachine.phaseSteps, MoveParserMachine.startSteps,
    rotateRightTag, Fin.reduceEq, or_false, MoveParserMachine.branchCount, pathLeftTag, pathRightTag, or_self, mul_zero,
    List.length_nil, add_zero, rotationSuccess]

theorem malformed_right_evaluation :
    evaluate (movePhase .start) (data [7,10,15] [] [] [1,1,0,15] [] [] []) =
      ⟨rotationSuccess, data [15] [] [] [1,0,1,15] [] [] [], 10⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, rotateLeftTag, Fin.reduceEq,
    ↓reduceIte, rotateRightTag, moveScanFinish, parsePathRun, endMoveTag, List.reverse_nil, List.append_nil,
    evaluatePosition, positionData, PositionedRotationMachine.evaluate_phase, PositionedRotationMachine.advance,
    nodeTag, and_self, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, emptyTag, List.tail_cons,
    PositionedRotationMachine.modeResult, PositionedRotationMachine.markerWord, List.cons_append, List.nil_append,
    PositionedRotationMachine.evaluate_result, zero_add, Nat.reduceAdd, setPositionData, MoveParserMachine.phaseSteps,
    MoveParserMachine.startSteps, or_true, MoveParserMachine.branchCount, pathLeftTag, pathRightTag, or_self, mul_zero,
    List.length_nil, add_zero, rotationSuccess]

theorem root_left_context_failure_evaluation :
    evaluate (movePhase .start) (data [6,10] [] [] (treeCode leftContext) [] [] []) =
      ⟨rotationFailure, data [] [] [] (treeCode leftContext) [] [] [], 20⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, leftContext, rightTwo,
    nilTree, oneTree, treeCode, nodeTag, emptyTag, List.cons_append, List.nil_append, rotateLeftTag, ↓reduceIte,
    moveScanFinish, parsePathRun, endMoveTag, List.reverse_nil, List.append_nil, evaluatePosition, positionData,
    PositionedRotationMachine.evaluate_phase, PositionedRotationMachine.advance, Fin.zero_eq_one_iff,
    OfNat.ofNat_ne_one, List.tail_cons, List.cons_ne_self, PositionedRotationMachine.modeResult, reduceCtorEq,
    PositionedRotationMachine.markerWord, PositionedRotationMachine.evaluate_result, zero_add, Nat.reduceAdd,
    setPositionData, MoveParserMachine.phaseSteps, MoveParserMachine.startSteps, rotateRightTag, Fin.reduceEq, or_false,
    MoveParserMachine.branchCount, pathLeftTag, pathRightTag, or_self, mul_zero, List.length_nil, add_zero,
    rotationFailure]

theorem old_path_changes_root_result_evaluation :
    evaluate (movePhase .start) (data [6,10] [] [.left] (treeCode leftContext) [] [] []) =
      ⟨rotationSuccess, data [] [] [] (treeCode (.node () leftTwo nilTree)) [] [] [], 13⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, leftContext, rightTwo,
    nilTree, oneTree, treeCode, nodeTag, emptyTag, List.cons_append, List.nil_append, rotateLeftTag, ↓reduceIte,
    moveScanFinish, parsePathRun, endMoveTag, List.reverse_nil, List.append_nil, evaluatePosition, positionData,
    PositionedRotationMachine.evaluate_phase, PositionedRotationMachine.advance, Fin.zero_eq_one_iff,
    OfNat.ofNat_ne_one, List.tail_cons, PositionedRotationMachine.modeResult, PositionedRotationMachine.markerWord,
    PositionedRotationMachine.evaluate_result, zero_add, Nat.reduceAdd, setPositionData, MoveParserMachine.phaseSteps,
    MoveParserMachine.startSteps, rotateRightTag, Fin.reduceEq, or_false, MoveParserMachine.branchCount, pathLeftTag,
    pathRightTag, or_self, mul_zero, List.length_nil, add_zero, rotationSuccess, leftTwo]

theorem author_saved_suffixes_evaluation :
    evaluate (movePhase .start) (data [6,10,15,2,7] [] [] (treeCode rightTwo ++ [14,5]) [12,3] [] []) =
      ⟨rotationSuccess, data [15,2,7] [] [] [3,12,1,1,0,0,0,14,5] [] [] [], 13⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, rightTwo, nilTree, oneTree,
    treeCode, nodeTag, emptyTag, List.cons_append, List.nil_append, rotateLeftTag, ↓reduceIte, moveScanFinish,
    parsePathRun, endMoveTag, List.reverse_nil, List.append_nil, evaluatePosition, positionData,
    PositionedRotationMachine.evaluate_phase, PositionedRotationMachine.advance, Fin.zero_eq_one_iff,
    OfNat.ofNat_ne_one, List.tail_cons, PositionedRotationMachine.modeResult, PositionedRotationMachine.markerWord,
    PositionedRotationMachine.evaluate_result, zero_add, Nat.reduceAdd, setPositionData, MoveParserMachine.phaseSteps,
    MoveParserMachine.startSteps, rotateRightTag, Fin.reduceEq, or_false, MoveParserMachine.branchCount, pathLeftTag,
    pathRightTag, or_self, mul_zero, List.length_nil, add_zero, rotationSuccess]

theorem independent_saved_left_evaluation :
    evaluate (movePhase .start) (data [6,10,15] [] [] (treeCode rightTwo ++ [15,2]) [12,3] [] []) =
      ⟨rotationSuccess, data [15] [] [] [3,12,1,1,0,0,0,15,2] [] [] [], 13⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, rightTwo, nilTree, oneTree,
    treeCode, nodeTag, emptyTag, List.cons_append, List.nil_append, rotateLeftTag, ↓reduceIte, moveScanFinish,
    parsePathRun, endMoveTag, List.reverse_nil, List.append_nil, evaluatePosition, positionData,
    PositionedRotationMachine.evaluate_phase, PositionedRotationMachine.advance, Fin.zero_eq_one_iff,
    OfNat.ofNat_ne_one, List.tail_cons, PositionedRotationMachine.modeResult, PositionedRotationMachine.markerWord,
    PositionedRotationMachine.evaluate_result, zero_add, Nat.reduceAdd, setPositionData, MoveParserMachine.phaseSteps,
    MoveParserMachine.startSteps, rotateRightTag, Fin.reduceEq, or_false, MoveParserMachine.branchCount, pathLeftTag,
    pathRightTag, or_self, mul_zero, List.length_nil, add_zero, rotationSuccess]

theorem independent_saved_right_evaluation :
    evaluate (movePhase .start) (data [7,10,15] [] [] (treeCode leftTwo ++ [15,2]) [12,3] [] []) =
      ⟨rotationSuccess, data [15] [] [] [3,12,1,0,1,0,0,15,2] [] [] [], 12⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, leftTwo, oneTree, nilTree,
    treeCode, nodeTag, emptyTag, List.cons_append, List.nil_append, rotateLeftTag, Fin.reduceEq, ↓reduceIte,
    rotateRightTag, moveScanFinish, parsePathRun, endMoveTag, List.reverse_nil, List.append_nil, evaluatePosition,
    positionData, PositionedRotationMachine.evaluate_phase, PositionedRotationMachine.advance, and_self,
    Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, List.tail_cons, PositionedRotationMachine.modeResult,
    PositionedRotationMachine.markerWord, PositionedRotationMachine.evaluate_result, zero_add, Nat.reduceAdd,
    setPositionData, MoveParserMachine.phaseSteps, MoveParserMachine.startSteps, or_true, MoveParserMachine.branchCount,
    pathLeftTag, pathRightTag, or_self, mul_zero, List.length_nil, add_zero, rotationSuccess]

theorem equal_source_cost_left_evaluation :
    evaluate (movePhase .start) (data [6,8,10] [] [] (treeCode twoRightTwos) [] [] []) =
      ⟨rotationSuccess, data [] [] [] (treeCode (.node () leftTwo rightTwo)) [] [] [], 15⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, twoRightTwos, rightTwo,
    nilTree, oneTree, treeCode, nodeTag, emptyTag, List.cons_append, List.nil_append, rotateLeftTag, ↓reduceIte,
    moveScanFinish, parsePathRun, endMoveTag, Fin.reduceEq, pathLeftTag, Resources.bind, Nat.reduceAdd,
    List.reverse_nil, List.append_nil, evaluatePosition, positionData, PositionedRotationMachine.evaluate_phase,
    PositionedRotationMachine.advance, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, List.tail_cons,
    PositionedRotationMachine.modeResult, PositionedRotationMachine.markerWord,
    PositionedRotationMachine.evaluate_result, zero_add, setPositionData, MoveParserMachine.phaseSteps,
    MoveParserMachine.startSteps, rotateRightTag, or_false, MoveParserMachine.branchCount, pathRightTag, or_self,
    mul_one, List.length_nil, add_zero, rotationSuccess, leftTwo]

theorem equal_source_cost_right_evaluation :
    evaluate (movePhase .start) (data [6,9,10] [] [] (treeCode twoRightTwos) [] [] []) =
      ⟨rotationSuccess, data [] [] [] (treeCode (.node () rightTwo leftTwo)) [] [] [], 25⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, twoRightTwos, rightTwo,
    nilTree, oneTree, treeCode, nodeTag, emptyTag, List.cons_append, List.nil_append, rotateLeftTag, ↓reduceIte,
    moveScanFinish, parsePathRun, endMoveTag, Fin.reduceEq, pathLeftTag, pathRightTag, Resources.bind, Nat.reduceAdd,
    List.reverse_nil, List.append_nil, evaluatePosition, positionData, PositionedRotationMachine.evaluate_phase,
    PositionedRotationMachine.advance, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, List.tail_cons, List.cons_ne_self,
    PositionedRotationMachine.modeResult, PositionedRotationMachine.markerWord,
    PositionedRotationMachine.evaluate_result, zero_add, setPositionData, MoveParserMachine.phaseSteps,
    MoveParserMachine.startSteps, rotateRightTag, or_false, MoveParserMachine.branchCount, or_true, or_self, mul_one,
    List.length_nil, add_zero, rotationSuccess, leftTwo]

theorem consumed_failing_head_evaluation :
    evaluate (movePhase .start) (data [7,8,9,8,10] [] [] (treeCode oneTree) [] [] []) =
      ⟨rotationFailure, data [] [] [.left] (treeCode oneTree) [] [] [], 15⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, oneTree, nilTree, treeCode,
    nodeTag, emptyTag, List.cons_append, List.nil_append, rotateLeftTag, Fin.reduceEq, ↓reduceIte, rotateRightTag,
    moveScanFinish, parsePathRun, endMoveTag, pathLeftTag, Resources.bind, pathRightTag, Nat.reduceAdd,
    List.reverse_nil, List.append_nil, evaluatePosition, positionData, PositionedRotationMachine.evaluate_phase,
    PositionedRotationMachine.advance, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one,
    PositionedRotationMachine.evaluate_result, zero_add, setPositionData, MoveParserMachine.phaseSteps,
    MoveParserMachine.startSteps, or_true, MoveParserMachine.branchCount, or_false, or_self, Nat.reduceMul,
    List.length_nil, add_zero, rotationFailure]

theorem nil_root_failure_evaluation :
    evaluate (movePhase .start) (data [6,10,15] [] [] [0] [] [] []) =
      ⟨rotationFailure, data [15] [] [] [0] [] [] [], 8⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, rotateLeftTag, ↓reduceIte,
    moveScanFinish, parsePathRun, endMoveTag, List.reverse_nil, List.append_nil, evaluatePosition, positionData,
    PositionedRotationMachine.evaluate_phase, PositionedRotationMachine.advance, nodeTag, Fin.zero_eq_one_iff,
    OfNat.ofNat_ne_one, PositionedRotationMachine.evaluate_result, zero_add, Nat.reduceAdd, setPositionData,
    MoveParserMachine.phaseSteps, MoveParserMachine.startSteps, rotateRightTag, Fin.reduceEq, or_false,
    MoveParserMachine.branchCount, pathLeftTag, pathRightTag, or_self, mul_zero, List.length_nil, add_zero,
    rotationFailure]

theorem nil_with_old_path_suffix_evaluation :
    evaluate (movePhase .start) (data [6,8,10,15] [] [.right,.left] [0] [] [] []) =
      ⟨rotationFailure, data [15] [] [.right,.left] [0] [] [] [], 9⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, rotateLeftTag, ↓reduceIte,
    moveScanFinish, parsePathRun, endMoveTag, Fin.reduceEq, pathLeftTag, Resources.bind, Nat.reduceAdd,
    List.reverse_nil, List.nil_append, List.cons_append, evaluatePosition, positionData,
    PositionedRotationMachine.evaluate_phase, PositionedRotationMachine.advance, nodeTag, Fin.zero_eq_one_iff,
    OfNat.ofNat_ne_one, PositionedRotationMachine.evaluate_result, zero_add, setPositionData,
    MoveParserMachine.phaseSteps, MoveParserMachine.startSteps, rotateRightTag, or_false, MoveParserMachine.branchCount,
    pathRightTag, or_self, mul_one, List.length_nil, add_zero, rotationFailure]

theorem dirty_direct_restore_evaluation :
    evaluate (positionPhase (.restoreScratch .successLeft)) (data [15,6] [.right,.left] [.right] [15] [12,3] [14,0] [(),()]) =
      ⟨rotationSuccess, data [15,6] [.right,.left] [.right] [3,12,1,1,0,14,15] [] [] [(),()], 6⟩ := by
  simp only [evaluate, positionPhase, evaluatePosition, positionData, data, Fin.isValue,
    PositionedRotationMachine.evaluate_phase, PositionedRotationMachine.advance, PositionedRotationMachine.modeResult,
    ↓reduceIte, PositionedRotationMachine.markerWord, nodeTag, List.cons_append, List.nil_append,
    PositionedRotationMachine.evaluate_result, zero_add, Nat.reduceAdd, setPositionData, rotationSuccess]

theorem dirty_scratch_principal_evaluation :
    evaluate (movePhase .start) (data [6,10] [] [] [1,0,1,15] [] [14] []) =
      ⟨rotationSuccess, data [] [] [] [1,1,14,0,15] [] [] [], 12⟩ := by
  simp only [evaluate, movePhase, evaluateDispatch, moveFinish, data, Fin.isValue, rotateLeftTag, ↓reduceIte,
    moveScanFinish, parsePathRun, endMoveTag, List.reverse_nil, List.append_nil, evaluatePosition, positionData,
    PositionedRotationMachine.evaluate_phase, PositionedRotationMachine.advance, nodeTag, Fin.zero_eq_one_iff,
    OfNat.ofNat_ne_one, emptyTag, List.tail_cons, PositionedRotationMachine.modeResult,
    PositionedRotationMachine.markerWord, List.cons_append, List.nil_append, PositionedRotationMachine.evaluate_result,
    zero_add, Nat.reduceAdd, setPositionData, MoveParserMachine.phaseSteps, MoveParserMachine.startSteps,
    rotateRightTag, Fin.reduceEq, or_false, MoveParserMachine.branchCount, pathLeftTag, pathRightTag, or_self, mul_zero,
    List.length_nil, add_zero, rotationSuccess]

theorem every_fixed_run_has_its_literal_evaluation
    (c : RunFixture) (member : c ∈ fixedRuns) :
    evaluate c.phase c.before = ⟨c.result, c.after, c.ticks⟩ := by
  simp only [fixedRuns, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact root_left_evaluation
  · exact root_right_evaluation
  · exact two_parsed_branches_evaluation
  · exact reversed_parsed_branches_evaluation
  · exact parsed_before_old_path_evaluation
  · exact dirty_reverse_then_empty_source_evaluation
  · exact dirty_immediate_foreign_evaluation
  · exact dirty_immediate_eof_evaluation
  · exact dirty_accepted_direction_failure_evaluation
  · exact foreign_with_dirty_tree_evaluation
  · exact eof_with_dirty_tree_evaluation
  · exact left_foreign_suffix_evaluation
  · exact right_foreign_suffix_evaluation
  · exact rotation_failure_after_consumption_evaluation
  · exact parser_failure_before_consumption_evaluation
  · exact old_pending_changes_outcome_evaluation
  · exact malformed_left_evaluation
  · exact malformed_right_evaluation
  · exact root_left_context_failure_evaluation
  · exact old_path_changes_root_result_evaluation
  · exact author_saved_suffixes_evaluation
  · exact independent_saved_left_evaluation
  · exact independent_saved_right_evaluation
  · exact equal_source_cost_left_evaluation
  · exact equal_source_cost_right_evaluation
  · exact consumed_failing_head_evaluation
  · exact nil_root_failure_evaluation
  · exact nil_with_old_path_suffix_evaluation
  · exact dirty_direct_restore_evaluation
  · exact dirty_scratch_principal_evaluation

theorem every_fixed_run_is_an_actual_first_live_result
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (c : RunFixture) (member : c ∈ fixedRuns) :
    FirstRun caller (cfg (some (phaseLabel c.phase)) regs c.before ctx) c.ticks
      (cfg (some (resultLabel c.result)) (reset regs) c.after ctx) :=
  fixture_firstRun_of_checked_evaluation caller c regs ctx
    (every_fixed_run_has_its_literal_evaluation c member)

theorem all_fixed_runs_keep_the_independent_context
    (caller : ExampleCaller) (flag : Bool) (c : RunFixture) (member : c ∈ fixedRuns) :
    c.Expected caller flag :=
  every_fixed_run_is_an_actual_first_live_result caller (stale flag) independentContext c member

theorem all_fixed_runs_keep_the_distinct_author_context
    (caller : AuthorCaller) (flag : Bool) (c : RunFixture) (member : c ∈ fixedRuns) :
    FirstRun caller (cfg (some (phaseLabel c.phase)) (stale flag) c.before authorContext) c.ticks
      (cfg (some (resultLabel c.result)) (clean flag) c.after authorContext) :=
  every_fixed_run_is_an_actual_first_live_result caller (stale flag) authorContext c member

def fixedRunInActualTime {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (c : RunFixture) (member : c ∈ fixedRuns) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel c.phase)) regs c.before ctx)
      (some (cfg (some (resultLabel c.result)) (reset regs) c.after ctx)) c.ticks :=
  fixtureInActualTime caller c regs ctx (every_fixed_run_has_its_literal_evaluation c member)

theorem fixed_run_timing_records_the_same_exact_steps
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (c : RunFixture) (member : c ∈ fixedRuns) :
    (fixedRunInActualTime caller regs ctx c member).steps = c.ticks := rfl

section DirtyParser
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem dirty_parser_eof_preserves_its_reverse_accumulator
    (B O : List Branch) (X F S : Word) (Hd : List Unit) :
    LocalRun caller 1
      (cfg (some (moveLabel .start)) regs (data [] B O X F S Hd) ctx)
      (cfg (some (dispatchLabel .failure)) (resetMove regs) (data [] B O X F S Hd) ctx) := by
  simpa only [MoveParserMachine.phaseSteps, MoveParserMachine.startSteps,
    moveFinish, data] using
    move_phase_localRun caller .start (data [] B O X F S Hd) regs ctx

theorem dirty_parser_foreign_first_tag_preserves_its_reverse_accumulator
    (tag : Tag) (C : Word) (B O : List Branch) (X F S : Word) (Hd : List Unit)
    (notLeft : tag ≠ rotateLeftTag) (notRight : tag ≠ rotateRightTag) :
    LocalRun caller 1
      (cfg (some (moveLabel .start)) regs (data (tag :: C) B O X F S Hd) ctx)
      (cfg (some (dispatchLabel .failure)) (resetMove regs)
        (data (tag :: C) B O X F S Hd) ctx) := by
  simpa [MoveParserMachine.phaseSteps, MoveParserMachine.startSteps,
    moveFinish, notLeft, notRight, data] using
    move_phase_localRun caller .start (data (tag :: C) B O X F S Hd) regs ctx

theorem dirty_scan_success_emits_reversed_old_accumulator_then_parsed_then_old_path
    (d : RotationDirection) (C rest : Word) (p B O : List Branch)
    (X F S : Word) (Hd : List Unit) (parsed : (parsePathRun C).1 = some (p, rest)) :
    LocalRun caller (2 * p.length + B.length + 2)
      (cfg (some (moveLabel (.scan d))) regs (data C B O X F S Hd) ctx)
      (cfg (some (dispatchLabel (.success d))) (resetMove regs)
        (data rest [] (B.reverse ++ p ++ O) X F S Hd) ctx) := by
  have rawEq := (parsePathRun_iff C p rest).mp parsed
  have count : MoveParserMachine.branchCount C = p.length := by
    rw [rawEq, MoveParserMachine.branchCount_code]
  simpa [MoveParserMachine.phaseSteps, MoveParserMachine.scanSteps, moveFinish,
    moveScanFinish, parsed, count, data, List.append_assoc] using
    move_phase_localRun caller (.scan d) (data C B O X F S Hd) regs ctx

theorem dirty_scan_failure_materializes_old_reverse_as_tags
    (d : RotationDirection) (C : Word) (B O : List Branch)
    (X F S : Word) (Hd : List Unit) (failed : (parsePathRun C).1 = none) :
    LocalRun caller (2 * MoveParserMachine.branchCount C + B.length + 2)
      (cfg (some (moveLabel (.scan d))) regs (data C B O X F S Hd) ctx)
      (cfg (some (dispatchLabel .failure)) (resetMove regs)
        (data (directionTag d :: (pathTags B.reverse ++ C)) [] O X F S Hd) ctx) := by
  simpa [MoveParserMachine.phaseSteps, MoveParserMachine.scanSteps, moveFinish,
    moveScanFinish, failed, data] using
    move_phase_localRun caller (.scan d) (data C B O X F S Hd) regs ctx

theorem dirty_start_success_keeps_both_old_path_segments
    (d : RotationDirection) (C rest : Word) (p B O : List Branch)
    (X F S : Word) (Hd : List Unit) (parsed : (parsePathRun C).1 = some (p, rest)) :
    LocalRun caller (2 * p.length + B.length + 3)
      (cfg (some (moveLabel .start)) regs (data (directionTag d :: C) B O X F S Hd) ctx)
      (cfg (some (dispatchLabel (.success d))) (resetMove regs)
        (data rest [] (B.reverse ++ p ++ O) X F S Hd) ctx) := by
  have rawEq := (parsePathRun_iff C p rest).mp parsed
  have count : MoveParserMachine.branchCount C = p.length := by
    rw [rawEq, MoveParserMachine.branchCount_code]
  have actual := move_phase_localRun caller .start
    (data (directionTag d :: C) B O X F S Hd) regs ctx
  cases d <;>
    simpa [MoveParserMachine.phaseSteps, MoveParserMachine.startSteps,
      moveFinish, moveScanFinish, directionTag, rotateLeftTag, rotateRightTag,
      parsed, count, data, List.append_assoc] using actual

theorem dirty_start_accepted_direction_failure_does_not_restore_only_the_original_word
    (d : RotationDirection) (C : Word) (B O : List Branch)
    (X F S : Word) (Hd : List Unit) (failed : (parsePathRun C).1 = none) :
    LocalRun caller (2 * MoveParserMachine.branchCount C + B.length + 3)
      (cfg (some (moveLabel .start)) regs (data (directionTag d :: C) B O X F S Hd) ctx)
      (cfg (some (dispatchLabel .failure)) (resetMove regs)
        (data (directionTag d :: (pathTags B.reverse ++ C)) [] O X F S Hd) ctx) := by
  have actual := move_phase_localRun caller .start
    (data (directionTag d :: C) B O X F S Hd) regs ctx
  cases d <;>
    simpa [MoveParserMachine.phaseSteps, MoveParserMachine.startSteps,
      moveFinish, moveScanFinish, directionTag, rotateLeftTag, rotateRightTag,
      failed, data] using actual

theorem arbitrary_dirty_emit_transfers_its_complete_reverse_stack
    (d : RotationDirection) (C : Word) (B O : List Branch)
    (X F S : Word) (Hd : List Unit) :
    LocalRun caller (B.length + 1)
      (cfg (some (moveLabel (.emit d))) regs (data C B O X F S Hd) ctx)
      (cfg (some (dispatchLabel (.success d))) (resetMove regs)
        (data C [] (B.reverse ++ O) X F S Hd) ctx) := by
  simpa only [MoveParserMachine.phaseSteps, moveFinish, data] using
    move_phase_localRun caller (.emit d) (data C B O X F S Hd) regs ctx

theorem arbitrary_dirty_undo_materializes_direction_after_reversed_branch_tags
    (d : RotationDirection) (C : Word) (B O : List Branch)
    (X F S : Word) (Hd : List Unit) :
    LocalRun caller (B.length + 1)
      (cfg (some (moveLabel (.undo d))) regs (data C B O X F S Hd) ctx)
      (cfg (some (dispatchLabel .failure)) (resetMove regs)
        (data (directionTag d :: (pathTags B.reverse ++ C)) [] O X F S Hd) ctx) := by
  simpa only [MoveParserMachine.phaseSteps, moveFinish, data] using
    move_phase_localRun caller (.undo d) (data C B O X F S Hd) regs ctx

theorem an_internal_parser_failure_pays_its_separate_dispatch
    (start : Cfg Γ Λ R) (n : Nat) (D : LocalData)
    (actual : LocalRun caller n start
      (cfg (some (dispatchLabel .failure)) (resetMove regs) D ctx)) :
    FirstRun caller start (n + 1)
      (cfg (some (resultLabel parseFailure)) (reset regs) D ctx) := by
  have joined := LocalRun.trans caller actual
    (dispatch_localRun caller .failure D (resetMove regs) ctx)
  apply local_run_gives_an_actual_first_return caller
  · simpa only [dispatchTarget, MoveApplyMachine.parseFailure, parseFailure,
      reset_resetMove] using joined
  · exact not_owned_result parseFailure

theorem dirty_author_orientation_is_an_actual_internal_boundary
    (X F S : Word) (Hd : List Unit) :
    Runs caller
      (cfg (some (moveLabel .start)) regs
        (data [6,8,9,10] [.right,.left] [.left] X F S Hd) ctx) 9
      (cfg (some (dispatchLabel (.success .left))) (resetMove regs)
        (data [] [] [.left,.right,.left,.right,.left] X F S Hd) ctx) := by
  exact LocalRun.iterate caller
    (dirty_start_success_keeps_both_old_path_segments caller regs ctx .left
      [8,9,10] [] [.left,.right] [.right,.left] [.left] X F S Hd rfl)

end DirtyParser


section FrontEndPhysicalCompatibility
variable {K Λ R : Type} {Γ : K → Type}

theorem front_end_view_accounts_for_all_sixteen_local_stores :
    frontEndStackEquiv (K := K) (.inl .framedRaw) = .inr (.inl .framedRaw) ∧
      frontEndStackEquiv (K := K) (.inl .frameFirstReverse) = .inr (.inl .frameFirstReverse) ∧
      frontEndStackEquiv (K := K) (.inl .frameCertReverse) = .inr (.inl .frameCertReverse) ∧
      frontEndStackEquiv (K := K) (.inl .inputBits) = .inr (.inl .inputBits) ∧
      frontEndStackEquiv (K := K) (.inl .certificateBits) = .inr (.inl .certificateBits) ∧
      frontEndStackEquiv (K := K) (.inl .inputRaw) = .inr (.inl .inputRaw) ∧
      frontEndStackEquiv (K := K) (.inl .targetTree) = .inr (.inl .targetTree) ∧
      frontEndStackEquiv (K := K) (.inl .fuel) = .inr (.inl .fuel) ∧
      frontEndStackEquiv (K := K) (.inl .bitsReverse) = .inr (.inl .bitsReverse) ∧
      frontEndStackEquiv (K := K) (.inl .certificateWord) = .inl .certificate ∧
      frontEndStackEquiv (K := K) (.inl .sourceTree) = .inl .source ∧
      frontEndStackEquiv (K := K) (.inl .treeReverse) = .inl .saved ∧
      frontEndStackEquiv (K := K) (.inl .decodeReverse) = .inl .scratch ∧
      frontEndStackEquiv (K := K) (.inl .pending) = .inl .pending ∧
      frontEndStackEquiv (K := K) (.inr (.inl .moveReverse)) = .inl .moveReverse ∧
      frontEndStackEquiv (K := K) (.inr (.inl .path)) = .inl .path ∧
      (∀ k : K, frontEndStackEquiv (.inr (.inr k)) = .inr (.inr k)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem front_end_complete_index_map_has_both_inverse_laws
    (source : FrontEndMachine.StackId (NewBranchStores ⊕ K))
    (target : StackId (FrontEndProtected ⊕ K)) :
    frontEndStackEquiv.symm (frontEndStackEquiv source) = source ∧
      frontEndStackEquiv (frontEndStackEquiv.symm target) = target :=
  ⟨frontEndStackEquiv.symm_apply_apply source, frontEndStackEquiv.apply_symm_apply target⟩

theorem front_end_dependent_words_are_transported_without_losing_cells
    [Fintype K]
    (stores : ∀ k, List (FrontEndMachine.Alphabet (FrontEndAddedAlphabet Γ) k)) :
    (∀ k, frontEndStacks stores (frontEndStackEquiv k) =
      (stores k).map (frontEndSymbolEquiv k)) ∧
    (∑ k, (frontEndStacks stores k).length) = ∑ k, (stores k).length :=
  ⟨frontEndStacks_apply stores, front_end_stack_cells stores⟩

theorem front_end_register_permutation_preserves_every_field
    (tag : Option Tag) (unit : Option Unit) (decoder : OpenDecoderMachine.Temporaries)
    (branch : Option Branch) (user : R) :
    frontEndRegisterEquiv ((tag, unit), (decoder, (branch, user))) =
      ((branch, (tag, unit)), (decoder, user)) ∧
    frontEndRegisterEquiv.symm ((branch, (tag, unit)), (decoder, user)) =
      ((tag, unit), (decoder, (branch, user))) := ⟨rfl, rfl⟩

theorem front_end_reset_keeps_its_protected_branch_until_the_paid_dispatch
    (regs : FrontEndMachine.Registers (Option Branch × R)) :
    frontEndRegisterEquiv (FrontEndMachine.reset regs) =
        ((regs.2.2.1, (none, none)), (BitDecoderMachine.zeroRegisters, regs.2.2.2)) ∧
      resetMove (frontEndRegisterEquiv (FrontEndMachine.reset regs)) =
        frontEndRegisterEquiv (FrontEndMachine.reset regs) ∧
      reset (frontEndRegisterEquiv (FrontEndMachine.reset regs)) =
        ((none, (none, none)), (BitDecoderMachine.zeroRegisters, regs.2.2.2)) :=
  ⟨frontEndRegisterEquiv_reset regs, frontEndRegisterEquiv_resetMove regs,
    frontEndRegisterEquiv_fullReset regs⟩

theorem actual_front_end_success_has_the_complete_label_neutral_physical_data
    (regs : FrontEndMachine.Registers (Option Branch × R)) (B O : List Branch)
    (ctx : ∀ k, List (Γ k)) (s t : BinaryTree Unit) (fuel : Bits) (cert : Word) :
    frontEndPhysicalData (FrontEndMachine.resultCfg (Λ := Λ) regs
      (frontEndAddedContext B O ctx) (.success s t fuel cert)) =
      (((regs.2.2.1, (none, none)), (BitDecoderMachine.zeroRegisters, regs.2.2.2)),
        (cfg (Λ := Unit) none (frontEndRegisterEquiv (FrontEndMachine.reset regs))
          (data cert B O (treeCode s) [] [] [])
          (frontEndSuccessContext t fuel ctx)).stk) :=
  front_end_success_physical_data regs B O ctx s t fuel cert

theorem front_end_keeps_target_fuel_and_the_external_context
    (t : BinaryTree Unit) (fuel : Bits) (ctx : ∀ k, List (Γ k)) :
    frontEndSuccessContext t fuel ctx (.inl .targetTree) = treeCode t ∧
      frontEndSuccessContext t fuel ctx (.inl .fuel) = fuel ∧
      (∀ k, frontEndSuccessContext t fuel ctx (.inr k) = ctx k) ∧
      frontEndSuccessContext t fuel ctx (.inl .inputRaw) = [] ∧
      frontEndSuccessContext t fuel ctx (.inl .framedRaw) = [] ∧
      frontEndSuccessContext t fuel ctx (.inl .frameFirstReverse) = [] ∧
      frontEndSuccessContext t fuel ctx (.inl .frameCertReverse) = [] ∧
      frontEndSuccessContext t fuel ctx (.inl .inputBits) = [] ∧
      frontEndSuccessContext t fuel ctx (.inl .certificateBits) = [] ∧
      frontEndSuccessContext t fuel ctx (.inl .bitsReverse) = [] :=
  ⟨rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem front_end_physical_dimensions_match_both_complete_presentations
    [Fintype K] [Fintype R] :
    Fintype.card (FrontEndMachine.StackId (NewBranchStores ⊕ K)) = 16 + Fintype.card K ∧
      Fintype.card (StackId (FrontEndProtected ⊕ K)) = 16 + Fintype.card K ∧
      Fintype.card (FrontEndMachine.Registers (Option Branch × R)) = 140454 * Fintype.card R ∧
      Fintype.card (Registers (OpenDecoderMachine.Temporaries × R)) = 140454 * Fintype.card R :=
  ⟨front_end_source_stack_card, front_end_stack_card,
    front_end_source_register_card, front_end_register_card⟩

theorem front_end_success_protected_cells_are_exact
    [Fintype K] (t : BinaryTree Unit) (fuel : Bits) (ctx : ∀ k, List (Γ k)) :
    (∑ k, (frontEndSuccessContext t fuel ctx k).length) =
      (treeCode t).length + fuel.length + ∑ k, (ctx k).length :=
  front_end_success_context_cells t fuel ctx

end FrontEndPhysicalCompatibility

def frontEndStale (flag : Bool) : FrontEndMachine.Registers (Option Branch × Bool) :=
  ((some (15 : Tag), some ()), (BitDecoderMachine.zeroRegisters, (some .right, flag)))

theorem stale_front_end_branch_is_not_a_full_move_reset (flag : Bool) :
    frontEndRegisterEquiv (FrontEndMachine.reset (frontEndStale flag)) =
      ((some .right, (none, none)), (BitDecoderMachine.zeroRegisters, flag)) ∧
    frontEndRegisterEquiv (FrontEndMachine.reset (frontEndStale flag)) ≠
      reset (frontEndRegisterEquiv (FrontEndMachine.reset (frontEndStale flag))) := by
  refine ⟨rfl, ?_⟩
  intro same
  have observed := congrArg (fun regs : Registers (OpenDecoderMachine.Temporaries × Bool) =>
    regs.1.1) same
  cases observed

theorem dirty_added_branch_words_remain_literal_at_front_end_success
    (flag : Bool) (s t : BinaryTree Unit) (fuel : Bits) (cert : Word) :
    frontEndPhysicalData (FrontEndMachine.resultCfg (Λ := Nat) (frontEndStale flag)
      (frontEndAddedContext [.right,.left] [.left] independentContext)
      (.success s t fuel cert)) =
      (((some .right, (none, none)), (BitDecoderMachine.zeroRegisters, flag)),
        (cfg (Λ := Unit) none
          ((some .right, (none, none)), (BitDecoderMachine.zeroRegisters, flag))
          (data cert [.right,.left] [.left] (treeCode s) [] [] [])
          (frontEndSuccessContext t fuel independentContext)).stk) :=
  actual_front_end_success_has_the_complete_label_neutral_physical_data
    (frontEndStale flag) [.right,.left] [.left] independentContext s t fuel cert

theorem clean_added_stores_at_front_end_success_keep_the_same_stale_branch
    (flag : Bool) (s t : BinaryTree Unit) (fuel : Bits) (cert : Word) :
    frontEndPhysicalData (FrontEndMachine.resultCfg (Λ := Nat) (frontEndStale flag)
      (frontEndAddedContext [] [] authorContext) (.success s t fuel cert)) =
      (((some .right, (none, none)), (BitDecoderMachine.zeroRegisters, flag)),
        (cfg (Λ := Unit) none
          ((some .right, (none, none)), (BitDecoderMachine.zeroRegisters, flag))
          (data cert [] [] (treeCode s) [] [] [])
          (frontEndSuccessContext t fuel authorContext)).stk) :=
  actual_front_end_success_has_the_complete_label_neutral_physical_data
    (frontEndStale flag) [] [] authorContext s t fuel cert


end Examples.RotationCertificateMoveApplyMachine
