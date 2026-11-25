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
    Nonempty (Fintype (alphabet IndependentAlphabet k)) := ⟨inferInstance⟩

theorem every_author_stack_alphabet_is_finite (k : StackId (Fin 2)) :
    Nonempty (Fintype (alphabet AuthorAlphabet k)) := ⟨inferInstance⟩

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
    (stores : ∀ k, List (FrontEndMachine.alphabet (frontEndAddedAlphabet Γ) k)) :
    (∀ k, frontEndStacks stores (frontEndStackEquiv k) =
      (stores k).map (frontEndSymbolEquiv k)) ∧
    (∑ k, (frontEndStacks stores k).length) = ∑ k, (stores k).length :=
  ⟨frontEndStacks_apply stores, frontEnd_stack_cells stores⟩

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
  frontEnd_success_physical_data regs B O ctx s t fuel cert

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
  ⟨frontEnd_source_stack_card, frontEnd_stack_card,
    frontEnd_source_register_card, frontEnd_register_card⟩

theorem front_end_success_protected_cells_are_exact
    [Fintype K] (t : BinaryTree Unit) (fuel : Bits) (ctx : ∀ k, List (Γ k)) :
    (∑ k, (frontEndSuccessContext t fuel ctx k).length) =
      (treeCode t).length + fuel.length + ∑ k, (ctx k).length :=
  frontEnd_success_context_cells t fuel ctx

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

section PrincipalConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem independent_first_result_is_the_public_strict_first_result
    (start : Cfg Γ Λ R) (r : FinalResult) :
    FirstResult caller start r ↔ MoveApplyMachine.FirstResult caller start r := by
  constructor
  · rintro ⟨n, finish, first, label⟩
    exact ⟨n, finish, first.1, label, first.2.2⟩
  · rintro ⟨n, finish, run, label, earlier⟩
    refine ⟨n, finish, ⟨run, ?_, earlier⟩, label⟩
    rw [label]
    exact not_owned_result r

theorem principal_parser_failure_has_the_complete_dirty_endpoint_and_paid_clock
    (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit) :
    ParserFailureExpected caller regs ctx C O X F S Hd := by
  intro failed
  refine ⟨parse_failure_boundary caller C O X F S Hd regs ctx failed, ?_,
    parser_failure_source_cost C failed⟩
  exact local_run_gives_an_actual_first_return caller
    (run_of_none_localRun caller C O X F S Hd regs ctx failed) (not_owned_result parseFailure)

theorem principal_parser_success_pays_for_the_complete_dirty_position_entry
    (C rest : Word) (mv : RotationMove) (O : List Branch)
    (X F S : Word) (Hd : List Unit) :
    ParserSuccessExpected caller regs ctx C rest mv O X F S Hd := by
  intro parsed
  have count := MoveParserMachine.fullSteps_of_some C mv rest parsed
  have paidCount : MoveParserMachine.fullSteps C + 1 = 2 * mv.position.length + 4 := by omega
  refine ⟨count, parse_success_boundary caller C mv rest O X F S Hd regs ctx parsed, ?_, ?_⟩
  · simpa only [Runs, paidCount, entry, entryData, parsedData, data] using
      paid_position_entry caller C mv rest O X F S Hd regs ctx parsed
  · have actual := local_run_gives_an_actual_first_return caller
      (run_of_some_localRun caller C mv rest O X F S Hd regs ctx parsed)
      (phaseResult_not_owned (MoveApplyMachine.positionPhase (.seek mv.direction)) regs
        (parsedData mv rest (entryData C O X F S Hd)) ctx)
    simpa only [paidCount, entry, entryData, parsedData, positionData,
      data, phaseResult_reset, positionPhase, MoveApplyMachine.positionPhase] using actual

theorem first_parse_failure_iff_the_actual_source_parser_failed
    (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit) :
    FirstResult caller
      (cfg (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx) parseFailure ↔
      (parseMoveRun C).1 = none := by
  rw [independent_first_result_is_the_public_strict_first_result]
  exact first_parseFailure_iff caller C O X F S Hd regs ctx

theorem first_rotation_failure_iff_the_actual_dirty_position_endpoint_failed
    (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit) :
    FirstResult caller
      (cfg (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx) rotationFailure ↔
      ∃ mv rest, (parseMoveRun C).1 = some (mv, rest) ∧
        (PositionedRotationMachine.phaseResult (Λ := PositionCallerLabel Λ) (.seek mv.direction)
          regs { source := X, saved := F, scratch := S, pending := Hd, path := mv.position ++ O }
          (positionContext { certificate := rest } ctx)).l =
            some (PositionedRotationMachine.resultLabel .failure) := by
  rw [independent_first_result_is_the_public_strict_first_result]
  exact first_rotationFailure_iff caller C O X F S Hd regs ctx

theorem first_success_iff_the_actual_dirty_position_endpoint_succeeded
    (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit) :
    FirstResult caller
      (cfg (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx) rotationSuccess ↔
      ∃ mv rest, (parseMoveRun C).1 = some (mv, rest) ∧
        (PositionedRotationMachine.phaseResult (Λ := PositionCallerLabel Λ) (.seek mv.direction)
          regs { source := X, saved := F, scratch := S, pending := Hd, path := mv.position ++ O }
          (positionContext { certificate := rest } ctx)).l =
            some (PositionedRotationMachine.resultLabel .success) := by
  rw [independent_first_result_is_the_public_strict_first_result]
  exact MoveApplyMachine.first_success_iff caller C O X F S Hd regs ctx

theorem each_of_the_three_first_results_fixes_the_same_complete_clock_and_configuration
    (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit)
    (r : FinalResult) (n : Nat) (finish : Cfg Γ Λ R)
    (first : FirstRun caller
      (cfg (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx) n finish)
    (label : finish.l = some (resultLabel r)) :
    n = runSteps C O X F S Hd ∧ finish = runResult regs C O X F S Hd ctx :=
  first_result_complete caller (MoveApplyMachine.movePhase .start)
    (entryData C O X F S Hd) regs ctx r n finish first.1 label first.2.2

def principalInActualTime (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx)
      (some (runResult regs C O X F S Hd ctx)) (runSteps C O X F S Hd) :=
  runInTimeExact caller C O X F S Hd regs ctx

theorem principal_typed_time_records_actual_composite_steps
    (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit) :
    (principalInActualTime caller regs ctx C O X F S Hd).steps = runSteps C O X F S Hd := rfl

end PrincipalConnections

section LiteralBoundarySteps
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

def parserObservationCaller : MoveParserMachine.External (MoveCallerLabel Λ) →
    MoveStatement Γ Λ R := fun _ => .halt
def positionObservationCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
    PositionStatement Γ Λ R := fun _ => .halt

theorem move_step_of_actual_component_observation
    (q : MoveParserMachine.Phase) (before after : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k))
    (label : Option (MoveParserMachine.Label (MoveCallerLabel Λ)))
    (outRegs : MoveParserMachine.Registers (MoveCallerRegister R))
    (observed : MoveParserMachine.step parserObservationCaller
      (moveView (some (MoveParserMachine.phaseLabel q)) (moveRegisterEquiv.symm regs) before ctx) =
        some (moveView label outRegs after ctx)) :
    step caller (cfg (some (moveLabel q)) regs before ctx) =
      some (cfg (label.map moveLabelEquiv) (moveRegisterEquiv outRegs) after ctx) := by
  have actual := move_step_transport caller parserObservationCaller
    (moveView (some (MoveParserMachine.phaseLabel q)) (moveRegisterEquiv.symm regs) before ctx)
    (by trivial)
  rw [observed, Option.map_some, moveCfg_view, moveCfg_view] at actual
  simpa only [Option.map_some, moveLabelEquiv_phase, Equiv.apply_symm_apply] using actual

theorem move_start_direction_actual (d : RotationDirection) (C : Word)
    (B O : List Branch) (X F S : Word) (Hd : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (moveLabel .start)) regs
      (data (directionTag d :: C) B O X F S Hd) ctx) =
      some (cfg (some (moveLabel (.scan d))) (resetMove regs) (data C B O X F S Hd) ctx) := by
  exact move_step_of_actual_component_observation caller .start _ _ regs ctx
    (some (MoveParserMachine.phaseLabel (.scan d)))
    (MoveParserMachine.reset (moveRegisterEquiv.symm regs))
    (MoveParserMachine.start_step_direction parserObservationCaller d C B O
      (moveRegisterEquiv.symm regs) (moveContext (data C B O X F S Hd) ctx))

theorem move_scan_branch_actual (d : RotationDirection) (b : Branch) (C : Word)
    (B O : List Branch) (X F S : Word) (Hd : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (moveLabel (.scan d))) regs
      (data (branchTag b :: C) B O X F S Hd) ctx) =
      some (cfg (some (moveLabel (.scan d))) (resetMove regs) (data C (b :: B) O X F S Hd) ctx) := by
  exact move_step_of_actual_component_observation caller (.scan d) _ _ regs ctx
    (some (MoveParserMachine.phaseLabel (.scan d)))
    (MoveParserMachine.reset (moveRegisterEquiv.symm regs))
    (MoveParserMachine.scan_step_branch parserObservationCaller d b C B O
      (moveRegisterEquiv.symm regs) (moveContext (data C B O X F S Hd) ctx))

theorem move_scan_end_actual (d : RotationDirection) (C : Word)
    (B O : List Branch) (X F S : Word) (Hd : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (moveLabel (.scan d))) regs
      (data (endMoveTag :: C) B O X F S Hd) ctx) =
      some (cfg (some (moveLabel (.emit d))) (resetMove regs) (data C B O X F S Hd) ctx) := by
  exact move_step_of_actual_component_observation caller (.scan d) _ _ regs ctx
    (some (MoveParserMachine.phaseLabel (.emit d)))
    (MoveParserMachine.reset (moveRegisterEquiv.symm regs))
    (MoveParserMachine.scan_step_end parserObservationCaller d C B O
      (moveRegisterEquiv.symm regs) (moveContext (data C B O X F S Hd) ctx))

theorem move_scan_eof_actual (d : RotationDirection)
    (B O : List Branch) (X F S : Word) (Hd : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (moveLabel (.scan d))) regs (data [] B O X F S Hd) ctx) =
      some (cfg (some (moveLabel (.undo d))) (resetMove regs) (data [] B O X F S Hd) ctx) := by
  exact move_step_of_actual_component_observation caller (.scan d) _ _ regs ctx
    (some (MoveParserMachine.phaseLabel (.undo d)))
    (MoveParserMachine.reset (moveRegisterEquiv.symm regs))
    (MoveParserMachine.scan_step_nil parserObservationCaller d B O
      (moveRegisterEquiv.symm regs) (moveContext (data [] B O X F S Hd) ctx))

theorem move_emit_empty_actual (d : RotationDirection) (C : Word)
    (O : List Branch) (X F S : Word) (Hd : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (moveLabel (.emit d))) regs (data C [] O X F S Hd) ctx) =
      some (cfg (some (dispatchLabel (.success d))) (resetMove regs) (data C [] O X F S Hd) ctx) := by
  exact move_step_of_actual_component_observation caller (.emit d) _ _ regs ctx
    (some (MoveParserMachine.resultLabel (.success d)))
    (MoveParserMachine.reset (moveRegisterEquiv.symm regs))
    (MoveParserMachine.emit_step_nil parserObservationCaller d C O
      (moveRegisterEquiv.symm regs) (moveContext (data C [] O X F S Hd) ctx))

theorem move_undo_branch_actual (d : RotationDirection) (b : Branch) (C : Word)
    (B O : List Branch) (X F S : Word) (Hd : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (moveLabel (.undo d))) regs (data C (b :: B) O X F S Hd) ctx) =
      some (cfg (some (moveLabel (.undo d))) (resetMove regs)
        (data (branchTag b :: C) B O X F S Hd) ctx) := by
  exact move_step_of_actual_component_observation caller (.undo d) _ _ regs ctx
    (some (MoveParserMachine.phaseLabel (.undo d)))
    (MoveParserMachine.reset (moveRegisterEquiv.symm regs))
    (MoveParserMachine.undo_step_cons parserObservationCaller d b C B O
      (moveRegisterEquiv.symm regs) (moveContext (data C B O X F S Hd) ctx))

theorem move_undo_empty_actual (d : RotationDirection) (C : Word)
    (O : List Branch) (X F S : Word) (Hd : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (moveLabel (.undo d))) regs (data C [] O X F S Hd) ctx) =
      some (cfg (some (dispatchLabel .failure)) (resetMove regs)
        (data (directionTag d :: C) [] O X F S Hd) ctx) := by
  exact move_step_of_actual_component_observation caller (.undo d) _ _ regs ctx
    (some (MoveParserMachine.resultLabel .failure))
    (MoveParserMachine.reset (moveRegisterEquiv.symm regs))
    (MoveParserMachine.undo_step_nil parserObservationCaller d C O
      (moveRegisterEquiv.symm regs) (moveContext (data C [] O X F S Hd) ctx))

theorem every_position_observation_uses_the_actual_transported_primitive_step
    (q : PositionedRotationMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (positionLabel q)) regs D ctx) =
      some (cfg (some (positionLabelEquiv
        (PositionedRotationMachine.controlLabel (PositionedRotationMachine.advance q (positionData D)).1)))
        (reset regs) (setPositionData D (PositionedRotationMachine.advance q (positionData D)).2) ctx) := by
  have labels (control : PositionedRotationMachine.Control) :
      positionLabelEquiv (PositionedRotationMachine.controlLabel control) =
        positionControlLabel (Λ := Λ) control := by
    cases control <;> rfl
  rw [labels]
  exact position_advance_step caller q D regs ctx

end LiteralBoundarySteps

private theorem boundary_run_succ {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) {start before after : Cfg Γ Λ R}
    {n : Nat} (prior : Runs caller start n before)
    (one : step caller before = some after) : Runs caller start (n + 1) after := by
  change (next caller)^[n] (some start) = some before at prior
  change (next caller)^[n + 1] (some start) = some after
  rw [Function.iterate_succ_apply', prior, next_some, one]

section LiteralBoundaryRuns
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem every_left_literal_row_is_the_actual_reached_configuration
    (b : Boundary) (member : b ∈ leftBoundaries) :
    Runs caller
      (cfg (some (moveLabel .start)) regs (data [6,10,15] [] [] [1,0,1,15] [] [] []) ctx)
      b.tick (b.cfg regs ctx) := by
  let c0 : Cfg Γ Λ R := (⟨0, .inl (movePhase .start), data [6,10,15] [] [] [1,0,1,15] [] [] [], .original, 7, 11⟩ : Boundary).cfg regs ctx
  let c1 : Cfg Γ Λ R := (⟨1, .inl (movePhase (.scan .left)), data [10,15] [] [] [1,0,1,15] [] [] [], .parser, 6, 11⟩ : Boundary).cfg regs ctx
  let c2 : Cfg Γ Λ R := (⟨2, .inl (movePhase (.emit .left)), data [15] [] [] [1,0,1,15] [] [] [], .parser, 5, 11⟩ : Boundary).cfg regs ctx
  let c3 : Cfg Γ Λ R := (⟨3, .inl (dispatchPhase (.success .left)), data [15] [] [] [1,0,1,15] [] [] [], .parser, 5, 11⟩ : Boundary).cfg regs ctx
  let c4 : Cfg Γ Λ R := (⟨4, .inl (positionPhase (.seek .left)), data [15] [] [] [1,0,1,15] [] [] [], .complete, 5, 9⟩ : Boundary).cfg regs ctx
  let c5 : Cfg Γ Λ R := (⟨5, .inl (positionPhase (.start .left)), data [15] [] [] [1,0,1,15] [] [] [], .complete, 5, 9⟩ : Boundary).cfg regs ctx
  let c6 : Cfg Γ Λ R := (⟨6, .inl (positionPhase (.scanScratch .left)), data [15] [] [] [0,1,15] [] [] [()], .complete, 5, 9⟩ : Boundary).cfg regs ctx
  let c7 : Cfg Γ Λ R := (⟨7, .inl (positionPhase .checkRight), data [15] [] [] [1,15] [] [0] [], .complete, 4, 7⟩ : Boundary).cfg regs ctx
  let c8 : Cfg Γ Λ R := (⟨8, .inl (positionPhase (.restoreScratch .successLeft)), data [15] [] [] [15] [] [0] [], .complete, 3, 5⟩ : Boundary).cfg regs ctx
  let c9 : Cfg Γ Λ R := (⟨9, .inl (positionPhase (.restoreScratch .successLeft)), data [15] [] [] [0,15] [] [] [], .complete, 3, 5⟩ : Boundary).cfg regs ctx
  let c10 : Cfg Γ Λ R := (⟨10, .inl (positionPhase (.restorePrefix .success)), data [15] [] [] [1,1,0,15] [] [] [], .complete, 5, 5⟩ : Boundary).cfg regs ctx
  let c11 : Cfg Γ Λ R := (⟨11, .inr rotationSuccess, data [15] [] [] [1,1,0,15] [] [] [], .complete, 5, 5⟩ : Boundary).cfg regs ctx
  have r0 : Runs caller c0 0 c0 := rfl
  have s1 : step caller c0 = some c1 := by
    dsimp only [c0, c1, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_start_direction_actual caller .left _ _ _ _ _ _ _ _ _
  have r1 := boundary_run_succ caller r0 s1
  have s2 : step caller c1 = some c2 := by
    dsimp only [c1, c2, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_scan_end_actual caller .left _ _ _ _ _ _ _ _ _
  have r2 := boundary_run_succ caller r1 s2
  have s3 : step caller c2 = some c3 := by
    dsimp only [c2, c3, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_emit_empty_actual caller .left _ _ _ _ _ _ _ _
  have r3 := boundary_run_succ caller r2 s3
  have s4 : step caller c3 = some c4 := by
    dsimp only [c3, c4, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact dispatch_step caller _ _ _ _
  have r4 := boundary_run_succ caller r3 s4
  have s5 : step caller c4 = some c5 := by
    dsimp only [c4, c5, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r5 := boundary_run_succ caller r4 s5
  have s6 : step caller c5 = some c6 := by
    dsimp only [c5, c6, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r6 := boundary_run_succ caller r5 s6
  have s7 : step caller c6 = some c7 := by
    dsimp only [c6, c7, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r7 := boundary_run_succ caller r6 s7
  have s8 : step caller c7 = some c8 := by
    dsimp only [c7, c8, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r8 := boundary_run_succ caller r7 s8
  have s9 : step caller c8 = some c9 := by
    dsimp only [c8, c9, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r9 := boundary_run_succ caller r8 s9
  have s10 : step caller c9 = some c10 := by
    dsimp only [c9, c10, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r10 := boundary_run_succ caller r9 s10
  have s11 : step caller c10 = some c11 := by
    dsimp only [c10, c11, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r11 := boundary_run_succ caller r10 s11
  simp only [leftBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7
  · exact r8
  · exact r9
  · exact r10
  · exact r11

theorem every_right_literal_row_is_the_actual_reached_configuration
    (b : Boundary) (member : b ∈ rightBoundaries) :
    Runs caller
      (cfg (some (moveLabel .start)) regs (data [7,10,15] [] [] [1,1,0,15] [] [] []) ctx)
      b.tick (b.cfg regs ctx) := by
  let c0 : Cfg Γ Λ R := (⟨0, .inl (movePhase .start), data [7,10,15] [] [] [1,1,0,15] [] [] [], .original, 7, 11⟩ : Boundary).cfg regs ctx
  let c1 : Cfg Γ Λ R := (⟨1, .inl (movePhase (.scan .right)), data [10,15] [] [] [1,1,0,15] [] [] [], .parser, 6, 11⟩ : Boundary).cfg regs ctx
  let c2 : Cfg Γ Λ R := (⟨2, .inl (movePhase (.emit .right)), data [15] [] [] [1,1,0,15] [] [] [], .parser, 5, 11⟩ : Boundary).cfg regs ctx
  let c3 : Cfg Γ Λ R := (⟨3, .inl (dispatchPhase (.success .right)), data [15] [] [] [1,1,0,15] [] [] [], .parser, 5, 11⟩ : Boundary).cfg regs ctx
  let c4 : Cfg Γ Λ R := (⟨4, .inl (positionPhase (.seek .right)), data [15] [] [] [1,1,0,15] [] [] [], .complete, 5, 9⟩ : Boundary).cfg regs ctx
  let c5 : Cfg Γ Λ R := (⟨5, .inl (positionPhase (.start .right)), data [15] [] [] [1,1,0,15] [] [] [], .complete, 5, 9⟩ : Boundary).cfg regs ctx
  let c6 : Cfg Γ Λ R := (⟨6, .inl (positionPhase (.scanScratch .right)), data [15] [] [] [0,15] [] [] [()], .complete, 4, 8⟩ : Boundary).cfg regs ctx
  let c7 : Cfg Γ Λ R := (⟨7, .inl (positionPhase (.restoreScratch .successRight)), data [15] [] [] [1,15] [] [0] [], .complete, 4, 5⟩ : Boundary).cfg regs ctx
  let c8 : Cfg Γ Λ R := (⟨8, .inl (positionPhase (.restoreScratch .successRight)), data [15] [] [] [0,1,15] [] [] [], .complete, 4, 5⟩ : Boundary).cfg regs ctx
  let c9 : Cfg Γ Λ R := (⟨9, .inl (positionPhase (.restorePrefix .success)), data [15] [] [] [1,0,1,15] [] [] [], .complete, 5, 5⟩ : Boundary).cfg regs ctx
  let c10 : Cfg Γ Λ R := (⟨10, .inr rotationSuccess, data [15] [] [] [1,0,1,15] [] [] [], .complete, 5, 5⟩ : Boundary).cfg regs ctx
  have r0 : Runs caller c0 0 c0 := rfl
  have s1 : step caller c0 = some c1 := by
    dsimp only [c0, c1, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_start_direction_actual caller .right _ _ _ _ _ _ _ _ _
  have r1 := boundary_run_succ caller r0 s1
  have s2 : step caller c1 = some c2 := by
    dsimp only [c1, c2, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_scan_end_actual caller .right _ _ _ _ _ _ _ _ _
  have r2 := boundary_run_succ caller r1 s2
  have s3 : step caller c2 = some c3 := by
    dsimp only [c2, c3, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_emit_empty_actual caller .right _ _ _ _ _ _ _ _
  have r3 := boundary_run_succ caller r2 s3
  have s4 : step caller c3 = some c4 := by
    dsimp only [c3, c4, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact dispatch_step caller _ _ _ _
  have r4 := boundary_run_succ caller r3 s4
  have s5 : step caller c4 = some c5 := by
    dsimp only [c4, c5, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r5 := boundary_run_succ caller r4 s5
  have s6 : step caller c5 = some c6 := by
    dsimp only [c5, c6, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r6 := boundary_run_succ caller r5 s6
  have s7 : step caller c6 = some c7 := by
    dsimp only [c6, c7, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r7 := boundary_run_succ caller r6 s7
  have s8 : step caller c7 = some c8 := by
    dsimp only [c7, c8, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r8 := boundary_run_succ caller r7 s8
  have s9 : step caller c8 = some c9 := by
    dsimp only [c8, c9, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r9 := boundary_run_succ caller r8 s9
  have s10 : step caller c9 = some c10 := by
    dsimp only [c9, c10, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    rw [position_advance_step]
    rfl
  have r10 := boundary_run_succ caller r9 s10
  simp only [rightBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7
  · exact r8
  · exact r9
  · exact r10

theorem every_parser_failure_row_keeps_every_dirty_tree_store
    (b : Boundary) (member : b ∈ parseFailureBoundaries) :
    Runs caller (cfg (some (moveLabel .start)) regs (failureData [6,8,9] []) ctx)
      b.tick (b.cfg regs ctx) := by
  let c0 : Cfg Γ Λ R := (⟨0, .inl (movePhase .start), failureData [6,8,9] [], .original, 12, 14⟩ : Boundary).cfg regs ctx
  let c1 : Cfg Γ Λ R := (⟨1, .inl (movePhase (.scan .left)), failureData [8,9] [], .parser, 11, 14⟩ : Boundary).cfg regs ctx
  let c2 : Cfg Γ Λ R := (⟨2, .inl (movePhase (.scan .left)), failureData [9] [.left], .parser, 11, 14⟩ : Boundary).cfg regs ctx
  let c3 : Cfg Γ Λ R := (⟨3, .inl (movePhase (.scan .left)), failureData [] [.right,.left], .parser, 11, 14⟩ : Boundary).cfg regs ctx
  let c4 : Cfg Γ Λ R := (⟨4, .inl (movePhase (.undo .left)), failureData [] [.right,.left], .parser, 11, 14⟩ : Boundary).cfg regs ctx
  let c5 : Cfg Γ Λ R := (⟨5, .inl (movePhase (.undo .left)), failureData [9] [.left], .parser, 11, 14⟩ : Boundary).cfg regs ctx
  let c6 : Cfg Γ Λ R := (⟨6, .inl (movePhase (.undo .left)), failureData [8,9] [], .parser, 11, 14⟩ : Boundary).cfg regs ctx
  let c7 : Cfg Γ Λ R := (⟨7, .inl (dispatchPhase .failure), failureData [6,8,9] [], .parser, 12, 14⟩ : Boundary).cfg regs ctx
  let c8 : Cfg Γ Λ R := (⟨8, .inr parseFailure, failureData [6,8,9] [], .complete, 12, 12⟩ : Boundary).cfg regs ctx
  have r0 : Runs caller c0 0 c0 := rfl
  have s1 : step caller c0 = some c1 := by
    dsimp only [c0, c1, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_start_direction_actual caller .left _ _ _ _ _ _ _ _ _
  have r1 := boundary_run_succ caller r0 s1
  have s2 : step caller c1 = some c2 := by
    dsimp only [c1, c2, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_scan_branch_actual caller .left .left _ _ _ _ _ _ _ _ _
  have r2 := boundary_run_succ caller r1 s2
  have s3 : step caller c2 = some c3 := by
    dsimp only [c2, c3, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_scan_branch_actual caller .left .right _ _ _ _ _ _ _ _ _
  have r3 := boundary_run_succ caller r2 s3
  have s4 : step caller c3 = some c4 := by
    dsimp only [c3, c4, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_scan_eof_actual caller .left _ _ _ _ _ _ _ _
  have r4 := boundary_run_succ caller r3 s4
  have s5 : step caller c4 = some c5 := by
    dsimp only [c4, c5, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_undo_branch_actual caller .left .right _ _ _ _ _ _ _ _ _
  have r5 := boundary_run_succ caller r4 s5
  have s6 : step caller c5 = some c6 := by
    dsimp only [c5, c6, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_undo_branch_actual caller .left .left _ _ _ _ _ _ _ _ _
  have r6 := boundary_run_succ caller r5 s6
  have s7 : step caller c6 = some c7 := by
    dsimp only [c6, c7, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact move_undo_empty_actual caller .left _ _ _ _ _ _ _ _
  have r7 := boundary_run_succ caller r6 s7
  have s8 : step caller c7 = some c8 := by
    dsimp only [c7, c8, Boundary.cfg, boundaryLabel, RegisterStage.apply,
      movePhase, dispatchPhase, positionPhase, phaseLabel]
    exact dispatch_step caller _ _ _ _
  have r8 := boundary_run_succ caller r7 s8
  simp only [parseFailureBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7
  · exact r8

theorem actual_prefix_has_the_exact_remaining_rank
    (start reached : Cfg Γ Λ R) (total n : Nat)
    (rank : remainingSteps start = total) (bound : n ≤ total)
    (executed : Runs caller start n reached) :
    remainingSteps reached = total - n ∧ (n < total ↔ Owned reached.l) := by
  have segment : LocalRun caller n start reached := LocalRun.of_iterate caller executed (by
    intro j strict
    exact LocalRun.owned_prefix caller (cfg_localRun caller start) j (by omega))
  have remaining := LocalRun.remaining caller segment
  have exactRank : remainingSteps reached = total - n := by omega
  refine ⟨exactRank, ?_⟩
  rw [← remainingSteps_pos_iff, exactRank]
  omega

omit [DecidableEq K] in
theorem literal_success_entry_ranks_are_eleven_and_ten :
    remainingSteps (cfg (Λ := Λ) (some (moveLabel .start)) regs
      (data [6,10,15] [] [] [1,0,1,15] [] [] []) ctx) = 11 ∧
    remainingSteps (cfg (Λ := Λ) (some (moveLabel .start)) regs
      (data [7,10,15] [] [] [1,1,0,15] [] [] []) ctx) = 10 := by
  constructor
  · change remainingSteps (cfg (Λ := Λ) (some (phaseLabel (movePhase .start))) regs _ ctx) = _
    rw [remainingSteps_phase_cfg]
    exact congrArg Evaluation.steps malformed_left_evaluation
  · change remainingSteps (cfg (Λ := Λ) (some (phaseLabel (movePhase .start))) regs _ ctx) = _
    rw [remainingSteps_phase_cfg]
    exact congrArg Evaluation.steps malformed_right_evaluation

omit [DecidableEq K] in
theorem literal_failure_entry_rank_is_eight :
    remainingSteps (cfg (Λ := Λ) (some (moveLabel .start)) regs (failureData [6,8,9] []) ctx) = 8 := by
  change remainingSteps (cfg (Λ := Λ) (some (phaseLabel (movePhase .start))) regs _ ctx) = _
  rw [remainingSteps_phase_cfg]
  simp [phaseSteps, evaluate, evaluateDispatch, moveFinish, moveScanFinish,
    MoveParserMachine.phaseSteps, MoveParserMachine.startSteps, MoveParserMachine.branchCount,
    parsePathRun, Resources.bind, pathTags, directionTag,
    rotateLeftTag, rotateRightTag, pathLeftTag, pathRightTag, endMoveTag,
    data, failureData, movePhase]

theorem all_literal_times_are_in_the_inclusive_first_prefix :
    (∀ b ∈ leftBoundaries, b.tick ≤ 11) ∧
      (∀ b ∈ rightBoundaries, b.tick ≤ 10) ∧
      (∀ b ∈ parseFailureBoundaries, b.tick ≤ 8) := by
  constructor
  · intro b member
    simp only [leftBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · constructor
    · intro b member
      simp only [rightBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro b member
      simp only [parseFailureBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end LiteralBoundaryRuns

/- One actual configuration carries every inclusive-prefix claim. -/
section PrefixConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

theorem all_configuration_prefixes_have_one_shared_complete_witness
    (start : Cfg Γ Λ R) (n : Nat) : PrefixExpected caller start n :=
  fun bound => owned_prefix_frame caller start n bound

theorem every_dirty_prefix_is_independent_of_all_later_caller_bodies
    (other : External Λ → Statement Γ Λ R) (start : Cfg Γ Λ R)
    (n : Nat) (bound : n ≤ remainingSteps start) :
    (next caller)^[n] (some start) = (next other)^[n] (some start) :=
  prefix_caller_independent caller other start n bound

theorem agreement_on_all_twenty_six_owned_bodies_transports_the_prefix
    (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ q, ambient (phaseLabel q) = program (fun _ => .halt) (phaseLabel q))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (flip bind (Turing.TM2.step ambient))^[n] (some start) =
      (next caller)^[n] (some start) :=
  ambient_prefix_eq caller ambient agrees start n bound

section Physical
variable [Fintype K]

theorem every_dirty_prefix_has_the_same_rank_frame_register_and_physical_witness
    (start : Cfg Γ Λ R) (n : Nat) : PrefixSpaceExpected caller start n :=
  fun bound => owned_prefix_space caller start n bound

omit [DecidableEq K] in
theorem every_local_store_and_every_protected_store_is_counted
    (label : Option (Label Λ)) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg label regs D ctx) =
      D.certificate.length + D.moveReverse.length + D.path.length + D.source.length +
        D.saved.length + D.scratch.length + D.pending.length + contextCells ctx :=
  stackCells_cfg label regs D ctx

omit [DecidableEq K] in
theorem the_three_dispatch_potentials_have_the_exact_paid_drops
    (d : RotationDirection) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    potential (cfg (Λ := Λ) (some (dispatchLabel (.success d))) regs D ctx) =
        potential (cfg (Λ := Λ) (some (positionLabel (.seek d))) (reset regs) D ctx) + 2 ∧
      potential (cfg (Λ := Λ) (some (dispatchLabel .failure)) regs D ctx) =
        potential (cfg (Λ := Λ) (some (resultLabel parseFailure)) (reset regs) D ctx) + D.source.length :=
  ⟨dispatch_success_potential (Λ := Λ) d D regs ctx, dispatch_failure_potential (Λ := Λ) D regs ctx⟩

end Physical
end PrefixConnections

theorem the_two_actual_protected_contexts_have_seven_and_five_cells :
    contextCells authorContext = 7 ∧ contextCells independentContext = 5 := by
  constructor
  · simp only [contextCells, Fin.sum_univ_two]
    rfl
  · simp only [contextCells, Fin.sum_univ_two]
    rfl

private theorem boundary_physical_fields {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (b : Boundary)
    (cells : localCells b.stores = b.cells)
    (weight : (match b.control with
      | .inl q => localCells b.stores + phaseDebt q + phaseCredit q b.stores
      | .inr _ => localCells b.stores) = b.creditCells) :
    (b.cfg (Λ := Λ) regs ctx).var = b.stage.apply regs ∧
      (∀ k, (b.cfg (Λ := Λ) regs ctx).stk (.inr k) = ctx k) ∧
      stackCells (b.cfg (Λ := Λ) regs ctx) = b.cells + contextCells ctx ∧
      potential (b.cfg (Λ := Λ) regs ctx) = b.creditCells + contextCells ctx := by
  rcases b with ⟨tick, control, D, stage, count, credit⟩
  change localCells D = count at cells
  rcases control with q | r
  · change localCells D + phaseDebt q + phaseCredit q D = credit at weight
    refine ⟨rfl, (fun _ => rfl), ?_, ?_⟩
    · change stackCells (cfg (Λ := Λ) _ _ D ctx) = count + contextCells ctx
      rw [stackCells_cfg, cells]
    · change potential (cfg (some (phaseLabel (Λ := Λ) q)) _ D ctx) = credit + contextCells ctx
      rw [potential_phase_cfg, weight]
  · change localCells D = credit at weight
    refine ⟨rfl, (fun _ => rfl), ?_, ?_⟩
    · change stackCells (cfg (Λ := Λ) _ _ D ctx) = count + contextCells ctx
      rw [stackCells_cfg, cells]
    · change potential (cfg (some (resultLabel (Λ := Λ) r)) _ D ctx) = credit + contextCells ctx
      rw [potential_result_cfg, weight]

section LiteralBoundaryPhysical
variable {K Λ R : Type} {Γ : K → Type} [Fintype K]
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem every_left_literal_row_has_its_fixed_physical_fields
    (b : Boundary) (member : b ∈ leftBoundaries) :
    (b.cfg (Λ := Λ) regs ctx).var = b.stage.apply regs ∧
      (∀ k, (b.cfg (Λ := Λ) regs ctx).stk (.inr k) = ctx k) ∧
      stackCells (b.cfg (Λ := Λ) regs ctx) = b.cells + contextCells ctx ∧
      potential (b.cfg (Λ := Λ) regs ctx) = b.creditCells + contextCells ctx := by
  simp only [leftBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact boundary_physical_fields regs ctx _ rfl rfl

theorem every_right_literal_row_has_its_fixed_physical_fields
    (b : Boundary) (member : b ∈ rightBoundaries) :
    (b.cfg (Λ := Λ) regs ctx).var = b.stage.apply regs ∧
      (∀ k, (b.cfg (Λ := Λ) regs ctx).stk (.inr k) = ctx k) ∧
      stackCells (b.cfg (Λ := Λ) regs ctx) = b.cells + contextCells ctx ∧
      potential (b.cfg (Λ := Λ) regs ctx) = b.creditCells + contextCells ctx := by
  simp only [rightBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact boundary_physical_fields regs ctx _ rfl rfl

theorem every_parser_failure_row_has_its_fixed_physical_fields
    (b : Boundary) (member : b ∈ parseFailureBoundaries) :
    (b.cfg (Λ := Λ) regs ctx).var = b.stage.apply regs ∧
      (∀ k, (b.cfg (Λ := Λ) regs ctx).stk (.inr k) = ctx k) ∧
      stackCells (b.cfg (Λ := Λ) regs ctx) = b.cells + contextCells ctx ∧
      potential (b.cfg (Λ := Λ) regs ctx) = b.creditCells + contextCells ctx := by
  simp only [parseFailureBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact boundary_physical_fields regs ctx _ rfl rfl

variable [DecidableEq K] (caller : External Λ → Statement Γ Λ R)

theorem every_left_literal_boundary_satisfies_the_complete_fixed_contract
    (b : Boundary) (member : b ∈ leftBoundaries) :
    b.Expected caller regs ctx (data [6,10,15] [] [] [1,0,1,15] [] [] []) 11 := by
  have executed := every_left_literal_row_is_the_actual_reached_configuration caller regs ctx b member
  have rank := actual_prefix_has_the_exact_remaining_rank caller _ _ 11 b.tick
    (literal_success_entry_ranks_are_eleven_and_ten (Λ := Λ) regs ctx).1
    (all_literal_times_are_in_the_inclusive_first_prefix.1 b member) executed
  have physical := every_left_literal_row_has_its_fixed_physical_fields (Λ := Λ) regs ctx b member
  exact ⟨executed, rank.1, rank.2, physical.1, physical.2.1, physical.2.2.1, physical.2.2.2⟩

theorem every_right_literal_boundary_satisfies_the_complete_fixed_contract
    (b : Boundary) (member : b ∈ rightBoundaries) :
    b.Expected caller regs ctx (data [7,10,15] [] [] [1,1,0,15] [] [] []) 10 := by
  have executed := every_right_literal_row_is_the_actual_reached_configuration caller regs ctx b member
  have rank := actual_prefix_has_the_exact_remaining_rank caller _ _ 10 b.tick
    (literal_success_entry_ranks_are_eleven_and_ten (Λ := Λ) regs ctx).2
    (all_literal_times_are_in_the_inclusive_first_prefix.2.1 b member) executed
  have physical := every_right_literal_row_has_its_fixed_physical_fields (Λ := Λ) regs ctx b member
  exact ⟨executed, rank.1, rank.2, physical.1, physical.2.1, physical.2.2.1, physical.2.2.2⟩

theorem every_parser_failure_boundary_satisfies_the_complete_fixed_contract
    (b : Boundary) (member : b ∈ parseFailureBoundaries) :
    b.Expected caller regs ctx (failureData [6,8,9] []) 8 := by
  have executed := every_parser_failure_row_keeps_every_dirty_tree_store caller regs ctx b member
  have rank := actual_prefix_has_the_exact_remaining_rank caller _ _ 8 b.tick
    (literal_failure_entry_rank_is_eight (Λ := Λ) regs ctx)
    (all_literal_times_are_in_the_inclusive_first_prefix.2.2 b member) executed
  have physical := every_parser_failure_row_has_its_fixed_physical_fields (Λ := Λ) regs ctx b member
  exact ⟨executed, rank.1, rank.2, physical.1, physical.2.1, physical.2.2.1, physical.2.2.2⟩

end LiteralBoundaryPhysical

/- The same literal rows specialize to both independently fixed protected contexts. -/
theorem all_literal_boundaries_keep_both_distinct_contexts
    (author : AuthorCaller) (independent : ExampleCaller) (flag : Bool) :
    (∀ b ∈ leftBoundaries, b.Expected author (stale flag) authorContext
      (data [6,10,15] [] [] [1,0,1,15] [] [] []) 11) ∧
    (∀ b ∈ rightBoundaries, b.Expected author (stale flag) authorContext
      (data [7,10,15] [] [] [1,1,0,15] [] [] []) 10) ∧
    (∀ b ∈ parseFailureBoundaries, b.Expected author (stale flag) authorContext
      (failureData [6,8,9] []) 8) ∧
    (∀ b ∈ leftBoundaries, b.Expected independent (stale flag) independentContext
      (data [6,10,15] [] [] [1,0,1,15] [] [] []) 11) ∧
    (∀ b ∈ rightBoundaries, b.Expected independent (stale flag) independentContext
      (data [7,10,15] [] [] [1,1,0,15] [] [] []) 10) ∧
    (∀ b ∈ parseFailureBoundaries, b.Expected independent (stale flag) independentContext
      (failureData [6,8,9] []) 8) :=
  ⟨every_left_literal_boundary_satisfies_the_complete_fixed_contract (stale flag) authorContext author,
    every_right_literal_boundary_satisfies_the_complete_fixed_contract (stale flag) authorContext author,
    every_parser_failure_boundary_satisfies_the_complete_fixed_contract (stale flag) authorContext author,
    every_left_literal_boundary_satisfies_the_complete_fixed_contract (stale flag) independentContext independent,
    every_right_literal_boundary_satisfies_the_complete_fixed_contract (stale flag) independentContext independent,
    every_parser_failure_boundary_satisfies_the_complete_fixed_contract (stale flag) independentContext independent⟩

section RepresentedAndRawConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem every_clean_raw_parse_returns_the_actual_physical_suffix_and_cleanup
    (mv : RotationMove) (rest X : Word) (O : List Branch) :
    RawExpected caller regs ctx mv rest X O := by
  obtain ⟨r, Y, remaining, actual, length, suffix, failed, succeeded⟩ :=
    run_raw caller mv rest O X regs ctx
  have exactClock := (LocalRun.phaseEndpoint caller (q := MoveApplyMachine.movePhase .start) actual).1
  refine ⟨r, Y, remaining, ?_, length, ?_, failed, succeeded⟩
  · rw [show phaseSteps (movePhase .start) (data (moveCode mv ++ rest) [] O X [] [] []) =
      2 * mv.position.length + 4 +
        PositionedRotationMachine.runSteps mv.direction X (mv.position ++ O) from exactClock]
    exact local_run_gives_an_actual_first_return caller actual (not_owned_result (.inr r))
  · obtain ⟨consumed, same⟩ := suffix
    exact ⟨consumed, same.symm⟩

theorem represented_rotation_preserves_the_complete_saved_word_suffix_and_physical_path
    (mv : RotationMove) (rest : Word) (O : List Branch)
    (s : BinaryTree Unit) (F z : Word) :
    RepresentedExpected caller regs ctx mv rest O s F z := by
  have first := local_run_gives_an_actual_first_return caller
    (run_code_represented_localRun caller mv rest O s F z regs ctx)
    (not_owned_result (representedResult mv O s))
  constructor
  · change FirstRun caller
      (entry regs (moveCode mv ++ rest) O (treeCode s ++ z) F [] [] ctx)
      (representedSteps mv O s F)
      (cfg (some (resultLabel (representedResult mv O s))) (reset regs)
        (representedFinalData mv rest O s F z) ctx)
    exact first
  · exact representedSource_length mv O s F z

theorem all_thirteen_represented_rows_connect_both_clocks_and_complete_physical_endpoints
    (c : RepresentedFixture) (member : c ∈ representedFixtures) (rest F z : Word) :
    c.Expected caller regs ctx rest F z := by
  obtain ⟨sourceRun, clock, remaining, sourceParser, wholeClock⟩ :=
    represented_fixture_source_observations c member
  have actual := (represented_rotation_preserves_the_complete_saved_word_suffix_and_physical_path
    caller regs ctx c.parsed rest c.oldPath c.tree F z).1
  refine ⟨arbitrary_certificate_suffix_has_the_same_source_parse_cost c member rest,
    sourceRun, clock, remaining, ?_⟩
  simpa only [sourceRun, clock, remaining, wholeClock] using actual

theorem represented_first_success_uses_the_parsed_path_before_the_old_path
    (C : Word) (O : List Branch) (s : BinaryTree Unit) (F z : Word) :
    FirstResult caller
      (cfg (some (moveLabel .start)) regs (data C [] O (treeCode s ++ z) F [] []) ctx)
      rotationSuccess ↔
      ∃ mv rest t, (parseMoveRun C).1 = some (mv, rest) ∧
        (applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).1 = some t := by
  rw [independent_first_result_is_the_public_strict_first_result]
  exact represented_raw_first_success_iff caller C O s F z regs ctx

theorem complete_represented_first_success_recovers_the_actual_parse_output_suffix_and_clock
    (C rest : Word) (O : List Branch) (s t : BinaryTree Unit)
    (F z outSuffix : Word) (ticks : Nat)
    (first : FirstRun caller
      (cfg (some (moveLabel .start)) regs (data C [] O (treeCode s ++ z) F [] []) ctx)
      ticks
      (cfg (some (resultLabel rotationSuccess)) (reset regs)
        (data rest [] [] (F.reverse ++ treeCode t ++ outSuffix) [] [] []) ctx)) :
    ∃ mv, (parseMoveRun C).1 = some (mv, rest) ∧
      (applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).1 = some t ∧ z = outSuffix ∧
      ticks = 2 * mv.position.length + 4 +
        PositionedRotationMachine.representedClock mv.direction (mv.position ++ O) s + F.length :=
  represented_raw_first_success_complete caller C rest O s t F z outSuffix regs ctx
    ticks first.1 first.2.2

theorem exact_success_endpoint_iff_includes_a_success_label_and_both_literal_suffixes
    (mv : RotationMove) (rest outRest : Word) (O : List Branch)
    (s t : BinaryTree Unit) (F z outSuffix : Word) (ticks : Nat) :
    FirstRun caller
      (cfg (some (moveLabel .start)) regs
        (data (moveCode mv ++ rest) [] O (treeCode s ++ z) F [] []) ctx)
      ticks
      (cfg (some (resultLabel rotationSuccess)) (reset regs)
        (data outRest [] [] (F.reverse ++ treeCode t ++ outSuffix) [] [] []) ctx) ↔
      (applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).1 = some t ∧
        rest = outRest ∧ z = outSuffix ∧
        ticks = 2 * mv.position.length + 4 +
          PositionedRotationMachine.representedClock mv.direction (mv.position ++ O) s + F.length := by
  constructor
  · intro first
    exact (represented_success_localRun_iff caller mv rest outRest O s t F z outSuffix
      regs ctx ticks).mp (LocalRun.of_iterate caller first.1 first.2.2)
  · intro successful
    exact local_run_gives_an_actual_first_return caller
      ((represented_success_localRun_iff caller mv rest outRest O s t F z outSuffix
        regs ctx ticks).mpr successful) (not_owned_result rotationSuccess)

include caller in
theorem first_success_also_has_the_source_rotation_node_count_and_source_tariff
    (mv : RotationMove) (rest : Word) (O : List Branch) (s t : BinaryTree Unit)
    (F z : Word)
    (endpoint : runResult (Λ := Λ) regs (moveCode mv ++ rest) O (treeCode s ++ z) F [] [] ctx =
      cfg (some (resultLabel rotationSuccess)) (reset regs)
        (data rest [] [] (F.reverse ++ treeCode t ++ z) [] [] []) ctx) :
    Trees.Rotations.applyMove? ⟨mv.direction, mv.position ++ O⟩ s = some t ∧
      t.numNodes = s.numNodes ∧
      (applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).2 =
        3 * (mv.position ++ O).length + 5 ∧
      (F.reverse ++ treeCode t ++ z).length = F.length + 2 * s.numNodes + 1 + z.length :=
  represented_success_semantics caller mv rest O s t F z regs ctx endpoint

theorem both_raw_root_success_characterizations_keep_arbitrary_registers_context_and_saved_words
    (rest X F : Word) : RootIffExpected caller regs ctx rest X F := by
  constructor
  · rw [independent_first_result_is_the_public_strict_first_result]
    simpa only [moveCode, directionTag, pathTags, List.map_nil, List.nil_append,
      List.append_assoc, List.cons_append, List.append_nil, nodeTag, rotateLeftTag, endMoveTag,
      rotationSuccess, MoveApplyMachine.success, entry, entryData, data] using
      root_left_first_success_iff caller X F rest regs ctx
  · rw [independent_first_result_is_the_public_strict_first_result]
    simpa only [moveCode, directionTag, pathTags, List.map_nil, List.nil_append,
      List.cons_append, List.append_nil, nodeTag, rotateRightTag, endMoveTag,
      rotationSuccess, MoveApplyMachine.success, entry, entryData, data] using
      root_right_first_success_iff caller X F rest regs ctx

theorem both_raw_root_patterns_return_the_literal_output_at_the_exact_first_clock
    (rest F z : Word) (A : BinaryTree Unit) :
    RootPatternsExpected caller regs ctx rest F z A := by
  constructor
  · have first := local_run_gives_an_actual_first_return caller
      (root_left_pattern_localRun caller A z F rest regs ctx)
      (not_owned_result MoveApplyMachine.success)
    simpa only [moveCode, directionTag, pathTags, List.map_nil, List.nil_append,
      List.append_assoc, List.cons_append, List.append_nil, nodeTag, rotateLeftTag, endMoveTag,
      rotationSuccess, MoveApplyMachine.success, entry, entryData, data] using first
  · have first := local_run_gives_an_actual_first_return caller
      (root_right_pattern_localRun caller A z F rest regs ctx)
      (not_owned_result MoveApplyMachine.success)
    simpa only [moveCode, directionTag, pathTags, List.map_nil, List.nil_append,
      List.append_assoc, List.cons_append, List.append_nil, nodeTag, rotateRightTag, endMoveTag,
      rotationSuccess, MoveApplyMachine.success, entry, entryData, data] using first

def representedInActualTime (mv : RotationMove) (rest : Word) (O : List Branch)
    (s : BinaryTree Unit) (F z : Word) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (moveLabel .start)) regs
        (data (moveCode mv ++ rest) [] O (treeCode s ++ z) F [] []) ctx)
      (some (cfg (some (resultLabel (if (applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).1.isSome
        then rotationSuccess else rotationFailure))) (reset regs)
        (data rest [] (PositionedRotationMachine.remainingPath (mv.position ++ O) s)
          (F.reverse ++ treeCode ((applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).1.getD s) ++ z)
          [] [] []) ctx))
      (2 * mv.position.length + 4 +
        PositionedRotationMachine.representedClock mv.direction (mv.position ++ O) s + F.length) :=
  representedInTime caller mv rest O s F z regs ctx

theorem represented_typed_time_retains_the_actual_saved_word_cost
    (mv : RotationMove) (rest : Word) (O : List Branch) (s : BinaryTree Unit) (F z : Word) :
    (representedInActualTime caller regs ctx mv rest O s F z).steps =
      2 * mv.position.length + 4 +
        PositionedRotationMachine.representedClock mv.direction (mv.position ++ O) s + F.length := rfl

def principalInLinearActualTime (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx)
      (some (runResult regs C O X F S Hd ctx))
      (3 * C.length + 3 * X.length + F.length + S.length + Hd.length + O.length + 3) :=
  runInLinearTime caller C O X F S Hd regs ctx

def parsedInSharperLinearActualTime (C rest : Word) (mv : RotationMove)
    (O : List Branch) (X F S : Word) (Hd : List Unit)
    (parsed : (parseMoveRun C).1 = some (mv, rest)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx)
      (some (runResult regs C O X F S Hd ctx))
      (3 * X.length + F.length + S.length + Hd.length + 3 * mv.position.length + O.length + 9) :=
  parsedRunInLinearTime caller C mv rest O X F S Hd regs ctx parsed

theorem linear_bounds_keep_the_actual_untruncated_count
    (C rest : Word) (mv : RotationMove) (O : List Branch) (X F S : Word) (Hd : List Unit)
    (parsed : (parseMoveRun C).1 = some (mv, rest)) :
    (principalInLinearActualTime caller regs ctx C O X F S Hd).steps = runSteps C O X F S Hd ∧
      (parsedInSharperLinearActualTime caller regs ctx C rest mv O X F S Hd parsed).steps =
        runSteps C O X F S Hd := ⟨rfl, rfl⟩

section Physical
variable [Fintype K]

theorem every_principal_prefix_keeps_every_dirty_cell_in_its_bound
    (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit) (n : Nat)
    (bound : n ≤ runSteps C O X F S Hd) (reached : Cfg Γ Λ R)
    (executed : Runs caller (cfg (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx) n reached) :
    stackCells reached ≤ C.length + O.length + 2 * X.length + F.length + S.length +
      Hd.length + contextCells ctx := by
  have cells := prefix_stackCells_le caller C O X F S Hd regs ctx n bound reached executed
  unfold principalCells at cells
  omega

theorem parse_failure_has_the_stronger_initial_physical_sum_bound
    (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit)
    (failed : (parseMoveRun C).1 = none) (n : Nat)
    (bound : n ≤ runSteps C O X F S Hd) (reached : Cfg Γ Λ R)
    (executed : Runs caller (cfg (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx) n reached) :
    stackCells reached ≤ C.length + O.length + X.length + F.length + S.length +
      Hd.length + contextCells ctx :=
  prefix_stackCells_le_of_none caller C O X F S Hd regs ctx failed n bound reached executed

theorem parsed_success_uses_the_larger_of_the_actual_parser_and_position_bounds
    (C rest : Word) (mv : RotationMove) (O : List Branch) (X F S : Word) (Hd : List Unit)
    (parsed : (parseMoveRun C).1 = some (mv, rest)) (n : Nat)
    (bound : n ≤ runSteps C O X F S Hd) (reached : Cfg Γ Λ R)
    (executed : Runs caller (cfg (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx) n reached) :
    stackCells reached ≤ max
      (C.length + O.length + X.length + F.length + S.length + Hd.length + contextCells ctx)
      (rest.length + mv.position.length + O.length + 2 * X.length + F.length + S.length +
        Hd.length + contextCells ctx) :=
  prefix_stackCells_le_of_some caller C mv rest O X F S Hd regs ctx parsed n bound reached executed

omit [DecidableEq K] in
theorem the_sharper_position_bound_is_exactly_two_below_initial_potential
    (C rest : Word) (mv : RotationMove) (O : List Branch) (X F S : Word) (Hd : List Unit)
    (parsed : (parseMoveRun C).1 = some (mv, rest)) :
    rest.length + mv.position.length + O.length + 2 * X.length + F.length + S.length +
      Hd.length + contextCells ctx + 2 =
      potential (cfg (Λ := Λ) (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx) := by
  have length := parseMoveRun_consumed_length C mv rest parsed
  rw [show potential (cfg (Λ := Λ) (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx) =
    principalCells C O X F S Hd ctx + X.length from entry_potential (Λ := Λ) C O X F S Hd regs ctx]
  unfold principalCells
  omega

end Physical
end RepresentedAndRawConnections

theorem all_thirteen_rows_keep_the_author_and_independent_protected_words
    (author : AuthorCaller) (independent : ExampleCaller) (flag : Bool)
    (c : RepresentedFixture) (member : c ∈ representedFixtures) (rest F z : Word) :
    c.Expected author (stale flag) authorContext rest F z ∧
      c.Expected independent (stale flag) independentContext rest F z :=
  ⟨all_thirteen_represented_rows_connect_both_clocks_and_complete_physical_endpoints
      author (stale flag) authorContext c member rest F z,
    all_thirteen_represented_rows_connect_both_clocks_and_complete_physical_endpoints
      independent (stale flag) independentContext c member rest F z⟩

/- Actual caller continuations begin after the fixed first live result. -/
section RootSegments
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem root_left_segment_with_arbitrary_certificate_suffix (rest : Word) :
    LocalRun caller 11
      (cfg (some (moveLabel .start)) regs (data ([6,10] ++ rest) [] [] (treeCode rightTwo) [] [] []) ctx)
      (cfg (some (resultLabel rotationSuccess)) (reset regs)
        (data rest [] [] (treeCode leftTwo) [] [] []) ctx) := by
  have actual := root_left_pattern_localRun caller nilTree [0,0] [] rest regs ctx
  exact actual

theorem root_right_segment_with_arbitrary_certificate_suffix (rest : Word) :
    LocalRun caller 10
      (cfg (some (moveLabel .start)) regs (data ([7,10] ++ rest) [] [] (treeCode leftTwo) [] [] []) ctx)
      (cfg (some (resultLabel rotationSuccess)) (reset regs)
        (data rest [] [] (treeCode rightTwo) [] [] []) ctx) := by
  have actual := root_right_pattern_localRun caller nilTree [0,0] [] rest regs ctx
  exact actual

theorem root_left_first_live_result_is_exactly_eleven (rest : Word) :
    FirstRun caller
      (cfg (some (moveLabel .start)) regs (data ([6,10] ++ rest) [] [] (treeCode rightTwo) [] [] []) ctx)
      11
      (cfg (some (resultLabel rotationSuccess)) (reset regs)
        (data rest [] [] (treeCode leftTwo) [] [] []) ctx) :=
  local_run_gives_an_actual_first_return caller
    (root_left_segment_with_arbitrary_certificate_suffix caller regs ctx rest)
    (not_owned_result rotationSuccess)

end RootSegments

def authorRootStart (flag : Bool) : AuthorCfg :=
  cfg (some (moveLabel .start)) (stale flag) (data [6,10] [] [] (treeCode rightTwo) [] [] []) authorContext

def authorRootLive (flag : Bool) : AuthorCfg :=
  cfg (some (resultLabel rotationSuccess)) (clean flag) (data [] [] [] (treeCode leftTwo) [] [] []) authorContext

def authorRootHalt (marker : Tag) (flag : Bool) : AuthorCfg :=
  cfg none (clean flag) (data [] [] [] (treeCode leftTwo) [] [] [])
    (authorWords (marker :: [15,2,7,10,3]) [(),()])

theorem sentinel_caller_has_live_eleven_present_halt_twelve_and_outer_none_thirteen
    (marker : Tag) (flag : Bool) :
    FirstRun (sentinelHaltCaller marker) (authorRootStart flag) 11 (authorRootLive flag) ∧
      Runs (sentinelHaltCaller marker) (authorRootStart flag) 12 (authorRootHalt marker flag) ∧
      (next (sentinelHaltCaller marker))^[13] (some (authorRootStart flag)) = none := by
  have first := root_left_first_live_result_is_exactly_eleven
    (sentinelHaltCaller marker) (stale flag) authorContext []
  have pushed := sentinel_push_and_halt_are_one_actual_activation marker rotationSuccess
    (clean flag) (data [] [] [] (treeCode leftTwo) [] [] []) [15,2,7,10,3] [(),()]
  have atTwelve := append_actual_step (sentinelHaltCaller marker) (authorRootStart flag)
    (authorRootLive flag) 11 first.1 (some (authorRootHalt marker flag)) pushed
  refine ⟨first, atTwelve, ?_⟩
  exact append_actual_step (sentinelHaltCaller marker) (authorRootStart flag)
    (authorRootHalt marker flag) 12 atTwelve none rfl

def sentinelCallerInActualTime (marker : Tag) (flag : Bool) :
    StateTransition.EvalsToInTime (step (sentinelHaltCaller marker))
      (authorRootStart flag) (some (authorRootHalt marker flag)) 12 :=
  appendTimed (sentinelHaltCaller marker) (authorRootStart flag) (authorRootLive flag)
    (some (authorRootHalt marker flag)) 11 1
    (localRunInActualTime (sentinelHaltCaller marker)
      (root_left_segment_with_arbitrary_certificate_suffix
        (sentinelHaltCaller marker) (stale flag) authorContext []))
    (oneActualStepTime (sentinelHaltCaller marker) (authorRootLive flag)
      (some (authorRootHalt marker flag))
      (sentinel_push_and_halt_are_one_actual_activation marker rotationSuccess
        (clean flag) (data [] [] [] (treeCode leftTwo) [] [] []) [15,2,7,10,3] [(),()]))

theorem sentinel_timing_contains_both_actual_segments (marker : Tag) (flag : Bool) :
    (sentinelCallerInActualTime marker flag).steps = 12 := rfl

def emptyAllocationStart (flag : Bool) : ExampleCfg :=
  cfg (some (moveLabel .start)) (stale flag) (data [] [] [] [] [] [] []) independentContext

def emptyAllocationLive (flag : Bool) : ExampleCfg :=
  cfg (some (resultLabel parseFailure)) (clean flag) (data [] [] [] [] [] [] []) independentContext

def emptyAllocationCaller (flag : Bool) : ExampleCfg :=
  cfg (some (callerLabel ())) ((clean flag).1, !flag) (data [] [] [] [] [] [] [])
    (independentWords [true,true,false,true] [11,15])

theorem empty_allocation_first_result_is_two_then_the_caller_escapes_the_initial_potential
    (flag : Bool) :
    FirstRun allocatingCaller (emptyAllocationStart flag) 2 (emptyAllocationLive flag) ∧
      Runs allocatingCaller (emptyAllocationStart flag) 3 (emptyAllocationCaller flag) ∧
      potential (emptyAllocationStart flag) = 5 ∧
      stackCells (emptyAllocationCaller flag) = 6 ∧
      potential (emptyAllocationStart flag) < stackCells (emptyAllocationCaller flag) := by
  have first : FirstRun allocatingCaller (emptyAllocationStart flag) 2 (emptyAllocationLive flag) :=
    local_run_gives_an_actual_first_return allocatingCaller
      (run_of_none_localRun allocatingCaller [] [] [] [] [] [] (stale flag) independentContext rfl)
      (not_owned_result parseFailure)
  have pushed := allocating_caller_changes_the_actual_protected_data_and_caller_register
    parseFailure (clean flag) (data [] [] [] [] [] [] []) [true,false,true] [11,15]
  have actual := append_actual_step allocatingCaller (emptyAllocationStart flag)
    (emptyAllocationLive flag) 2 first.1 (some (emptyAllocationCaller flag)) pushed
  have initial : potential (emptyAllocationStart flag) = 5 := by
    change potential (cfg (some (phaseLabel (movePhase .start))) (stale flag)
      (data [] [] [] [] [] [] []) independentContext) = _
    rw [potential_phase_cfg, the_two_actual_protected_contexts_have_seven_and_five_cells.2]
    rfl
  have later : stackCells (emptyAllocationCaller flag) = 6 := by
    rw [emptyAllocationCaller, stackCells_cfg]
    simp only [localCells, data, contextCells, Fin.sum_univ_two]
    rfl
  exact ⟨first, actual, initial, later, by omega⟩

def misleadingStart (flag : Bool) : ExampleCfg :=
  cfg (some (moveLabel .start)) (stale flag) (failureData [6,8,9] []) independentContext

def misleadingLive (flag : Bool) : ExampleCfg :=
  cfg (some (resultLabel parseFailure)) (clean flag) (failureData [6,8,9] []) independentContext

def misleadingLater (flag : Bool) : ExampleCfg :=
  cfg (some (resultLabel rotationSuccess)) (clean flag) (failureData [6,8,9] []) independentContext

theorem a_later_success_label_does_not_change_the_first_parse_failure (flag : Bool) :
    FirstRun misleadingCaller (misleadingStart flag) 8 (misleadingLive flag) ∧
      Runs misleadingCaller (misleadingStart flag) 9 (misleadingLater flag) ∧
      ¬ FirstResult misleadingCaller (misleadingStart flag) rotationSuccess := by
  have first : FirstRun misleadingCaller (misleadingStart flag) 8 (misleadingLive flag) :=
    local_run_gives_an_actual_first_return misleadingCaller
      (run_of_none_localRun misleadingCaller [6,8,9] [.right,.left] [1,15] [12,3] [14]
        [(),()] (stale flag) independentContext rfl) (not_owned_result parseFailure)
  refine ⟨first, ?_, ?_⟩
  · exact append_actual_step misleadingCaller (misleadingStart flag) (misleadingLive flag)
      8 first.1 (some (misleadingLater flag))
      (misleading_success_is_a_later_paid_caller_step (clean flag)
        (failureData [6,8,9] []) independentContext)
  · rintro ⟨n, reached, purported, label⟩
    have same := firstRun_unique misleadingCaller (misleadingStart flag) reached
      (misleadingLive flag) n 8 purported first
    rw [same.2] at label
    cases label

def reentryStart (flag : Bool) : ExampleCfg :=
  cfg (some (moveLabel .start)) (stale flag)
    (data [6,10,7,10] [] [] (treeCode rightTwo) [] [] []) independentContext

def reentryMiddle (flag : Bool) : ExampleCfg :=
  cfg (some (resultLabel rotationSuccess)) (clean flag)
    (data [7,10] [] [] (treeCode leftTwo) [] [] []) independentContext

def reentryJoined (flag : Bool) : ExampleCfg :=
  cfg (some (moveLabel .start)) (clean flag)
    (data [7,10] [] [] (treeCode leftTwo) [] [] []) independentContext

def reentryFinish (flag : Bool) : ExampleCfg :=
  cfg (some (resultLabel rotationSuccess)) (clean flag)
    (data [] [] [] (treeCode rightTwo) [] [] []) independentContext

theorem actual_reentry_is_eleven_then_one_then_ten_and_not_one_first_return (flag : Bool) :
    FirstRun reentryCaller (reentryStart flag) 11 (reentryMiddle flag) ∧
      Runs reentryCaller (reentryStart flag) 12 (reentryJoined flag) ∧
      Runs reentryCaller (reentryStart flag) 22 (reentryFinish flag) ∧
      ¬ FirstRun reentryCaller (reentryStart flag) 22 (reentryFinish flag) := by
  have first := root_left_first_live_result_is_exactly_eleven
    reentryCaller (stale flag) independentContext [7,10]
  have joined := append_actual_step reentryCaller (reentryStart flag) (reentryMiddle flag)
    11 first.1 (some (reentryJoined flag))
    (reentry_jump_preserves_every_actual_store (clean flag)
      (data [7,10] [] [] (treeCode leftTwo) [] [] []) independentContext)
  have inverse := LocalRun.iterate reentryCaller
    (root_right_segment_with_arbitrary_certificate_suffix reentryCaller (clean flag) independentContext [])
  have completed := runs_trans reentryCaller (reentryStart flag) (reentryJoined flag)
    (reentryFinish flag) 12 10 joined inverse
  refine ⟨first, joined, completed, ?_⟩
  intro purported
  have impossible := (firstRun_unique reentryCaller (reentryStart flag) (reentryMiddle flag)
    (reentryFinish flag) 11 22 first purported).1
  omega

def reentryFirstAndJumpInActualTime (flag : Bool) :
    StateTransition.EvalsToInTime (step reentryCaller)
      (reentryStart flag) (some (reentryJoined flag)) 12 :=
  appendTimed reentryCaller (reentryStart flag) (reentryMiddle flag) (some (reentryJoined flag)) 11 1
    (localRunInActualTime reentryCaller
      (root_left_segment_with_arbitrary_certificate_suffix reentryCaller (stale flag) independentContext [7,10]))
    (oneActualStepTime reentryCaller (reentryMiddle flag) (some (reentryJoined flag))
      (reentry_jump_preserves_every_actual_store (clean flag)
        (data [7,10] [] [] (treeCode leftTwo) [] [] []) independentContext))

def reentryInActualTime (flag : Bool) :
    StateTransition.EvalsToInTime (step reentryCaller)
      (reentryStart flag) (some (reentryFinish flag)) 22 :=
  appendTimed reentryCaller (reentryStart flag) (reentryJoined flag) (some (reentryFinish flag)) 12 10
    (reentryFirstAndJumpInActualTime flag)
    (localRunInActualTime reentryCaller
      (root_right_segment_with_arbitrary_certificate_suffix reentryCaller (clean flag) independentContext []))

theorem reentry_timed_data_keeps_the_paid_caller_jump (flag : Bool) :
    (reentryInActualTime flag).steps = 22 := rfl

section SharpFamilyConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem exact_peak_of_the_universal_actual_bound_and_an_attained_prefix
    (start : Cfg Γ Λ R) (ticks peak : Nat) (clock : remainingSteps start = ticks)
    (upper : ∀ j, j ≤ ticks → ∀ reached, Runs caller start j reached → stackCells reached ≤ peak)
    (attained : ∃ j reached, j ≤ ticks ∧ Runs caller start j reached ∧ stackCells reached = peak) :
    HasExactPeak caller start ticks peak := by
  constructor
  · intro j bound
    obtain ⟨reached, actual, _, _, _⟩ := owned_prefix caller start j (by omega)
    exact ⟨reached, actual, upper j bound reached actual⟩
  · obtain ⟨j, reached, bound, actual, cells⟩ := attained
    exact ⟨j, bound, reached, actual, cells⟩

theorem all_left_node_families_have_the_fixed_run_drop_rank_and_exact_peak
    (n : Nat) (rest : Word) : LeftNodesExpected caller regs ctx n rest := by
  have peak := left_nodes_peak caller rest n regs ctx
  refine ⟨local_run_gives_an_actual_first_return caller
    (left_nodes_run caller rest n regs ctx) (not_owned_result rotationFailure),
    LocalRun.iterate caller (left_nodes_drop caller rest n regs ctx),
    left_nodes_drop_rank caller rest n regs ctx, ?_, ?_⟩
  · simpa only [data, Nat.add_comm rest.length] using
      left_nodes_drop_cells (Λ := Λ) rest n (reset regs) ctx
  · exact exact_peak_of_the_universal_actual_bound_and_an_attained_prefix caller _ _ _
      (left_nodes_exact_clock caller rest n regs ctx) peak.1 peak.2

theorem all_right_node_families_have_the_fixed_run_drop_rank_and_exact_peak
    (m : Nat) (rest : Word) : RightNodesExpected caller regs ctx m rest := by
  have peak := right_nodes_peak caller rest m regs ctx
  refine ⟨local_run_gives_an_actual_first_return caller
    (right_nodes_run caller rest m regs ctx) (not_owned_result rotationFailure),
    LocalRun.iterate caller (right_nodes_drop caller rest m regs ctx),
    right_nodes_drop_rank caller rest m regs ctx, ?_, ?_⟩
  · have cells := right_nodes_drop_cells (Λ := Λ) rest m (reset regs) ctx
    change stackCells (cfg (some (positionLabel .dropPending)) (reset regs)
      (data rest [] [] (List.replicate (m + 2) nodeTag) [] [] (List.replicate (m + 1) ())) ctx) = _
    unfold data
    omega
  · exact exact_peak_of_the_universal_actual_bound_and_an_attained_prefix caller _ _ _
      (right_nodes_exact_clock caller rest m regs ctx) peak.1 peak.2

theorem every_unterminated_parser_family_restores_all_dirty_tree_and_path_stores
    (k : Nat) (O : List Branch) (X F S : Word) (Hd : List Unit) :
    ParserNodesExpected caller regs ctx k O X F S Hd := by
  have peak := parser_eof_peak caller k O X F S Hd regs ctx
  constructor
  · exact local_run_gives_an_actual_first_return caller
      (parser_eof_run caller k O X F S Hd regs ctx) (not_owned_result parseFailure)
  · apply exact_peak_of_the_universal_actual_bound_and_an_attained_prefix caller _ _ _
      (show remainingSteps (entry (Λ := Λ) regs (rotateLeftTag :: List.replicate k pathLeftTag)
        O X F S Hd ctx) = 2 * k + 4 from
        parser_eof_exact_clock caller k O X F S Hd regs ctx)
    · simpa only [Runs, entry, entryData, data, rotateLeftTag, List.cons_append,
        List.nil_append, List.length_cons, List.length_replicate] using peak.1
    · simpa only [Runs, entry, entryData, data, rotateLeftTag, List.cons_append,
        List.nil_append, List.length_cons, List.length_replicate] using peak.2

end SharpFamilyConnections

theorem zero_one_two_left_and_zero_right_keep_the_small_input_peak_exceptions
    (caller : ExampleCaller) (flag : Bool) :
    LeftNodesExpected caller (stale flag) independentContext 0 [] ∧
      LeftNodesExpected caller (stale flag) independentContext 1 [] ∧
      LeftNodesExpected caller (stale flag) independentContext 2 [] ∧
      RightNodesExpected caller (stale flag) independentContext 0 [] ∧
      max (0 + 2) (2 * 0) + 5 = 7 ∧
      max (1 + 2) (2 * 1) + 5 = 8 ∧
      max (2 + 2) (2 * 2) + 5 = 9 ∧
      max (0 + 4) (2 * 0 + 3) + 5 = 9 :=
  ⟨all_left_node_families_have_the_fixed_run_drop_rank_and_exact_peak caller (stale flag) independentContext 0 [],
    all_left_node_families_have_the_fixed_run_drop_rank_and_exact_peak caller (stale flag) independentContext 1 [],
    all_left_node_families_have_the_fixed_run_drop_rank_and_exact_peak caller (stale flag) independentContext 2 [],
    all_right_node_families_have_the_fixed_run_drop_rank_and_exact_peak caller (stale flag) independentContext 0 [],
    rfl, rfl, rfl, rfl⟩

theorem every_sharp_family_also_keeps_the_author_context
    (caller : AuthorCaller) (flag : Bool) (n m k : Nat) (rest : Word) :
    LeftNodesExpected caller (stale flag) authorContext n rest ∧
      RightNodesExpected caller (stale flag) authorContext m rest ∧
      ParserNodesExpected caller (stale flag) authorContext k [.right,.left]
        [1,15] [12,3] [14] [(),()] :=
  ⟨all_left_node_families_have_the_fixed_run_drop_rank_and_exact_peak caller (stale flag) authorContext n rest,
    all_right_node_families_have_the_fixed_run_drop_rank_and_exact_peak caller (stale flag) authorContext m rest,
    every_unterminated_parser_family_restores_all_dirty_tree_and_path_stores
      caller (stale flag) authorContext k [.right,.left] [1,15] [12,3] [14] [(),()]⟩

section PhysicalSeparators
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem undo_empty_adds_one_real_cell_while_spending_one_unit_of_debt
    (d : RotationDirection) (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit) :
    let before := cfg (some (moveLabel (.undo d))) regs (data C [] O X F S Hd) ctx
    let after := cfg (some (dispatchLabel .failure)) (resetMove regs)
      (data (directionTag d :: C) [] O X F S Hd) ctx
    step caller before = some after ∧ stackCells after = stackCells before + 1 ∧
      debt before.l = 1 ∧ debt after.l = 0 ∧ potential after = potential before := by
  refine ⟨move_undo_empty_actual caller d C O X F S Hd regs ctx, ?_, rfl, rfl, ?_⟩
  · rw [stackCells_cfg, stackCells_cfg]
    simp only [localCells, data, List.length_nil, List.length_cons]
    omega
  · change potential (cfg (Λ := Λ) (some (phaseLabel (MoveApplyMachine.dispatchPhase .failure)))
      (resetMove regs) (data (directionTag d :: C) [] O X F S Hd) ctx) =
      potential (cfg (Λ := Λ) (some (phaseLabel (MoveApplyMachine.movePhase (.undo d))))
        regs (data C [] O X F S Hd) ctx)
    rw [potential_phase_cfg, potential_phase_cfg]
    simp only [phaseDebt, phaseCredit, MoveApplyMachine.movePhase,
      MoveApplyMachine.dispatchPhase, MoveParserMachine.phaseDebt, localCells, data,
      List.length_nil, List.length_cons]
    omega

theorem position_scanner_can_add_a_pending_cell_using_source_credit
    (rest : Word) :
    let before := cfg (some (positionLabel (.scanScratch .left))) regs
      (data rest [] [] [1] [] [] [()]) ctx
    let after := cfg (some (positionLabel (.scanScratch .left))) (reset regs)
      (data rest [] [] [] [] [1] [(),()]) ctx
    step caller before = some after ∧ stackCells after = stackCells before + 1 ∧
      credit before = 1 ∧ credit after = 0 ∧ potential after = potential before := by
  refine ⟨?_, ?_, rfl, rfl, ?_⟩
  · exact position_advance_step caller (.scanScratch .left)
      (data rest [] [] [1] [] [] [()]) regs ctx
  · rw [stackCells_cfg, stackCells_cfg]
    simp only [localCells, data, List.length_nil, List.length_cons]
    omega
  · change potential (cfg (Λ := Λ) (some (phaseLabel (MoveApplyMachine.positionPhase (.scanScratch .left))))
      (reset regs) (data rest [] [] [] [] [1] [(),()]) ctx) =
      potential (cfg (Λ := Λ) (some (phaseLabel (MoveApplyMachine.positionPhase (.scanScratch .left))))
        regs (data rest [] [] [1] [] [] [()]) ctx)
    rw [potential_phase_cfg, potential_phase_cfg]
    simp only [phaseDebt, phaseCredit, MoveApplyMachine.positionPhase,
      PositionedRotationMachine.phaseDebt, PositionedRotationMachine.phaseCredit,
      positionData, localCells, data, List.length_nil, List.length_cons]

end PhysicalSeparators

/- The actual bundled finite machine and its genuine one-input initializer. -/
def independentPackage (caller : ExampleCaller) (initial : Bool) : Turing.FinTM2 :=
  machine caller initial

def authorPackage (caller : AuthorCaller) (initial : Bool) : Turing.FinTM2 :=
  machine caller initial

def twoLabelPackage
    (caller : External (Fin 2) → Statement IndependentAlphabet (Fin 2) Bool)
    (initial : Bool) : Turing.FinTM2 := machine caller initial

theorem actual_unit_and_two_label_packages_have_nine_stacks_and_two_hundred_four_registers
    (caller : ExampleCaller)
    (twoCaller : External (Fin 2) → Statement IndependentAlphabet (Fin 2) Bool) (initial : Bool) :
    @Fintype.card (independentPackage caller initial).K (independentPackage caller initial).kFin = 9 ∧
      @Fintype.card (independentPackage caller initial).Λ (independentPackage caller initial).ΛFin = 30 ∧
      @Fintype.card (independentPackage caller initial).σ (independentPackage caller initial).σFin = 204 ∧
      @Fintype.card (twoLabelPackage twoCaller initial).K (twoLabelPackage twoCaller initial).kFin = 9 ∧
      @Fintype.card (twoLabelPackage twoCaller initial).Λ (twoLabelPackage twoCaller initial).ΛFin = 31 ∧
      @Fintype.card (twoLabelPackage twoCaller initial).σ (twoLabelPackage twoCaller initial).σFin = 204 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      @Fintype.card (independentPackage caller initial).K (independentPackage caller initial).kFin =
          Fintype.card (StackId (Fin 2)) :=
        @Fintype.card_congr (independentPackage caller initial).K (StackId (Fin 2))
          (independentPackage caller initial).kFin inferInstance (Equiv.refl _)
      _ = 9 := by simpa using card_stackId (K := Fin 2)
  · calc
      @Fintype.card (independentPackage caller initial).Λ (independentPackage caller initial).ΛFin =
          Fintype.card (Label Unit) :=
        @Fintype.card_congr (independentPackage caller initial).Λ (Label Unit)
          (independentPackage caller initial).ΛFin inferInstance (Equiv.refl _)
      _ = 30 := by simpa using card_label (Λ := Unit)
  · calc
      @Fintype.card (independentPackage caller initial).σ (independentPackage caller initial).σFin =
          Fintype.card (Registers Bool) :=
        @Fintype.card_congr (independentPackage caller initial).σ (Registers Bool)
          (independentPackage caller initial).σFin inferInstance (Equiv.refl _)
      _ = 204 := by simpa using card_registers (R := Bool)
  · calc
      @Fintype.card (twoLabelPackage twoCaller initial).K (twoLabelPackage twoCaller initial).kFin =
          Fintype.card (StackId (Fin 2)) :=
        @Fintype.card_congr (twoLabelPackage twoCaller initial).K (StackId (Fin 2))
          (twoLabelPackage twoCaller initial).kFin inferInstance (Equiv.refl _)
      _ = 9 := by simpa using card_stackId (K := Fin 2)
  · calc
      @Fintype.card (twoLabelPackage twoCaller initial).Λ (twoLabelPackage twoCaller initial).ΛFin =
          Fintype.card (Label (Fin 2)) :=
        @Fintype.card_congr (twoLabelPackage twoCaller initial).Λ (Label (Fin 2))
          (twoLabelPackage twoCaller initial).ΛFin inferInstance (Equiv.refl _)
      _ = 31 := by simpa using card_label (Λ := Fin 2)
  · calc
      @Fintype.card (twoLabelPackage twoCaller initial).σ (twoLabelPackage twoCaller initial).σFin =
          Fintype.card (Registers Bool) :=
        @Fintype.card_congr (twoLabelPackage twoCaller initial).σ (Registers Bool)
          (twoLabelPackage twoCaller initial).σFin inferInstance (Equiv.refl _)
      _ = 204 := by simpa using card_registers (R := Bool)

theorem every_alphabet_in_each_actual_package_is_finite
    (caller : ExampleCaller) (author : AuthorCaller)
    (twoCaller : External (Fin 2) → Statement IndependentAlphabet (Fin 2) Bool) (initial : Bool) :
    (∀ k : (independentPackage caller initial).K,
      Nonempty (Fintype ((independentPackage caller initial).Γ k))) ∧
    (∀ k : (authorPackage author initial).K,
      Nonempty (Fintype ((authorPackage author initial).Γ k))) ∧
    (∀ k : (twoLabelPackage twoCaller initial).K,
      Nonempty (Fintype ((twoLabelPackage twoCaller initial).Γ k))) :=
  ⟨fun k => ⟨machineAlphabetFintype caller initial k⟩,
    fun k => ⟨machineAlphabetFintype author initial k⟩,
    fun k => ⟨machineAlphabetFintype twoCaller initial k⟩⟩

theorem package_input_output_and_initial_control_are_actual_fields
    (caller : ExampleCaller) (initial : Bool) :
    (independentPackage caller initial).k₀ = .inl .certificate ∧
      (independentPackage caller initial).k₁ = .inl .source ∧
      (independentPackage caller initial).main = moveLabel .start ∧
      (independentPackage caller initial).initialState = clean initial := ⟨rfl, rfl, rfl, rfl⟩

section GenericPackageConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : External Λ → Statement Γ Λ R) (initial : R)

theorem actual_package_executes_every_installed_configuration
    (start : Cfg Γ Λ R) :
    (fun state : Option (Cfg Γ Λ R) => state.bind (machine caller initial).step)^[remainingSteps start]
      (some start) = some (finalCfg start) := machine_cfg_run caller initial start

def installedPackageInActualTime (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (machine caller initial).step start
      (some (finalCfg start)) (remainingSteps start) := machineCfgInTime caller initial start

theorem installed_package_timing_keeps_its_actual_rank (start : Cfg Γ Λ R) :
    (installedPackageInActualTime caller initial start).steps = remainingSteps start := rfl

theorem package_prefix_space_counts_all_seven_local_stores_and_the_context
    (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : (fun state : Option (Cfg Γ Λ R) => state.bind (machine caller initial).step)^[n]
      (some start) = some reached) : stackCells reached ≤ potential start :=
  machine_prefix_space caller initial start n bound reached executed

theorem real_initializer_sets_only_certificate_and_resets_all_temporaries (C : Word) :
    Turing.initList (machine caller initial) C =
      cfg (some (moveLabel .start)) ((none, (none, none)), initial)
        (data C [] [] [] [] [] []) (fun _ => []) := initList_eq caller initial C

theorem every_genuine_input_first_returns_one_of_the_two_live_failures (C : Word) :
    (initOutcome C = parseFailure ∨ initOutcome C = rotationFailure) ∧
      (fun state : Option (Cfg Γ Λ R) => state.bind (machine caller initial).step)^[initClock C]
        (some (Turing.initList (machine caller initial) C)) =
          some (cfg (some (resultLabel (initOutcome C))) ((none, (none, none)), initial)
            (initData C) (fun _ => [])) ∧
      ∀ j, j < initClock C → ∃ reached,
        (fun state : Option (Cfg Γ Λ R) => state.bind (machine caller initial).step)^[j]
          (some (Turing.initList (machine caller initial) C)) = some reached ∧ Owned reached.l :=
  machine_init_first_result caller initial C

def genuineInitializerInActualTime (C : Word) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (Turing.initList (machine caller initial) C)
      (some (cfg (some (resultLabel (initOutcome C))) ((none, (none, none)), initial)
        (initData C) (fun _ => []))) (initClock C) where
  steps := initClock C
  evals_in_steps := (machine_init_first_result caller initial C).2.1
  steps_le_m := Nat.le_refl _

theorem actual_initializer_time_is_its_branch_specific_count (C : Word) :
    (genuineInitializerInActualTime caller initial C).steps = initClock C := rfl

theorem every_genuine_initializer_prefix_fits_the_actual_input_word
    (C : Word) (n : Nat) (bound : n ≤ initClock C) (reached : Cfg Γ Λ R)
    (executed : (fun state : Option (Cfg Γ Λ R) => state.bind (machine caller initial).step)^[n]
      (some (Turing.initList (machine caller initial) C)) = some reached) :
    stackCells reached ≤ C.length := machine_init_space caller initial C n bound reached executed

end GenericPackageConnections

def InitFixture.Expected (c : InitFixture) (caller : ExampleCaller) (initial : Bool) : Prop :=
  let start := Turing.initList (independentPackage caller initial) c.input
  let finish := cfg (some (resultLabel c.result)) (clean initial)
    (data c.certificate [] c.path [] [] [] []) (fun _ : Fin 2 => [])
  FirstRun caller start c.ticks finish ∧
    (fun state : Option ExampleCfg => state.bind (independentPackage caller initial).step)^[c.ticks]
      (some start) = some finish ∧
    HasExactPeak caller start c.ticks c.peak

theorem initializer_fixture_observations (c : InitFixture) (member : c ∈ initFixtures) :
    initClock c.input = c.ticks ∧ initOutcome c.input = c.result ∧
      initData c.input = data c.certificate [] c.path [] [] [] [] ∧ c.input.length = c.peak := by
  simp only [initFixtures, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem all_five_literal_initializers_use_the_actual_package_first_return_and_exact_peak
    (caller : ExampleCaller) (initial : Bool) (c : InitFixture) (member : c ∈ initFixtures) :
    c.Expected caller initial := by
  obtain ⟨clock, outcome, physical, peak⟩ := initializer_fixture_observations c member
  have actual := machine_init_first_result caller initial c.input
  rw [clock, outcome, physical] at actual
  refine ⟨⟨actual.2.1, not_owned_result c.result, actual.2.2⟩, actual.2.1, ?_⟩
  have rank : remainingSteps (Turing.initList (independentPackage caller initial) c.input) = c.ticks := by
    rw [show Turing.initList (independentPackage caller initial) c.input =
      cfg (some (moveLabel .start)) (clean initial) (data c.input [] [] [] [] [] []) (fun _ => [])
        from initList_eq caller initial c.input]
    exact (initClock_eq c.input).trans clock
  apply exact_peak_of_the_universal_actual_bound_and_an_attained_prefix caller _ _ _ rank
  · intro n bound reached executed
    have cells := machine_init_space caller initial c.input n (by omega) reached executed
    omega
  · refine ⟨0, Turing.initList (independentPackage caller initial) c.input, by omega, rfl, ?_⟩
    rw [show Turing.initList (independentPackage caller initial) c.input =
      cfg (some (moveLabel .start)) (clean initial) (data c.input [] [] [] [] [] []) (fun _ => [])
        from initList_eq caller initial c.input, stackCells_cfg]
    simpa [localCells, data, contextCells] using peak

theorem certificate_only_root_input_has_empty_source_and_an_eight_step_failure
    (caller : ExampleCaller) (initial : Bool) :
    FirstRun caller (Turing.initList (independentPackage caller initial) ([6,10] : Word)) 8
      (cfg (some (resultLabel rotationFailure)) (clean initial) (data [] [] [] [] [] [] [])
        (fun _ : Fin 2 => [])) ∧
      (Turing.initList (independentPackage caller initial) ([6,10] : Word)).stk (.inl .source) = [] ∧
      treeCode nilTree = [0] ∧
      (Turing.initList (independentPackage caller initial) ([6,10] : Word)).stk (.inl .source) ≠ treeCode nilTree := by
  have actual := (machine_init_first_result caller initial ([6,10] : Word)).2
  refine ⟨⟨actual.1, not_owned_result rotationFailure, actual.2⟩, ?_, rfl, ?_⟩
  · change ([] : Word) = []
    rfl
  · change ([] : Word) ≠ [0]
    intro impossible
    cases impossible

theorem installed_root_tree_success_is_a_different_actual_eleven_step_configuration
    (caller : ExampleCaller) (initial : Bool) :
    FirstRun caller
      (cfg (some (moveLabel .start)) (clean initial)
        (data [6,10] [] [] (treeCode rightTwo) [] [] []) independentContext)
      11
      (cfg (some (resultLabel rotationSuccess)) (clean initial)
        (data [] [] [] (treeCode leftTwo) [] [] []) independentContext) ∧
    Turing.initList (independentPackage caller initial) ([6,10] : Word) ≠
      cfg (some (moveLabel .start)) (clean initial)
        (data [6,10] [] [] (treeCode rightTwo) [] [] []) independentContext := by
  have actual : LocalRun caller 11
      (cfg (some (moveLabel .start)) (clean initial)
        (data [6,10] [] [] (treeCode rightTwo) [] [] []) independentContext)
      (cfg (some (resultLabel rotationSuccess)) (clean initial)
        (data [] [] [] (treeCode leftTwo) [] [] []) independentContext) :=
    root_left_pattern_localRun caller nilTree [0,0] [] [] (clean initial) independentContext
  refine ⟨⟨LocalRun.iterate caller actual, not_owned_result rotationSuccess,
    fun n before => LocalRun.owned_prefix caller actual n before⟩, ?_⟩
  intro equal
  have source := congrArg (fun state : ExampleCfg => state.stk (.inl .source)) equal
  change ([] : Word) = [1,0,1,0,0] at source
  cases source

section FurtherInstallationConnections
variable {K Λ R K' Λ' R' : Type} {Γ : K → Type} {Γ' : K' → Type}
variable [DecidableEq K] [DecidableEq K']
variable (caller : External Λ → Statement Γ Λ R)
variable (names : StackId K ≃ K') (symbols : ∀ k, alphabet Γ k ≃ Γ' (names k))
variable (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
variable (installed : ∀ label, Owned (some label) →
  ambient (labels label) =
    FrontEndMachine.Transport.statement names symbols registers labels (program caller label))

include installed in
theorem a_complete_installation_preserves_every_actual_owned_prefix
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (some (FrontEndMachine.Transport.cfg names symbols registers labels start)) =
      ((next caller)^[n] (some start)).map
        (FrontEndMachine.Transport.cfg names symbols registers labels) :=
  installed_owned_prefix caller names symbols registers labels ambient installed start n bound

def furtherInstallationInActualTime (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (FrontEndMachine.Transport.cfg names symbols registers labels start)
      (some (FrontEndMachine.Transport.cfg names symbols registers labels (finalCfg start)))
      (remainingSteps start) :=
  installed_owned_timed caller names symbols registers labels ambient installed start

theorem complete_installed_timing_keeps_the_exact_local_steps (start : Cfg Γ Λ R) :
    (furtherInstallationInActualTime caller names symbols registers labels ambient installed start).steps =
      remainingSteps start := rfl

def furtherPrefixInActualTime (start reached : Cfg Γ Λ R) (n : Nat)
    (bound : n ≤ remainingSteps start) (actual : Runs caller start n reached) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (FrontEndMachine.Transport.cfg names symbols registers labels start)
      (some (FrontEndMachine.Transport.cfg names symbols registers labels reached)) n :=
  installed_owned_prefix_timed caller names symbols registers labels ambient installed
    start n bound reached actual

section Physical
variable [Fintype K] [Fintype K']

omit [DecidableEq K] [DecidableEq K'] in
theorem all_complete_stack_equivalences_preserve_the_actual_sum
    (start : Cfg Γ Λ R) :
    (∑ k, ((FrontEndMachine.Transport.cfg names symbols registers labels start).stk k).length) =
      stackCells start := installed_stack_cells names symbols registers labels start

include caller installed in
theorem owned_installation_space_needs_no_agreement_at_the_later_caller_labels
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Turing.TM2.Cfg Γ' Λ' R')
    (actual : (FrontEndMachine.Transport.next ambient)^[n]
      (some (FrontEndMachine.Transport.cfg names symbols registers labels start)) = some reached) :
    (∑ k, (reached.stk k).length) ≤ potential start :=
  installed_owned_prefix_space caller names symbols registers labels ambient installed
    start n bound reached actual

end Physical

/-- Full caller continuation transport has the explicitly stronger all-label premise. -/
theorem later_caller_iterations_require_complete_program_agreement
    (everyLabel : ∀ label, ambient (labels label) =
      FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (n : Nat) (start : Option (Cfg Γ Λ R)) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (start.map (FrontEndMachine.Transport.cfg names symbols registers labels)) =
      ((next caller)^[n] start).map (FrontEndMachine.Transport.cfg names symbols registers labels) :=
  installed_iterate caller names symbols registers labels ambient everyLabel n start

end FurtherInstallationConnections

theorem natural_number_callers_keep_finite_physical_stores_and_the_full_prefix_contract
    (caller : External Nat → Statement IndependentAlphabet Nat Bool)
    (start : Cfg IndependentAlphabet Nat Bool) (n : Nat) :
    Fintype.card (OwnedLabel Nat) = 26 ∧ Fintype.card (StackId (Fin 2)) = 9 ∧
      PrefixSpaceExpected caller start n :=
  ⟨card_ownedLabel, by simpa using (card_stackId (K := Fin 2)),
    every_dirty_prefix_has_the_same_rank_frame_register_and_physical_witness caller start n⟩

section FrontEndOneCallSpace
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]

theorem clean_added_branch_words_give_the_fixed_front_end_one_call_bound
    (physicalCaller : External Λ → Statement (frontEndProtectedAlphabet Γ) Λ
      (OpenDecoderMachine.Temporaries × R))
    (regs : FrontEndMachine.Registers (Option Branch × R))
    (source target : BinaryTree Unit) (fuel : List Bool) (cert : Word)
    (ctx : ∀ k, List (Γ k)) (n : Nat)
    (bound : n ≤ phaseSteps (movePhase .start) (frontEndSuccessData source cert [] []))
    (reached : Cfg (frontEndProtectedAlphabet Γ) Λ (OpenDecoderMachine.Temporaries × R))
    (actual : Runs physicalCaller
      (cfg (Λ := Λ) (some (moveLabel .start)) (frontEndRegisterEquiv (FrontEndMachine.reset regs))
        (frontEndSuccessData source cert [] []) (frontEndSuccessContext target fuel ctx)) n reached) :
    stackCells reached ≤ cert.length + 2 * (treeCode source).length +
      (treeCode target).length + fuel.length + ∑ k, (ctx k).length :=
  frontEnd_success_prefix_space physicalCaller regs source target fuel cert ctx n bound reached actual

end FrontEndOneCallSpace

section ComponentPrefixSpecializations
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem every_parser_phase_prefix_preserves_its_actual_tree_complement
    (q : MoveParserMachine.Phase) (D : LocalData) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ MoveParserMachine.phaseSteps q D.certificate D.moveReverse)
    (actual : Runs caller (cfg (some (moveLabel q)) regs D ctx) n reached) :
    reached.var = (if n = 0 then regs else resetMove regs) ∧ reached.var.2 = regs.2 ∧
      reached.stk (.inl .source) = D.source ∧ reached.stk (.inl .saved) = D.saved ∧
      reached.stk (.inl .scratch) = D.scratch ∧ reached.stk (.inl .pending) = D.pending ∧
      ∀ k, reached.stk (.inr k) = ctx k :=
  move_phase_prefix_frame caller q D regs ctx n reached bound actual

theorem every_position_phase_prefix_preserves_its_actual_certificate_complement
    (q : PositionedRotationMachine.Phase) (D : LocalData) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ PositionedRotationMachine.phaseSteps q (positionData D))
    (actual : Runs caller (cfg (some (positionLabel q)) regs D ctx) n reached) :
    reached.var = (if n = 0 then regs else reset regs) ∧ reached.var.2 = regs.2 ∧
      reached.stk (.inl .certificate) = D.certificate ∧
      reached.stk (.inl .moveReverse) = D.moveReverse ∧
      ∀ k, reached.stk (.inr k) = ctx k :=
  position_phase_prefix_frame caller q D regs ctx n reached bound actual

theorem clean_two_branch_parse_has_its_literal_internal_path_at_seven_and_paid_entry_at_eight :
    Runs caller (cfg (some (moveLabel .start)) regs
      (data [6,8,9,10] [] [] (treeCode nestedRight) [] [] []) ctx) 7
      (cfg (some (dispatchLabel (.success .left))) (resetMove regs)
        (data [] [] [.left,.right] (treeCode nestedRight) [] [] []) ctx) ∧
    Runs caller (cfg (some (moveLabel .start)) regs
      (data [6,8,9,10] [] [] (treeCode nestedRight) [] [] []) ctx) 8
      (cfg (some (positionLabel (.seek .left))) (reset regs)
        (data [] [] [.left,.right] (treeCode nestedRight) [] [] []) ctx) :=
  ⟨parse_success_boundary caller [6,8,9,10] ⟨.left,[.left,.right]⟩ [] []
      (treeCode nestedRight) [] [] [] regs ctx rfl,
    paid_position_entry caller [6,8,9,10] ⟨.left,[.left,.right]⟩ [] []
      (treeCode nestedRight) [] [] [] regs ctx rfl⟩

theorem the_internal_parser_success_is_owned_and_the_whole_success_is_external
    (d : RotationDirection) :
    Owned (some (dispatchLabel (Λ := Λ) (.success d))) ∧
      ¬ Owned (some (resultLabel (Λ := Λ) rotationSuccess)) :=
  ⟨True.intro, not_owned_result rotationSuccess⟩

end ComponentPrefixSpecializations

theorem every_fixed_halt_caller_has_the_paid_live_halt_and_outer_none_boundaries
    (flag : Bool) (c : RunFixture) (member : c ∈ fixedRuns) :
    FirstRun haltCaller (atPhase c.phase flag c.before) c.ticks (atResult c.result flag c.after) ∧
      Runs haltCaller (atPhase c.phase flag c.before) (c.ticks + 1)
        (cfg none (clean flag) c.after independentContext) ∧
      (next haltCaller)^[c.ticks + 2] (some (atPhase c.phase flag c.before)) = none := by
  have first := every_fixed_run_is_an_actual_first_live_result haltCaller (stale flag) independentContext c member
  have halt := (halt_is_one_paid_activation_before_outer_none c.result (clean flag) c.after independentContext).1
  have stopped := append_actual_step haltCaller (atPhase c.phase flag c.before)
    (atResult c.result flag c.after) c.ticks first.1
    (some (cfg none (clean flag) c.after independentContext)) halt
  refine ⟨first, stopped, ?_⟩
  exact append_actual_step haltCaller (atPhase c.phase flag c.before)
    (cfg none (clean flag) c.after independentContext) (c.ticks + 1) stopped none rfl

theorem initially_present_halt_has_identity_zero_prefix_and_immediate_outer_none
    (flag : Bool) (D : LocalData) :
    remainingSteps (cfg none (stale flag) D independentContext : ExampleCfg) = 0 ∧
      Runs haltCaller (cfg none (stale flag) D independentContext) 0
        (cfg none (stale flag) D independentContext) ∧
      next haltCaller (some (cfg none (stale flag) D independentContext)) = none := ⟨rfl, rfl, rfl⟩

theorem arbitrary_sentinel_callers_agree_through_eleven_and_differ_at_twelve
    (marker other : Tag) (distinct : marker ≠ other) (flag : Bool) :
    (∀ n, n ≤ 11 →
      (next (sentinelHaltCaller marker))^[n] (some (authorRootStart flag)) =
        (next (sentinelHaltCaller other))^[n] (some (authorRootStart flag))) ∧
    (next (sentinelHaltCaller marker))^[12] (some (authorRootStart flag)) ≠
      (next (sentinelHaltCaller other))^[12] (some (authorRootStart flag)) := by
  constructor
  · intro n bound
    apply prefix_caller_independent (sentinelHaltCaller marker) (sentinelHaltCaller other)
    have clock := (LocalRun.phaseEndpoint (sentinelHaltCaller marker)
      (q := MoveApplyMachine.movePhase .start)
      (root_left_segment_with_arbitrary_certificate_suffix
        (sentinelHaltCaller marker) (stale flag) authorContext [])).1
    change remainingSteps (authorRootStart flag) = 11 at clock
    rw [clock]
    exact bound
  · rw [(sentinel_caller_has_live_eleven_present_halt_twelve_and_outer_none_thirteen marker flag).2.1,
      (sentinel_caller_has_live_eleven_present_halt_twelve_and_outer_none_thirteen other flag).2.1]
    intro same
    have tags := congrArg (fun state : AuthorCfg => state.stk (.inr (0 : Fin 2))) (Option.some.inj same)
    exact distinct (List.cons.inj tags).1

section LiteralPeakSpecializations
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem literal_left_table_has_the_exact_initial_peak :
    HasExactPeak caller
      (cfg (some (moveLabel .start)) regs (data [6,10,15] [] [] [1,0,1,15] [] [] []) ctx)
      11 (7 + contextCells ctx) := by
  constructor
  · intro n bound
    let b := leftBoundaries[n]'(by change n < 12; omega)
    have member : b ∈ leftBoundaries := List.getElem_mem _
    have fields : b.tick = n ∧ b.cells ≤ 7 := by
      interval_cases n <;> exact ⟨rfl, of_decide_eq_true rfl⟩
    obtain ⟨tick, cells⟩ := fields
    have actual := every_left_literal_boundary_satisfies_the_complete_fixed_contract regs ctx caller b member
    refine ⟨b.cfg regs ctx, ?_, ?_⟩
    · simpa only [tick] using actual.1
    · rw [actual.2.2.2.2.2.1]
      omega
  · refine ⟨0, by omega, _, rfl, ?_⟩
    rw [stackCells_cfg]
    rfl

theorem literal_right_table_has_the_exact_initial_peak :
    HasExactPeak caller
      (cfg (some (moveLabel .start)) regs (data [7,10,15] [] [] [1,1,0,15] [] [] []) ctx)
      10 (7 + contextCells ctx) := by
  constructor
  · intro n bound
    let b := rightBoundaries[n]'(by change n < 11; omega)
    have member : b ∈ rightBoundaries := List.getElem_mem _
    have fields : b.tick = n ∧ b.cells ≤ 7 := by
      interval_cases n <;> exact ⟨rfl, of_decide_eq_true rfl⟩
    obtain ⟨tick, cells⟩ := fields
    have actual := every_right_literal_boundary_satisfies_the_complete_fixed_contract regs ctx caller b member
    refine ⟨b.cfg regs ctx, ?_, ?_⟩
    · simpa only [tick] using actual.1
    · rw [actual.2.2.2.2.2.1]
      omega
  · refine ⟨0, by omega, _, rfl, ?_⟩
    rw [stackCells_cfg]
    rfl

theorem literal_parser_failure_table_has_the_exact_initial_peak :
    HasExactPeak caller
      (cfg (some (moveLabel .start)) regs (failureData [6,8,9] []) ctx)
      8 (12 + contextCells ctx) := by
  constructor
  · intro n bound
    let b := parseFailureBoundaries[n]'(by change n < 9; omega)
    have member : b ∈ parseFailureBoundaries := List.getElem_mem _
    have fields : b.tick = n ∧ b.cells ≤ 12 := by
      interval_cases n <;> exact ⟨rfl, of_decide_eq_true rfl⟩
    obtain ⟨tick, cells⟩ := fields
    have actual := every_parser_failure_boundary_satisfies_the_complete_fixed_contract regs ctx caller b member
    refine ⟨b.cfg regs ctx, ?_, ?_⟩
    · simpa only [tick] using actual.1
    · rw [actual.2.2.2.2.2.1]
      omega
  · refine ⟨0, by omega, _, rfl, ?_⟩
    rw [stackCells_cfg]
    rfl

end LiteralPeakSpecializations

section ActualPackageRepresentedTiming
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : External Λ → Statement Γ Λ R) (initial : R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

def representedPackageInActualTime (mv : RotationMove) (rest : Word) (O : List Branch)
    (s : BinaryTree Unit) (F z : Word) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (cfg (Λ := Λ) (some (moveLabel .start)) regs
        (data (moveCode mv ++ rest) [] O (treeCode s ++ z) F [] []) ctx)
      (some (cfg (Λ := Λ) (some (resultLabel (if (applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).1.isSome
        then rotationSuccess else rotationFailure))) (reset regs)
        (data rest [] (PositionedRotationMachine.remainingPath (mv.position ++ O) s)
          (F.reverse ++ treeCode ((applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).1.getD s) ++ z)
          [] [] []) ctx))
      (2 * mv.position.length + 4 +
        PositionedRotationMachine.representedClock mv.direction (mv.position ++ O) s + F.length) :=
  machineRepresentedInTime caller initial mv rest O s F z regs ctx

def principalPackageInLinearActualTime (C : Word) (O : List Branch)
    (X F S : Word) (Hd : List Unit) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (cfg (Λ := Λ) (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx)
      (some (runResult (Λ := Λ) regs C O X F S Hd ctx))
      (3 * C.length + 3 * X.length + F.length + S.length + Hd.length + O.length + 3) :=
  machineRunInLinearTime caller initial C O X F S Hd regs ctx

theorem both_actual_package_budgets_retain_their_exact_execution_counts
    (mv : RotationMove) (rest C : Word) (O : List Branch)
    (s : BinaryTree Unit) (X F S z : Word) (Hd : List Unit) :
    (representedPackageInActualTime caller initial regs ctx mv rest O s F z).steps =
        2 * mv.position.length + 4 +
          PositionedRotationMachine.representedClock mv.direction (mv.position ++ O) s + F.length ∧
      (principalPackageInLinearActualTime caller initial regs ctx C O X F S Hd).steps =
        runSteps C O X F S Hd := ⟨rfl, rfl⟩

theorem actual_package_parser_failure_keeps_the_sharper_initial_cell_bound
    (C : Word) (O : List Branch) (X F S : Word) (Hd : List Unit)
    (failed : (parseMoveRun C).1 = none) (n : Nat) (bound : n ≤ runSteps C O X F S Hd)
    (reached : Cfg Γ Λ R)
    (actual : (fun state : Option (Cfg Γ Λ R) => state.bind (machine caller initial).step)^[n]
      (some (cfg (Λ := Λ) (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx)) = some reached) :
    stackCells reached ≤ C.length + O.length + X.length + F.length + S.length +
      Hd.length + contextCells ctx :=
  machine_principal_prefix_space_of_none caller initial C O X F S Hd regs ctx failed n bound reached actual

theorem actual_package_parsed_execution_keeps_the_maximum_of_both_stage_bounds
    (C rest : Word) (mv : RotationMove) (O : List Branch) (X F S : Word) (Hd : List Unit)
    (parsed : (parseMoveRun C).1 = some (mv, rest)) (n : Nat) (bound : n ≤ runSteps C O X F S Hd)
    (reached : Cfg Γ Λ R)
    (actual : (fun state : Option (Cfg Γ Λ R) => state.bind (machine caller initial).step)^[n]
      (some (cfg (Λ := Λ) (some (moveLabel .start)) regs (data C [] O X F S Hd) ctx)) = some reached) :
    stackCells reached ≤ max
      (C.length + O.length + X.length + F.length + S.length + Hd.length + contextCells ctx)
      (rest.length + mv.position.length + O.length + 2 * X.length + F.length + S.length +
        Hd.length + contextCells ctx) :=
  machine_principal_prefix_space_of_some caller initial C mv rest O X F S Hd regs ctx parsed n bound reached actual

end ActualPackageRepresentedTiming

section InstalledRepresentedTiming
variable {K Λ R K' Λ' R' : Type} {Γ : K → Type} {Γ' : K' → Type}
variable [DecidableEq K] [DecidableEq K']
variable (caller : External Λ → Statement Γ Λ R)
variable (names : StackId K ≃ K') (symbols : ∀ k, alphabet Γ k ≃ Γ' (names k))
variable (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
variable (installed : ∀ label, Owned (some label) → ambient (labels label) =
  FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

def representedFurtherInstallationInActualTime (mv : RotationMove) (rest : Word)
    (O : List Branch) (s : BinaryTree Unit) (F z : Word) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels
        (cfg (Λ := Λ) (some (moveLabel .start)) regs
          (data (moveCode mv ++ rest) [] O (treeCode s ++ z) F [] []) ctx))
      (some (installedCfg names symbols registers labels
        (cfg (Λ := Λ) (some (resultLabel (if (applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).1.isSome
          then rotationSuccess else rotationFailure))) (reset regs)
          (data rest [] (PositionedRotationMachine.remainingPath (mv.position ++ O) s)
            (F.reverse ++ treeCode ((applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).1.getD s) ++ z)
            [] [] []) ctx)))
      (2 * mv.position.length + 4 +
        PositionedRotationMachine.representedClock mv.direction (mv.position ++ O) s + F.length) :=
  installed_representedInTime caller names symbols registers labels ambient installed
    mv rest O s F z regs ctx

theorem further_installed_represented_timing_keeps_the_source_and_saved_word_clock
    (mv : RotationMove) (rest : Word) (O : List Branch) (s : BinaryTree Unit) (F z : Word) :
    (representedFurtherInstallationInActualTime caller names symbols registers labels ambient installed
      regs ctx mv rest O s F z).steps =
      2 * mv.position.length + 4 +
        PositionedRotationMachine.representedClock mv.direction (mv.position ++ O) s + F.length := rfl

end InstalledRepresentedTiming

/- Exact source tariffs and parsed-prefix uniqueness stay separate from machine timing. -/
theorem source_application_cost_uses_the_actual_stopped_cursor_on_failure
    (mv : RotationMove) (O : List Branch) (s : BinaryTree Unit) :
    (applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).2 =
      if (applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).1.isSome then
        3 * PositionedRotationMachine.descentCount (mv.position ++ O) s + 5
      else 2 * PositionedRotationMachine.descentCount (mv.position ++ O) s +
        if PositionedRotationMachine.stoppedPath (mv.position ++ O) s = [] then 3 else 2 :=
  source_application_cost_eq_stopped mv O s

theorem parsed_source_observation_keeps_the_actual_application_failure_tariff
    (C rest : Word) (mv : RotationMove) (O : List Branch) (s : BinaryTree Unit)
    (parsed : (parseMoveRun C).1 = some (mv, rest)) :
    sourceObservationCost C mv O s =
      3 * mv.position.length + 4 + (applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).2 :=
  sourceObservationCost_of_parse C mv rest O s parsed

theorem a_certificate_has_one_parsed_move_and_one_unconsumed_certificate_suffix
    (C rest otherRest : Word) (mv other : RotationMove)
    (parsed : (parseMoveRun C).1 = some (mv, rest))
    (alsoParsed : (parseMoveRun C).1 = some (other, otherRest)) :
    mv = other ∧ rest = otherRest := parsed_prefix_unique C mv other rest otherRest parsed alsoParsed

theorem complete_first_success_has_a_unique_parse_and_both_unchanged_literal_suffixes
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (C rest : Word) (O : List Branch) (s t : BinaryTree Unit) (F z outSuffix : Word) (ticks : Nat)
    (first : FirstRun caller
      (cfg (some (moveLabel .start)) regs (data C [] O (treeCode s ++ z) F [] []) ctx) ticks
      (cfg (some (resultLabel rotationSuccess)) (reset regs)
        (data rest [] [] (F.reverse ++ treeCode t ++ outSuffix) [] [] []) ctx)) :
    ∃ mv, (parseMoveRun C).1 = some (mv, rest) ∧
      (applyMoveRun ⟨mv.direction, mv.position ++ O⟩ s).1 = some t ∧ z = outSuffix ∧
      ticks = 2 * mv.position.length + 4 +
        PositionedRotationMachine.representedClock mv.direction (mv.position ++ O) s + F.length ∧
      ∀ other otherRest, (parseMoveRun C).1 = some (other, otherRest) →
        other = mv ∧ otherRest = rest :=
  represented_raw_first_success_unique caller C rest O s t F z outSuffix regs ctx ticks first.1 first.2.2

end Examples.RotationCertificateMoveApplyMachine
