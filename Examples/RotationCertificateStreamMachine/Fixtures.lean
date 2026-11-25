import Applications.Resources.RotationCertificate.StreamMachine
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Connected clients of the physical finite stream controller

The literal expectations come from the independently fixed Stream cases and
retain their original and post-read provenance. They include actual first
results, every returned physical word, exact machine and source observations,
all paid joins, staged registers, protected contexts and exact inclusive peaks.
The producer's proof-side evaluator does not define these expected outcomes.

Validation and audit evidence is recorded separately from the timeless
mathematical contracts retained in this module.
-/

namespace Examples.RotationCertificateStreamMachine

open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.StreamMachine

def IndependentAlphabet : Fin 2 → Type := Fin.cases Bool (fun _ => Tag)

instance independentAlphabetFintype (k : Fin 2) : Fintype (IndependentAlphabet k) :=
  Fin.cases (motive := fun k : Fin 2 => Fintype (IndependentAlphabet k))
    (inferInstance : Fintype Bool) (fun _ => (inferInstance : Fintype Tag)) k

def independentWords (bits : Bits) (tags : Word) : ∀ k, List (IndependentAlphabet k) :=
  Fin.cases bits (fun _ => tags)

def ordinaryContext : ∀ k, List (IndependentAlphabet k) :=
  independentWords [true, false, true] [11, 15]

def stale (flag : Bool) : Registers Bool :=
  (some true, ((some .right, (some (15 : Tag), some ())), flag))

def clean (flag : Bool) : Registers Bool :=
  (none, ((none, (none, none)), flag))

abbrev ExampleCfg := Cfg IndependentAlphabet Unit Bool
abbrev ExampleCaller := External Unit → Statement IndependentAlphabet Unit Bool
abbrev TwoLabelCfg := Cfg IndependentAlphabet (Fin 2) Bool
abbrev InfiniteLabelCfg := Cfg IndependentAlphabet Nat Bool

def data (C : Word) (B O : List Branch) (X Fv Sv : Word)
    (u : List Unit) (fuel : Bits) (T : Word) : LocalData :=
  { certificate := C, moveReverse := B, path := O, source := X,
    saved := Fv, scratch := Sv, units := u, fuel := fuel, target := T }

def nilTree : BinaryTree Unit := .nil
def oneTree : BinaryTree Unit := .node () nilTree nilTree
def rightTwo : BinaryTree Unit := .node () nilTree oneTree
def leftTwo : BinaryTree Unit := .node () oneTree nilTree
def rightAtLeft : BinaryTree Unit := .node () rightTwo nilTree
def leftAtLeft : BinaryTree Unit := .node () leftTwo nilTree
def rightAtRight : BinaryTree Unit := .node () nilTree rightTwo
def leftAtRight : BinaryTree Unit := .node () nilTree leftTwo

/-- Actual iteration of the supplied machine step, retaining the outer Option. -/
def Runs {K Λ R : Type} {Γ : K → Type}
    (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (start : Cfg Γ Λ R) (ticks : Nat) (finish : Cfg Γ Λ R) : Prop :=
  (fun state : Option (Cfg Γ Λ R) => state.bind transition)^[ticks] (some start) = some finish

/-- Every strict earlier state is actually reached and owned by this controller. -/
def FirstRun {K Λ R : Type} {Γ : K → Type}
    (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (start : Cfg Γ Λ R) (ticks : Nat) (finish : Cfg Γ Λ R) : Prop :=
  Runs transition start ticks finish ∧ ¬ Owned finish.l ∧
    ∀ n, n < ticks → ∃ reached, Runs transition start n reached ∧ Owned reached.l

def FirstResult {K Λ R : Type} {Γ : K → Type}
    (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (start : Cfg Γ Λ R) (result : Bool) : Prop :=
  ∃ ticks finish, FirstRun transition start ticks finish ∧
    finish.l = some (resultLabel result)

def physicalCells {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (c : Cfg Γ Λ R) : Nat := ∑ k, (c.stk k).length

def externalCells {K : Type} {Γ : K → Type} [Fintype K]
    (ctx : ∀ k, List (Γ k)) : Nat := ∑ k, (ctx k).length

/-- A peak requires both a bound at every actual prefix and actual attainment. -/
def ExactPeak {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (start : Cfg Γ Λ R) (ticks peak : Nat) : Prop :=
  (∀ n, n ≤ ticks → ∀ reached, Runs transition start n reached → physicalCells reached ≤ peak) ∧
  ∃ n reached, n ≤ ticks ∧ Runs transition start n reached ∧ physicalCells reached = peak

structure RunFixture where
  name : String
  phase : Phase
  before : LocalData
  result : Bool
  after : LocalData
  ticks : Nat
  peak : Nat

def RunFixture.start {K Λ R : Type} {Γ : K → Type}
    (c : RunFixture) (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (phaseLabel c.phase)) regs c.before ctx

def RunFixture.finish {K Λ R : Type} {Γ : K → Type}
    (c : RunFixture) (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (resultLabel c.result)) (resetAll regs) c.after ctx

def RunFixture.RunExpected {K Λ R : Type} {Γ : K → Type}
    (c : RunFixture) (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  FirstRun transition (c.start regs ctx) c.ticks (c.finish regs ctx)

def RunFixture.Expected {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (c : RunFixture) (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  c.RunExpected transition regs ctx ∧
  ExactPeak transition (c.start regs ctx) c.ticks (c.peak + externalCells ctx)

/-! ## Literal original cases A01–A21 and D01–D13 -/

def a01 : RunFixture where
  name := "A01-genuine-empty"
  phase := inspectPhase
  before := data [] [] [] [] [] [] [] [] []
  result := true
  after := data [] [] [] [] [] [] [] [] []
  ticks := 4
  peak := 0

def a02 : RunFixture where
  name := "A02-genuine-nonempty"
  phase := inspectPhase
  before := data [15] [] [] [] [] [] [] [] []
  result := false
  after := data [15] [] [] [] [] [] [] [] []
  ticks := 4
  peak := 1

def a03 : RunFixture where
  name := "A03-represented-nil-eof"
  phase := inspectPhase
  before := data [] [] [] [0] [] [] [] [] [0]
  result := true
  after := data [] [] [] [] [] [] [] [] []
  ticks := 5
  peak := 2

def a04 : RunFixture where
  name := "A04-represented-one-eof"
  phase := inspectPhase
  before := data [] [] [] [1, 0, 0] [] [] [] [false] [1, 0, 0]
  result := true
  after := data [] [] [] [] [] [] [] [false] []
  ticks := 7
  peak := 7

def a05 : RunFixture where
  name := "A05-represented-two-eof"
  phase := inspectPhase
  before := data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0]
  result := true
  after := data [] [] [] [] [] [] [] [false, false] []
  ticks := 9
  peak := 12

def a06 : RunFixture where
  name := "A06-unequal-eof"
  phase := inspectPhase
  before := data [] [] [] [1, 0, 0] [] [] [] [] [0]
  result := false
  after := data [] [] [] [0, 0] [] [] [] [] []
  ticks := 4
  peak := 4

def a07 : RunFixture where
  name := "A07-malformed-equal-eof"
  phase := inspectPhase
  before := data [] [] [] [15] [] [] [] [true] [15]
  result := true
  after := data [] [] [] [] [] [] [] [true] []
  ticks := 5
  peak := 3

def a08 : RunFixture where
  name := "A08-common-prefix-mismatch"
  phase := inspectPhase
  before := data [] [] [] [1, 0, 15, 2] [] [] [] [] [1, 0, 3, 11]
  result := false
  after := data [] [] [] [2] [] [] [] [] [11]
  ticks := 6
  peak := 8

def a09 : RunFixture where
  name := "A09-zero-before-parser"
  phase := inspectPhase
  before := data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0]
  result := false
  after := data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0]
  ticks := 8
  peak := 14

def a10 : RunFixture where
  name := "A10-foreign-parser"
  phase := inspectPhase
  before := data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0]
  result := false
  after := data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0]
  ticks := 7
  peak := 12

def a11 : RunFixture where
  name := "A11-unterminated-path"
  phase := inspectPhase
  before := data [6, 8, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0]
  result := false
  after := data [6, 8, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0]
  ticks := 11
  peak := 14

def a12 : RunFixture where
  name := "A12-root-left-success"
  phase := inspectPhase
  before := data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0]
  result := true
  after := data [] [] [] [] [] [] [] [false] []
  ticks := 25
  peak := 13

def a13 : RunFixture where
  name := "A13-root-right-success"
  phase := inspectPhase
  before := data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0]
  result := true
  after := data [] [] [] [] [] [] [] [false] []
  ticks := 24
  peak := 13

def a14 : RunFixture where
  name := "A14-root-nil-failure"
  phase := inspectPhase
  before := data [6, 10] [] [] [0] [] [] [] [true] [0]
  result := false
  after := data [] [] [] [0] [] [] [] [false] [0]
  ticks := 13
  peak := 5

def a15 : RunFixture where
  name := "A15-missing-path"
  phase := inspectPhase
  before := data [6, 8, 8, 10] [] [] [0] [] [] [] [true] [0]
  result := false
  after := data [] [] [.left] [0] [] [] [] [false] [0]
  ticks := 16
  peak := 7

def a16 : RunFixture where
  name := "A16-left-descent"
  phase := inspectPhase
  before := data [6, 8, 10] [] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [true] [1, 1, 1, 0, 0, 0, 0]
  result := true
  after := data [] [] [] [] [] [] [] [false] []
  ticks := 31
  peak := 18

def a17 : RunFixture where
  name := "A17-right-descent"
  phase := inspectPhase
  before := data [6, 9, 10] [] [] [1, 0, 1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 1, 0, 0, 0]
  result := true
  after := data [] [] [] [] [] [] [] [false] []
  ticks := 33
  peak := 18

def a18 : RunFixture where
  name := "A18-inverse-pair"
  phase := inspectPhase
  before := data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0]
  result := true
  after := data [] [] [] [] [] [] [] [false, false] []
  ticks := 42
  peak := 16

def a19 : RunFixture where
  name := "A19-insufficient-fuel"
  phase := inspectPhase
  before := data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0]
  result := false
  after := data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0]
  ticks := 22
  peak := 15

def a20 : RunFixture where
  name := "A20-foreign-suffix"
  phase := inspectPhase
  before := data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 1, 0, 0, 0]
  result := false
  after := data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0]
  ticks := 25
  peak := 15

def a21 : RunFixture where
  name := "A21-malformed-rotation-acceptance"
  phase := inspectPhase
  before := data [6, 10] [] [] [1, 0, 1, 15] [] [] [] [true] [1, 1, 0, 15]
  result := true
  after := data [] [] [] [] [] [] [] [false] []
  ticks := 24
  peak := 11

def d01 : RunFixture where
  name := "D01-dirty-eof"
  phase := inspectPhase
  before := data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] []
  result := true
  after := data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] []
  ticks := 4
  peak := 8

def d02 : RunFixture where
  name := "D02-dirty-borrow-positive"
  phase := inspectPhase
  before := data [15] [.right, .left] [.right] [15] [12] [3] [(), ()] [true] [2]
  result := false
  after := data [15] [.right, .left] [.right] [15] [12] [3] [] [true, true, false] [2]
  ticks := 9
  peak := 11

def d03 : RunFixture where
  name := "D03-dirty-borrow-zero"
  phase := inspectPhase
  before := data [15] [] [] [] [] [] [(), ()] [] []
  result := false
  after := data [15] [] [] [] [] [] [] [false, false] []
  ticks := 6
  peak := 3

def d04 : RunFixture where
  name := "D04-old-reverse-preserved"
  phase := inspectPhase
  before := data [15] [.right, .left] [.right] [1] [12] [3] [] [true] [0]
  result := false
  after := data [15] [.right, .left] [.right] [1] [12] [3] [] [false] [0]
  ticks := 7
  peak := 9

def d05 : RunFixture where
  name := "D05-old-reverse-materialized"
  phase := inspectPhase
  before := data [6, 8, 15] [.right, .left] [.right] [1] [12] [3] [] [true] [0]
  result := false
  after := data [6, 8, 9, 8, 15] [] [.right] [1] [12] [3] [] [false] [0]
  ticks := 13
  peak := 11

def d06 : RunFixture where
  name := "D06-old-reverse-executed"
  phase := inspectPhase
  before := data [6, 10] [.left] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [true] [1, 1, 1, 0, 0, 0, 0]
  result := true
  after := data [] [] [] [] [] [] [] [false] []
  ticks := 30
  peak := 18

def d07 : RunFixture where
  name := "D07-old-forward-executed"
  phase := inspectPhase
  before := data [6, 10] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [true] [1, 1, 1, 0, 0, 0, 0]
  result := true
  after := data [] [] [] [] [] [] [] [false] []
  ticks := 29
  peak := 18

def d08 : RunFixture where
  name := "D08-partial-success-dirty-aux"
  phase := applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))
  before := data [] [] [.right] [0] [] [15] [(), ()] [] [0]
  result := true
  after := data [] [] [.right] [] [] [15] [(), ()] [] []
  ticks := 7
  peak := 6

def d09 : RunFixture where
  name := "D09-direct-h-success"
  phase := applyJoinPhase MoveApplyMachine.success
  before := data [] [] [] [] [] [] [] [] []
  result := true
  after := data [] [] [] [] [] [] [] [] []
  ticks := 5
  peak := 0

def d10 : RunFixture where
  name := "D10-direct-f-positive"
  phase := fuelJoinPhase .positive
  before := data [] [] [] [] [] [] [] [] []
  result := false
  after := data [] [] [] [] [] [] [] [] []
  ticks := 4
  peak := 0

def d11 : RunFixture where
  name := "D11-direct-f-eof"
  phase := fuelJoinPhase .atEnd
  before := data [15] [] [] [] [] [] [] [] []
  result := true
  after := data [15] [] [] [] [] [] [] [] []
  ticks := 3
  peak := 1

def d12 : RunFixture where
  name := "D12-direct-e-compare"
  phase := comparePhase
  before := data [15] [] [] [] [] [] [] [] []
  result := true
  after := data [15] [] [] [] [] [] [] [] []
  ticks := 2
  peak := 1

def d13 : RunFixture where
  name := "D13-direct-e-equal"
  phase := equalityJoinPhase .equal
  before := data [15] [] [] [1] [] [] [] [] [0]
  result := true
  after := data [15] [] [] [1] [] [] [] [] [0]
  ticks := 1
  peak := 3

/-! ## Explicitly post-read cases R01–R10 -/

def r01 : RunFixture where
  name := "R01-direct-restore-true"
  phase := counterPhase .restoreTrue
  before := data [15] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [] [1, 1, 0, 0, 0]
  result := false
  after := data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true] [1, 1, 0, 0, 0]
  ticks := 7
  peak := 13

def r02 : RunFixture where
  name := "R02-direct-restore-false"
  phase := counterPhase .restoreFalse
  before := data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [true] [1, 1, 0, 0, 0]
  result := false
  after := data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, true] [1, 1, 0, 0, 0]
  ticks := 4
  peak := 15

def r03 : RunFixture where
  name := "R03-direct-h-emit"
  phase := applyPhase (MoveApplyMachine.movePhase (.emit .left))
  before := data [15] [.left] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0]
  result := false
  after := data [15] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0]
  ticks := 17
  peak := 16

def r04 : RunFixture where
  name := "R04-direct-dirty-borrow"
  phase := counterPhase .borrow
  before := data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [()] [false, true] [1, 1, 0, 0, 0]
  result := true
  after := data [] [] [] [] [] [] [] [true, true, false] []
  ticks := 27
  peak := 15

def r05 : RunFixture where
  name := "R05-prefix-target-longer"
  phase := inspectPhase
  before := data [] [] [] [1, 0] [] [] [] [true] [1, 0, 15, 2]
  result := false
  after := data [] [] [] [] [] [] [] [true] [2]
  ticks := 6
  peak := 7

def r06 : RunFixture where
  name := "R06-prefix-source-longer"
  phase := inspectPhase
  before := data [] [] [] [1, 0, 15, 2] [] [] [] [true] [1, 0]
  result := false
  after := data [] [] [] [2] [] [] [] [true] []
  ticks := 6
  peak := 7

def r07 : RunFixture where
  name := "R07-foreign-suffix-no-fuel"
  phase := inspectPhase
  before := data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0]
  result := false
  after := data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0]
  ticks := 22
  peak := 14

def r08 : RunFixture where
  name := "R08-inverse-sentinel-zero"
  phase := inspectPhase
  before := data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0]
  result := false
  after := data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0]
  ticks := 41
  peak := 17

def r09 : RunFixture where
  name := "R09-inverse-sentinel-positive"
  phase := inspectPhase
  before := data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true] [1, 0, 1, 0, 0]
  result := false
  after := data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0]
  ticks := 40
  peak := 17

def r10 : RunFixture where
  name := "R10-fe-dirty-branch-data"
  phase := inspectPhase
  before := data [6, 10] [.right] [.left] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0]
  result := false
  after := data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0]
  ticks := 20
  peak := 15

def initialCases : List RunFixture :=
  [a01, a02, a03, a04, a05, a06, a07, a08, a09, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, d01, d02, d03, d04, d05, d06, d07, d08, d09, d10, d11, d12, d13]

def postReadCases : List RunFixture :=
  [r01, r02, r03, r04, r05, r06, r07, r08, r09, r10]

def allCases : List RunFixture := initialCases ++ postReadCases

theorem initial_cases_count : initialCases.length = 34 := rfl
theorem post_read_cases_count : postReadCases.length = 10 := rfl
theorem all_cases_count : allCases.length = 44 := rfl

/-! ## Represented source observations remain separate from machine clocks -/

structure SourceFixture where
  run : RunFixture
  source : BinaryTree Unit
  target : BinaryTree Unit
  sourceTicks : Nat

def SourceFixture.SourceExpected (c : SourceFixture) : Prop :=
  c.run.before.source = treeCode c.source ∧
  c.run.before.target = treeCode c.target ∧
  checkStreamRun c.run.before.fuel c.source c.target c.run.before.certificate =
    (c.run.result, c.sourceTicks)

def sourceCases : List SourceFixture :=
  [⟨a03, nilTree, nilTree, 3⟩,
   ⟨a04, oneTree, oneTree, 6⟩,
   ⟨a05, rightTwo, rightTwo, 9⟩,
   ⟨a06, oneTree, nilTree, 3⟩,
   ⟨a09, rightTwo, leftTwo, 8⟩,
   ⟨a10, rightTwo, leftTwo, 7⟩,
   ⟨a11, rightTwo, leftTwo, 11⟩,
   ⟨a12, rightTwo, leftTwo, 22⟩,
   ⟨a13, leftTwo, rightTwo, 22⟩,
   ⟨a14, nilTree, nilTree, 12⟩,
   ⟨a15, nilTree, nilTree, 17⟩,
   ⟨a16, rightAtLeft, leftAtLeft, 31⟩,
   ⟨a17, rightAtRight, leftAtRight, 31⟩,
   ⟨a18, rightTwo, rightTwo, 38⟩,
   ⟨a19, rightTwo, rightTwo, 19⟩,
   ⟨a20, rightTwo, leftTwo, 23⟩,
   ⟨r07, rightTwo, leftTwo, 19⟩,
   ⟨r08, rightTwo, rightTwo, 37⟩,
   ⟨r09, rightTwo, rightTwo, 36⟩]

theorem source_cases_count : sourceCases.length = 19 := rfl

/-! ## Independent complete boundary records and register stages -/

inductive RegisterStage
  | original | fuel | parser | applied | equality | complete
  deriving DecidableEq

def RegisterStage.apply {R : Type} : RegisterStage → Registers R → Registers R
  | .original, regs => regs
  | .fuel, regs => (none, regs.2)
  | .parser, regs =>
      (regs.1, ((regs.2.1.1, (none, regs.2.1.2.2)), regs.2.2))
  | .applied, regs => (regs.1, ((none, (none, none)), regs.2.2))
  | .equality, regs => (regs.1, ((regs.2.1.1, (none, none)), regs.2.2))
  | .complete, regs => (none, ((none, (none, none)), regs.2.2))

structure Boundary where
  tick : Nat
  control : Phase ⊕ Bool
  stores : LocalData
  stage : RegisterStage
  cells : Nat
  remaining : Nat

def boundaryLabel {Λ : Type} : Phase ⊕ Bool → Label Λ
  | .inl q => phaseLabel q
  | .inr b => resultLabel b

def Boundary.reached {K Λ R : Type} {Γ : K → Type}
    (c : Boundary) (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (boundaryLabel c.control)) (c.stage.apply regs) c.stores ctx

def Boundary.RunExpected {K Λ R : Type} {Γ : K → Type}
    (c : Boundary) (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (start : Cfg Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  Runs transition start c.tick (c.reached regs ctx)

def rootLeftBoundaries : List Boundary :=
  [⟨0, .inl (inspectPhase), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .original, 13, 25⟩,
   ⟨1, .inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .fuel, 13, 24⟩,
   ⟨2, .inl (counterPhase .restoreTrue), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel, 13, 23⟩,
   ⟨3, .inl (fuelJoinPhase .positive), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel, 13, 22⟩,
   ⟨4, .inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete, 13, 21⟩,
   ⟨7, .inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete, 11, 18⟩,
   ⟨8, .inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete, 11, 17⟩,
   ⟨15, .inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete, 11, 10⟩,
   ⟨16, .inl (inspectPhase), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete, 11, 9⟩,
   ⟨17, .inl (fuelJoinPhase .atEnd), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete, 11, 8⟩,
   ⟨18, .inl (comparePhase), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete, 11, 7⟩,
   ⟨24, .inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false] [], .complete, 1, 1⟩,
   ⟨25, .inr true, data [] [] [] [] [] [] [] [false] [], .complete, 1, 0⟩]

def frontEndDirtyBoundaries : List Boundary :=
  [⟨0, .inl (inspectPhase), data [6, 10] [.right] [.left] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .original, 15, 20⟩,
   ⟨1, .inl (counterPhase .borrow), data [6, 10] [.right] [.left] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .fuel, 15, 19⟩,
   ⟨3, .inl (fuelJoinPhase .positive), data [6, 10] [.right] [.left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel, 15, 17⟩,
   ⟨4, .inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10] [.right] [.left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete, 15, 16⟩,
   ⟨20, .inr false, data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete, 11, 0⟩]

theorem root_left_boundary_count : rootLeftBoundaries.length = 13 := rfl
theorem front_end_dirty_boundary_count : frontEndDirtyBoundaries.length = 5 := rfl

/-! ## Eight actual one-step joins and eleven sampled component branches -/

structure JoinFixture where
  source : Phase
  target : Phase ⊕ Bool

def joinCases : List JoinFixture :=
  [⟨fuelJoinPhase .atEnd, .inl comparePhase⟩,
   ⟨fuelJoinPhase .positive, .inl (applyPhase (MoveApplyMachine.movePhase .start))⟩,
   ⟨fuelJoinPhase .zero, .inr false⟩,
   ⟨applyJoinPhase MoveApplyMachine.parseFailure, .inr false⟩,
   ⟨applyJoinPhase MoveApplyMachine.rotationFailure, .inr false⟩,
   ⟨applyJoinPhase MoveApplyMachine.success, .inl inspectPhase⟩,
   ⟨equalityJoinPhase .equal, .inr true⟩,
   ⟨equalityJoinPhase .different, .inr false⟩]

def joinData : LocalData :=
  data [6, 15] [.right] [.left] [1, 0] [12] [3] [(), ()] [false, true] [0]

def JoinFixture.Expected {K Λ R : Type} {Γ : K → Type}
    (c : JoinFixture) (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  transition (cfg (some (phaseLabel c.source)) regs D ctx) =
    some (cfg (some (boundaryLabel c.target)) (resetAll regs) D ctx)

theorem join_cases_count : joinCases.length = 8 := rfl

structure ResetFixture where
  source : Phase
  before : LocalData
  target : Phase ⊕ Bool
  after : LocalData
  stage : RegisterStage

def resetCases : List ResetFixture :=
  [⟨inspectPhase, {}, .inl (fuelJoinPhase .atEnd), {}, .fuel⟩,
   ⟨inspectPhase, {certificate := [15]}, .inl (counterPhase .borrow),
     {certificate := [15]}, .fuel⟩,
   ⟨counterPhase .borrow, {fuel := [false, true]}, .inl (counterPhase .borrow),
     {units := [()], fuel := [true]}, .fuel⟩,
   ⟨counterPhase .borrow, {fuel := [true]}, .inl (counterPhase .restoreTrue),
     {fuel := [false]}, .fuel⟩,
   ⟨counterPhase .restoreTrue, {units := [()]}, .inl (counterPhase .restoreTrue),
     {fuel := [true]}, .fuel⟩,
   ⟨counterPhase .restoreFalse, {}, .inl (fuelJoinPhase .zero), {}, .fuel⟩,
   ⟨comparePhase, {source := [15], target := [15]}, .inl comparePhase, {}, .equality⟩,
   ⟨comparePhase, {source := [1], target := [0]}, .inl (equalityJoinPhase .different),
     {}, .equality⟩,
   ⟨applyPhase (MoveApplyMachine.movePhase .start), {certificate := [6, 10]},
     .inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))),
     {certificate := [10]}, .parser⟩,
   ⟨applyPhase (MoveApplyMachine.dispatchPhase (.success .left)), {},
     .inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), {}, .applied⟩,
   ⟨applyPhase (MoveApplyMachine.positionPhase (.seek .left)),
     {source := [1, 0], path := [.left]},
     .inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))),
     {source := [0], saved := [1]}, .applied⟩]

def ResetFixture.Expected {K Λ R : Type} {Γ : K → Type}
    (c : ResetFixture) (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  transition (cfg (some (phaseLabel c.source)) regs c.before ctx) =
    some (cfg (some (boundaryLabel c.target)) (c.stage.apply regs) c.after ctx)

theorem reset_cases_count : resetCases.length = 11 := rfl

/-! ## Pure connections to the actual finite carriers and data constructors -/

theorem actual_unit_carriers_have_eleven_stacks_forty_two_labels_six_twelve_registers :
    Fintype.card (StackId (Fin 2)) = 11 ∧
    Fintype.card (Label Unit) = 42 ∧ Fintype.card (Registers Bool) = 612 := by
  constructor
  · simpa using (card_stackId (K := Fin 2))
  constructor
  · simpa using (card_label (Λ := Unit))
  · simpa using (card_registers (R := Bool))

theorem actual_two_label_carriers_have_eleven_stacks_forty_three_labels_six_twelve_registers :
    Fintype.card (StackId (Fin 2)) = 11 ∧
    Fintype.card (Label (Fin 2)) = 43 ∧ Fintype.card (Registers Bool) = 612 := by
  constructor
  · simpa using (card_stackId (K := Fin 2))
  constructor
  · simpa using (card_label (Λ := Fin 2))
  · simpa using (card_registers (R := Bool))

theorem infinite_caller_labels_still_have_exactly_thirty_nine_owned_labels :
    Fintype.card (OwnedLabel Nat) = 39 := card_ownedLabel

theorem actual_temporaries_and_two_caller_values_give_six_twelve_registers :
    Fintype.card Temporaries = 306 ∧ Fintype.card (Registers Bool) = 612 := by
  exact ⟨card_temporaries, by simpa using (card_registers (R := Bool))⟩

theorem register_stages_are_the_actual_partial_and_full_resets {R : Type} (regs : Registers R) :
    RegisterStage.apply .original regs = regs ∧
    RegisterStage.apply .fuel regs = resetFuel regs ∧
    RegisterStage.apply .parser regs = resetMove regs ∧
    RegisterStage.apply .applied regs = resetApply regs ∧
    RegisterStage.apply .equality regs = resetEquality regs ∧
    RegisterStage.apply .complete regs = resetAll regs := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem complete_cfg_keeps_every_literal_local_and_external_word
    {K Λ R : Type} {Γ : K → Type} (label : Option (Label Λ))
    (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    dataOfCfg (cfg label regs D ctx) = D ∧
    contextOfCfg (cfg label regs D ctx) = ctx ∧
    (cfg label regs D ctx).l = label ∧ (cfg label regs D ctx).var = regs :=
  ⟨dataOfCfg_cfg label regs D ctx, contextOfCfg_cfg label regs D ctx, rfl, rfl⟩

/-! ## Complete component carriers and actual paid joins -/

theorem the_counter_and_rotation_pending_views_use_the_same_physical_unit_word {K : Type} :
    fuelStackEquiv (K := K) (.inl .borrowed) = .inl .units ∧
    applyStackEquiv (K := K) (.inl .pending) = .inl .units ∧
    equalityStackEquiv (K := K) (.inr (.inl .units)) = .inl .units := by
  exact ⟨rfl, rfl, rfl⟩

theorem every_component_view_retains_the_complete_nine_word_configuration
    {K Λ R : Type} {Γ : K → Type} (regs : Registers R)
    (D : LocalData) (ctx : ∀ k, List (Γ k))
    (fuelLabel : Option (FuelDispatchMachine.Label (FuelCallerLabel Λ)))
    (applyLabel : Option (MoveApplyMachine.Label (ApplyCallerLabel Λ)))
    (equalityLabel : Option (TreeEqualityMachine.Label (EqualityCallerLabel Λ))) :
    fuelCfg (fuelView fuelLabel (fuelRegisterEquiv.symm regs) D ctx) =
      cfg (fuelLabel.map fuelLabelEquiv) regs D ctx ∧
    applyCfg (applyView applyLabel (applyRegisterEquiv.symm regs) D ctx) =
      cfg (applyLabel.map applyLabelEquiv) regs D ctx ∧
    equalityCfg (equalityView equalityLabel (equalityRegisterEquiv.symm regs) D ctx) =
      cfg (equalityLabel.map equalityLabelEquiv) regs D ctx := by
  constructor
  · simpa only [Equiv.apply_symm_apply] using
      fuelCfg_view fuelLabel (fuelRegisterEquiv.symm regs) D ctx
  constructor
  · simpa only [Equiv.apply_symm_apply] using
      applyCfg_view applyLabel (applyRegisterEquiv.symm regs) D ctx
  · simpa only [Equiv.apply_symm_apply] using
      equalityCfg_view equalityLabel (equalityRegisterEquiv.symm regs) D ctx

theorem full_component_label_maps_recover_any_global_label {Λ : Type} (label : Label Λ) :
    fuelLabelEquiv (fuelLabelEquiv.symm label) = label ∧
    applyLabelEquiv (applyLabelEquiv.symm label) = label ∧
    equalityLabelEquiv (equalityLabelEquiv.symm label) = label :=
  ⟨fuelLabelEquiv.apply_symm_apply label, applyLabelEquiv.apply_symm_apply label,
    equalityLabelEquiv.apply_symm_apply label⟩

theorem full_component_stack_maps_recover_any_physical_index {K : Type} (k : StackId K) :
    fuelStackEquiv (fuelStackEquiv.symm k) = k ∧
    applyStackEquiv (applyStackEquiv.symm k) = k ∧
    equalityStackEquiv (equalityStackEquiv.symm k) = k :=
  ⟨fuelStackEquiv.apply_symm_apply k, applyStackEquiv.apply_symm_apply k,
    equalityStackEquiv.apply_symm_apply k⟩

theorem all_eight_join_source_phases_remain_distinct :
    (joinCases.map JoinFixture.source).Nodup := by
  simp [joinCases, fuelJoinPhase, FuelDispatchMachine.exitLabel, FuelDispatchMachine.atEndLabel,
    FuelDispatchMachine.positiveLabel, FuelDispatchMachine.zeroLabel,
    Resources.BinaryCounter.FixedWidthMachine.callerLabel,
    Resources.BinaryCounter.FixedWidthMachine.resultLabel,
    applyJoinPhase, MoveApplyMachine.resultLabel, MoveApplyMachine.parseFailure,
    MoveApplyMachine.rotationFailure, MoveApplyMachine.success,
    equalityJoinPhase, TreeEqualityMachine.resultLabel]

theorem all_eight_paid_joins_are_actual_complete_cfg_steps
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ∀ c ∈ joinCases, c.Expected (step caller) D regs ctx := by
  intro c member
  simp only [joinCases, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fuel_join_step caller .atEnd D regs ctx
  · exact fuel_join_step caller .positive D regs ctx
  · exact fuel_join_step caller .zero D regs ctx
  · exact apply_join_step caller MoveApplyMachine.parseFailure D regs ctx
  · exact apply_join_step caller MoveApplyMachine.rotationFailure D regs ctx
  · exact apply_join_step caller MoveApplyMachine.success D regs ctx
  · exact equality_join_step caller .equal D regs ctx
  · exact equality_join_step caller .different D regs ctx

theorem every_fixed_join_preserves_dirty_words_for_every_finite_register
    (caller : ExampleCaller) (regs : Registers Bool) :
    ∀ c ∈ joinCases, c.Expected (step caller) joinData regs ordinaryContext :=
  all_eight_paid_joins_are_actual_complete_cfg_steps caller joinData regs ordinaryContext

theorem each_paid_join_has_one_actual_activation
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (c : JoinFixture)
    (member : c ∈ joinCases) :
    Runs (step caller) (cfg (some (phaseLabel c.source)) regs D ctx) 1
      (cfg (some (boundaryLabel c.target)) (resetAll regs) D ctx) :=
  all_eight_paid_joins_are_actual_complete_cfg_steps caller D regs ctx c member

theorem ordinary_protected_context_has_five_physical_cells :
    externalCells ordinaryContext = 5 := by
  change (∑ k : Fin 2, (ordinaryContext k).length) = 5
  rw [Fin.sum_univ_two]
  rfl

/-! ## Nonowned starts, live halt and outer none are different states -/

theorem first_result_from_a_nonowned_start_is_its_zero_step_live_label
    {K Λ R : Type} {Γ : K → Type}
    (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R)) (start : Cfg Γ Λ R)
    (result : Bool) (outside : ¬ Owned start.l) :
    FirstResult transition start result ↔ start.l = some (resultLabel result) := by
  constructor
  · rintro ⟨ticks, finish, ⟨executed, _, earlier⟩, label⟩
    cases ticks with
    | zero =>
        have same : start = finish := Option.some.inj executed
        exact same.symm ▸ label
    | succ ticks =>
        obtain ⟨reached, zero, owned⟩ := earlier 0 (Nat.zero_lt_succ ticks)
        have same : start = reached := Option.some.inj zero
        exact False.elim (outside (same.symm ▸ owned))
  · intro label
    refine ⟨0, start, ⟨rfl, outside, ?_⟩, label⟩
    intro n less
    exact False.elim (Nat.not_lt_zero n less)

theorem outer_none_is_fixed_by_the_actual_optional_iteration
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (n : Nat) :
    (next caller)^[n] none = none := next_iterate_none caller n

theorem a_live_halt_configuration_takes_an_actual_step_to_outer_none
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg none regs D ctx) = none := rfl

theorem a_live_boolean_can_be_followed_by_a_distinct_live_halt_configuration
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (result : Bool) (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    step (fun _ => .halt) (cfg (some (resultLabel (Λ := Λ) result)) regs D ctx) =
      some (cfg none regs D ctx) := rfl

/-! ## Complete dirty entry states and their actual first handoff -/

section GenericCanonicalRuns

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

theorem every_owned_phase_has_its_exact_complete_first_handoff
    (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstRun (step caller) (cfg (some (phaseLabel q)) regs D ctx)
      (phaseSteps q D) (phaseResult q regs D ctx) :=
  phase_first_return caller q D regs ctx

theorem every_configuration_has_its_exact_canonical_first_handoff
    (start : Cfg Γ Λ R) :
    FirstRun (step caller) start (remainingSteps start) (finalCfg start) :=
  cfg_firstRun caller start

theorem actual_first_handoff_fixes_both_time_and_the_entire_configuration
    (start finish : Cfg Γ Λ R) (n : Nat) :
    FirstRun (step caller) start n finish ↔
      n = remainingSteps start ∧ finish = finalCfg start :=
  firstRun_iff caller start finish n

theorem every_owned_entry_has_exactly_its_evaluated_first_boolean
    (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (result : Bool) :
    FirstResult (step caller) (cfg (some (phaseLabel q)) regs D ctx) result ↔
      (evaluate q D).result = result :=
  phase_firstResult_iff caller q D regs ctx result

theorem arbitrary_dirty_configuration_result_is_its_canonical_live_label
    (start : Cfg Γ Λ R) (result : Bool) :
    FirstResult (step caller) start result ↔
      (finalCfg start).l = some (resultLabel result) :=
  firstResult_iff_finalCfg caller start result

omit [DecidableEq K] in
theorem the_countdown_is_positive_exactly_on_owned_configurations
    (c : Cfg Γ Λ R) : 0 < remainingSteps c ↔ Owned c.l :=
  remainingSteps_pos_iff c

theorem every_real_owned_activation_decreases_the_countdown_by_one
    (before after : Cfg Γ Λ R) (owned : Owned before.l)
    (executed : step caller before = some after) :
    remainingSteps before = remainingSteps after + 1 ∧
      finalCfg before = finalCfg after :=
  ⟨local_step_remaining caller ⟨owned, executed⟩,
    finalCfg_step caller ⟨owned, executed⟩⟩

theorem a_single_actual_prefix_witness_has_the_rank_path_and_ownership
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, Runs (step caller) start n reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) :=
  owned_prefix caller start n bound

theorem arbitrary_caller_bodies_agree_through_the_actual_first_handoff
    (other : External Λ → Statement Γ Λ R) (start : Cfg Γ Λ R)
    (n : Nat) (bound : n ≤ remainingSteps start) :
    (next caller)^[n] (some start) = (next other)^[n] (some start) :=
  prefix_caller_independent caller other start n bound

theorem complete_ambient_installation_needs_only_owned_bodies_for_each_prefix
    (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ q, ambient (phaseLabel q) = program (fun _ => .halt) (phaseLabel q))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (fun state : Option (Cfg Γ Λ R) => state.bind (Turing.TM2.step ambient))^[n]
      (some start) = (next caller)^[n] (some start) :=
  ambient_prefix_eq caller ambient agrees start n bound

omit [DecidableEq K] in
theorem nonowned_configurations_have_zero_countdown_and_identity_endpoint
    (start : Cfg Γ Λ R) (outside : ¬ Owned start.l) :
    remainingSteps start = 0 ∧ finalCfg start = start :=
  ⟨nonowned_remaining start outside, nonowned_finalCfg start outside⟩

omit [DecidableEq K] in
theorem option_none_has_zero_lifted_countdown :
    stateRemainingSteps (Γ := Γ) (Λ := Λ) (R := R) none = 0 := rfl

end GenericCanonicalRuns

/-! ## Actual component segments preserve arbitrary dirty complementary words -/

section DirtyComponentConnections

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

theorem dirty_borrow_uses_the_old_units_as_low_false_bits
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    let outcome := Resources.BinaryCounter.FixedWidthMachine.predSpec
      (List.replicate D.units.length false ++ D.fuel)
    Runs (step caller) (cfg (some (phaseLabel (counterPhase .borrow))) regs D ctx)
      (Resources.BinaryCounter.FixedWidthMachine.runSteps D.fuel + D.units.length)
      (cfg (some (phaseLabel (fuelJoinPhase (FuelDispatchMachine.exitOfResult outcome.1))))
        (resetFuel regs) {D with fuel := outcome.2, units := []} ctx) :=
  (counter_phase_localRun caller .borrow D regs ctx).iterate caller

theorem dirty_restore_true_prepends_exactly_the_old_unit_count
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (cfg (some (phaseLabel (counterPhase .restoreTrue))) regs D ctx)
      (D.units.length + 1)
      (cfg (some (phaseLabel (fuelJoinPhase .positive))) (resetFuel regs)
        {D with fuel := List.replicate D.units.length true ++ D.fuel, units := []} ctx) :=
  (counter_phase_localRun caller .restoreTrue D regs ctx).iterate caller

theorem dirty_restore_false_can_return_zero_with_a_nonzero_old_suffix
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (cfg (some (phaseLabel (counterPhase .restoreFalse))) regs D ctx)
      (D.units.length + 1)
      (cfg (some (phaseLabel (fuelJoinPhase .zero))) (resetFuel regs)
        {D with fuel := List.replicate D.units.length false ++ D.fuel, units := []} ctx) :=
  (counter_phase_localRun caller .restoreFalse D regs ctx).iterate caller

theorem dirty_inspection_reaches_its_actual_fuel_join_without_extra_cleanup
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (cfg (some (phaseLabel inspectPhase)) regs D ctx)
      (inspectStageFinish D).steps
      (cfg (some (phaseLabel (fuelJoinPhase (inspectStageFinish D).result)))
        (resetFuel regs) (inspectStageFinish D).data ctx) :=
  (inspect_stage_localRun caller D regs ctx).iterate caller

theorem every_dirty_apply_phase_reaches_the_actual_apply_join
    (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (cfg (some (phaseLabel (applyPhase q))) regs D ctx)
      (applyFinish q D).steps
      (cfg (some (phaseLabel (applyJoinPhase (applyFinish q D).result)))
        (resetApply regs) (applyFinish q D).data ctx) :=
  (apply_phase_localRun caller q D regs ctx).iterate caller

theorem raw_equality_consumes_the_actual_mismatching_heads_and_preserves_other_words
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    let n := TreeEqualityMachine.runSteps D.source D.target
    Runs (step caller) (cfg (some (phaseLabel comparePhase)) regs D ctx) n
      (cfg (some (phaseLabel (equalityJoinPhase
        (TreeEqualityMachine.wordResult D.source D.target))))
        (resetEquality regs)
        {D with source := D.source.drop n, target := D.target.drop n} ctx) :=
  (equality_phase_localRun caller D regs ctx).iterate caller

end DirtyComponentConnections

theorem parsing_a_full_dirty_start_prepends_the_reverse_word_in_physical_order
    (D : MoveApplyMachine.LocalData) (move : RotationMove) (rest : Word)
    (parsed : (parseMoveRun D.certificate).1 = some (move, rest)) :
    MoveApplyMachine.moveFinish .start D =
      ⟨.success move.direction,
        {D with certificate := rest, moveReverse := [], path := D.moveReverse.reverse ++ move.position ++ D.path}⟩ ∧
    MoveParserMachine.phaseSteps .start D.certificate D.moveReverse =
      2 * move.position.length + D.moveReverse.length + 3 :=
  ⟨move_start_parse_success_data D move rest parsed,
    move_start_parse_success_steps D move rest parsed⟩

theorem a_full_dirty_start_success_exposes_the_actual_shorter_certificate
    (D : MoveApplyMachine.LocalData)
    (returned : (MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start) D).result =
      MoveApplyMachine.success) :
    ∃ move rest,
      (parseMoveRun D.certificate).1 = some (move, rest) ∧
      MoveApplyMachine.moveFinish .start D =
        ⟨.success move.direction,
          {D with certificate := rest, moveReverse := [], path := D.moveReverse.reverse ++ move.position ++ D.path}⟩ ∧
      (MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start) D).data.certificate = rest ∧
      D.certificate = moveCode move ++ rest ∧
      D.certificate.length = move.position.length + 2 + rest.length ∧
      rest.length + 2 ≤ D.certificate.length ∧ rest.length < D.certificate.length :=
  move_start_success_has_parse D returned

theorem two_old_reverse_branches_are_not_dropped_or_reversed_twice
    (rest source saved scratch : Word) (pending : List Unit) :
    let D : MoveApplyMachine.LocalData :=
      ⟨moveCode ⟨.left, [.right]⟩ ++ rest, [.left, .right], [.left],
        source, saved, scratch, pending⟩
    MoveApplyMachine.moveFinish .start D =
      ⟨.success .left, ⟨rest, [], [.right, .left, .right, .left],
        source, saved, scratch, pending⟩⟩ ∧
      MoveParserMachine.phaseSteps .start D.certificate D.moveReverse = 7 :=
  move_start_dirty_reverse_example rest source saved scratch pending


end Examples.RotationCertificateStreamMachine
