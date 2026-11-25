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

/-! ## Finite local certificates for exact inclusive peaks

These certificates contain independently fixed finite states. Every adjacent
pair must be justified by an actual public machine step. The generic argument
then identifies any actual prefix by determinism and proves its physical bound.
-/

def fixtureCells (D : LocalData) : Nat :=
  D.certificate.length + D.moveReverse.length + D.path.length + D.source.length +
  D.saved.length + D.scratch.length + D.units.length + D.fuel.length + D.target.length

structure TracePoint where
  control : Phase ⊕ Bool
  stores : LocalData
  stage : RegisterStage

def TracePoint.reached {K Λ R : Type} {Γ : K → Type}
    (p : TracePoint) (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (boundaryLabel p.control)) (p.stage.apply regs) p.stores ctx

theorem local_physical_index_sum (f : LocalStack → Nat) :
    ∑ k, f k = f .certificate + f .moveReverse + f .path + f .source +
      f .saved + f .scratch + f .units + f .fuel + f .target := by
  change (∑ k ∈ ({.certificate, .moveReverse, .path, .source, .saved, .scratch,
    .units, .fuel, .target} : Finset LocalStack), f k) = _
  simp [Nat.add_comm, Nat.add_left_comm]

theorem actual_physical_cells_of_complete_cfg
    {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (label : Option (Label Λ)) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    physicalCells (cfg label regs D ctx) = fixtureCells D + externalCells ctx := by
  rw [physicalCells, Fintype.sum_sum_type, local_physical_index_sum]
  rfl

section FiniteTraceConnections

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem finite_trace_actual_prefix (points : Nat → TracePoint) (ticks : Nat)
    (adjacent : ∀ n, n < ticks →
      step caller ((points n).reached regs ctx) = some ((points (n + 1)).reached regs ctx))
    (n : Nat) (bound : n ≤ ticks) :
    Runs (step caller) ((points 0).reached regs ctx) n ((points n).reached regs ctx) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have before := ih (by omega)
      change (next caller)^[n] (some ((points 0).reached regs ctx)) =
        some ((points n).reached regs ctx) at before
      change (next caller)^[n + 1] (some ((points 0).reached regs ctx)) = _
      rw [Function.iterate_succ_apply', before, next_some]
      exact adjacent n (by omega)

variable [Fintype K]

theorem finite_trace_has_its_exact_inclusive_peak (points : Nat → TracePoint)
    (ticks peak : Nat)
    (adjacent : ∀ n, n < ticks →
      step caller ((points n).reached regs ctx) = some ((points (n + 1)).reached regs ctx))
    (bounded : ∀ n, n ≤ ticks → fixtureCells (points n).stores ≤ peak)
    (attained : fixtureCells (points 0).stores = peak) :
    ExactPeak (step caller) ((points 0).reached regs ctx) ticks
      (peak + externalCells ctx) := by
  constructor
  · intro n bound reached executed
    have actual := finite_trace_actual_prefix caller regs ctx points ticks adjacent n bound
    have same : reached = (points n).reached regs ctx :=
      Option.some.inj (executed.symm.trans actual)
    subst reached
    rw [TracePoint.reached, actual_physical_cells_of_complete_cfg]
    exact Nat.add_le_add_right (bounded n bound) _
  · refine ⟨0, (points 0).reached regs ctx, Nat.zero_le _, rfl, ?_⟩
    rw [TracePoint.reached, actual_physical_cells_of_complete_cfg, attained]

end FiniteTraceConnections

/-! ### Fixed small local-state certificates; all edges require actual step proofs -/

def trace_a01 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [] [] [] [] [] [], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [] [] [] [] [] [], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [] [], .complete⟩
  | 3 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [] [], .complete⟩

def trace_a02 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [15] [] [] [] [] [] [] [] [], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [15] [] [] [] [] [] [] [] [], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreFalse), data [15] [] [] [] [] [] [] [] [], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .zero), data [15] [] [] [] [] [] [] [] [], .fuel⟩
  | _ => ⟨.inr false, data [15] [] [] [] [] [] [] [] [], .complete⟩

def trace_a03 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [0] [] [] [] [] [0], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [0] [] [] [] [] [0], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [] [0], .complete⟩
  | 3 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [] [], .complete⟩
  | 4 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [] [], .complete⟩

def trace_a04 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [1, 0, 0] [] [] [] [false] [1, 0, 0], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 0, 0] [] [] [] [false] [1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0] [] [] [] [false] [1, 0, 0], .complete⟩
  | 3 => ⟨.inl (comparePhase), data [] [] [] [0, 0] [] [] [] [false] [0, 0], .complete⟩
  | 4 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 5 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | 6 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false] [], .complete⟩

def trace_a05 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 3 => ⟨.inl (comparePhase), data [] [] [] [0, 1, 0, 0] [] [] [] [false, false] [0, 1, 0, 0], .complete⟩
  | 4 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0] [] [] [] [false, false] [1, 0, 0], .complete⟩
  | 5 => ⟨.inl (comparePhase), data [] [] [] [0, 0] [] [] [] [false, false] [0, 0], .complete⟩
  | 6 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false, false] [0], .complete⟩
  | 7 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false, false] [], .complete⟩
  | 8 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false, false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false, false] [], .complete⟩

def trace_a06 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [1, 0, 0] [] [] [] [] [0], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 0, 0] [] [] [] [] [0], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0] [] [] [] [] [0], .complete⟩
  | 3 => ⟨.inl (equalityJoinPhase .different), data [] [] [] [0, 0] [] [] [] [] [], .complete⟩
  | _ => ⟨.inr false, data [] [] [] [0, 0] [] [] [] [] [], .complete⟩

def trace_a07 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [15] [] [] [] [true] [15], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [15] [] [] [] [true] [15], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [15] [] [] [] [true] [15], .complete⟩
  | 3 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [true] [], .complete⟩
  | 4 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [true] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [true] [], .complete⟩

def trace_a08 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [1, 0, 15, 2] [] [] [] [] [1, 0, 3, 11], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 0, 15, 2] [] [] [] [] [1, 0, 3, 11], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 15, 2] [] [] [] [] [1, 0, 3, 11], .complete⟩
  | 3 => ⟨.inl (comparePhase), data [] [] [] [0, 15, 2] [] [] [] [] [0, 3, 11], .complete⟩
  | 4 => ⟨.inl (comparePhase), data [] [] [] [15, 2] [] [] [] [] [3, 11], .complete⟩
  | 5 => ⟨.inl (equalityJoinPhase .different), data [] [] [] [2] [] [] [] [] [11], .complete⟩
  | _ => ⟨.inr false, data [] [] [] [2] [] [] [] [] [11], .complete⟩

def trace_a09 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [()] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [] [1, 1, 0, 0, 0], .fuel⟩
  | 5 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [()] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 6 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0], .fuel⟩
  | 7 => ⟨.inl (fuelJoinPhase .zero), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0], .fuel⟩
  | _ => ⟨.inr false, data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0], .complete⟩

def trace_a10 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩

def trace_a11 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 8, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 8, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 8, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 8, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 8, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [8, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [15] [.left] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.undo .left))), data [15] [.left] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.undo .left))), data [8, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [6, 8, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [6, 8, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [6, 8, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩

def trace_a12 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [] [] [] [0, 1, 0, 0] [] [] [()] [false] [1, 1, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [] [] [] [1, 0, 0] [] [0] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0] [] [0] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (inspectPhase), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 17 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 18 => ⟨.inl (comparePhase), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 19 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0, 0] [] [] [] [false] [1, 0, 0, 0], .complete⟩
  | 20 => ⟨.inl (comparePhase), data [] [] [] [0, 0, 0] [] [] [] [false] [0, 0, 0], .complete⟩
  | 21 => ⟨.inl (comparePhase), data [] [] [] [0, 0] [] [] [] [false] [0, 0], .complete⟩
  | 22 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 23 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | 24 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false] [], .complete⟩

def trace_a13 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .right))), data [10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .right))), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .right))), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .right))), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .right))), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .right))), data [] [] [] [0, 0, 0] [] [] [()] [false] [1, 0, 1, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successRight))), data [] [] [] [1, 0, 0] [] [0] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successRight))), data [] [] [] [0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 15 => ⟨.inl (inspectPhase), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 16 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 17 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 18 => ⟨.inl (comparePhase), data [] [] [] [0, 1, 0, 0] [] [] [] [false] [0, 1, 0, 0], .complete⟩
  | 19 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0] [] [] [] [false] [1, 0, 0], .complete⟩
  | 20 => ⟨.inl (comparePhase), data [] [] [] [0, 0] [] [] [] [false] [0, 0], .complete⟩
  | 21 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 22 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | 23 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false] [], .complete⟩

def trace_a14 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10] [] [] [0] [] [] [] [true] [0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [0] [] [] [] [true] [0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 10] [] [] [0] [] [] [] [false] [0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 10] [] [] [0] [] [] [] [false] [0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .dropPending)), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure))), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 12 => ⟨.inl (applyJoinPhase MoveApplyMachine.rotationFailure), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | _ => ⟨.inr false, data [] [] [] [0] [] [] [] [false] [0], .complete⟩

def trace_a15 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 8, 8, 10] [] [] [0] [] [] [] [true] [0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 8, 8, 10] [] [] [0] [] [] [] [true] [0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 8, 8, 10] [] [] [0] [] [] [] [false] [0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 8, 8, 10] [] [] [0] [] [] [] [false] [0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 8, 8, 10] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [8, 8, 10] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [8, 10] [.left] [] [0] [] [] [] [false] [0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [.left, .left] [] [0] [] [] [] [false] [0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [.left, .left] [] [0] [] [] [] [false] [0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [.left] [.left] [0] [] [] [] [false] [0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [.left, .left] [0] [] [] [] [false] [0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [.left, .left] [0] [] [] [] [false] [0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [.left, .left] [0] [] [] [] [false] [0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .dropPending)), data [] [] [.left] [0] [] [] [] [false] [0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure))), data [] [] [.left] [0] [] [] [] [false] [0], .complete⟩
  | 15 => ⟨.inl (applyJoinPhase MoveApplyMachine.rotationFailure), data [] [] [.left] [0] [] [] [] [false] [0], .complete⟩
  | _ => ⟨.inr false, data [] [] [.left] [0] [] [] [] [false] [0], .complete⟩

def trace_a16 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 8, 10] [] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [true] [1, 1, 1, 0, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 8, 10] [] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [true] [1, 1, 1, 0, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 8, 10] [] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 8, 10] [] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 8, 10] [] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [8, 10] [] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [.left] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [.left] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [1, 0, 1, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [] [] [] [1, 0, 1, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [] [] [] [0, 1, 0, 0, 0] [1] [] [()] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [] [] [] [1, 0, 0, 0] [1] [0] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0, 0] [1] [0] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 17 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 1, 0, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 18 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 19 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 20 => ⟨.inl (inspectPhase), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 21 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 22 => ⟨.inl (comparePhase), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 23 => ⟨.inl (comparePhase), data [] [] [] [1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0, 0], .complete⟩
  | 24 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0, 0, 0] [] [] [] [false] [1, 0, 0, 0, 0], .complete⟩
  | 25 => ⟨.inl (comparePhase), data [] [] [] [0, 0, 0, 0] [] [] [] [false] [0, 0, 0, 0], .complete⟩
  | 26 => ⟨.inl (comparePhase), data [] [] [] [0, 0, 0] [] [] [] [false] [0, 0, 0], .complete⟩
  | 27 => ⟨.inl (comparePhase), data [] [] [] [0, 0] [] [] [] [false] [0, 0], .complete⟩
  | 28 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 29 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | 30 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false] [], .complete⟩

def trace_a17 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 9, 10] [] [] [1, 0, 1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 9, 10] [] [] [1, 0, 1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 9, 10] [] [] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 9, 10] [] [] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 9, 10] [] [] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [9, 10] [] [] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [.right] [] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [.right] [] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [.right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [.right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [.right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanPrefix .left))), data [] [] [] [0, 1, 0, 1, 0, 0] [1] [] [()] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [1, 0, 1, 0, 0] [0, 1] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [] [] [] [1, 0, 1, 0, 0] [0, 1] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [] [] [] [0, 1, 0, 0] [0, 1] [] [()] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [] [] [] [1, 0, 0] [0, 1] [0] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0] [0, 1] [0] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 17 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0, 0] [0, 1] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 18 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 1, 0, 0, 0] [0, 1] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 19 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [0, 1, 1, 0, 0, 0] [1] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 20 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 0, 1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 21 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [1, 0, 1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 22 => ⟨.inl (inspectPhase), data [] [] [] [1, 0, 1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 23 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 0, 1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 24 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 25 => ⟨.inl (comparePhase), data [] [] [] [0, 1, 1, 0, 0, 0] [] [] [] [false] [0, 1, 1, 0, 0, 0], .complete⟩
  | 26 => ⟨.inl (comparePhase), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 27 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0, 0] [] [] [] [false] [1, 0, 0, 0], .complete⟩
  | 28 => ⟨.inl (comparePhase), data [] [] [] [0, 0, 0] [] [] [] [false] [0, 0, 0], .complete⟩
  | 29 => ⟨.inl (comparePhase), data [] [] [] [0, 0] [] [] [] [false] [0, 0], .complete⟩
  | 30 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 31 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | 32 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false] [], .complete⟩

def trace_a18 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .borrow), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [()] [true] [1, 0, 1, 0, 0], .fuel⟩
  | 3 => ⟨.inl (counterPhase .restoreTrue), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [()] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 4 => ⟨.inl (counterPhase .restoreTrue), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .fuel⟩
  | 5 => ⟨.inl (fuelJoinPhase .positive), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .fuel⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [7, 10] [] [] [0, 1, 0, 0] [] [] [()] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [7, 10] [] [] [1, 0, 0] [] [0] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [7, 10] [] [] [0, 0] [] [0] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [7, 10] [] [] [0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 16 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 17 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 18 => ⟨.inl (inspectPhase), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 19 => ⟨.inl (counterPhase .borrow), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 20 => ⟨.inl (counterPhase .restoreTrue), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 21 => ⟨.inl (fuelJoinPhase .positive), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 22 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 23 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .right))), data [10] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 24 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .right))), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 25 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .right))), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 26 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .right))), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 27 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .right))), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 28 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .right))), data [] [] [] [0, 0, 0] [] [] [()] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 29 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successRight))), data [] [] [] [1, 0, 0] [] [0] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 30 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successRight))), data [] [] [] [0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 31 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 32 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 33 => ⟨.inl (inspectPhase), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 34 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 35 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 36 => ⟨.inl (comparePhase), data [] [] [] [0, 1, 0, 0] [] [] [] [false, false] [0, 1, 0, 0], .complete⟩
  | 37 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0] [] [] [] [false, false] [1, 0, 0], .complete⟩
  | 38 => ⟨.inl (comparePhase), data [] [] [] [0, 0] [] [] [] [false, false] [0, 0], .complete⟩
  | 39 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false, false] [0], .complete⟩
  | 40 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false, false] [], .complete⟩
  | 41 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false, false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false, false] [], .complete⟩

def trace_a19 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10, 7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [7, 10] [] [] [0, 1, 0, 0] [] [] [()] [false] [1, 0, 1, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [7, 10] [] [] [1, 0, 0] [] [0] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [7, 10] [] [] [0, 0] [] [0] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [7, 10] [] [] [0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 16 => ⟨.inl (inspectPhase), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 17 => ⟨.inl (counterPhase .borrow), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 18 => ⟨.inl (counterPhase .borrow), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [()] [] [1, 0, 1, 0, 0], .complete⟩
  | 19 => ⟨.inl (counterPhase .restoreFalse), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [()] [] [1, 0, 1, 0, 0], .complete⟩
  | 20 => ⟨.inl (counterPhase .restoreFalse), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 21 => ⟨.inl (fuelJoinPhase .zero), data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [7, 10] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩

def trace_a20 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .borrow), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [()] [true] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (counterPhase .restoreTrue), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [()] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (counterPhase .restoreTrue), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .fuel⟩
  | 5 => ⟨.inl (fuelJoinPhase .positive), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .fuel⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [15] [] [] [0, 1, 0, 0] [] [] [()] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [15] [] [] [1, 0, 0] [] [0] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [15] [] [] [0, 0] [] [0] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [15] [] [] [0, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 17 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 18 => ⟨.inl (inspectPhase), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 19 => ⟨.inl (counterPhase .borrow), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 1, 0, 0, 0], .complete⟩
  | 20 => ⟨.inl (counterPhase .restoreTrue), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0], .complete⟩
  | 21 => ⟨.inl (fuelJoinPhase .positive), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0], .complete⟩
  | 22 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0], .complete⟩
  | 23 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0], .complete⟩
  | 24 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 1, 0, 0, 0], .complete⟩

def trace_a21 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10] [] [] [1, 0, 1, 15] [] [] [] [true] [1, 1, 0, 15], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 15] [] [] [] [true] [1, 1, 0, 15], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 10] [] [] [1, 0, 1, 15] [] [] [] [false] [1, 1, 0, 15], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 10] [] [] [1, 0, 1, 15] [] [] [] [false] [1, 1, 0, 15], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10] [] [] [1, 0, 1, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [] [] [1, 0, 1, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [] [1, 0, 1, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [] [1, 0, 1, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [1, 0, 1, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [] [] [] [1, 0, 1, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [] [] [] [0, 1, 15] [] [] [()] [false] [1, 1, 0, 15], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [] [] [] [1, 15] [] [0] [] [false] [1, 1, 0, 15], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [15] [] [0] [] [false] [1, 1, 0, 15], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 1, 0, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 15 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [1, 1, 0, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 16 => ⟨.inl (inspectPhase), data [] [] [] [1, 1, 0, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 17 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 1, 0, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 18 => ⟨.inl (comparePhase), data [] [] [] [1, 1, 0, 15] [] [] [] [false] [1, 1, 0, 15], .complete⟩
  | 19 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 15] [] [] [] [false] [1, 0, 15], .complete⟩
  | 20 => ⟨.inl (comparePhase), data [] [] [] [0, 15] [] [] [] [false] [0, 15], .complete⟩
  | 21 => ⟨.inl (comparePhase), data [] [] [] [15] [] [] [] [false] [15], .complete⟩
  | 22 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | 23 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false] [], .complete⟩

def trace_d01 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .complete⟩
  | 3 => ⟨.inl (equalityJoinPhase .equal), data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .complete⟩
  | _ => ⟨.inr true, data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .complete⟩

def trace_d02 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [15] [.right, .left] [.right] [15] [12] [3] [(), ()] [true] [2], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [15] [.right, .left] [.right] [15] [12] [3] [(), ()] [true] [2], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [15] [.right, .left] [.right] [15] [12] [3] [(), ()] [false] [2], .fuel⟩
  | 3 => ⟨.inl (counterPhase .restoreTrue), data [15] [.right, .left] [.right] [15] [12] [3] [()] [true, false] [2], .fuel⟩
  | 4 => ⟨.inl (counterPhase .restoreTrue), data [15] [.right, .left] [.right] [15] [12] [3] [] [true, true, false] [2], .fuel⟩
  | 5 => ⟨.inl (fuelJoinPhase .positive), data [15] [.right, .left] [.right] [15] [12] [3] [] [true, true, false] [2], .fuel⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [15] [.right, .left] [.right] [15] [12] [3] [] [true, true, false] [2], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [15] [.right, .left] [.right] [15] [12] [3] [] [true, true, false] [2], .complete⟩
  | 8 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [15] [.right, .left] [.right] [15] [12] [3] [] [true, true, false] [2], .complete⟩
  | _ => ⟨.inr false, data [15] [.right, .left] [.right] [15] [12] [3] [] [true, true, false] [2], .complete⟩

def trace_d03 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [15] [] [] [] [] [] [(), ()] [] [], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [15] [] [] [] [] [] [(), ()] [] [], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreFalse), data [15] [] [] [] [] [] [(), ()] [] [], .fuel⟩
  | 3 => ⟨.inl (counterPhase .restoreFalse), data [15] [] [] [] [] [] [()] [false] [], .fuel⟩
  | 4 => ⟨.inl (counterPhase .restoreFalse), data [15] [] [] [] [] [] [] [false, false] [], .fuel⟩
  | 5 => ⟨.inl (fuelJoinPhase .zero), data [15] [] [] [] [] [] [] [false, false] [], .fuel⟩
  | _ => ⟨.inr false, data [15] [] [] [] [] [] [] [false, false] [], .complete⟩

def trace_d04 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [15] [.right, .left] [.right] [1] [12] [3] [] [true] [0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [15] [.right, .left] [.right] [1] [12] [3] [] [true] [0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [15] [.right, .left] [.right] [1] [12] [3] [] [false] [0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [15] [.right, .left] [.right] [1] [12] [3] [] [false] [0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [15] [.right, .left] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [15] [.right, .left] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | 6 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [15] [.right, .left] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | _ => ⟨.inr false, data [15] [.right, .left] [.right] [1] [12] [3] [] [false] [0], .complete⟩

def trace_d05 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 8, 15] [.right, .left] [.right] [1] [12] [3] [] [true] [0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 8, 15] [.right, .left] [.right] [1] [12] [3] [] [true] [0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 8, 15] [.right, .left] [.right] [1] [12] [3] [] [false] [0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 8, 15] [.right, .left] [.right] [1] [12] [3] [] [false] [0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 8, 15] [.right, .left] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [8, 15] [.right, .left] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [15] [.left, .right, .left] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.undo .left))), data [15] [.left, .right, .left] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.undo .left))), data [8, 15] [.right, .left] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.undo .left))), data [9, 8, 15] [.left] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.undo .left))), data [8, 9, 8, 15] [] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [6, 8, 9, 8, 15] [] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | 12 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [6, 8, 9, 8, 15] [] [.right] [1] [12] [3] [] [false] [0], .complete⟩
  | _ => ⟨.inr false, data [6, 8, 9, 8, 15] [] [.right] [1] [12] [3] [] [false] [0], .complete⟩

def trace_d06 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10] [.left] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [true] [1, 1, 1, 0, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [.left] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [true] [1, 1, 1, 0, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 10] [.left] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 10] [.left] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10] [.left] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [.left] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [.left] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [1, 0, 1, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [] [] [] [1, 0, 1, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [] [] [] [0, 1, 0, 0, 0] [1] [] [()] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [] [] [] [1, 0, 0, 0] [1] [0] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0, 0] [1] [0] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 1, 0, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 17 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 18 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 19 => ⟨.inl (inspectPhase), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 20 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 21 => ⟨.inl (comparePhase), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 22 => ⟨.inl (comparePhase), data [] [] [] [1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0, 0], .complete⟩
  | 23 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0, 0, 0] [] [] [] [false] [1, 0, 0, 0, 0], .complete⟩
  | 24 => ⟨.inl (comparePhase), data [] [] [] [0, 0, 0, 0] [] [] [] [false] [0, 0, 0, 0], .complete⟩
  | 25 => ⟨.inl (comparePhase), data [] [] [] [0, 0, 0] [] [] [] [false] [0, 0, 0], .complete⟩
  | 26 => ⟨.inl (comparePhase), data [] [] [] [0, 0] [] [] [] [false] [0, 0], .complete⟩
  | 27 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 28 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | 29 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false] [], .complete⟩

def trace_d07 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [true] [1, 1, 1, 0, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [true] [1, 1, 1, 0, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 10] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 10] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [1, 0, 1, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [] [] [] [1, 0, 1, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [] [] [] [0, 1, 0, 0, 0] [1] [] [()] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [] [] [] [1, 0, 0, 0] [1] [0] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0, 0] [1] [0] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 1, 0, 0, 0, 0] [1] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 17 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 18 => ⟨.inl (inspectPhase), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 19 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 20 => ⟨.inl (comparePhase), data [] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 21 => ⟨.inl (comparePhase), data [] [] [] [1, 1, 0, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0, 0], .complete⟩
  | 22 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0, 0, 0] [] [] [] [false] [1, 0, 0, 0, 0], .complete⟩
  | 23 => ⟨.inl (comparePhase), data [] [] [] [0, 0, 0, 0] [] [] [] [false] [0, 0, 0, 0], .complete⟩
  | 24 => ⟨.inl (comparePhase), data [] [] [] [0, 0, 0] [] [] [] [false] [0, 0, 0], .complete⟩
  | 25 => ⟨.inl (comparePhase), data [] [] [] [0, 0] [] [] [] [false] [0, 0], .complete⟩
  | 26 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false] [0], .complete⟩
  | 27 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | 28 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false] [], .complete⟩

def trace_d08 : Nat → TracePoint
  | 0 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [.right] [0] [] [15] [(), ()] [] [0], .original⟩
  | 1 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [.right] [0] [] [15] [(), ()] [] [0], .applied⟩
  | 2 => ⟨.inl (inspectPhase), data [] [] [.right] [0] [] [15] [(), ()] [] [0], .complete⟩
  | 3 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [.right] [0] [] [15] [(), ()] [] [0], .complete⟩
  | 4 => ⟨.inl (comparePhase), data [] [] [.right] [0] [] [15] [(), ()] [] [0], .complete⟩
  | 5 => ⟨.inl (comparePhase), data [] [] [.right] [] [] [15] [(), ()] [] [], .complete⟩
  | 6 => ⟨.inl (equalityJoinPhase .equal), data [] [] [.right] [] [] [15] [(), ()] [] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [.right] [] [] [15] [(), ()] [] [], .complete⟩

def trace_d09 : Nat → TracePoint
  | 0 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [] [] [] [] [] [], .original⟩
  | 1 => ⟨.inl (inspectPhase), data [] [] [] [] [] [] [] [] [], .complete⟩
  | 2 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [] [] [] [] [] [], .complete⟩
  | 3 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [] [], .complete⟩
  | 4 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [] [], .complete⟩

def trace_d10 : Nat → TracePoint
  | 0 => ⟨.inl (fuelJoinPhase .positive), data [] [] [] [] [] [] [] [] [], .original⟩
  | 1 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [] [] [] [] [] [] [] [] [], .complete⟩
  | 2 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [] [] [] [] [] [] [] [] [], .complete⟩
  | 3 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [] [] [] [] [] [] [] [] [], .complete⟩
  | _ => ⟨.inr false, data [] [] [] [] [] [] [] [] [], .complete⟩

def trace_d11 : Nat → TracePoint
  | 0 => ⟨.inl (fuelJoinPhase .atEnd), data [15] [] [] [] [] [] [] [] [], .original⟩
  | 1 => ⟨.inl (comparePhase), data [15] [] [] [] [] [] [] [] [], .complete⟩
  | 2 => ⟨.inl (equalityJoinPhase .equal), data [15] [] [] [] [] [] [] [] [], .complete⟩
  | _ => ⟨.inr true, data [15] [] [] [] [] [] [] [] [], .complete⟩

def trace_d12 : Nat → TracePoint
  | 0 => ⟨.inl (comparePhase), data [15] [] [] [] [] [] [] [] [], .original⟩
  | 1 => ⟨.inl (equalityJoinPhase .equal), data [15] [] [] [] [] [] [] [] [], .equality⟩
  | _ => ⟨.inr true, data [15] [] [] [] [] [] [] [] [], .complete⟩

def trace_d13 : Nat → TracePoint
  | 0 => ⟨.inl (equalityJoinPhase .equal), data [15] [] [] [1] [] [] [] [] [0], .original⟩
  | _ => ⟨.inr true, data [15] [] [] [1] [] [] [] [] [0], .complete⟩

def trace_r01 : Nat → TracePoint
  | 0 => ⟨.inl (counterPhase .restoreTrue), data [15] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .restoreTrue), data [15] [] [] [1, 0, 1, 0, 0] [] [] [()] [true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true] [1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true] [1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true] [1, 1, 0, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true] [1, 1, 0, 0, 0], .complete⟩

def trace_r02 : Nat → TracePoint
  | 0 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [true] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [()] [false, true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, true] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .zero), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, true] [1, 1, 0, 0, 0], .fuel⟩
  | _ => ⟨.inr false, data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, true] [1, 1, 0, 0, 0], .complete⟩

def trace_r03 : Nat → TracePoint
  | 0 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [15] [.left] [] [1, 1, 0, 1, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [15] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0], .parser⟩
  | 2 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [15] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0], .parser⟩
  | 3 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [15] [] [.left] [1, 1, 0, 1, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0], .applied⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [15] [] [] [1, 0, 1, 0, 0, 0] [1] [] [] [] [1, 1, 1, 0, 0, 0, 0], .applied⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [15] [] [] [1, 0, 1, 0, 0, 0] [1] [] [] [] [1, 1, 1, 0, 0, 0, 0], .applied⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [15] [] [] [0, 1, 0, 0, 0] [1] [] [()] [] [1, 1, 1, 0, 0, 0, 0], .applied⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [15] [] [] [1, 0, 0, 0] [1] [0] [] [] [1, 1, 1, 0, 0, 0, 0], .applied⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [15] [] [] [0, 0, 0] [1] [0] [] [] [1, 1, 1, 0, 0, 0, 0], .applied⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [15] [] [] [0, 0, 0, 0] [1] [] [] [] [1, 1, 1, 0, 0, 0, 0], .applied⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [15] [] [] [1, 1, 0, 0, 0, 0] [1] [] [] [] [1, 1, 1, 0, 0, 0, 0], .applied⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [15] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0], .applied⟩
  | 12 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [15] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0], .applied⟩
  | 13 => ⟨.inl (inspectPhase), data [15] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (counterPhase .borrow), data [15] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (counterPhase .restoreFalse), data [15] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (fuelJoinPhase .zero), data [15] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [15] [] [] [1, 1, 1, 0, 0, 0, 0] [] [] [] [] [1, 1, 1, 0, 0, 0, 0], .complete⟩

def trace_r04 : Nat → TracePoint
  | 0 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [()] [false, true] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (counterPhase .restoreTrue), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [()] [true, false] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (counterPhase .restoreTrue), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .fuel⟩
  | 5 => ⟨.inl (fuelJoinPhase .positive), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .fuel⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [] [] [] [0, 1, 0, 0] [] [] [()] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [] [] [] [1, 0, 0] [] [0] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0] [] [0] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 17 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 18 => ⟨.inl (inspectPhase), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 19 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 20 => ⟨.inl (comparePhase), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [true, true, false] [1, 1, 0, 0, 0], .complete⟩
  | 21 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0, 0] [] [] [] [true, true, false] [1, 0, 0, 0], .complete⟩
  | 22 => ⟨.inl (comparePhase), data [] [] [] [0, 0, 0] [] [] [] [true, true, false] [0, 0, 0], .complete⟩
  | 23 => ⟨.inl (comparePhase), data [] [] [] [0, 0] [] [] [] [true, true, false] [0, 0], .complete⟩
  | 24 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [true, true, false] [0], .complete⟩
  | 25 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [true, true, false] [], .complete⟩
  | 26 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [true, true, false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [true, true, false] [], .complete⟩

def trace_r05 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [1, 0] [] [] [] [true] [1, 0, 15, 2], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 0] [] [] [] [true] [1, 0, 15, 2], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [1, 0] [] [] [] [true] [1, 0, 15, 2], .complete⟩
  | 3 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [true] [0, 15, 2], .complete⟩
  | 4 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [true] [15, 2], .complete⟩
  | 5 => ⟨.inl (equalityJoinPhase .different), data [] [] [] [] [] [] [] [true] [2], .complete⟩
  | _ => ⟨.inr false, data [] [] [] [] [] [] [] [true] [2], .complete⟩

def trace_r06 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [1, 0, 15, 2] [] [] [] [true] [1, 0], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 0, 15, 2] [] [] [] [true] [1, 0], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 15, 2] [] [] [] [true] [1, 0], .complete⟩
  | 3 => ⟨.inl (comparePhase), data [] [] [] [0, 15, 2] [] [] [] [true] [0], .complete⟩
  | 4 => ⟨.inl (comparePhase), data [] [] [] [15, 2] [] [] [] [true] [], .complete⟩
  | 5 => ⟨.inl (equalityJoinPhase .different), data [] [] [] [2] [] [] [] [true] [], .complete⟩
  | _ => ⟨.inr false, data [] [] [] [2] [] [] [] [true] [], .complete⟩

def trace_r07 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [15] [] [] [0, 1, 0, 0] [] [] [()] [false] [1, 1, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [15] [] [] [1, 0, 0] [] [0] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [15] [] [] [0, 0] [] [0] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [15] [] [] [0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (inspectPhase), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 17 => ⟨.inl (counterPhase .borrow), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 18 => ⟨.inl (counterPhase .borrow), data [15] [] [] [1, 1, 0, 0, 0] [] [] [()] [] [1, 1, 0, 0, 0], .complete⟩
  | 19 => ⟨.inl (counterPhase .restoreFalse), data [15] [] [] [1, 1, 0, 0, 0] [] [] [()] [] [1, 1, 0, 0, 0], .complete⟩
  | 20 => ⟨.inl (counterPhase .restoreFalse), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 21 => ⟨.inl (fuelJoinPhase .zero), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩

def trace_r08 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .borrow), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [()] [true] [1, 0, 1, 0, 0], .fuel⟩
  | 3 => ⟨.inl (counterPhase .restoreTrue), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [()] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 4 => ⟨.inl (counterPhase .restoreTrue), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .fuel⟩
  | 5 => ⟨.inl (fuelJoinPhase .positive), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .fuel⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [7, 10, 15] [] [] [0, 1, 0, 0] [] [] [()] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [7, 10, 15] [] [] [1, 0, 0] [] [0] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [7, 10, 15] [] [] [0, 0] [] [0] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [7, 10, 15] [] [] [0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 16 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 17 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 18 => ⟨.inl (inspectPhase), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 19 => ⟨.inl (counterPhase .borrow), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 20 => ⟨.inl (counterPhase .restoreTrue), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 21 => ⟨.inl (fuelJoinPhase .positive), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 22 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 23 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .right))), data [10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 24 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .right))), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 25 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .right))), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 26 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .right))), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 27 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .right))), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 28 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .right))), data [15] [] [] [0, 0, 0] [] [] [()] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 29 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successRight))), data [15] [] [] [1, 0, 0] [] [0] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 30 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successRight))), data [15] [] [] [0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 31 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 32 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 33 => ⟨.inl (inspectPhase), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 34 => ⟨.inl (counterPhase .borrow), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 35 => ⟨.inl (counterPhase .borrow), data [15] [] [] [1, 0, 1, 0, 0] [] [] [()] [false] [1, 0, 1, 0, 0], .complete⟩
  | 36 => ⟨.inl (counterPhase .borrow), data [15] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [] [1, 0, 1, 0, 0], .complete⟩
  | 37 => ⟨.inl (counterPhase .restoreFalse), data [15] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [] [1, 0, 1, 0, 0], .complete⟩
  | 38 => ⟨.inl (counterPhase .restoreFalse), data [15] [] [] [1, 0, 1, 0, 0] [] [] [()] [false] [1, 0, 1, 0, 0], .complete⟩
  | 39 => ⟨.inl (counterPhase .restoreFalse), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 40 => ⟨.inl (fuelJoinPhase .zero), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩

def trace_r09 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true] [1, 0, 1, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, true] [1, 0, 1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10, 7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [7, 10, 15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [7, 10, 15] [] [] [0, 1, 0, 0] [] [] [()] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [7, 10, 15] [] [] [1, 0, 0] [] [0] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [7, 10, 15] [] [] [0, 0] [] [0] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [7, 10, 15] [] [] [0, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 16 => ⟨.inl (inspectPhase), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 17 => ⟨.inl (counterPhase .borrow), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [false, true] [1, 0, 1, 0, 0], .complete⟩
  | 18 => ⟨.inl (counterPhase .borrow), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [()] [true] [1, 0, 1, 0, 0], .complete⟩
  | 19 => ⟨.inl (counterPhase .restoreTrue), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [()] [false] [1, 0, 1, 0, 0], .complete⟩
  | 20 => ⟨.inl (counterPhase .restoreTrue), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 21 => ⟨.inl (fuelJoinPhase .positive), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 22 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [7, 10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 23 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .right))), data [10, 15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 24 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .right))), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 25 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .right))), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 26 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .right))), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 27 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .right))), data [15] [] [] [1, 1, 0, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 28 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .right))), data [15] [] [] [0, 0, 0] [] [] [()] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 29 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successRight))), data [15] [] [] [1, 0, 0] [] [0] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 30 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successRight))), data [15] [] [] [0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 31 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 32 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 33 => ⟨.inl (inspectPhase), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 34 => ⟨.inl (counterPhase .borrow), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false] [1, 0, 1, 0, 0], .complete⟩
  | 35 => ⟨.inl (counterPhase .restoreTrue), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 36 => ⟨.inl (fuelJoinPhase .positive), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 37 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 38 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | 39 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩

def trace_r10 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10] [.right] [.left] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [.right] [.left] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 10] [.right] [.left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 10] [.right] [.left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10] [.right] [.left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [.right] [.left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [.right] [.left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [.right, .left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [.right, .left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [.right, .left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanPrefix .left))), data [] [] [.left] [0, 1, 0, 0] [1] [] [()] [false] [1, 1, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [.left] [1, 0, 0] [0, 1] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [0, 0] [1, 0, 1] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [] [] [] [0, 0] [1, 0, 1] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .dropPending)), data [] [] [] [0, 0] [1, 0, 1] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure))), data [] [] [] [0, 0] [1, 0, 1] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure))), data [] [] [] [1, 0, 0] [0, 1] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 17 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure))), data [] [] [] [0, 1, 0, 0] [1] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 18 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 19 => ⟨.inl (applyJoinPhase MoveApplyMachine.rotationFailure), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩


section LiteralTraceEdges
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem trace_a01_steps (n : Nat) (bound : n < 4) :
    step caller ((trace_a01 n).reached regs ctx) =
      some ((trace_a01 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_a01 0).stores rfl ((trace_a01 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a01 1).stores ((trace_a01 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a01 2).stores ((trace_a01 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_a01 2).stage.apply regs)) (equalityContext (trace_a01 2).stores ctx))
  · exact equality_join_step caller .equal (trace_a01 3).stores ((trace_a01 3).stage.apply regs) ctx

theorem trace_a02_steps (n : Nat) (bound : n < 4) :
    step caller ((trace_a02 n).reached regs ctx) =
      some ((trace_a02 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a02 0).stores 15 [] rfl ((trace_a02 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a02 1).stores ((trace_a02 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((trace_a02 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a02 1).stores.certificate) (fuelContext (trace_a02 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_a02 2).stores ((trace_a02 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a02 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_a02 2).stores.certificate) (fuelContext (trace_a02 2).stores ctx)))
  · exact fuel_join_step caller .zero (trace_a02 3).stores ((trace_a02 3).stage.apply regs) ctx

theorem trace_a03_steps (n : Nat) (bound : n < 5) :
    step caller ((trace_a03 n).reached regs ctx) =
      some ((trace_a03 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_a03 0).stores rfl ((trace_a03 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a03 1).stores ((trace_a03 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a03 2).stores ((trace_a03 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_a03 2).stage.apply regs)) (equalityContext (trace_a03 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a03 3).stores ((trace_a03 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_a03 3).stage.apply regs)) (equalityContext (trace_a03 3).stores ctx))
  · exact equality_join_step caller .equal (trace_a03 4).stores ((trace_a03 4).stage.apply regs) ctx

theorem trace_a04_steps (n : Nat) (bound : n < 7) :
    step caller ((trace_a04 n).reached regs ctx) =
      some ((trace_a04 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_a04 0).stores rfl ((trace_a04 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a04 1).stores ((trace_a04 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a04 2).stores ((trace_a04 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((trace_a04 2).stage.apply regs)) (equalityContext (trace_a04 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a04 3).stores ((trace_a04 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((trace_a04 3).stage.apply regs)) (equalityContext (trace_a04 3).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a04 4).stores ((trace_a04 4).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_a04 4).stage.apply regs)) (equalityContext (trace_a04 4).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a04 5).stores ((trace_a04 5).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_a04 5).stage.apply regs)) (equalityContext (trace_a04 5).stores ctx))
  · exact equality_join_step caller .equal (trace_a04 6).stores ((trace_a04 6).stage.apply regs) ctx

theorem trace_a05_steps (n : Nat) (bound : n < 9) :
    step caller ((trace_a05 n).reached regs ctx) =
      some ((trace_a05 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_a05 0).stores rfl ((trace_a05 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a05 1).stores ((trace_a05 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a05 2).stores ((trace_a05 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 1, 0, 0] [0, 1, 0, 0] (equalityRegisterEquiv.symm ((trace_a05 2).stage.apply regs)) (equalityContext (trace_a05 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a05 3).stores ((trace_a05 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [1, 0, 0] [1, 0, 0] (equalityRegisterEquiv.symm ((trace_a05 3).stage.apply regs)) (equalityContext (trace_a05 3).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a05 4).stores ((trace_a05 4).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((trace_a05 4).stage.apply regs)) (equalityContext (trace_a05 4).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a05 5).stores ((trace_a05 5).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((trace_a05 5).stage.apply regs)) (equalityContext (trace_a05 5).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a05 6).stores ((trace_a05 6).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_a05 6).stage.apply regs)) (equalityContext (trace_a05 6).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a05 7).stores ((trace_a05 7).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_a05 7).stage.apply regs)) (equalityContext (trace_a05 7).stores ctx))
  · exact equality_join_step caller .equal (trace_a05 8).stores ((trace_a05 8).stage.apply regs) ctx

theorem trace_a06_steps (n : Nat) (bound : n < 4) :
    step caller ((trace_a06 n).reached regs ctx) =
      some ((trace_a06 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_a06 0).stores rfl ((trace_a06 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a06 1).stores ((trace_a06 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a06 2).stores ((trace_a06 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_different (fun _ => .halt) 1 0 [0, 0] [] (equalityRegisterEquiv.symm ((trace_a06 2).stage.apply regs)) (equalityContext (trace_a06 2).stores ctx) (by decide))
  · exact equality_join_step caller .different (trace_a06 3).stores ((trace_a06 3).stage.apply regs) ctx

theorem trace_a07_steps (n : Nat) (bound : n < 5) :
    step caller ((trace_a07 n).reached regs ctx) =
      some ((trace_a07 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_a07 0).stores rfl ((trace_a07 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a07 1).stores ((trace_a07 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a07 2).stores ((trace_a07 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 15 [] [] (equalityRegisterEquiv.symm ((trace_a07 2).stage.apply regs)) (equalityContext (trace_a07 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a07 3).stores ((trace_a07 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_a07 3).stage.apply regs)) (equalityContext (trace_a07 3).stores ctx))
  · exact equality_join_step caller .equal (trace_a07 4).stores ((trace_a07 4).stage.apply regs) ctx

theorem trace_a08_steps (n : Nat) (bound : n < 6) :
    step caller ((trace_a08 n).reached regs ctx) =
      some ((trace_a08 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_a08 0).stores rfl ((trace_a08 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a08 1).stores ((trace_a08 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a08 2).stores ((trace_a08 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 15, 2] [0, 3, 11] (equalityRegisterEquiv.symm ((trace_a08 2).stage.apply regs)) (equalityContext (trace_a08 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a08 3).stores ((trace_a08 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [15, 2] [3, 11] (equalityRegisterEquiv.symm ((trace_a08 3).stage.apply regs)) (equalityContext (trace_a08 3).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a08 4).stores ((trace_a08 4).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_different (fun _ => .halt) 15 3 [2] [11] (equalityRegisterEquiv.symm ((trace_a08 4).stage.apply regs)) (equalityContext (trace_a08 4).stores ctx) (by decide))
  · exact equality_join_step caller .different (trace_a08 5).stores ((trace_a08 5).stage.apply regs) ctx

theorem trace_a09_steps (n : Nat) (bound : n < 8) :
    step caller ((trace_a09 n).reached regs ctx) =
      some ((trace_a09 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a09 0).stores 6 [10] rfl ((trace_a09 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a09 1).stores ((trace_a09 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a09 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a09 1).stores.certificate) (fuelContext (trace_a09 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a09 2).stores ((trace_a09 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a09 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_a09 2).stores.certificate) (fuelContext (trace_a09 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a09 3).stores ((trace_a09 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((trace_a09 3).stage.apply regs) [(), ()] (FuelDispatchMachine.stores ((trace_a09 3).stores.certificate) (fuelContext (trace_a09 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_a09 4).stores ((trace_a09 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a09 4).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_a09 4).stores.certificate) (fuelContext (trace_a09 4).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_a09 5).stores ((trace_a09 5).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a09 5).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a09 5).stores.certificate) (fuelContext (trace_a09 5).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_a09 6).stores ((trace_a09 6).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((trace_a09 6).stage.apply regs) (FuelDispatchMachine.stores ((trace_a09 6).stores.certificate) (fuelContext (trace_a09 6).stores ctx)))
  · exact fuel_join_step caller .zero (trace_a09 7).stores ((trace_a09 7).stage.apply regs) ctx

theorem trace_a10_steps (n : Nat) (bound : n < 7) :
    step caller ((trace_a10 n).reached regs ctx) =
      some ((trace_a10 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a10 0).stores 15 [] rfl ((trace_a10 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a10 1).stores ((trace_a10 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a10 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a10 1).stores.certificate) (fuelContext (trace_a10 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a10 2).stores ((trace_a10 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a10 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_a10 2).stores.certificate) (fuelContext (trace_a10 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a10 3).stores ((trace_a10 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a10 4).stores ((trace_a10 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_foreign (fun _ => .halt) 15 [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a10 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a10 4).stores) (applyContext (trace_a10 4).stores ctx)) (by decide) (by decide))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_a10 5).stores ((trace_a10 5).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_a10 5).stores)
        (applyRegisterEquiv.symm ((trace_a10 5).stage.apply regs)) (applyContext (trace_a10 5).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_a10 6).stores ((trace_a10 6).stage.apply regs) ctx

theorem trace_a11_steps (n : Nat) (bound : n < 11) :
    step caller ((trace_a11 n).reached regs ctx) =
      some ((trace_a11 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a11 0).stores 6 [8, 15] rfl ((trace_a11 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a11 1).stores ((trace_a11 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a11 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a11 1).stores.certificate) (fuelContext (trace_a11 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a11 2).stores ((trace_a11 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a11 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_a11 2).stores.certificate) (fuelContext (trace_a11 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a11 3).stores ((trace_a11 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a11 4).stores ((trace_a11 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [8, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a11 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a11 4).stores) (applyContext (trace_a11 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a11 5).stores ((trace_a11 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .left [15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a11 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a11 5).stores) (applyContext (trace_a11 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a11 6).stores ((trace_a11 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_foreign (fun _ => .halt) .left 15 [] [.left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a11 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a11 6).stores) (applyContext (trace_a11 6).stores ctx)) (by decide) (by decide) (by decide))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (trace_a11 7).stores ((trace_a11 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_cons (fun _ => .halt) .left .left [15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a11 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a11 7).stores) (applyContext (trace_a11 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (trace_a11 8).stores ((trace_a11 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_nil (fun _ => .halt) .left [8, 15] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a11 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a11 8).stores) (applyContext (trace_a11 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_a11 9).stores ((trace_a11 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_a11 9).stores)
        (applyRegisterEquiv.symm ((trace_a11 9).stage.apply regs)) (applyContext (trace_a11 9).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_a11 10).stores ((trace_a11 10).stage.apply regs) ctx

theorem trace_a12_steps (n : Nat) (bound : n < 25) :
    step caller ((trace_a12 n).reached regs ctx) =
      some ((trace_a12 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a12 0).stores 6 [10] rfl ((trace_a12 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a12 1).stores ((trace_a12 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a12 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a12 1).stores.certificate) (fuelContext (trace_a12 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a12 2).stores ((trace_a12 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a12 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_a12 2).stores.certificate) (fuelContext (trace_a12 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a12 3).stores ((trace_a12 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a12 4).stores ((trace_a12 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a12 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a12 4).stores) (applyContext (trace_a12 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a12 5).stores ((trace_a12 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a12 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a12 5).stores) (applyContext (trace_a12 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a12 6).stores ((trace_a12 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a12 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a12 6).stores) (applyContext (trace_a12 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_a12 7).stores ((trace_a12 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_a12 7).stores)
        (applyRegisterEquiv.symm ((trace_a12 7).stage.apply regs)) (applyContext (trace_a12 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_a12 8).stores ((trace_a12 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_a12 9).stores ((trace_a12 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_a12 10).stores ((trace_a12 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_a12 11).stores ((trace_a12 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a12 12).stores ((trace_a12 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a12 13).stores ((trace_a12 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a12 14).stores ((trace_a12 14).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_a12 15).stores ((trace_a12 15).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_a12 16).stores rfl ((trace_a12 16).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a12 17).stores ((trace_a12 17).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a12 18).stores ((trace_a12 18).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 0, 0] [1, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_a12 18).stage.apply regs)) (equalityContext (trace_a12 18).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a12 19).stores ((trace_a12 19).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0, 0] [0, 0, 0] (equalityRegisterEquiv.symm ((trace_a12 19).stage.apply regs)) (equalityContext (trace_a12 19).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a12 20).stores ((trace_a12 20).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((trace_a12 20).stage.apply regs)) (equalityContext (trace_a12 20).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a12 21).stores ((trace_a12 21).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((trace_a12 21).stage.apply regs)) (equalityContext (trace_a12 21).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a12 22).stores ((trace_a12 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_a12 22).stage.apply regs)) (equalityContext (trace_a12 22).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a12 23).stores ((trace_a12 23).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_a12 23).stage.apply regs)) (equalityContext (trace_a12 23).stores ctx))
  · exact equality_join_step caller .equal (trace_a12 24).stores ((trace_a12 24).stage.apply regs) ctx

theorem trace_a13_steps (n : Nat) (bound : n < 24) :
    step caller ((trace_a13 n).reached regs ctx) =
      some ((trace_a13 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a13 0).stores 7 [10] rfl ((trace_a13 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a13 1).stores ((trace_a13 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a13 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a13 1).stores.certificate) (fuelContext (trace_a13 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a13 2).stores ((trace_a13 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a13 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_a13 2).stores.certificate) (fuelContext (trace_a13 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a13 3).stores ((trace_a13 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a13 4).stores ((trace_a13 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .right [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a13 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a13 4).stores) (applyContext (trace_a13 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .right) (trace_a13 5).stores ((trace_a13 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .right [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a13 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a13 5).stores) (applyContext (trace_a13 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .right) (trace_a13 6).stores ((trace_a13 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .right [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a13 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a13 6).stores) (applyContext (trace_a13 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .right)) (trace_a13 7).stores ((trace_a13 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .right) (applyData (trace_a13 7).stores)
        (applyRegisterEquiv.symm ((trace_a13 7).stage.apply regs)) (applyContext (trace_a13 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .right) (trace_a13 8).stores ((trace_a13 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .right) (trace_a13 9).stores ((trace_a13 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .right) (trace_a13 10).stores ((trace_a13 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (trace_a13 11).stores ((trace_a13 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (trace_a13 12).stores ((trace_a13 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a13 13).stores ((trace_a13 13).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_a13 14).stores ((trace_a13 14).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_a13 15).stores rfl ((trace_a13 15).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a13 16).stores ((trace_a13 16).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a13 17).stores ((trace_a13 17).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 1, 0, 0] [0, 1, 0, 0] (equalityRegisterEquiv.symm ((trace_a13 17).stage.apply regs)) (equalityContext (trace_a13 17).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a13 18).stores ((trace_a13 18).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [1, 0, 0] [1, 0, 0] (equalityRegisterEquiv.symm ((trace_a13 18).stage.apply regs)) (equalityContext (trace_a13 18).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a13 19).stores ((trace_a13 19).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((trace_a13 19).stage.apply regs)) (equalityContext (trace_a13 19).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a13 20).stores ((trace_a13 20).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((trace_a13 20).stage.apply regs)) (equalityContext (trace_a13 20).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a13 21).stores ((trace_a13 21).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_a13 21).stage.apply regs)) (equalityContext (trace_a13 21).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a13 22).stores ((trace_a13 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_a13 22).stage.apply regs)) (equalityContext (trace_a13 22).stores ctx))
  · exact equality_join_step caller .equal (trace_a13 23).stores ((trace_a13 23).stage.apply regs) ctx

theorem trace_a14_steps (n : Nat) (bound : n < 13) :
    step caller ((trace_a14 n).reached regs ctx) =
      some ((trace_a14 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a14 0).stores 6 [10] rfl ((trace_a14 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a14 1).stores ((trace_a14 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a14 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a14 1).stores.certificate) (fuelContext (trace_a14 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a14 2).stores ((trace_a14 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a14 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_a14 2).stores.certificate) (fuelContext (trace_a14 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a14 3).stores ((trace_a14 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a14 4).stores ((trace_a14 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a14 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a14 4).stores) (applyContext (trace_a14 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a14 5).stores ((trace_a14 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a14 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a14 5).stores) (applyContext (trace_a14 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a14 6).stores ((trace_a14 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a14 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a14 6).stores) (applyContext (trace_a14 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_a14 7).stores ((trace_a14 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_a14 7).stores)
        (applyRegisterEquiv.symm ((trace_a14 7).stage.apply regs)) (applyContext (trace_a14 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_a14 8).stores ((trace_a14 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_a14 9).stores ((trace_a14 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller .dropPending (trace_a14 10).stores ((trace_a14 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (trace_a14 11).stores ((trace_a14 11).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.rotationFailure (trace_a14 12).stores ((trace_a14 12).stage.apply regs) ctx

theorem trace_a15_steps (n : Nat) (bound : n < 16) :
    step caller ((trace_a15 n).reached regs ctx) =
      some ((trace_a15 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a15 0).stores 6 [8, 8, 10] rfl ((trace_a15 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a15 1).stores ((trace_a15 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a15 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a15 1).stores.certificate) (fuelContext (trace_a15 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a15 2).stores ((trace_a15 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a15 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_a15 2).stores.certificate) (fuelContext (trace_a15 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a15 3).stores ((trace_a15 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a15 4).stores ((trace_a15 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [8, 8, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a15 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a15 4).stores) (applyContext (trace_a15 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a15 5).stores ((trace_a15 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .left [8, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a15 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a15 5).stores) (applyContext (trace_a15 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a15 6).stores ((trace_a15 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .left [10] [.left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a15 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a15 6).stores) (applyContext (trace_a15 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a15 7).stores ((trace_a15 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [.left, .left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a15 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a15 7).stores) (applyContext (trace_a15 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a15 8).stores ((trace_a15 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .left [] [.left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a15 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a15 8).stores) (applyContext (trace_a15 8).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a15 9).stores ((trace_a15 9).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .left [] [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a15 9).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a15 9).stores) (applyContext (trace_a15 9).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a15 10).stores ((trace_a15 10).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.left, .left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a15 10).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a15 10).stores) (applyContext (trace_a15 10).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_a15 11).stores ((trace_a15 11).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_a15 11).stores)
        (applyRegisterEquiv.symm ((trace_a15 11).stage.apply regs)) (applyContext (trace_a15 11).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_a15 12).stores ((trace_a15 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller .dropPending (trace_a15 13).stores ((trace_a15 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (trace_a15 14).stores ((trace_a15 14).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.rotationFailure (trace_a15 15).stores ((trace_a15 15).stage.apply regs) ctx

theorem trace_a16_steps (n : Nat) (bound : n < 31) :
    step caller ((trace_a16 n).reached regs ctx) =
      some ((trace_a16 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a16 0).stores 6 [8, 10] rfl ((trace_a16 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a16 1).stores ((trace_a16 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a16 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a16 1).stores.certificate) (fuelContext (trace_a16 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a16 2).stores ((trace_a16 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a16 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_a16 2).stores.certificate) (fuelContext (trace_a16 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a16 3).stores ((trace_a16 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a16 4).stores ((trace_a16 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [8, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a16 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a16 4).stores) (applyContext (trace_a16 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a16 5).stores ((trace_a16 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a16 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a16 5).stores) (applyContext (trace_a16 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a16 6).stores ((trace_a16 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [.left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a16 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a16 6).stores) (applyContext (trace_a16 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a16 7).stores ((trace_a16 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a16 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a16 7).stores) (applyContext (trace_a16 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a16 8).stores ((trace_a16 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a16 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a16 8).stores) (applyContext (trace_a16 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_a16 9).stores ((trace_a16 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_a16 9).stores)
        (applyRegisterEquiv.symm ((trace_a16 9).stage.apply regs)) (applyContext (trace_a16 9).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_a16 10).stores ((trace_a16 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (trace_a16 11).stores ((trace_a16 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_a16 12).stores ((trace_a16 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_a16 13).stores ((trace_a16 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_a16 14).stores ((trace_a16 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a16 15).stores ((trace_a16 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a16 16).stores ((trace_a16 16).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a16 17).stores ((trace_a16 17).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a16 18).stores ((trace_a16 18).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_a16 19).stores ((trace_a16 19).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_a16 20).stores rfl ((trace_a16 20).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a16 21).stores ((trace_a16 21).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a16 22).stores ((trace_a16 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 1, 0, 0, 0, 0] [1, 1, 0, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_a16 22).stage.apply regs)) (equalityContext (trace_a16 22).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a16 23).stores ((trace_a16 23).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 0, 0, 0] [1, 0, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_a16 23).stage.apply regs)) (equalityContext (trace_a16 23).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a16 24).stores ((trace_a16 24).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0, 0, 0] [0, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_a16 24).stage.apply regs)) (equalityContext (trace_a16 24).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a16 25).stores ((trace_a16 25).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0, 0] [0, 0, 0] (equalityRegisterEquiv.symm ((trace_a16 25).stage.apply regs)) (equalityContext (trace_a16 25).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a16 26).stores ((trace_a16 26).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((trace_a16 26).stage.apply regs)) (equalityContext (trace_a16 26).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a16 27).stores ((trace_a16 27).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((trace_a16 27).stage.apply regs)) (equalityContext (trace_a16 27).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a16 28).stores ((trace_a16 28).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_a16 28).stage.apply regs)) (equalityContext (trace_a16 28).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a16 29).stores ((trace_a16 29).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_a16 29).stage.apply regs)) (equalityContext (trace_a16 29).stores ctx))
  · exact equality_join_step caller .equal (trace_a16 30).stores ((trace_a16 30).stage.apply regs) ctx

theorem trace_a17_steps (n : Nat) (bound : n < 33) :
    step caller ((trace_a17 n).reached regs ctx) =
      some ((trace_a17 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a17 0).stores 6 [9, 10] rfl ((trace_a17 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a17 1).stores ((trace_a17 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a17 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a17 1).stores.certificate) (fuelContext (trace_a17 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a17 2).stores ((trace_a17 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a17 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_a17 2).stores.certificate) (fuelContext (trace_a17 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a17 3).stores ((trace_a17 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a17 4).stores ((trace_a17 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [9, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a17 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a17 4).stores) (applyContext (trace_a17 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a17 5).stores ((trace_a17 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .right [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a17 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a17 5).stores) (applyContext (trace_a17 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a17 6).stores ((trace_a17 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [.right] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a17 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a17 6).stores) (applyContext (trace_a17 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a17 7).stores ((trace_a17 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .right [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a17 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a17 7).stores) (applyContext (trace_a17 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a17 8).stores ((trace_a17 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a17 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a17 8).stores) (applyContext (trace_a17 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_a17 9).stores ((trace_a17 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_a17 9).stores)
        (applyRegisterEquiv.symm ((trace_a17 9).stage.apply regs)) (applyContext (trace_a17 9).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_a17 10).stores ((trace_a17 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanPrefix .left) (trace_a17 11).stores ((trace_a17 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (trace_a17 12).stores ((trace_a17 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_a17 13).stores ((trace_a17 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_a17 14).stores ((trace_a17 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_a17 15).stores ((trace_a17 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a17 16).stores ((trace_a17 16).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a17 17).stores ((trace_a17 17).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a17 18).stores ((trace_a17 18).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a17 19).stores ((trace_a17 19).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a17 20).stores ((trace_a17 20).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_a17 21).stores ((trace_a17 21).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_a17 22).stores rfl ((trace_a17 22).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a17 23).stores ((trace_a17 23).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a17 24).stores ((trace_a17 24).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 1, 1, 0, 0, 0] [0, 1, 1, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_a17 24).stage.apply regs)) (equalityContext (trace_a17 24).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a17 25).stores ((trace_a17 25).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [1, 1, 0, 0, 0] [1, 1, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_a17 25).stage.apply regs)) (equalityContext (trace_a17 25).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a17 26).stores ((trace_a17 26).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 0, 0] [1, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_a17 26).stage.apply regs)) (equalityContext (trace_a17 26).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a17 27).stores ((trace_a17 27).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0, 0] [0, 0, 0] (equalityRegisterEquiv.symm ((trace_a17 27).stage.apply regs)) (equalityContext (trace_a17 27).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a17 28).stores ((trace_a17 28).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((trace_a17 28).stage.apply regs)) (equalityContext (trace_a17 28).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a17 29).stores ((trace_a17 29).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((trace_a17 29).stage.apply regs)) (equalityContext (trace_a17 29).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a17 30).stores ((trace_a17 30).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_a17 30).stage.apply regs)) (equalityContext (trace_a17 30).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a17 31).stores ((trace_a17 31).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_a17 31).stage.apply regs)) (equalityContext (trace_a17 31).stores ctx))
  · exact equality_join_step caller .equal (trace_a17 32).stores ((trace_a17 32).stage.apply regs) ctx

theorem trace_a18_steps (n : Nat) (bound : n < 42) :
    step caller ((trace_a18 n).reached regs ctx) =
      some ((trace_a18 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a18 0).stores 6 [10, 7, 10] rfl ((trace_a18 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a18 1).stores ((trace_a18 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((trace_a18 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a18 1).stores.certificate) (fuelContext (trace_a18 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a18 2).stores ((trace_a18 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a18 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_a18 2).stores.certificate) (fuelContext (trace_a18 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a18 3).stores ((trace_a18 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a18 3).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a18 3).stores.certificate) (fuelContext (trace_a18 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a18 4).stores ((trace_a18 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, false] ((trace_a18 4).stage.apply regs) (FuelDispatchMachine.stores ((trace_a18 4).stores.certificate) (fuelContext (trace_a18 4).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a18 5).stores ((trace_a18 5).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a18 6).stores ((trace_a18 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10, 7, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a18 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a18 6).stores) (applyContext (trace_a18 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a18 7).stores ((trace_a18 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [7, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a18 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a18 7).stores) (applyContext (trace_a18 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a18 8).stores ((trace_a18 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [7, 10] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a18 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a18 8).stores) (applyContext (trace_a18 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_a18 9).stores ((trace_a18 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_a18 9).stores)
        (applyRegisterEquiv.symm ((trace_a18 9).stage.apply regs)) (applyContext (trace_a18 9).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_a18 10).stores ((trace_a18 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_a18 11).stores ((trace_a18 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_a18 12).stores ((trace_a18 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_a18 13).stores ((trace_a18 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a18 14).stores ((trace_a18 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a18 15).stores ((trace_a18 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a18 16).stores ((trace_a18 16).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_a18 17).stores ((trace_a18 17).stage.apply regs) ctx
  · exact inspect_step_cons caller (trace_a18 18).stores 7 [10] rfl ((trace_a18 18).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a18 19).stores ((trace_a18 19).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a18 19).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a18 19).stores.certificate) (fuelContext (trace_a18 19).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a18 20).stores ((trace_a18 20).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((trace_a18 20).stage.apply regs) (FuelDispatchMachine.stores ((trace_a18 20).stores.certificate) (fuelContext (trace_a18 20).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a18 21).stores ((trace_a18 21).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a18 22).stores ((trace_a18 22).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .right [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a18 22).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a18 22).stores) (applyContext (trace_a18 22).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .right) (trace_a18 23).stores ((trace_a18 23).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .right [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a18 23).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a18 23).stores) (applyContext (trace_a18 23).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .right) (trace_a18 24).stores ((trace_a18 24).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .right [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a18 24).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a18 24).stores) (applyContext (trace_a18 24).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .right)) (trace_a18 25).stores ((trace_a18 25).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .right) (applyData (trace_a18 25).stores)
        (applyRegisterEquiv.symm ((trace_a18 25).stage.apply regs)) (applyContext (trace_a18 25).stores ctx))
  · exact apply_position_advance_step caller (.seek .right) (trace_a18 26).stores ((trace_a18 26).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .right) (trace_a18 27).stores ((trace_a18 27).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .right) (trace_a18 28).stores ((trace_a18 28).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (trace_a18 29).stores ((trace_a18 29).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (trace_a18 30).stores ((trace_a18 30).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a18 31).stores ((trace_a18 31).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_a18 32).stores ((trace_a18 32).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_a18 33).stores rfl ((trace_a18 33).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a18 34).stores ((trace_a18 34).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a18 35).stores ((trace_a18 35).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 1, 0, 0] [0, 1, 0, 0] (equalityRegisterEquiv.symm ((trace_a18 35).stage.apply regs)) (equalityContext (trace_a18 35).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a18 36).stores ((trace_a18 36).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [1, 0, 0] [1, 0, 0] (equalityRegisterEquiv.symm ((trace_a18 36).stage.apply regs)) (equalityContext (trace_a18 36).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a18 37).stores ((trace_a18 37).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((trace_a18 37).stage.apply regs)) (equalityContext (trace_a18 37).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a18 38).stores ((trace_a18 38).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((trace_a18 38).stage.apply regs)) (equalityContext (trace_a18 38).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a18 39).stores ((trace_a18 39).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_a18 39).stage.apply regs)) (equalityContext (trace_a18 39).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a18 40).stores ((trace_a18 40).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_a18 40).stage.apply regs)) (equalityContext (trace_a18 40).stores ctx))
  · exact equality_join_step caller .equal (trace_a18 41).stores ((trace_a18 41).stage.apply regs) ctx

theorem trace_a19_steps (n : Nat) (bound : n < 22) :
    step caller ((trace_a19 n).reached regs ctx) =
      some ((trace_a19 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a19 0).stores 6 [10, 7, 10] rfl ((trace_a19 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a19 1).stores ((trace_a19 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a19 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a19 1).stores.certificate) (fuelContext (trace_a19 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a19 2).stores ((trace_a19 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a19 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_a19 2).stores.certificate) (fuelContext (trace_a19 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a19 3).stores ((trace_a19 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a19 4).stores ((trace_a19 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10, 7, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a19 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a19 4).stores) (applyContext (trace_a19 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a19 5).stores ((trace_a19 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [7, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a19 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a19 5).stores) (applyContext (trace_a19 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a19 6).stores ((trace_a19 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [7, 10] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a19 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a19 6).stores) (applyContext (trace_a19 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_a19 7).stores ((trace_a19 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_a19 7).stores)
        (applyRegisterEquiv.symm ((trace_a19 7).stage.apply regs)) (applyContext (trace_a19 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_a19 8).stores ((trace_a19 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_a19 9).stores ((trace_a19 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_a19 10).stores ((trace_a19 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_a19 11).stores ((trace_a19 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a19 12).stores ((trace_a19 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a19 13).stores ((trace_a19 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a19 14).stores ((trace_a19 14).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_a19 15).stores ((trace_a19 15).stage.apply regs) ctx
  · exact inspect_step_cons caller (trace_a19 16).stores 7 [10] rfl ((trace_a19 16).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a19 17).stores ((trace_a19 17).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a19 17).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a19 17).stores.certificate) (fuelContext (trace_a19 17).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a19 18).stores ((trace_a19 18).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((trace_a19 18).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_a19 18).stores.certificate) (fuelContext (trace_a19 18).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_a19 19).stores ((trace_a19 19).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a19 19).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a19 19).stores.certificate) (fuelContext (trace_a19 19).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_a19 20).stores ((trace_a19 20).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a19 20).stage.apply regs) (FuelDispatchMachine.stores ((trace_a19 20).stores.certificate) (fuelContext (trace_a19 20).stores ctx)))
  · exact fuel_join_step caller .zero (trace_a19 21).stores ((trace_a19 21).stage.apply regs) ctx

theorem trace_a20_steps (n : Nat) (bound : n < 25) :
    step caller ((trace_a20 n).reached regs ctx) =
      some ((trace_a20 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a20 0).stores 6 [10, 15] rfl ((trace_a20 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a20 1).stores ((trace_a20 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((trace_a20 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a20 1).stores.certificate) (fuelContext (trace_a20 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a20 2).stores ((trace_a20 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a20 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_a20 2).stores.certificate) (fuelContext (trace_a20 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a20 3).stores ((trace_a20 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a20 3).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a20 3).stores.certificate) (fuelContext (trace_a20 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a20 4).stores ((trace_a20 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, false] ((trace_a20 4).stage.apply regs) (FuelDispatchMachine.stores ((trace_a20 4).stores.certificate) (fuelContext (trace_a20 4).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a20 5).stores ((trace_a20 5).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a20 6).stores ((trace_a20 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a20 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a20 6).stores) (applyContext (trace_a20 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a20 7).stores ((trace_a20 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a20 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a20 7).stores) (applyContext (trace_a20 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a20 8).stores ((trace_a20 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [15] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a20 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a20 8).stores) (applyContext (trace_a20 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_a20 9).stores ((trace_a20 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_a20 9).stores)
        (applyRegisterEquiv.symm ((trace_a20 9).stage.apply regs)) (applyContext (trace_a20 9).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_a20 10).stores ((trace_a20 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_a20 11).stores ((trace_a20 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_a20 12).stores ((trace_a20 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_a20 13).stores ((trace_a20 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a20 14).stores ((trace_a20 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a20 15).stores ((trace_a20 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a20 16).stores ((trace_a20 16).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_a20 17).stores ((trace_a20 17).stage.apply regs) ctx
  · exact inspect_step_cons caller (trace_a20 18).stores 15 [] rfl ((trace_a20 18).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a20 19).stores ((trace_a20 19).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a20 19).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a20 19).stores.certificate) (fuelContext (trace_a20 19).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a20 20).stores ((trace_a20 20).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((trace_a20 20).stage.apply regs) (FuelDispatchMachine.stores ((trace_a20 20).stores.certificate) (fuelContext (trace_a20 20).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a20 21).stores ((trace_a20 21).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a20 22).stores ((trace_a20 22).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_foreign (fun _ => .halt) 15 [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a20 22).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a20 22).stores) (applyContext (trace_a20 22).stores ctx)) (by decide) (by decide))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_a20 23).stores ((trace_a20 23).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_a20 23).stores)
        (applyRegisterEquiv.symm ((trace_a20 23).stage.apply regs)) (applyContext (trace_a20 23).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_a20 24).stores ((trace_a20 24).stage.apply regs) ctx

theorem trace_a21_steps (n : Nat) (bound : n < 24) :
    step caller ((trace_a21 n).reached regs ctx) =
      some ((trace_a21 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_a21 0).stores 6 [10] rfl ((trace_a21 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_a21 1).stores ((trace_a21 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_a21 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_a21 1).stores.certificate) (fuelContext (trace_a21 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_a21 2).stores ((trace_a21 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_a21 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_a21 2).stores.certificate) (fuelContext (trace_a21 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_a21 3).stores ((trace_a21 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_a21 4).stores ((trace_a21 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a21 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a21 4).stores) (applyContext (trace_a21 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_a21 5).stores ((trace_a21 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a21 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a21 5).stores) (applyContext (trace_a21 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_a21 6).stores ((trace_a21 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_a21 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_a21 6).stores) (applyContext (trace_a21 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_a21 7).stores ((trace_a21 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_a21 7).stores)
        (applyRegisterEquiv.symm ((trace_a21 7).stage.apply regs)) (applyContext (trace_a21 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_a21 8).stores ((trace_a21 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_a21 9).stores ((trace_a21 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_a21 10).stores ((trace_a21 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_a21 11).stores ((trace_a21 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a21 12).stores ((trace_a21 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_a21 13).stores ((trace_a21 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_a21 14).stores ((trace_a21 14).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_a21 15).stores ((trace_a21 15).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_a21 16).stores rfl ((trace_a21 16).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_a21 17).stores ((trace_a21 17).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a21 18).stores ((trace_a21 18).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 15] [1, 0, 15] (equalityRegisterEquiv.symm ((trace_a21 18).stage.apply regs)) (equalityContext (trace_a21 18).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a21 19).stores ((trace_a21 19).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 15] [0, 15] (equalityRegisterEquiv.symm ((trace_a21 19).stage.apply regs)) (equalityContext (trace_a21 19).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a21 20).stores ((trace_a21 20).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [15] [15] (equalityRegisterEquiv.symm ((trace_a21 20).stage.apply regs)) (equalityContext (trace_a21 20).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a21 21).stores ((trace_a21 21).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 15 [] [] (equalityRegisterEquiv.symm ((trace_a21 21).stage.apply regs)) (equalityContext (trace_a21 21).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_a21 22).stores ((trace_a21 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_a21 22).stage.apply regs)) (equalityContext (trace_a21 22).stores ctx))
  · exact equality_join_step caller .equal (trace_a21 23).stores ((trace_a21 23).stage.apply regs) ctx

theorem trace_d01_steps (n : Nat) (bound : n < 4) :
    step caller ((trace_d01 n).reached regs ctx) =
      some ((trace_d01 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_d01 0).stores rfl ((trace_d01 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_d01 1).stores ((trace_d01 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d01 2).stores ((trace_d01 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_d01 2).stage.apply regs)) (equalityContext (trace_d01 2).stores ctx))
  · exact equality_join_step caller .equal (trace_d01 3).stores ((trace_d01 3).stage.apply regs) ctx

theorem trace_d02_steps (n : Nat) (bound : n < 9) :
    step caller ((trace_d02 n).reached regs ctx) =
      some ((trace_d02 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_d02 0).stores 15 [] rfl ((trace_d02 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_d02 1).stores ((trace_d02 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_d02 1).stage.apply regs) [(), ()] (FuelDispatchMachine.stores ((trace_d02 1).stores.certificate) (fuelContext (trace_d02 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_d02 2).stores ((trace_d02 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_d02 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_d02 2).stores.certificate) (fuelContext (trace_d02 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_d02 3).stores ((trace_d02 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, false] ((trace_d02 3).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_d02 3).stores.certificate) (fuelContext (trace_d02 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_d02 4).stores ((trace_d02 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, true, false] ((trace_d02 4).stage.apply regs) (FuelDispatchMachine.stores ((trace_d02 4).stores.certificate) (fuelContext (trace_d02 4).stores ctx)))
  · exact fuel_join_step caller .positive (trace_d02 5).stores ((trace_d02 5).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_d02 6).stores ((trace_d02 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_foreign (fun _ => .halt) 15 [] [.right, .left] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d02 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d02 6).stores) (applyContext (trace_d02 6).stores ctx)) (by decide) (by decide))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_d02 7).stores ((trace_d02 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_d02 7).stores)
        (applyRegisterEquiv.symm ((trace_d02 7).stage.apply regs)) (applyContext (trace_d02 7).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_d02 8).stores ((trace_d02 8).stage.apply regs) ctx

theorem trace_d03_steps (n : Nat) (bound : n < 6) :
    step caller ((trace_d03 n).reached regs ctx) =
      some ((trace_d03 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_d03 0).stores 15 [] rfl ((trace_d03 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_d03 1).stores ((trace_d03 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((trace_d03 1).stage.apply regs) [(), ()] (FuelDispatchMachine.stores ((trace_d03 1).stores.certificate) (fuelContext (trace_d03 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_d03 2).stores ((trace_d03 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_d03 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_d03 2).stores.certificate) (fuelContext (trace_d03 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_d03 3).stores ((trace_d03 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_d03 3).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_d03 3).stores.certificate) (fuelContext (trace_d03 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_d03 4).stores ((trace_d03 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((trace_d03 4).stage.apply regs) (FuelDispatchMachine.stores ((trace_d03 4).stores.certificate) (fuelContext (trace_d03 4).stores ctx)))
  · exact fuel_join_step caller .zero (trace_d03 5).stores ((trace_d03 5).stage.apply regs) ctx

theorem trace_d04_steps (n : Nat) (bound : n < 7) :
    step caller ((trace_d04 n).reached regs ctx) =
      some ((trace_d04 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_d04 0).stores 15 [] rfl ((trace_d04 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_d04 1).stores ((trace_d04 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_d04 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_d04 1).stores.certificate) (fuelContext (trace_d04 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_d04 2).stores ((trace_d04 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_d04 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_d04 2).stores.certificate) (fuelContext (trace_d04 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_d04 3).stores ((trace_d04 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_d04 4).stores ((trace_d04 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_foreign (fun _ => .halt) 15 [] [.right, .left] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d04 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d04 4).stores) (applyContext (trace_d04 4).stores ctx)) (by decide) (by decide))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_d04 5).stores ((trace_d04 5).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_d04 5).stores)
        (applyRegisterEquiv.symm ((trace_d04 5).stage.apply regs)) (applyContext (trace_d04 5).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_d04 6).stores ((trace_d04 6).stage.apply regs) ctx

theorem trace_d05_steps (n : Nat) (bound : n < 13) :
    step caller ((trace_d05 n).reached regs ctx) =
      some ((trace_d05 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_d05 0).stores 6 [8, 15] rfl ((trace_d05 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_d05 1).stores ((trace_d05 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_d05 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_d05 1).stores.certificate) (fuelContext (trace_d05 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_d05 2).stores ((trace_d05 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_d05 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_d05 2).stores.certificate) (fuelContext (trace_d05 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_d05 3).stores ((trace_d05 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_d05 4).stores ((trace_d05 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [8, 15] [.right, .left] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d05 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d05 4).stores) (applyContext (trace_d05 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_d05 5).stores ((trace_d05 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .left [15] [.right, .left] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d05 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d05 5).stores) (applyContext (trace_d05 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_d05 6).stores ((trace_d05 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_foreign (fun _ => .halt) .left 15 [] [.left, .right, .left] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d05 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d05 6).stores) (applyContext (trace_d05 6).stores ctx)) (by decide) (by decide) (by decide))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (trace_d05 7).stores ((trace_d05 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_cons (fun _ => .halt) .left .left [15] [.right, .left] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d05 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d05 7).stores) (applyContext (trace_d05 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (trace_d05 8).stores ((trace_d05 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_cons (fun _ => .halt) .left .right [8, 15] [.left] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d05 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d05 8).stores) (applyContext (trace_d05 8).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (trace_d05 9).stores ((trace_d05 9).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_cons (fun _ => .halt) .left .left [9, 8, 15] [] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d05 9).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d05 9).stores) (applyContext (trace_d05 9).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (trace_d05 10).stores ((trace_d05 10).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_nil (fun _ => .halt) .left [8, 9, 8, 15] [.right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d05 10).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d05 10).stores) (applyContext (trace_d05 10).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_d05 11).stores ((trace_d05 11).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_d05 11).stores)
        (applyRegisterEquiv.symm ((trace_d05 11).stage.apply regs)) (applyContext (trace_d05 11).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_d05 12).stores ((trace_d05 12).stage.apply regs) ctx

theorem trace_d06_steps (n : Nat) (bound : n < 30) :
    step caller ((trace_d06 n).reached regs ctx) =
      some ((trace_d06 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_d06 0).stores 6 [10] rfl ((trace_d06 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_d06 1).stores ((trace_d06 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_d06 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_d06 1).stores.certificate) (fuelContext (trace_d06 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_d06 2).stores ((trace_d06 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_d06 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_d06 2).stores.certificate) (fuelContext (trace_d06 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_d06 3).stores ((trace_d06 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_d06 4).stores ((trace_d06 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [.left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d06 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d06 4).stores) (applyContext (trace_d06 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_d06 5).stores ((trace_d06 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [.left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d06 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d06 5).stores) (applyContext (trace_d06 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_d06 6).stores ((trace_d06 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d06 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d06 6).stores) (applyContext (trace_d06 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_d06 7).stores ((trace_d06 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d06 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d06 7).stores) (applyContext (trace_d06 7).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_d06 8).stores ((trace_d06 8).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_d06 8).stores)
        (applyRegisterEquiv.symm ((trace_d06 8).stage.apply regs)) (applyContext (trace_d06 8).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_d06 9).stores ((trace_d06 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (trace_d06 10).stores ((trace_d06 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_d06 11).stores ((trace_d06 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_d06 12).stores ((trace_d06 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_d06 13).stores ((trace_d06 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_d06 14).stores ((trace_d06 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_d06 15).stores ((trace_d06 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_d06 16).stores ((trace_d06 16).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_d06 17).stores ((trace_d06 17).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_d06 18).stores ((trace_d06 18).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_d06 19).stores rfl ((trace_d06 19).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_d06 20).stores ((trace_d06 20).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d06 21).stores ((trace_d06 21).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 1, 0, 0, 0, 0] [1, 1, 0, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_d06 21).stage.apply regs)) (equalityContext (trace_d06 21).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d06 22).stores ((trace_d06 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 0, 0, 0] [1, 0, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_d06 22).stage.apply regs)) (equalityContext (trace_d06 22).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d06 23).stores ((trace_d06 23).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0, 0, 0] [0, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_d06 23).stage.apply regs)) (equalityContext (trace_d06 23).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d06 24).stores ((trace_d06 24).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0, 0] [0, 0, 0] (equalityRegisterEquiv.symm ((trace_d06 24).stage.apply regs)) (equalityContext (trace_d06 24).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d06 25).stores ((trace_d06 25).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((trace_d06 25).stage.apply regs)) (equalityContext (trace_d06 25).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d06 26).stores ((trace_d06 26).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((trace_d06 26).stage.apply regs)) (equalityContext (trace_d06 26).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d06 27).stores ((trace_d06 27).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_d06 27).stage.apply regs)) (equalityContext (trace_d06 27).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d06 28).stores ((trace_d06 28).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_d06 28).stage.apply regs)) (equalityContext (trace_d06 28).stores ctx))
  · exact equality_join_step caller .equal (trace_d06 29).stores ((trace_d06 29).stage.apply regs) ctx

theorem trace_d07_steps (n : Nat) (bound : n < 29) :
    step caller ((trace_d07 n).reached regs ctx) =
      some ((trace_d07 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_d07 0).stores 6 [10] rfl ((trace_d07 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_d07 1).stores ((trace_d07 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_d07 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_d07 1).stores.certificate) (fuelContext (trace_d07 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_d07 2).stores ((trace_d07 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_d07 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_d07 2).stores.certificate) (fuelContext (trace_d07 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_d07 3).stores ((trace_d07 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_d07 4).stores ((trace_d07 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d07 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d07 4).stores) (applyContext (trace_d07 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_d07 5).stores ((trace_d07 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d07 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d07 5).stores) (applyContext (trace_d07 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_d07 6).stores ((trace_d07 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d07 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d07 6).stores) (applyContext (trace_d07 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_d07 7).stores ((trace_d07 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_d07 7).stores)
        (applyRegisterEquiv.symm ((trace_d07 7).stage.apply regs)) (applyContext (trace_d07 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_d07 8).stores ((trace_d07 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (trace_d07 9).stores ((trace_d07 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_d07 10).stores ((trace_d07 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_d07 11).stores ((trace_d07 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_d07 12).stores ((trace_d07 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_d07 13).stores ((trace_d07 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_d07 14).stores ((trace_d07 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_d07 15).stores ((trace_d07 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_d07 16).stores ((trace_d07 16).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_d07 17).stores ((trace_d07 17).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_d07 18).stores rfl ((trace_d07 18).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_d07 19).stores ((trace_d07 19).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d07 20).stores ((trace_d07 20).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 1, 0, 0, 0, 0] [1, 1, 0, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_d07 20).stage.apply regs)) (equalityContext (trace_d07 20).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d07 21).stores ((trace_d07 21).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 0, 0, 0] [1, 0, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_d07 21).stage.apply regs)) (equalityContext (trace_d07 21).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d07 22).stores ((trace_d07 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0, 0, 0] [0, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_d07 22).stage.apply regs)) (equalityContext (trace_d07 22).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d07 23).stores ((trace_d07 23).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0, 0] [0, 0, 0] (equalityRegisterEquiv.symm ((trace_d07 23).stage.apply regs)) (equalityContext (trace_d07 23).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d07 24).stores ((trace_d07 24).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((trace_d07 24).stage.apply regs)) (equalityContext (trace_d07 24).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d07 25).stores ((trace_d07 25).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((trace_d07 25).stage.apply regs)) (equalityContext (trace_d07 25).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d07 26).stores ((trace_d07 26).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_d07 26).stage.apply regs)) (equalityContext (trace_d07 26).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d07 27).stores ((trace_d07 27).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_d07 27).stage.apply regs)) (equalityContext (trace_d07 27).stores ctx))
  · exact equality_join_step caller .equal (trace_d07 28).stores ((trace_d07 28).stage.apply regs) ctx

theorem trace_d08_steps (n : Nat) (bound : n < 7) :
    step caller ((trace_d08 n).reached regs ctx) =
      some ((trace_d08 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_d08 0).stores ((trace_d08 0).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_d08 1).stores ((trace_d08 1).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_d08 2).stores rfl ((trace_d08 2).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_d08 3).stores ((trace_d08 3).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d08 4).stores ((trace_d08 4).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_d08 4).stage.apply regs)) (equalityContext (trace_d08 4).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d08 5).stores ((trace_d08 5).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_d08 5).stage.apply regs)) (equalityContext (trace_d08 5).stores ctx))
  · exact equality_join_step caller .equal (trace_d08 6).stores ((trace_d08 6).stage.apply regs) ctx

theorem trace_d09_steps (n : Nat) (bound : n < 5) :
    step caller ((trace_d09 n).reached regs ctx) =
      some ((trace_d09 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact apply_join_step caller MoveApplyMachine.success (trace_d09 0).stores ((trace_d09 0).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_d09 1).stores rfl ((trace_d09 1).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_d09 2).stores ((trace_d09 2).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d09 3).stores ((trace_d09 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_d09 3).stage.apply regs)) (equalityContext (trace_d09 3).stores ctx))
  · exact equality_join_step caller .equal (trace_d09 4).stores ((trace_d09 4).stage.apply regs) ctx

theorem trace_d10_steps (n : Nat) (bound : n < 4) :
    step caller ((trace_d10 n).reached regs ctx) =
      some ((trace_d10 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact fuel_join_step caller .positive (trace_d10 0).stores ((trace_d10 0).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_d10 1).stores ((trace_d10 1).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_nil (fun _ => .halt) [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_d10 1).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_d10 1).stores) (applyContext (trace_d10 1).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_d10 2).stores ((trace_d10 2).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_d10 2).stores)
        (applyRegisterEquiv.symm ((trace_d10 2).stage.apply regs)) (applyContext (trace_d10 2).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_d10 3).stores ((trace_d10 3).stage.apply regs) ctx

theorem trace_d11_steps (n : Nat) (bound : n < 3) :
    step caller ((trace_d11 n).reached regs ctx) =
      some ((trace_d11 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact fuel_join_step caller .atEnd (trace_d11 0).stores ((trace_d11 0).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d11 1).stores ((trace_d11 1).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_d11 1).stage.apply regs)) (equalityContext (trace_d11 1).stores ctx))
  · exact equality_join_step caller .equal (trace_d11 2).stores ((trace_d11 2).stage.apply regs) ctx

theorem trace_d12_steps (n : Nat) (bound : n < 2) :
    step caller ((trace_d12 n).reached regs ctx) =
      some ((trace_d12 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact equality_step_of_step caller (fun _ => .halt) (trace_d12 0).stores ((trace_d12 0).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_d12 0).stage.apply regs)) (equalityContext (trace_d12 0).stores ctx))
  · exact equality_join_step caller .equal (trace_d12 1).stores ((trace_d12 1).stage.apply regs) ctx

theorem trace_d13_steps (n : Nat) (bound : n < 1) :
    step caller ((trace_d13 n).reached regs ctx) =
      some ((trace_d13 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact equality_join_step caller .equal (trace_d13 0).stores ((trace_d13 0).stage.apply regs) ctx

theorem trace_r01_steps (n : Nat) (bound : n < 7) :
    step caller ((trace_r01 n).reached regs ctx) =
      some ((trace_r01 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r01 0).stores ((trace_r01 0).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_r01 0).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_r01 0).stores.certificate) (fuelContext (trace_r01 0).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r01 1).stores ((trace_r01 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((trace_r01 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r01 1).stores.certificate) (fuelContext (trace_r01 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r01 2).stores ((trace_r01 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, true] ((trace_r01 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_r01 2).stores.certificate) (fuelContext (trace_r01 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_r01 3).stores ((trace_r01 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_r01 4).stores ((trace_r01 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_foreign (fun _ => .halt) 15 [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r01 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r01 4).stores) (applyContext (trace_r01 4).stores ctx)) (by decide) (by decide))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_r01 5).stores ((trace_r01 5).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_r01 5).stores)
        (applyRegisterEquiv.symm ((trace_r01 5).stage.apply regs)) (applyContext (trace_r01 5).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_r01 6).stores ((trace_r01 6).stage.apply regs) ctx

theorem trace_r02_steps (n : Nat) (bound : n < 4) :
    step caller ((trace_r02 n).reached regs ctx) =
      some ((trace_r02 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_r02 0).stores ((trace_r02 0).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((trace_r02 0).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_r02 0).stores.certificate) (fuelContext (trace_r02 0).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_r02 1).stores ((trace_r02 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, true] ((trace_r02 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r02 1).stores.certificate) (fuelContext (trace_r02 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_r02 2).stores ((trace_r02 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false, true] ((trace_r02 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_r02 2).stores.certificate) (fuelContext (trace_r02 2).stores ctx)))
  · exact fuel_join_step caller .zero (trace_r02 3).stores ((trace_r02 3).stage.apply regs) ctx

theorem trace_r03_steps (n : Nat) (bound : n < 17) :
    step caller ((trace_r03 n).reached regs ctx) =
      some ((trace_r03 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_r03 0).stores ((trace_r03 0).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .left [15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r03 0).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r03 0).stores) (applyContext (trace_r03 0).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_r03 1).stores ((trace_r03 1).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [15] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r03 1).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r03 1).stores) (applyContext (trace_r03 1).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_r03 2).stores ((trace_r03 2).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_r03 2).stores)
        (applyRegisterEquiv.symm ((trace_r03 2).stage.apply regs)) (applyContext (trace_r03 2).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_r03 3).stores ((trace_r03 3).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (trace_r03 4).stores ((trace_r03 4).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_r03 5).stores ((trace_r03 5).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_r03 6).stores ((trace_r03 6).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_r03 7).stores ((trace_r03 7).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_r03 8).stores ((trace_r03 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_r03 9).stores ((trace_r03 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_r03 10).stores ((trace_r03 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_r03 11).stores ((trace_r03 11).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_r03 12).stores ((trace_r03 12).stage.apply regs) ctx
  · exact inspect_step_cons caller (trace_r03 13).stores 15 [] rfl ((trace_r03 13).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r03 14).stores ((trace_r03 14).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((trace_r03 14).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r03 14).stores.certificate) (fuelContext (trace_r03 14).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_r03 15).stores ((trace_r03 15).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_r03 15).stage.apply regs) (FuelDispatchMachine.stores ((trace_r03 15).stores.certificate) (fuelContext (trace_r03 15).stores ctx)))
  · exact fuel_join_step caller .zero (trace_r03 16).stores ((trace_r03 16).stage.apply regs) ctx

theorem trace_r04_steps (n : Nat) (bound : n < 27) :
    step caller ((trace_r04 n).reached regs ctx) =
      some ((trace_r04 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r04 0).stores ((trace_r04 0).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((trace_r04 0).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_r04 0).stores.certificate) (fuelContext (trace_r04 0).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r04 1).stores ((trace_r04 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_r04 1).stage.apply regs) [(), ()] (FuelDispatchMachine.stores ((trace_r04 1).stores.certificate) (fuelContext (trace_r04 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r04 2).stores ((trace_r04 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_r04 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_r04 2).stores.certificate) (fuelContext (trace_r04 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r04 3).stores ((trace_r04 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, false] ((trace_r04 3).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r04 3).stores.certificate) (fuelContext (trace_r04 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r04 4).stores ((trace_r04 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, true, false] ((trace_r04 4).stage.apply regs) (FuelDispatchMachine.stores ((trace_r04 4).stores.certificate) (fuelContext (trace_r04 4).stores ctx)))
  · exact fuel_join_step caller .positive (trace_r04 5).stores ((trace_r04 5).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_r04 6).stores ((trace_r04 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r04 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r04 6).stores) (applyContext (trace_r04 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_r04 7).stores ((trace_r04 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r04 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r04 7).stores) (applyContext (trace_r04 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_r04 8).stores ((trace_r04 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r04 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r04 8).stores) (applyContext (trace_r04 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_r04 9).stores ((trace_r04 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_r04 9).stores)
        (applyRegisterEquiv.symm ((trace_r04 9).stage.apply regs)) (applyContext (trace_r04 9).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_r04 10).stores ((trace_r04 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_r04 11).stores ((trace_r04 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_r04 12).stores ((trace_r04 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_r04 13).stores ((trace_r04 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_r04 14).stores ((trace_r04 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_r04 15).stores ((trace_r04 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_r04 16).stores ((trace_r04 16).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_r04 17).stores ((trace_r04 17).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_r04 18).stores rfl ((trace_r04 18).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_r04 19).stores ((trace_r04 19).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r04 20).stores ((trace_r04 20).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 0, 0] [1, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_r04 20).stage.apply regs)) (equalityContext (trace_r04 20).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r04 21).stores ((trace_r04 21).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0, 0] [0, 0, 0] (equalityRegisterEquiv.symm ((trace_r04 21).stage.apply regs)) (equalityContext (trace_r04 21).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r04 22).stores ((trace_r04 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((trace_r04 22).stage.apply regs)) (equalityContext (trace_r04 22).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r04 23).stores ((trace_r04 23).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((trace_r04 23).stage.apply regs)) (equalityContext (trace_r04 23).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r04 24).stores ((trace_r04 24).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_r04 24).stage.apply regs)) (equalityContext (trace_r04 24).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r04 25).stores ((trace_r04 25).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_r04 25).stage.apply regs)) (equalityContext (trace_r04 25).stores ctx))
  · exact equality_join_step caller .equal (trace_r04 26).stores ((trace_r04 26).stage.apply regs) ctx

theorem trace_r05_steps (n : Nat) (bound : n < 6) :
    step caller ((trace_r05 n).reached regs ctx) =
      some ((trace_r05 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_r05 0).stores rfl ((trace_r05 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_r05 1).stores ((trace_r05 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r05 2).stores ((trace_r05 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0] [0, 15, 2] (equalityRegisterEquiv.symm ((trace_r05 2).stage.apply regs)) (equalityContext (trace_r05 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r05 3).stores ((trace_r05 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [15, 2] (equalityRegisterEquiv.symm ((trace_r05 3).stage.apply regs)) (equalityContext (trace_r05 3).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r05 4).stores ((trace_r05 4).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_cons (fun _ => .halt) 15 [2] (equalityRegisterEquiv.symm ((trace_r05 4).stage.apply regs)) (equalityContext (trace_r05 4).stores ctx))
  · exact equality_join_step caller .different (trace_r05 5).stores ((trace_r05 5).stage.apply regs) ctx

theorem trace_r06_steps (n : Nat) (bound : n < 6) :
    step caller ((trace_r06 n).reached regs ctx) =
      some ((trace_r06 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_r06 0).stores rfl ((trace_r06 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_r06 1).stores ((trace_r06 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r06 2).stores ((trace_r06 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 15, 2] [0] (equalityRegisterEquiv.symm ((trace_r06 2).stage.apply regs)) (equalityContext (trace_r06 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r06 3).stores ((trace_r06 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [15, 2] [] (equalityRegisterEquiv.symm ((trace_r06 3).stage.apply regs)) (equalityContext (trace_r06 3).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_r06 4).stores ((trace_r06 4).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_cons_nil (fun _ => .halt) 15 [2] (equalityRegisterEquiv.symm ((trace_r06 4).stage.apply regs)) (equalityContext (trace_r06 4).stores ctx))
  · exact equality_join_step caller .different (trace_r06 5).stores ((trace_r06 5).stage.apply regs) ctx

theorem trace_r07_steps (n : Nat) (bound : n < 22) :
    step caller ((trace_r07 n).reached regs ctx) =
      some ((trace_r07 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_r07 0).stores 6 [10, 15] rfl ((trace_r07 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r07 1).stores ((trace_r07 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_r07 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r07 1).stores.certificate) (fuelContext (trace_r07 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r07 2).stores ((trace_r07 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_r07 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_r07 2).stores.certificate) (fuelContext (trace_r07 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_r07 3).stores ((trace_r07 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_r07 4).stores ((trace_r07 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r07 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r07 4).stores) (applyContext (trace_r07 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_r07 5).stores ((trace_r07 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r07 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r07 5).stores) (applyContext (trace_r07 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_r07 6).stores ((trace_r07 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [15] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r07 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r07 6).stores) (applyContext (trace_r07 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_r07 7).stores ((trace_r07 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_r07 7).stores)
        (applyRegisterEquiv.symm ((trace_r07 7).stage.apply regs)) (applyContext (trace_r07 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_r07 8).stores ((trace_r07 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_r07 9).stores ((trace_r07 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_r07 10).stores ((trace_r07 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_r07 11).stores ((trace_r07 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_r07 12).stores ((trace_r07 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_r07 13).stores ((trace_r07 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_r07 14).stores ((trace_r07 14).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_r07 15).stores ((trace_r07 15).stage.apply regs) ctx
  · exact inspect_step_cons caller (trace_r07 16).stores 15 [] rfl ((trace_r07 16).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r07 17).stores ((trace_r07 17).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_r07 17).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r07 17).stores.certificate) (fuelContext (trace_r07 17).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r07 18).stores ((trace_r07 18).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((trace_r07 18).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_r07 18).stores.certificate) (fuelContext (trace_r07 18).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_r07 19).stores ((trace_r07 19).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_r07 19).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r07 19).stores.certificate) (fuelContext (trace_r07 19).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_r07 20).stores ((trace_r07 20).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_r07 20).stage.apply regs) (FuelDispatchMachine.stores ((trace_r07 20).stores.certificate) (fuelContext (trace_r07 20).stores ctx)))
  · exact fuel_join_step caller .zero (trace_r07 21).stores ((trace_r07 21).stage.apply regs) ctx

theorem trace_r08_steps (n : Nat) (bound : n < 41) :
    step caller ((trace_r08 n).reached regs ctx) =
      some ((trace_r08 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_r08 0).stores 6 [10, 7, 10, 15] rfl ((trace_r08 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r08 1).stores ((trace_r08 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((trace_r08 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r08 1).stores.certificate) (fuelContext (trace_r08 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r08 2).stores ((trace_r08 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_r08 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_r08 2).stores.certificate) (fuelContext (trace_r08 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r08 3).stores ((trace_r08 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_r08 3).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r08 3).stores.certificate) (fuelContext (trace_r08 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r08 4).stores ((trace_r08 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, false] ((trace_r08 4).stage.apply regs) (FuelDispatchMachine.stores ((trace_r08 4).stores.certificate) (fuelContext (trace_r08 4).stores ctx)))
  · exact fuel_join_step caller .positive (trace_r08 5).stores ((trace_r08 5).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_r08 6).stores ((trace_r08 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10, 7, 10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r08 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r08 6).stores) (applyContext (trace_r08 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_r08 7).stores ((trace_r08 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [7, 10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r08 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r08 7).stores) (applyContext (trace_r08 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_r08 8).stores ((trace_r08 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [7, 10, 15] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r08 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r08 8).stores) (applyContext (trace_r08 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_r08 9).stores ((trace_r08 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_r08 9).stores)
        (applyRegisterEquiv.symm ((trace_r08 9).stage.apply regs)) (applyContext (trace_r08 9).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_r08 10).stores ((trace_r08 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_r08 11).stores ((trace_r08 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_r08 12).stores ((trace_r08 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_r08 13).stores ((trace_r08 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_r08 14).stores ((trace_r08 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_r08 15).stores ((trace_r08 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_r08 16).stores ((trace_r08 16).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_r08 17).stores ((trace_r08 17).stage.apply regs) ctx
  · exact inspect_step_cons caller (trace_r08 18).stores 7 [10, 15] rfl ((trace_r08 18).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r08 19).stores ((trace_r08 19).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_r08 19).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r08 19).stores.certificate) (fuelContext (trace_r08 19).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r08 20).stores ((trace_r08 20).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((trace_r08 20).stage.apply regs) (FuelDispatchMachine.stores ((trace_r08 20).stores.certificate) (fuelContext (trace_r08 20).stores ctx)))
  · exact fuel_join_step caller .positive (trace_r08 21).stores ((trace_r08 21).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_r08 22).stores ((trace_r08 22).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .right [10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r08 22).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r08 22).stores) (applyContext (trace_r08 22).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .right) (trace_r08 23).stores ((trace_r08 23).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .right [15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r08 23).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r08 23).stores) (applyContext (trace_r08 23).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .right) (trace_r08 24).stores ((trace_r08 24).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .right [15] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r08 24).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r08 24).stores) (applyContext (trace_r08 24).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .right)) (trace_r08 25).stores ((trace_r08 25).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .right) (applyData (trace_r08 25).stores)
        (applyRegisterEquiv.symm ((trace_r08 25).stage.apply regs)) (applyContext (trace_r08 25).stores ctx))
  · exact apply_position_advance_step caller (.seek .right) (trace_r08 26).stores ((trace_r08 26).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .right) (trace_r08 27).stores ((trace_r08 27).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .right) (trace_r08 28).stores ((trace_r08 28).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (trace_r08 29).stores ((trace_r08 29).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (trace_r08 30).stores ((trace_r08 30).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_r08 31).stores ((trace_r08 31).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_r08 32).stores ((trace_r08 32).stage.apply regs) ctx
  · exact inspect_step_cons caller (trace_r08 33).stores 15 [] rfl ((trace_r08 33).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r08 34).stores ((trace_r08 34).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_r08 34).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r08 34).stores.certificate) (fuelContext (trace_r08 34).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r08 35).stores ((trace_r08 35).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_r08 35).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_r08 35).stores.certificate) (fuelContext (trace_r08 35).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r08 36).stores ((trace_r08 36).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((trace_r08 36).stage.apply regs) [(), ()] (FuelDispatchMachine.stores ((trace_r08 36).stores.certificate) (fuelContext (trace_r08 36).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_r08 37).stores ((trace_r08 37).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_r08 37).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_r08 37).stores.certificate) (fuelContext (trace_r08 37).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_r08 38).stores ((trace_r08 38).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_r08 38).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r08 38).stores.certificate) (fuelContext (trace_r08 38).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_r08 39).stores ((trace_r08 39).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((trace_r08 39).stage.apply regs) (FuelDispatchMachine.stores ((trace_r08 39).stores.certificate) (fuelContext (trace_r08 39).stores ctx)))
  · exact fuel_join_step caller .zero (trace_r08 40).stores ((trace_r08 40).stage.apply regs) ctx

theorem trace_r09_steps (n : Nat) (bound : n < 40) :
    step caller ((trace_r09 n).reached regs ctx) =
      some ((trace_r09 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_r09 0).stores 6 [10, 7, 10, 15] rfl ((trace_r09 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r09 1).stores ((trace_r09 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((trace_r09 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r09 1).stores.certificate) (fuelContext (trace_r09 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r09 2).stores ((trace_r09 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, true] ((trace_r09 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_r09 2).stores.certificate) (fuelContext (trace_r09 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_r09 3).stores ((trace_r09 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_r09 4).stores ((trace_r09 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10, 7, 10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r09 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r09 4).stores) (applyContext (trace_r09 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_r09 5).stores ((trace_r09 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [7, 10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r09 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r09 5).stores) (applyContext (trace_r09 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_r09 6).stores ((trace_r09 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [7, 10, 15] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r09 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r09 6).stores) (applyContext (trace_r09 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_r09 7).stores ((trace_r09 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_r09 7).stores)
        (applyRegisterEquiv.symm ((trace_r09 7).stage.apply regs)) (applyContext (trace_r09 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_r09 8).stores ((trace_r09 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_r09 9).stores ((trace_r09 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_r09 10).stores ((trace_r09 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_r09 11).stores ((trace_r09 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_r09 12).stores ((trace_r09 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_r09 13).stores ((trace_r09 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_r09 14).stores ((trace_r09 14).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_r09 15).stores ((trace_r09 15).stage.apply regs) ctx
  · exact inspect_step_cons caller (trace_r09 16).stores 7 [10, 15] rfl ((trace_r09 16).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r09 17).stores ((trace_r09 17).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] ((trace_r09 17).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r09 17).stores.certificate) (fuelContext (trace_r09 17).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r09 18).stores ((trace_r09 18).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_r09 18).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_r09 18).stores.certificate) (fuelContext (trace_r09 18).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r09 19).stores ((trace_r09 19).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_r09 19).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r09 19).stores.certificate) (fuelContext (trace_r09 19).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r09 20).stores ((trace_r09 20).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true, false] ((trace_r09 20).stage.apply regs) (FuelDispatchMachine.stores ((trace_r09 20).stores.certificate) (fuelContext (trace_r09 20).stores ctx)))
  · exact fuel_join_step caller .positive (trace_r09 21).stores ((trace_r09 21).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_r09 22).stores ((trace_r09 22).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .right [10, 15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r09 22).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r09 22).stores) (applyContext (trace_r09 22).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .right) (trace_r09 23).stores ((trace_r09 23).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .right [15] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r09 23).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r09 23).stores) (applyContext (trace_r09 23).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .right) (trace_r09 24).stores ((trace_r09 24).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .right [15] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r09 24).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r09 24).stores) (applyContext (trace_r09 24).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .right)) (trace_r09 25).stores ((trace_r09 25).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .right) (applyData (trace_r09 25).stores)
        (applyRegisterEquiv.symm ((trace_r09 25).stage.apply regs)) (applyContext (trace_r09 25).stores ctx))
  · exact apply_position_advance_step caller (.seek .right) (trace_r09 26).stores ((trace_r09 26).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .right) (trace_r09 27).stores ((trace_r09 27).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .right) (trace_r09 28).stores ((trace_r09 28).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (trace_r09 29).stores ((trace_r09 29).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successRight) (trace_r09 30).stores ((trace_r09 30).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_r09 31).stores ((trace_r09 31).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_r09 32).stores ((trace_r09 32).stage.apply regs) ctx
  · exact inspect_step_cons caller (trace_r09 33).stores 15 [] rfl ((trace_r09 33).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r09 34).stores ((trace_r09 34).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_r09 34).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r09 34).stores.certificate) (fuelContext (trace_r09 34).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r09 35).stores ((trace_r09 35).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((trace_r09 35).stage.apply regs) (FuelDispatchMachine.stores ((trace_r09 35).stores.certificate) (fuelContext (trace_r09 35).stores ctx)))
  · exact fuel_join_step caller .positive (trace_r09 36).stores ((trace_r09 36).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_r09 37).stores ((trace_r09 37).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_foreign (fun _ => .halt) 15 [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r09 37).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r09 37).stores) (applyContext (trace_r09 37).stores ctx)) (by decide) (by decide))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_r09 38).stores ((trace_r09 38).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_r09 38).stores)
        (applyRegisterEquiv.symm ((trace_r09 38).stage.apply regs)) (applyContext (trace_r09 38).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_r09 39).stores ((trace_r09 39).stage.apply regs) ctx

theorem trace_r10_steps (n : Nat) (bound : n < 20) :
    step caller ((trace_r10 n).reached regs ctx) =
      some ((trace_r10 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_r10 0).stores 6 [10] rfl ((trace_r10 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_r10 1).stores ((trace_r10 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_r10 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_r10 1).stores.certificate) (fuelContext (trace_r10 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_r10 2).stores ((trace_r10 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_r10 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_r10 2).stores.certificate) (fuelContext (trace_r10 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_r10 3).stores ((trace_r10 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_r10 4).stores ((trace_r10 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [.right] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r10 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r10 4).stores) (applyContext (trace_r10 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_r10 5).stores ((trace_r10 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [.right] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r10 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r10 5).stores) (applyContext (trace_r10 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_r10 6).stores ((trace_r10 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .right [] [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r10 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r10 6).stores) (applyContext (trace_r10 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_r10 7).stores ((trace_r10 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.right, .left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_r10 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_r10 7).stores) (applyContext (trace_r10 7).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_r10 8).stores ((trace_r10 8).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_r10 8).stores)
        (applyRegisterEquiv.symm ((trace_r10 8).stage.apply regs)) (applyContext (trace_r10 8).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_r10 9).stores ((trace_r10 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanPrefix .left) (trace_r10 10).stores ((trace_r10 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (trace_r10 11).stores ((trace_r10 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (trace_r10 12).stores ((trace_r10 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_r10 13).stores ((trace_r10 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller .dropPending (trace_r10 14).stores ((trace_r10 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (trace_r10 15).stores ((trace_r10 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (trace_r10 16).stores ((trace_r10 16).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (trace_r10 17).stores ((trace_r10 17).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (trace_r10 18).stores ((trace_r10 18).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.rotationFailure (trace_r10 19).stores ((trace_r10 19).stage.apply regs) ctx

end LiteralTraceEdges

theorem trace_a01_owned (n : Nat) (bound : n < 4) :
    (trace_a01 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a01_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (trace_a01 n).stores ≤ 0 := by
  interval_cases n <;> decide

theorem trace_a02_owned (n : Nat) (bound : n < 4) :
    (trace_a02 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a02_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (trace_a02 n).stores ≤ 1 := by
  interval_cases n <;> decide

theorem trace_a03_owned (n : Nat) (bound : n < 5) :
    (trace_a03 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a03_cells (n : Nat) (bound : n ≤ 5) :
    fixtureCells (trace_a03 n).stores ≤ 2 := by
  interval_cases n <;> decide

theorem trace_a04_owned (n : Nat) (bound : n < 7) :
    (trace_a04 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a04_cells (n : Nat) (bound : n ≤ 7) :
    fixtureCells (trace_a04 n).stores ≤ 7 := by
  interval_cases n <;> decide

theorem trace_a05_owned (n : Nat) (bound : n < 9) :
    (trace_a05 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a05_cells (n : Nat) (bound : n ≤ 9) :
    fixtureCells (trace_a05 n).stores ≤ 12 := by
  interval_cases n <;> decide

theorem trace_a06_owned (n : Nat) (bound : n < 4) :
    (trace_a06 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a06_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (trace_a06 n).stores ≤ 4 := by
  interval_cases n <;> decide

theorem trace_a07_owned (n : Nat) (bound : n < 5) :
    (trace_a07 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a07_cells (n : Nat) (bound : n ≤ 5) :
    fixtureCells (trace_a07 n).stores ≤ 3 := by
  interval_cases n <;> decide

theorem trace_a08_owned (n : Nat) (bound : n < 6) :
    (trace_a08 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a08_cells (n : Nat) (bound : n ≤ 6) :
    fixtureCells (trace_a08 n).stores ≤ 8 := by
  interval_cases n <;> decide

theorem trace_a09_owned (n : Nat) (bound : n < 8) :
    (trace_a09 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a09_cells (n : Nat) (bound : n ≤ 8) :
    fixtureCells (trace_a09 n).stores ≤ 14 := by
  interval_cases n <;> decide

theorem trace_a10_owned (n : Nat) (bound : n < 7) :
    (trace_a10 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a10_cells (n : Nat) (bound : n ≤ 7) :
    fixtureCells (trace_a10 n).stores ≤ 12 := by
  interval_cases n <;> decide

theorem trace_a11_owned (n : Nat) (bound : n < 11) :
    (trace_a11 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a11_cells (n : Nat) (bound : n ≤ 11) :
    fixtureCells (trace_a11 n).stores ≤ 14 := by
  interval_cases n <;> decide

theorem trace_a12_owned (n : Nat) (bound : n < 25) :
    (trace_a12 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a12_cells (n : Nat) (bound : n ≤ 25) :
    fixtureCells (trace_a12 n).stores ≤ 13 := by
  interval_cases n <;> decide

theorem trace_a13_owned (n : Nat) (bound : n < 24) :
    (trace_a13 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a13_cells (n : Nat) (bound : n ≤ 24) :
    fixtureCells (trace_a13 n).stores ≤ 13 := by
  interval_cases n <;> decide

theorem trace_a14_owned (n : Nat) (bound : n < 13) :
    (trace_a14 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a14_cells (n : Nat) (bound : n ≤ 13) :
    fixtureCells (trace_a14 n).stores ≤ 5 := by
  interval_cases n <;> decide

theorem trace_a15_owned (n : Nat) (bound : n < 16) :
    (trace_a15 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a15_cells (n : Nat) (bound : n ≤ 16) :
    fixtureCells (trace_a15 n).stores ≤ 7 := by
  interval_cases n <;> decide

theorem trace_a16_owned (n : Nat) (bound : n < 31) :
    (trace_a16 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a16_cells (n : Nat) (bound : n ≤ 31) :
    fixtureCells (trace_a16 n).stores ≤ 18 := by
  interval_cases n <;> decide

theorem trace_a17_owned (n : Nat) (bound : n < 33) :
    (trace_a17 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a17_cells (n : Nat) (bound : n ≤ 33) :
    fixtureCells (trace_a17 n).stores ≤ 18 := by
  interval_cases n <;> decide

theorem trace_a18_owned (n : Nat) (bound : n < 42) :
    (trace_a18 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a18_cells (n : Nat) (bound : n ≤ 42) :
    fixtureCells (trace_a18 n).stores ≤ 16 := by
  interval_cases n <;> decide

theorem trace_a19_owned (n : Nat) (bound : n < 22) :
    (trace_a19 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a19_cells (n : Nat) (bound : n ≤ 22) :
    fixtureCells (trace_a19 n).stores ≤ 15 := by
  interval_cases n <;> decide

theorem trace_a20_owned (n : Nat) (bound : n < 25) :
    (trace_a20 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a20_cells (n : Nat) (bound : n ≤ 25) :
    fixtureCells (trace_a20 n).stores ≤ 15 := by
  interval_cases n <;> decide

theorem trace_a21_owned (n : Nat) (bound : n < 24) :
    (trace_a21 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_a21_cells (n : Nat) (bound : n ≤ 24) :
    fixtureCells (trace_a21 n).stores ≤ 11 := by
  interval_cases n <;> decide

theorem trace_d01_owned (n : Nat) (bound : n < 4) :
    (trace_d01 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d01_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (trace_d01 n).stores ≤ 8 := by
  interval_cases n <;> decide

theorem trace_d02_owned (n : Nat) (bound : n < 9) :
    (trace_d02 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d02_cells (n : Nat) (bound : n ≤ 9) :
    fixtureCells (trace_d02 n).stores ≤ 11 := by
  interval_cases n <;> decide

theorem trace_d03_owned (n : Nat) (bound : n < 6) :
    (trace_d03 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d03_cells (n : Nat) (bound : n ≤ 6) :
    fixtureCells (trace_d03 n).stores ≤ 3 := by
  interval_cases n <;> decide

theorem trace_d04_owned (n : Nat) (bound : n < 7) :
    (trace_d04 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d04_cells (n : Nat) (bound : n ≤ 7) :
    fixtureCells (trace_d04 n).stores ≤ 9 := by
  interval_cases n <;> decide

theorem trace_d05_owned (n : Nat) (bound : n < 13) :
    (trace_d05 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d05_cells (n : Nat) (bound : n ≤ 13) :
    fixtureCells (trace_d05 n).stores ≤ 11 := by
  interval_cases n <;> decide

theorem trace_d06_owned (n : Nat) (bound : n < 30) :
    (trace_d06 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d06_cells (n : Nat) (bound : n ≤ 30) :
    fixtureCells (trace_d06 n).stores ≤ 18 := by
  interval_cases n <;> decide

theorem trace_d07_owned (n : Nat) (bound : n < 29) :
    (trace_d07 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d07_cells (n : Nat) (bound : n ≤ 29) :
    fixtureCells (trace_d07 n).stores ≤ 18 := by
  interval_cases n <;> decide

theorem trace_d08_owned (n : Nat) (bound : n < 7) :
    (trace_d08 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d08_cells (n : Nat) (bound : n ≤ 7) :
    fixtureCells (trace_d08 n).stores ≤ 6 := by
  interval_cases n <;> decide

theorem trace_d09_owned (n : Nat) (bound : n < 5) :
    (trace_d09 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d09_cells (n : Nat) (bound : n ≤ 5) :
    fixtureCells (trace_d09 n).stores ≤ 0 := by
  interval_cases n <;> decide

theorem trace_d10_owned (n : Nat) (bound : n < 4) :
    (trace_d10 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d10_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (trace_d10 n).stores ≤ 0 := by
  interval_cases n <;> decide

theorem trace_d11_owned (n : Nat) (bound : n < 3) :
    (trace_d11 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d11_cells (n : Nat) (bound : n ≤ 3) :
    fixtureCells (trace_d11 n).stores ≤ 1 := by
  interval_cases n <;> decide

theorem trace_d12_owned (n : Nat) (bound : n < 2) :
    (trace_d12 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d12_cells (n : Nat) (bound : n ≤ 2) :
    fixtureCells (trace_d12 n).stores ≤ 1 := by
  interval_cases n <;> decide

theorem trace_d13_owned (n : Nat) (bound : n < 1) :
    (trace_d13 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_d13_cells (n : Nat) (bound : n ≤ 1) :
    fixtureCells (trace_d13 n).stores ≤ 3 := by
  interval_cases n <;> decide

theorem trace_r01_owned (n : Nat) (bound : n < 7) :
    (trace_r01 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_r01_cells (n : Nat) (bound : n ≤ 7) :
    fixtureCells (trace_r01 n).stores ≤ 13 := by
  interval_cases n <;> decide

theorem trace_r02_owned (n : Nat) (bound : n < 4) :
    (trace_r02 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_r02_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (trace_r02 n).stores ≤ 15 := by
  interval_cases n <;> decide

theorem trace_r03_owned (n : Nat) (bound : n < 17) :
    (trace_r03 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_r03_cells (n : Nat) (bound : n ≤ 17) :
    fixtureCells (trace_r03 n).stores ≤ 16 := by
  interval_cases n <;> decide

theorem trace_r04_owned (n : Nat) (bound : n < 27) :
    (trace_r04 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_r04_cells (n : Nat) (bound : n ≤ 27) :
    fixtureCells (trace_r04 n).stores ≤ 15 := by
  interval_cases n <;> decide

theorem trace_r05_owned (n : Nat) (bound : n < 6) :
    (trace_r05 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_r05_cells (n : Nat) (bound : n ≤ 6) :
    fixtureCells (trace_r05 n).stores ≤ 7 := by
  interval_cases n <;> decide

theorem trace_r06_owned (n : Nat) (bound : n < 6) :
    (trace_r06 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_r06_cells (n : Nat) (bound : n ≤ 6) :
    fixtureCells (trace_r06 n).stores ≤ 7 := by
  interval_cases n <;> decide

theorem trace_r07_owned (n : Nat) (bound : n < 22) :
    (trace_r07 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_r07_cells (n : Nat) (bound : n ≤ 22) :
    fixtureCells (trace_r07 n).stores ≤ 14 := by
  interval_cases n <;> decide

theorem trace_r08_owned (n : Nat) (bound : n < 41) :
    (trace_r08 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_r08_cells (n : Nat) (bound : n ≤ 41) :
    fixtureCells (trace_r08 n).stores ≤ 17 := by
  interval_cases n <;> decide

theorem trace_r09_owned (n : Nat) (bound : n < 40) :
    (trace_r09 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_r09_cells (n : Nat) (bound : n ≤ 40) :
    fixtureCells (trace_r09 n).stores ≤ 17 := by
  interval_cases n <;> decide

theorem trace_r10_owned (n : Nat) (bound : n < 20) :
    (trace_r10 n).control.isLeft = true := by
  interval_cases n
  all_goals rfl

theorem trace_r10_cells (n : Nat) (bound : n ≤ 20) :
    fixtureCells (trace_r10 n).stores ≤ 15 := by
  interval_cases n <;> decide


theorem trace_point_with_phase_control_is_owned
    {K Λ R : Type} {Γ : K → Type} (p : TracePoint)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (phase : p.control.isLeft = true) : Owned (p.reached (Λ := Λ) regs ctx).l := by
  change Owned (some (boundaryLabel p.control))
  cases label : p.control with
  | inl q => exact owned_phase q
  | inr b => simp only [label, Sum.isLeft, Bool.false_eq_true] at phase

section TraceFirstConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem literal_trace_is_an_actual_first_run (c : RunFixture) (points : Nat → TracePoint)
    (first : (points 0).reached (Λ := Λ) regs ctx = c.start regs ctx)
    (last : (points c.ticks).reached (Λ := Λ) regs ctx = c.finish regs ctx)
    (adjacent : ∀ n, n < c.ticks →
      step caller ((points n).reached regs ctx) = some ((points (n + 1)).reached regs ctx))
    (owned : ∀ n, n < c.ticks → (points n).control.isLeft = true) :
    c.RunExpected (step caller) regs ctx := by
  refine ⟨?_, not_owned_result c.result, ?_⟩
  · simpa only [first, last] using
      finite_trace_actual_prefix caller regs ctx points c.ticks adjacent c.ticks (Nat.le_refl _)
  · intro n strict
    refine ⟨(points n).reached regs ctx, ?_, trace_point_with_phase_control_is_owned
      (points n) regs ctx (owned n strict)⟩
    simpa only [first] using
      finite_trace_actual_prefix caller regs ctx points c.ticks adjacent n (Nat.le_of_lt strict)

theorem literal_evaluation_follows_from_its_actual_first_run (c : RunFixture)
    (first : c.RunExpected (step caller) regs ctx) :
    evaluate c.phase c.before = ⟨c.result, c.after, c.ticks⟩ := by
  obtain ⟨clock, endpoint⟩ := first_return_unique caller c.phase c.before regs ctx
    c.ticks (c.finish regs ctx) first.1 first.2.1 first.2.2
  rcases actual : evaluate c.phase c.before with ⟨b, D, n⟩
  have exactClock : c.ticks = n := by simpa only [phaseSteps, actual] using clock
  have exactEndpoint : c.finish (Λ := Λ) regs ctx =
      cfg (some (resultLabel b)) (resetAll regs) D ctx := by
    simpa only [phaseResult, evaluationCfg, actual] using endpoint
  have exactWords : c.after = D := by
    simpa only [RunFixture.finish, dataOfCfg_cfg] using congrArg dataOfCfg exactEndpoint
  have exactResult : c.result = b := by
    have labels := congrArg Turing.TM2.Cfg.l exactEndpoint
    change some (resultLabel (Λ := Λ) c.result) = some (resultLabel b) at labels
    simpa only [resultLabel, Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq] using labels
  rw [← exactClock, ← exactWords, ← exactResult]

end TraceFirstConnections

theorem a01_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a01.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a01 trace_a01 rfl rfl
    (trace_a01_steps caller regs ctx) trace_a01_owned

theorem a01_literal_evaluation :
    evaluate a01.phase a01.before = ⟨a01.result, a01.after, a01.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a01
    (a01_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a01_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a01.start regs ctx) a01.ticks
      (a01.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_a01
    4 0 (trace_a01_steps caller regs ctx) trace_a01_cells rfl

theorem a02_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a02.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a02 trace_a02 rfl rfl
    (trace_a02_steps caller regs ctx) trace_a02_owned

theorem a02_literal_evaluation :
    evaluate a02.phase a02.before = ⟨a02.result, a02.after, a02.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a02
    (a02_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a02_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a02.start regs ctx) a02.ticks
      (a02.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_a02
    4 1 (trace_a02_steps caller regs ctx) trace_a02_cells rfl

theorem a03_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a03.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a03 trace_a03 rfl rfl
    (trace_a03_steps caller regs ctx) trace_a03_owned

theorem a03_literal_evaluation :
    evaluate a03.phase a03.before = ⟨a03.result, a03.after, a03.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a03
    (a03_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a03_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a03.start regs ctx) a03.ticks
      (a03.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_a03
    5 2 (trace_a03_steps caller regs ctx) trace_a03_cells rfl

theorem a04_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a04.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a04 trace_a04 rfl rfl
    (trace_a04_steps caller regs ctx) trace_a04_owned

theorem a04_literal_evaluation :
    evaluate a04.phase a04.before = ⟨a04.result, a04.after, a04.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a04
    (a04_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a04_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a04.start regs ctx) a04.ticks
      (a04.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_a04
    7 7 (trace_a04_steps caller regs ctx) trace_a04_cells rfl

theorem a05_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a05.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a05 trace_a05 rfl rfl
    (trace_a05_steps caller regs ctx) trace_a05_owned

theorem a05_literal_evaluation :
    evaluate a05.phase a05.before = ⟨a05.result, a05.after, a05.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a05
    (a05_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a05_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a05.start regs ctx) a05.ticks
      (a05.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_a05
    9 12 (trace_a05_steps caller regs ctx) trace_a05_cells rfl

theorem a06_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a06.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a06 trace_a06 rfl rfl
    (trace_a06_steps caller regs ctx) trace_a06_owned

theorem a06_literal_evaluation :
    evaluate a06.phase a06.before = ⟨a06.result, a06.after, a06.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a06
    (a06_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a06_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a06.start regs ctx) a06.ticks
      (a06.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_a06
    4 4 (trace_a06_steps caller regs ctx) trace_a06_cells rfl

theorem a07_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a07.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a07 trace_a07 rfl rfl
    (trace_a07_steps caller regs ctx) trace_a07_owned

theorem a07_literal_evaluation :
    evaluate a07.phase a07.before = ⟨a07.result, a07.after, a07.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a07
    (a07_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a07_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a07.start regs ctx) a07.ticks
      (a07.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_a07
    5 3 (trace_a07_steps caller regs ctx) trace_a07_cells rfl

theorem a08_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a08.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a08 trace_a08 rfl rfl
    (trace_a08_steps caller regs ctx) trace_a08_owned

theorem a08_literal_evaluation :
    evaluate a08.phase a08.before = ⟨a08.result, a08.after, a08.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a08
    (a08_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a08_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a08.start regs ctx) a08.ticks
      (a08.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_a08
    6 8 (trace_a08_steps caller regs ctx) trace_a08_cells rfl

theorem a09_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a09.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a09 trace_a09 rfl rfl
    (trace_a09_steps caller regs ctx) trace_a09_owned

theorem a09_literal_evaluation :
    evaluate a09.phase a09.before = ⟨a09.result, a09.after, a09.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a09
    (a09_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a09_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a09.start regs ctx) a09.ticks
      (a09.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_a09
    8 14 (trace_a09_steps caller regs ctx) trace_a09_cells rfl

theorem a10_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a10.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a10 trace_a10 rfl rfl
    (trace_a10_steps caller regs ctx) trace_a10_owned

theorem a10_literal_evaluation :
    evaluate a10.phase a10.before = ⟨a10.result, a10.after, a10.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a10
    (a10_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a10_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a10.start regs ctx) a10.ticks
      (a10.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_a10
    7 12 (trace_a10_steps caller regs ctx) trace_a10_cells rfl

theorem a11_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a11.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a11 trace_a11 rfl rfl
    (trace_a11_steps caller regs ctx) trace_a11_owned

theorem a11_literal_evaluation :
    evaluate a11.phase a11.before = ⟨a11.result, a11.after, a11.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a11
    (a11_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a11_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a11.start regs ctx) a11.ticks
      (a11.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_a11
    11 14 (trace_a11_steps caller regs ctx) trace_a11_cells rfl

theorem a12_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a12.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a12 trace_a12 rfl rfl
    (trace_a12_steps caller regs ctx) trace_a12_owned

theorem a12_literal_evaluation :
    evaluate a12.phase a12.before = ⟨a12.result, a12.after, a12.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a12
    (a12_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a12_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a12.start regs ctx) a12.ticks
      (a12.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_a12
    25 13 (trace_a12_steps caller regs ctx) trace_a12_cells rfl

theorem a13_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a13.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a13 trace_a13 rfl rfl
    (trace_a13_steps caller regs ctx) trace_a13_owned

theorem a13_literal_evaluation :
    evaluate a13.phase a13.before = ⟨a13.result, a13.after, a13.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a13
    (a13_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a13_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a13.start regs ctx) a13.ticks
      (a13.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_a13
    24 13 (trace_a13_steps caller regs ctx) trace_a13_cells rfl

theorem a14_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a14.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a14 trace_a14 rfl rfl
    (trace_a14_steps caller regs ctx) trace_a14_owned

theorem a14_literal_evaluation :
    evaluate a14.phase a14.before = ⟨a14.result, a14.after, a14.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a14
    (a14_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a14_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a14.start regs ctx) a14.ticks
      (a14.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_a14
    13 5 (trace_a14_steps caller regs ctx) trace_a14_cells rfl

theorem a15_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a15.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a15 trace_a15 rfl rfl
    (trace_a15_steps caller regs ctx) trace_a15_owned

theorem a15_literal_evaluation :
    evaluate a15.phase a15.before = ⟨a15.result, a15.after, a15.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a15
    (a15_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a15_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a15.start regs ctx) a15.ticks
      (a15.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_a15
    16 7 (trace_a15_steps caller regs ctx) trace_a15_cells rfl

theorem a16_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a16.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a16 trace_a16 rfl rfl
    (trace_a16_steps caller regs ctx) trace_a16_owned

theorem a16_literal_evaluation :
    evaluate a16.phase a16.before = ⟨a16.result, a16.after, a16.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a16
    (a16_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a16_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a16.start regs ctx) a16.ticks
      (a16.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_a16
    31 18 (trace_a16_steps caller regs ctx) trace_a16_cells rfl

theorem a17_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a17.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a17 trace_a17 rfl rfl
    (trace_a17_steps caller regs ctx) trace_a17_owned

theorem a17_literal_evaluation :
    evaluate a17.phase a17.before = ⟨a17.result, a17.after, a17.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a17
    (a17_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a17_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a17.start regs ctx) a17.ticks
      (a17.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_a17
    33 18 (trace_a17_steps caller regs ctx) trace_a17_cells rfl

theorem a18_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a18.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a18 trace_a18 rfl rfl
    (trace_a18_steps caller regs ctx) trace_a18_owned

theorem a18_literal_evaluation :
    evaluate a18.phase a18.before = ⟨a18.result, a18.after, a18.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a18
    (a18_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a18_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a18.start regs ctx) a18.ticks
      (a18.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_a18
    42 16 (trace_a18_steps caller regs ctx) trace_a18_cells rfl

theorem a19_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a19.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a19 trace_a19 rfl rfl
    (trace_a19_steps caller regs ctx) trace_a19_owned

theorem a19_literal_evaluation :
    evaluate a19.phase a19.before = ⟨a19.result, a19.after, a19.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a19
    (a19_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a19_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a19.start regs ctx) a19.ticks
      (a19.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_a19
    22 15 (trace_a19_steps caller regs ctx) trace_a19_cells rfl

theorem a20_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a20.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a20 trace_a20 rfl rfl
    (trace_a20_steps caller regs ctx) trace_a20_owned

theorem a20_literal_evaluation :
    evaluate a20.phase a20.before = ⟨a20.result, a20.after, a20.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a20
    (a20_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a20_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a20.start regs ctx) a20.ticks
      (a20.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_a20
    25 15 (trace_a20_steps caller regs ctx) trace_a20_cells rfl

theorem a21_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : a21.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx a21 trace_a21 rfl rfl
    (trace_a21_steps caller regs ctx) trace_a21_owned

theorem a21_literal_evaluation :
    evaluate a21.phase a21.before = ⟨a21.result, a21.after, a21.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext a21
    (a21_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem a21_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (a21.start regs ctx) a21.ticks
      (a21.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_a21
    24 11 (trace_a21_steps caller regs ctx) trace_a21_cells rfl

theorem d01_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d01.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d01 trace_d01 rfl rfl
    (trace_d01_steps caller regs ctx) trace_d01_owned

theorem d01_literal_evaluation :
    evaluate d01.phase d01.before = ⟨d01.result, d01.after, d01.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d01
    (d01_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d01_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d01.start regs ctx) d01.ticks
      (d01.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_d01
    4 8 (trace_d01_steps caller regs ctx) trace_d01_cells rfl

theorem d02_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d02.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d02 trace_d02 rfl rfl
    (trace_d02_steps caller regs ctx) trace_d02_owned

theorem d02_literal_evaluation :
    evaluate d02.phase d02.before = ⟨d02.result, d02.after, d02.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d02
    (d02_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d02_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d02.start regs ctx) d02.ticks
      (d02.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_d02
    9 11 (trace_d02_steps caller regs ctx) trace_d02_cells rfl

theorem d03_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d03.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d03 trace_d03 rfl rfl
    (trace_d03_steps caller regs ctx) trace_d03_owned

theorem d03_literal_evaluation :
    evaluate d03.phase d03.before = ⟨d03.result, d03.after, d03.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d03
    (d03_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d03_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d03.start regs ctx) d03.ticks
      (d03.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_d03
    6 3 (trace_d03_steps caller regs ctx) trace_d03_cells rfl

theorem d04_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d04.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d04 trace_d04 rfl rfl
    (trace_d04_steps caller regs ctx) trace_d04_owned

theorem d04_literal_evaluation :
    evaluate d04.phase d04.before = ⟨d04.result, d04.after, d04.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d04
    (d04_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d04_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d04.start regs ctx) d04.ticks
      (d04.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_d04
    7 9 (trace_d04_steps caller regs ctx) trace_d04_cells rfl

theorem d05_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d05.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d05 trace_d05 rfl rfl
    (trace_d05_steps caller regs ctx) trace_d05_owned

theorem d05_literal_evaluation :
    evaluate d05.phase d05.before = ⟨d05.result, d05.after, d05.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d05
    (d05_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d05_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d05.start regs ctx) d05.ticks
      (d05.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_d05
    13 11 (trace_d05_steps caller regs ctx) trace_d05_cells rfl

theorem d06_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d06.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d06 trace_d06 rfl rfl
    (trace_d06_steps caller regs ctx) trace_d06_owned

theorem d06_literal_evaluation :
    evaluate d06.phase d06.before = ⟨d06.result, d06.after, d06.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d06
    (d06_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d06_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d06.start regs ctx) d06.ticks
      (d06.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_d06
    30 18 (trace_d06_steps caller regs ctx) trace_d06_cells rfl

theorem d07_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d07.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d07 trace_d07 rfl rfl
    (trace_d07_steps caller regs ctx) trace_d07_owned

theorem d07_literal_evaluation :
    evaluate d07.phase d07.before = ⟨d07.result, d07.after, d07.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d07
    (d07_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d07_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d07.start regs ctx) d07.ticks
      (d07.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_d07
    29 18 (trace_d07_steps caller regs ctx) trace_d07_cells rfl

theorem d08_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d08.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d08 trace_d08 rfl rfl
    (trace_d08_steps caller regs ctx) trace_d08_owned

theorem d08_literal_evaluation :
    evaluate d08.phase d08.before = ⟨d08.result, d08.after, d08.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d08
    (d08_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d08_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d08.start regs ctx) d08.ticks
      (d08.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_d08
    7 6 (trace_d08_steps caller regs ctx) trace_d08_cells rfl

theorem d09_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d09.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d09 trace_d09 rfl rfl
    (trace_d09_steps caller regs ctx) trace_d09_owned

theorem d09_literal_evaluation :
    evaluate d09.phase d09.before = ⟨d09.result, d09.after, d09.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d09
    (d09_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d09_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d09.start regs ctx) d09.ticks
      (d09.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_d09
    5 0 (trace_d09_steps caller regs ctx) trace_d09_cells rfl

theorem d10_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d10.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d10 trace_d10 rfl rfl
    (trace_d10_steps caller regs ctx) trace_d10_owned

theorem d10_literal_evaluation :
    evaluate d10.phase d10.before = ⟨d10.result, d10.after, d10.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d10
    (d10_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d10_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d10.start regs ctx) d10.ticks
      (d10.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_d10
    4 0 (trace_d10_steps caller regs ctx) trace_d10_cells rfl

theorem d11_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d11.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d11 trace_d11 rfl rfl
    (trace_d11_steps caller regs ctx) trace_d11_owned

theorem d11_literal_evaluation :
    evaluate d11.phase d11.before = ⟨d11.result, d11.after, d11.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d11
    (d11_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d11_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d11.start regs ctx) d11.ticks
      (d11.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_d11
    3 1 (trace_d11_steps caller regs ctx) trace_d11_cells rfl

theorem d12_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d12.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d12 trace_d12 rfl rfl
    (trace_d12_steps caller regs ctx) trace_d12_owned

theorem d12_literal_evaluation :
    evaluate d12.phase d12.before = ⟨d12.result, d12.after, d12.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d12
    (d12_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d12_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d12.start regs ctx) d12.ticks
      (d12.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_d12
    2 1 (trace_d12_steps caller regs ctx) trace_d12_cells rfl

theorem d13_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : d13.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx d13 trace_d13 rfl rfl
    (trace_d13_steps caller regs ctx) trace_d13_owned

theorem d13_literal_evaluation :
    evaluate d13.phase d13.before = ⟨d13.result, d13.after, d13.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext d13
    (d13_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem d13_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (d13.start regs ctx) d13.ticks
      (d13.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_d13
    1 3 (trace_d13_steps caller regs ctx) trace_d13_cells rfl

theorem r01_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : r01.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx r01 trace_r01 rfl rfl
    (trace_r01_steps caller regs ctx) trace_r01_owned

theorem r01_literal_evaluation :
    evaluate r01.phase r01.before = ⟨r01.result, r01.after, r01.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext r01
    (r01_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem r01_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (r01.start regs ctx) r01.ticks
      (r01.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_r01
    7 13 (trace_r01_steps caller regs ctx) trace_r01_cells rfl

theorem r02_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : r02.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx r02 trace_r02 rfl rfl
    (trace_r02_steps caller regs ctx) trace_r02_owned

theorem r02_literal_evaluation :
    evaluate r02.phase r02.before = ⟨r02.result, r02.after, r02.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext r02
    (r02_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem r02_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (r02.start regs ctx) r02.ticks
      (r02.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_r02
    4 15 (trace_r02_steps caller regs ctx) trace_r02_cells rfl

theorem r03_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : r03.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx r03 trace_r03 rfl rfl
    (trace_r03_steps caller regs ctx) trace_r03_owned

theorem r03_literal_evaluation :
    evaluate r03.phase r03.before = ⟨r03.result, r03.after, r03.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext r03
    (r03_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem r03_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (r03.start regs ctx) r03.ticks
      (r03.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_r03
    17 16 (trace_r03_steps caller regs ctx) trace_r03_cells rfl

theorem r04_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : r04.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx r04 trace_r04 rfl rfl
    (trace_r04_steps caller regs ctx) trace_r04_owned

theorem r04_literal_evaluation :
    evaluate r04.phase r04.before = ⟨r04.result, r04.after, r04.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext r04
    (r04_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem r04_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (r04.start regs ctx) r04.ticks
      (r04.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_r04
    27 15 (trace_r04_steps caller regs ctx) trace_r04_cells rfl

theorem r05_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : r05.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx r05 trace_r05 rfl rfl
    (trace_r05_steps caller regs ctx) trace_r05_owned

theorem r05_literal_evaluation :
    evaluate r05.phase r05.before = ⟨r05.result, r05.after, r05.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext r05
    (r05_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem r05_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (r05.start regs ctx) r05.ticks
      (r05.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_r05
    6 7 (trace_r05_steps caller regs ctx) trace_r05_cells rfl

theorem r06_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : r06.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx r06 trace_r06 rfl rfl
    (trace_r06_steps caller regs ctx) trace_r06_owned

theorem r06_literal_evaluation :
    evaluate r06.phase r06.before = ⟨r06.result, r06.after, r06.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext r06
    (r06_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem r06_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (r06.start regs ctx) r06.ticks
      (r06.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_r06
    6 7 (trace_r06_steps caller regs ctx) trace_r06_cells rfl

theorem r07_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : r07.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx r07 trace_r07 rfl rfl
    (trace_r07_steps caller regs ctx) trace_r07_owned

theorem r07_literal_evaluation :
    evaluate r07.phase r07.before = ⟨r07.result, r07.after, r07.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext r07
    (r07_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem r07_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (r07.start regs ctx) r07.ticks
      (r07.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_r07
    22 14 (trace_r07_steps caller regs ctx) trace_r07_cells rfl

theorem r08_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : r08.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx r08 trace_r08 rfl rfl
    (trace_r08_steps caller regs ctx) trace_r08_owned

theorem r08_literal_evaluation :
    evaluate r08.phase r08.before = ⟨r08.result, r08.after, r08.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext r08
    (r08_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem r08_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (r08.start regs ctx) r08.ticks
      (r08.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_r08
    41 17 (trace_r08_steps caller regs ctx) trace_r08_cells rfl

theorem r09_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : r09.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx r09 trace_r09 rfl rfl
    (trace_r09_steps caller regs ctx) trace_r09_owned

theorem r09_literal_evaluation :
    evaluate r09.phase r09.before = ⟨r09.result, r09.after, r09.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext r09
    (r09_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem r09_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (r09.start regs ctx) r09.ticks
      (r09.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_r09
    40 17 (trace_r09_steps caller regs ctx) trace_r09_cells rfl

theorem r10_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : r10.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx r10 trace_r10 rfl rfl
    (trace_r10_steps caller regs ctx) trace_r10_owned

theorem r10_literal_evaluation :
    evaluate r10.phase r10.before = ⟨r10.result, r10.after, r10.ticks⟩ :=
  literal_evaluation_follows_from_its_actual_first_run
    (fun _ : External Unit => .halt) (stale true) ordinaryContext r10
    (r10_actual_first_run (fun _ => .halt) (stale true) ordinaryContext)

theorem r10_actual_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (r10.start regs ctx) r10.ticks
      (r10.peak + externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_r10
    20 15 (trace_r10_steps caller regs ctx) trace_r10_cells rfl

theorem every_fixed_literal_evaluation_is_exact :
    ∀ c ∈ allCases, evaluate c.phase c.before = ⟨c.result, c.after, c.ticks⟩ := by
  intro c member
  simp only [allCases, initialCases, postReadCases, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact a01_literal_evaluation
  · exact a02_literal_evaluation
  · exact a03_literal_evaluation
  · exact a04_literal_evaluation
  · exact a05_literal_evaluation
  · exact a06_literal_evaluation
  · exact a07_literal_evaluation
  · exact a08_literal_evaluation
  · exact a09_literal_evaluation
  · exact a10_literal_evaluation
  · exact a11_literal_evaluation
  · exact a12_literal_evaluation
  · exact a13_literal_evaluation
  · exact a14_literal_evaluation
  · exact a15_literal_evaluation
  · exact a16_literal_evaluation
  · exact a17_literal_evaluation
  · exact a18_literal_evaluation
  · exact a19_literal_evaluation
  · exact a20_literal_evaluation
  · exact a21_literal_evaluation
  · exact d01_literal_evaluation
  · exact d02_literal_evaluation
  · exact d03_literal_evaluation
  · exact d04_literal_evaluation
  · exact d05_literal_evaluation
  · exact d06_literal_evaluation
  · exact d07_literal_evaluation
  · exact d08_literal_evaluation
  · exact d09_literal_evaluation
  · exact d10_literal_evaluation
  · exact d11_literal_evaluation
  · exact d12_literal_evaluation
  · exact d13_literal_evaluation
  · exact r01_literal_evaluation
  · exact r02_literal_evaluation
  · exact r03_literal_evaluation
  · exact r04_literal_evaluation
  · exact r05_literal_evaluation
  · exact r06_literal_evaluation
  · exact r07_literal_evaluation
  · exact r08_literal_evaluation
  · exact r09_literal_evaluation
  · exact r10_literal_evaluation

theorem every_original_and_post_read_fixture_is_an_actual_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ∀ c ∈ allCases, c.RunExpected (step caller) regs ctx := by
  intro c member
  simp only [allCases, initialCases, postReadCases, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact a01_actual_first_run caller regs ctx
  · exact a02_actual_first_run caller regs ctx
  · exact a03_actual_first_run caller regs ctx
  · exact a04_actual_first_run caller regs ctx
  · exact a05_actual_first_run caller regs ctx
  · exact a06_actual_first_run caller regs ctx
  · exact a07_actual_first_run caller regs ctx
  · exact a08_actual_first_run caller regs ctx
  · exact a09_actual_first_run caller regs ctx
  · exact a10_actual_first_run caller regs ctx
  · exact a11_actual_first_run caller regs ctx
  · exact a12_actual_first_run caller regs ctx
  · exact a13_actual_first_run caller regs ctx
  · exact a14_actual_first_run caller regs ctx
  · exact a15_actual_first_run caller regs ctx
  · exact a16_actual_first_run caller regs ctx
  · exact a17_actual_first_run caller regs ctx
  · exact a18_actual_first_run caller regs ctx
  · exact a19_actual_first_run caller regs ctx
  · exact a20_actual_first_run caller regs ctx
  · exact a21_actual_first_run caller regs ctx
  · exact d01_actual_first_run caller regs ctx
  · exact d02_actual_first_run caller regs ctx
  · exact d03_actual_first_run caller regs ctx
  · exact d04_actual_first_run caller regs ctx
  · exact d05_actual_first_run caller regs ctx
  · exact d06_actual_first_run caller regs ctx
  · exact d07_actual_first_run caller regs ctx
  · exact d08_actual_first_run caller regs ctx
  · exact d09_actual_first_run caller regs ctx
  · exact d10_actual_first_run caller regs ctx
  · exact d11_actual_first_run caller regs ctx
  · exact d12_actual_first_run caller regs ctx
  · exact d13_actual_first_run caller regs ctx
  · exact r01_actual_first_run caller regs ctx
  · exact r02_actual_first_run caller regs ctx
  · exact r03_actual_first_run caller regs ctx
  · exact r04_actual_first_run caller regs ctx
  · exact r05_actual_first_run caller regs ctx
  · exact r06_actual_first_run caller regs ctx
  · exact r07_actual_first_run caller regs ctx
  · exact r08_actual_first_run caller regs ctx
  · exact r09_actual_first_run caller regs ctx
  · exact r10_actual_first_run caller regs ctx

theorem every_fixed_original_and_post_read_run_has_its_exact_inclusive_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ∀ c ∈ allCases, c.Expected (step caller) regs ctx := by
  intro c member
  refine ⟨every_original_and_post_read_fixture_is_an_actual_first_run caller regs ctx c member, ?_⟩
  simp only [allCases, initialCases, postReadCases, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact a01_actual_exact_peak caller regs ctx
  · exact a02_actual_exact_peak caller regs ctx
  · exact a03_actual_exact_peak caller regs ctx
  · exact a04_actual_exact_peak caller regs ctx
  · exact a05_actual_exact_peak caller regs ctx
  · exact a06_actual_exact_peak caller regs ctx
  · exact a07_actual_exact_peak caller regs ctx
  · exact a08_actual_exact_peak caller regs ctx
  · exact a09_actual_exact_peak caller regs ctx
  · exact a10_actual_exact_peak caller regs ctx
  · exact a11_actual_exact_peak caller regs ctx
  · exact a12_actual_exact_peak caller regs ctx
  · exact a13_actual_exact_peak caller regs ctx
  · exact a14_actual_exact_peak caller regs ctx
  · exact a15_actual_exact_peak caller regs ctx
  · exact a16_actual_exact_peak caller regs ctx
  · exact a17_actual_exact_peak caller regs ctx
  · exact a18_actual_exact_peak caller regs ctx
  · exact a19_actual_exact_peak caller regs ctx
  · exact a20_actual_exact_peak caller regs ctx
  · exact a21_actual_exact_peak caller regs ctx
  · exact d01_actual_exact_peak caller regs ctx
  · exact d02_actual_exact_peak caller regs ctx
  · exact d03_actual_exact_peak caller regs ctx
  · exact d04_actual_exact_peak caller regs ctx
  · exact d05_actual_exact_peak caller regs ctx
  · exact d06_actual_exact_peak caller regs ctx
  · exact d07_actual_exact_peak caller regs ctx
  · exact d08_actual_exact_peak caller regs ctx
  · exact d09_actual_exact_peak caller regs ctx
  · exact d10_actual_exact_peak caller regs ctx
  · exact d11_actual_exact_peak caller regs ctx
  · exact d12_actual_exact_peak caller regs ctx
  · exact d13_actual_exact_peak caller regs ctx
  · exact r01_actual_exact_peak caller regs ctx
  · exact r02_actual_exact_peak caller regs ctx
  · exact r03_actual_exact_peak caller regs ctx
  · exact r04_actual_exact_peak caller regs ctx
  · exact r05_actual_exact_peak caller regs ctx
  · exact r06_actual_exact_peak caller regs ctx
  · exact r07_actual_exact_peak caller regs ctx
  · exact r08_actual_exact_peak caller regs ctx
  · exact r09_actual_exact_peak caller regs ctx
  · exact r10_actual_exact_peak caller regs ctx

/-! ## Selected partial resets preserve every other register component -/

theorem all_eleven_component_steps_keep_the_independently_fixed_reset_stages
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ∀ c ∈ resetCases, c.Expected (step caller) regs ctx := by
  intro c member
  simp only [resetCases, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact inspect_step_nil caller ({} : LocalData) rfl regs ctx
  · exact inspect_step_cons caller ({certificate := [15]} : LocalData) 15 [] rfl regs ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow ({fuel := [false, true]} : LocalData) regs ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] regs [] (FuelDispatchMachine.stores (({fuel := [false, true]} : LocalData).certificate) (fuelContext ({fuel := [false, true]} : LocalData) ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow ({fuel := [true]} : LocalData) regs ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] regs [] (FuelDispatchMachine.stores (({fuel := [true]} : LocalData).certificate) (fuelContext ({fuel := [true]} : LocalData) ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue ({units := [()]} : LocalData) regs ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] regs [] (FuelDispatchMachine.stores (({units := [()]} : LocalData).certificate) (fuelContext ({units := [()]} : LocalData) ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse ({} : LocalData) regs ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] regs (FuelDispatchMachine.stores (({} : LocalData).certificate) (fuelContext ({} : LocalData) ctx)))
  · exact equality_step_of_step caller (fun _ => .halt) ({source := [15], target := [15]} : LocalData) regs ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 15 [] [] (equalityRegisterEquiv.symm regs) (equalityContext ({source := [15], target := [15]} : LocalData) ctx))
  · exact equality_step_of_step caller (fun _ => .halt) ({source := [1], target := [0]} : LocalData) regs ctx _ _ _ _
      (TreeEqualityMachine.compare_step_different (fun _ => .halt) 1 0 [] [] (equalityRegisterEquiv.symm regs) (equalityContext ({source := [1], target := [0]} : LocalData) ctx) (by decide))
  · exact apply_move_step_of_step caller (fun _ => .halt) .start ({certificate := [6, 10]} : LocalData) regs ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm regs)) (MoveApplyMachine.moveContext (applyData ({certificate := [6, 10]} : LocalData)) (applyContext ({certificate := [6, 10]} : LocalData) ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) ({} : LocalData) regs ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData ({} : LocalData))
        (applyRegisterEquiv.symm regs) (applyContext ({} : LocalData) ctx))
  · exact apply_position_advance_step caller (.seek .left) ({source := [1, 0], path := [.left]} : LocalData) regs ctx

/-! ## The nineteen literal source observations and the same actual executions -/

theorem all_nineteen_literal_source_observations_are_exact :
    ∀ c ∈ sourceCases, c.SourceExpected := by
  intro c member
  simp only [sourceCases, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [SourceFixture.SourceExpected,
    a03, a04, a05, a06, a09, a10, a11, a12, a13, a14, a15,
    a16, a17, a18, a19, a20, r07, r08, r09, data,
    nilTree, oneTree, rightTwo, leftTwo, rightAtLeft, leftAtLeft, rightAtRight, leftAtRight,
    treeCode, nodeTag, emptyTag, checkStreamRun_nil, checkStreamRun_cons,
    Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
    applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
    rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
    Resources.bind, Resources.CallCount.tick]

theorem every_source_fixture_is_one_of_the_fixed_actual_run_fixtures :
    ∀ c ∈ sourceCases, c.run ∈ allCases := by
  intro c member
  simp only [sourceCases, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [allCases, initialCases, postReadCases]

theorem every_represented_literal_keeps_source_cost_separate_from_machine_time
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ∀ c ∈ sourceCases, c.SourceExpected ∧ c.run.RunExpected (step caller) regs ctx := by
  intro c member
  exact ⟨all_nineteen_literal_source_observations_are_exact c member,
    every_original_and_post_read_fixture_is_an_actual_first_run caller regs ctx c.run
      (every_source_fixture_is_one_of_the_fixed_actual_run_fixtures c member)⟩

/-! ## Complete selected boundaries, exact remaining rank and physical cells -/

def Boundary.Expected {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (b : Boundary) (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (start : Cfg Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  b.RunExpected transition start regs ctx ∧
  remainingSteps (b.reached (Λ := Λ) regs ctx) = b.remaining ∧
  physicalCells (b.reached (Λ := Λ) regs ctx) = b.cells + externalCells ctx ∧
  (b.reached (Λ := Λ) regs ctx).var = b.stage.apply regs ∧
  ∀ k, (b.reached (Λ := Λ) regs ctx).stk (.inr k) = ctx k

section LiteralBoundaryConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem boundary_expected_of_actual_trace (c : RunFixture) (points : Nat → TracePoint)
    (literal : evaluate c.phase c.before = ⟨c.result, c.after, c.ticks⟩)
    (first : (points 0).reached (Λ := Λ) regs ctx = c.start regs ctx)
    (adjacent : ∀ n, n < c.ticks →
      step caller ((points n).reached regs ctx) = some ((points (n + 1)).reached regs ctx))
    (b : Boundary) (bound : b.tick ≤ c.ticks)
    (state : (points b.tick).reached (Λ := Λ) regs ctx = b.reached regs ctx)
    (count : fixtureCells b.stores = b.cells)
    (rank : b.remaining = c.ticks - b.tick) :
    b.Expected (step caller) (c.start regs ctx) regs ctx := by
  have executed : Runs (step caller) (c.start regs ctx) b.tick (b.reached regs ctx) := by
    simpa only [first, state] using
      finite_trace_actual_prefix caller regs ctx points c.ticks adjacent b.tick bound
  have initialRank : remainingSteps (c.start (Λ := Λ) regs ctx) = c.ticks := by
    rw [RunFixture.start, remainingSteps_phase_cfg]
    change (evaluate c.phase c.before).steps = c.ticks
    rw [literal]
  obtain ⟨reached, actual, remaining, _, _⟩ := owned_prefix caller (c.start regs ctx)
    b.tick (by rwa [initialRank])
  have same : reached = b.reached regs ctx := Option.some.inj (actual.symm.trans executed)
  subst reached
  refine ⟨executed, ?_, ?_, rfl, fun _ => rfl⟩
  · simpa only [initialRank, rank] using remaining
  · rw [Boundary.reached, actual_physical_cells_of_complete_cfg, count]

theorem all_thirteen_root_left_literal_boundaries_have_their_actual_rank_and_cells :
    ∀ b ∈ rootLeftBoundaries, b.Expected (step caller) (a12.start regs ctx) regs ctx := by
  intro b member
  apply boundary_expected_of_actual_trace caller regs ctx a12 trace_a12
    a12_literal_evaluation rfl (trace_a12_steps caller regs ctx) b
  all_goals
    simp only [rootLeftBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | decide

theorem all_five_dirty_branch_boundaries_have_their_actual_rank_and_cells :
    ∀ b ∈ frontEndDirtyBoundaries, b.Expected (step caller) (r10.start regs ctx) regs ctx := by
  intro b member
  apply boundary_expected_of_actual_trace caller regs ctx r10 trace_r10
    r10_literal_evaluation rfl (trace_r10_steps caller regs ctx) b
  all_goals
    simp only [frontEndDirtyBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | decide

end LiteralBoundaryConnections

theorem every_fixed_run_uses_the_actual_finite_register_carrier_and_five_protected_cells
    (caller : ExampleCaller) (regs : Registers Bool) :
    ∀ c ∈ allCases, c.RunExpected (step caller) regs ordinaryContext ∧
      ExactPeak (step caller) (c.start regs ordinaryContext) c.ticks (c.peak + 5) := by
  intro c member
  have actual := every_fixed_original_and_post_read_run_has_its_exact_inclusive_peak
    caller regs ordinaryContext c member
  simpa only [RunFixture.Expected, ordinary_protected_context_has_five_physical_cells] using actual

theorem the_same_finite_physical_examples_allow_infinitely_many_caller_labels
    (caller : External Nat → Statement IndependentAlphabet Nat Bool)
    (regs : Registers Bool) :
    Fintype.card (OwnedLabel Nat) = 39 ∧
      ∀ c ∈ allCases, c.Expected (step caller) regs ordinaryContext :=
  ⟨card_ownedLabel, every_fixed_original_and_post_read_run_has_its_exact_inclusive_peak
    caller regs ordinaryContext⟩

/-! ## Caller continuations are later activations, outside the first result -/

def certificateReentryCaller : ExampleCaller
  | .inl true => .push (.inl .certificate) (fun _ => 15)
      (.goto (fun _ => phaseLabel inspectPhase))
  | _ => .halt

def protectedReentryCaller : ExampleCaller
  | .inl true => .push (.inr 0) (fun _ => true)
      (.goto (fun _ => phaseLabel inspectPhase))
  | _ => .halt

def enlargedContext : ∀ k, List (IndependentAlphabet k) :=
  independentWords [true, true, false, true] [11, 15]

theorem a_later_certificate_push_changes_the_result_only_after_the_first_true
    (flag : Bool) :
    FirstRun (step certificateReentryCaller) (a01.start (stale flag) ordinaryContext) 4
      (a01.finish (stale flag) ordinaryContext) ∧
    Runs (step certificateReentryCaller) (a01.start (stale flag) ordinaryContext) 5
      (cfg (some (phaseLabel inspectPhase)) (clean flag) {certificate := [15]} ordinaryContext) ∧
    Runs (step certificateReentryCaller) (a01.start (stale flag) ordinaryContext) 9
      (cfg (some (resultLabel false)) (clean flag) {certificate := [15]} ordinaryContext) := by
  have first := a01_actual_first_run certificateReentryCaller (stale flag) ordinaryContext
  have push : step certificateReentryCaller (a01.finish (stale flag) ordinaryContext) =
      some (cfg (some (phaseLabel inspectPhase)) (clean flag) {certificate := [15]} ordinaryContext) := by
    apply congrArg some
    apply cfg_ext <;> first | rfl | (funext k; cases k with
      | inl k => cases k <;> rfl
      | inr k => rfl)
  have atFive := iterate_trans certificateReentryCaller first.1 (show
    (next certificateReentryCaller)^[1] (some (a01.finish (stale flag) ordinaryContext)) = _ from push)
  have second := a02_actual_first_run certificateReentryCaller (clean flag) ordinaryContext
  exact ⟨first, atFive, iterate_trans certificateReentryCaller atFive second.1⟩

theorem the_later_false_is_not_the_initial_first_result (flag : Bool) :
    ¬ FirstResult (step certificateReentryCaller) (a01.start (stale flag) ordinaryContext) false := by
  intro later
  have value := (every_owned_entry_has_exactly_its_evaluated_first_boolean
    certificateReentryCaller a01.phase a01.before (stale flag) ordinaryContext false).mp later
  rw [a01_literal_evaluation] at value
  cases value

theorem a_protected_caller_push_occurs_at_five_and_reenters_until_nine
    (flag : Bool) :
    FirstRun (step protectedReentryCaller) (a01.start (stale flag) ordinaryContext) 4
      (a01.finish (stale flag) ordinaryContext) ∧
    Runs (step protectedReentryCaller) (a01.start (stale flag) ordinaryContext) 5
      (cfg (some (phaseLabel inspectPhase)) (clean flag) {} enlargedContext) ∧
    Runs (step protectedReentryCaller) (a01.start (stale flag) ordinaryContext) 9
      (cfg (some (resultLabel true)) (clean flag) {} enlargedContext) := by
  have first := a01_actual_first_run protectedReentryCaller (stale flag) ordinaryContext
  have push : step protectedReentryCaller (a01.finish (stale flag) ordinaryContext) =
      some (cfg (some (phaseLabel inspectPhase)) (clean flag) {} enlargedContext) := by
    apply congrArg some
    apply cfg_ext
    · rfl
    · rfl
    · funext k
      cases k with
      | inl k => cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  have atFive := iterate_trans protectedReentryCaller first.1 (show
    (next protectedReentryCaller)^[1] (some (a01.finish (stale flag) ordinaryContext)) = _ from push)
  have second := a01_actual_first_run protectedReentryCaller (clean flag) enlargedContext
  exact ⟨first, atFive, iterate_trans protectedReentryCaller atFive second.1⟩

theorem the_post_return_protected_push_exceeds_the_owned_prefix_peak
    (flag : Bool) :
    physicalCells (cfg (some (phaseLabel (Λ := Unit) inspectPhase)) (clean flag)
      ({} : LocalData) enlargedContext) = 6 ∧
    (cfg (some (phaseLabel (Λ := Unit) inspectPhase)) (clean flag)
      ({} : LocalData) enlargedContext).stk (.inr 0) = [true, true, false, true] ∧
    5 < physicalCells (cfg (some (phaseLabel (Λ := Unit) inspectPhase)) (clean flag)
      ({} : LocalData) enlargedContext) := by
  have cells : physicalCells (cfg (some (phaseLabel (Λ := Unit) inspectPhase)) (clean flag)
      ({} : LocalData) enlargedContext) = 6 := by
    rw [actual_physical_cells_of_complete_cfg]
    change (∑ k : Fin 2, (enlargedContext k).length) = 6
    rw [Fin.sum_univ_two]
    rfl
  exact ⟨cells, rfl, by omega⟩

theorem halting_the_caller_is_live_at_five_and_outer_none_at_six
    (flag : Bool) :
    Runs (step (fun _ : External Unit => .halt)) (a01.start (stale flag) ordinaryContext) 5
      (cfg none (clean flag) {} ordinaryContext) ∧
    (next (fun _ : External Unit => .halt))^[6]
      (some (a01.start (stale flag) ordinaryContext)) = none := by
  let caller : ExampleCaller := fun _ => .halt
  have first := a01_actual_first_run caller (stale flag) ordinaryContext
  have after : (next caller)^[1] (some (a01.finish (stale flag) ordinaryContext)) =
      some (cfg none (clean flag) {} ordinaryContext) := by
    change step caller (cfg (some (resultLabel true)) (clean flag) {} ordinaryContext) = _
    exact a_live_boolean_can_be_followed_by_a_distinct_live_halt_configuration
      true (clean flag) {} ordinaryContext
  have atFive : (next caller)^[5] (some (a01.start (stale flag) ordinaryContext)) =
      some (cfg none (clean flag) {} ordinaryContext) := iterate_trans caller first.1 after
  refine ⟨atFive, ?_⟩
  change (next caller)^[5 + 1] (some (a01.start (stale flag) ordinaryContext)) = none
  rw [Function.iterate_succ_apply', atFive, next_some]
  rfl

/-! ## Two universal malformed families and eighteen independent finite instances -/

def nodeWord (n : Nat) : Word := List.replicate n 1

def sharpStart {K Λ R : Type} {Γ : K → Type} (direction : RotationDirection)
    (rest : Word) (count : Nat) (target : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (phaseLabel inspectPhase)) regs
    (data (moveCode ⟨direction, []⟩ ++ rest) [] [] (nodeWord count) [] [] [] [true] target) ctx

def sharpFinish {K Λ R : Type} {Γ : K → Type}
    (rest : Word) (count : Nat) (target : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (resultLabel false)) (resetAll regs)
    (data rest [] [] (nodeWord count) [] [] [] [false] target) ctx

def sharpDrop {K Λ R : Type} {Γ : K → Type}
    (rest : Word) (count pending : Nat) (target : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase .dropPending))))
    (resetAll regs) (data rest [] [] (nodeWord count) [] [] (List.replicate pending ())
      [false] target) ctx

def LeftSharpExpected {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (rest : Word) (n : Nat) (target : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  FirstRun transition (sharpStart .left rest n target regs ctx) (3 * n + 13)
    (sharpFinish rest n target regs ctx) ∧
  Runs transition (sharpStart .left rest n target regs ctx) (2 * n + 10)
    (sharpDrop rest n n target regs ctx) ∧
  remainingSteps (sharpDrop (Λ := Λ) rest n n target regs ctx) = n + 3 ∧
  physicalCells (sharpDrop (Λ := Λ) rest n n target regs ctx) =
    rest.length + 2 * n + 1 + target.length + externalCells ctx ∧
  ExactPeak transition (sharpStart .left rest n target regs ctx) (3 * n + 13)
    (rest.length + max (n + 2) (2 * n) + 1 + target.length + externalCells ctx)

def RightSharpExpected {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (rest : Word) (m : Nat) (target : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  FirstRun transition (sharpStart .right rest (m + 2) target regs ctx) (3 * m + 16)
    (sharpFinish rest (m + 2) target regs ctx) ∧
  Runs transition (sharpStart .right rest (m + 2) target regs ctx) (2 * m + 12)
    (sharpDrop rest (m + 2) (m + 1) target regs ctx) ∧
  remainingSteps (sharpDrop (Λ := Λ) rest (m + 2) (m + 1) target regs ctx) = m + 4 ∧
  physicalCells (sharpDrop (Λ := Λ) rest (m + 2) (m + 1) target regs ctx) =
    rest.length + 2 * m + 4 + target.length + externalCells ctx ∧
  ExactPeak transition (sharpStart .right rest (m + 2) target regs ctx) (3 * m + 16)
    (rest.length + max (m + 4) (2 * m + 3) + 1 + target.length + externalCells ctx)

structure SharpFixture where
  direction : RotationDirection
  parameter : Nat
  ticks : Nat
  dropTime : Nat
  remaining : Nat
  peak : Nat
  dropCells : Nat

def SharpFixture.sourceCount (c : SharpFixture) : Nat :=
  match c.direction with | .left => c.parameter | .right => c.parameter + 2

def SharpFixture.pendingCount (c : SharpFixture) : Nat :=
  match c.direction with | .left => c.parameter | .right => c.parameter + 1

def SharpFixture.Expected (c : SharpFixture) (transition : ExampleCfg → Option ExampleCfg)
    (regs : Registers Bool) : Prop :=
  FirstRun transition (sharpStart c.direction [15, 2] c.sourceCount [15] regs ordinaryContext)
    c.ticks (sharpFinish [15, 2] c.sourceCount [15] regs ordinaryContext) ∧
  Runs transition (sharpStart c.direction [15, 2] c.sourceCount [15] regs ordinaryContext)
    c.dropTime (sharpDrop [15, 2] c.sourceCount c.pendingCount [15] regs ordinaryContext) ∧
  remainingSteps (sharpDrop (Λ := Unit) [15, 2] c.sourceCount c.pendingCount [15] regs ordinaryContext) =
    c.remaining ∧
  physicalCells (sharpDrop (Λ := Unit) [15, 2] c.sourceCount c.pendingCount [15] regs ordinaryContext) =
    c.dropCells ∧
  ExactPeak transition (sharpStart c.direction [15, 2] c.sourceCount [15] regs ordinaryContext)
    c.ticks c.peak

def sharpCases : List SharpFixture :=
  [⟨.left, 0, 13, 10, 3, 11, 9⟩,
   ⟨.left, 1, 16, 12, 4, 12, 11⟩,
   ⟨.left, 2, 19, 14, 5, 13, 13⟩,
   ⟨.left, 3, 22, 16, 6, 15, 15⟩,
   ⟨.left, 4, 25, 18, 7, 17, 17⟩,
   ⟨.left, 5, 28, 20, 8, 19, 19⟩,
   ⟨.left, 6, 31, 22, 9, 21, 21⟩,
   ⟨.left, 7, 34, 24, 10, 23, 23⟩,
   ⟨.left, 8, 37, 26, 11, 25, 25⟩,
   ⟨.right, 0, 16, 12, 4, 13, 12⟩,
   ⟨.right, 1, 19, 14, 5, 14, 14⟩,
   ⟨.right, 2, 22, 16, 6, 16, 16⟩,
   ⟨.right, 3, 25, 18, 7, 18, 18⟩,
   ⟨.right, 4, 28, 20, 8, 20, 20⟩,
   ⟨.right, 5, 31, 22, 9, 22, 22⟩,
   ⟨.right, 6, 34, 24, 10, 24, 24⟩,
   ⟨.right, 7, 37, 26, 11, 26, 26⟩,
   ⟨.right, 8, 40, 28, 12, 28, 28⟩]

theorem sharp_cases_count : sharpCases.length = 18 := rfl

/-! ## Complete component physical sums, prefix frames and typed clocks -/

section ComponentPhysicalSums
variable {K Λ R : Type} {Γ : K → Type} [Fintype K]

theorem every_component_view_counts_all_local_and_external_physical_words
    (f : FuelCfg Γ Λ R) (h : ApplyCfg Γ Λ R) (e : EqualityCfg Γ Λ R) :
    physicalCells (fuelCfg f) = FuelDispatchMachine.stackCells f ∧
      physicalCells (applyCfg h) = MoveApplyMachine.stackCells h ∧
      physicalCells (equalityCfg e) = TreeEqualityMachine.stackCells e :=
  ⟨stackCells_fuelCfg f, stackCells_applyCfg h, stackCells_equalityCfg e⟩

theorem dirty_move_allowance_is_the_actual_installed_component_potential
    (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    hAllowance q D ctx = fixtureCells D + externalCells ctx +
        MoveApplyMachine.phaseDebt q + MoveApplyMachine.phaseCredit q (applyData D) ∧
      hAllowance q D ctx = MoveApplyMachine.potential
        (applyView (Λ := Λ) (some (MoveApplyMachine.phaseLabel q))
          (applyRegisterEquiv.symm regs) D ctx) :=
  ⟨rfl, hAllowance_eq_potential q D regs ctx⟩

end ComponentPhysicalSums

section ComponentPrefixContracts
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

theorem fuel_prefix_preserves_its_entire_component_complement
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    (start : FuelCfg Γ Λ R) (n : Nat) (bound : n ≤ FuelDispatchMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : Runs (step caller) (fuelCfg start) n reached) :
    ∃ middle, reached = fuelCfg middle ∧ middle.var.2 = start.var.2 ∧
      ∀ k, middle.stk (.inr k) = start.stk (.inr k) :=
  fuel_prefix_frame caller localCaller start n bound reached executed

theorem apply_prefix_preserves_fuel_target_bool_and_all_external_data
    (localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R)
    (start : ApplyCfg Γ Λ R) (n : Nat) (bound : n ≤ MoveApplyMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : Runs (step caller) (applyCfg start) n reached) :
    ∃ middle, reached = applyCfg middle ∧ middle.var.2 = start.var.2 ∧
      ∀ k, middle.stk (.inr k) = start.stk (.inr k) :=
  apply_prefix_frame caller localCaller start n bound reached executed

theorem equality_prefix_preserves_seven_local_complements_and_the_external_frame
    (localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R)
    (start : EqualityCfg Γ Λ R) (n : Nat) (bound : n ≤ TreeEqualityMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : Runs (step caller) (equalityCfg start) n reached) :
    ∃ middle, reached = equalityCfg middle ∧ middle.var.2 = start.var.2 ∧
      ∀ k, middle.stk (.inr k) = start.stk (.inr k) :=
  equality_prefix_frame caller localCaller start n bound reached executed

def exact_phase_timing (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel q)) regs D ctx)
      (some (phaseResult q regs D ctx)) (phaseSteps q D) := phaseInTime caller q D regs ctx

def exact_configuration_timing (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (step caller) start (some (finalCfg start)) (remainingSteps start) :=
  cfgInTime caller start

def exact_dirty_inspection_timing (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel inspectPhase)) regs D ctx)
      (some (inspectResult regs D ctx)) (inspectSteps D) := inspectInTime caller D regs ctx

def exact_dirty_counter_stage_timing (q : Resources.BinaryCounter.FixedWidthMachine.Phase)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (counterPhase q))) regs D ctx)
      (some (cfg (some (phaseLabel (fuelJoinPhase (FuelDispatchMachine.exitOfResult (counterFinish q D).result))))
        (resetFuel regs) (counterFinish q D).data ctx)) (counterFinish q D).steps :=
  counterStageInTime caller q D regs ctx

def exact_dirty_inspection_stage_timing (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel inspectPhase)) regs D ctx)
      (some (cfg (some (phaseLabel (fuelJoinPhase (inspectStageFinish D).result)))
        (resetFuel regs) (inspectStageFinish D).data ctx)) (inspectStageFinish D).steps :=
  fuelStageInTime caller D regs ctx

def exact_dirty_apply_stage_timing (q : MoveApplyMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel (applyPhase q))) regs D ctx)
      (some (cfg (some (phaseLabel (applyJoinPhase (applyFinish q D).result)))
        (resetApply regs) (applyFinish q D).data ctx)) (applyFinish q D).steps :=
  applyStageInTime caller q D regs ctx

def exact_raw_equality_stage_timing (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel comparePhase)) regs D ctx)
      (some (cfg (some (phaseLabel (equalityJoinPhase (equalityFinish D).result)))
        (resetEquality regs) (equalityFinish D).data ctx)) (equalityFinish D).steps :=
  equalityStageInTime caller D regs ctx

def every_fuel_join_is_a_one_step_typed_value (r : FuelDispatchMachine.Exit)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (fuelJoinPhase r))) regs D ctx)
      (some (cfg (some (fuelJoinTarget r)) (resetAll regs) D ctx)) 1 :=
  fuelJoinInTime caller r D regs ctx

def every_apply_join_is_a_one_step_typed_value (r : MoveApplyMachine.FinalResult)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (applyJoinPhase r))) regs D ctx)
      (some (cfg (some (applyJoinTarget r)) (resetAll regs) D ctx)) 1 :=
  applyJoinInTime caller r D regs ctx

def every_equality_join_is_a_one_step_typed_value (r : TreeEqualityMachine.Result)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (equalityJoinPhase r))) regs D ctx)
      (some (cfg (some (equalityJoinTarget r)) (resetAll regs) D ctx)) 1 :=
  equalityJoinInTime caller r D regs ctx

theorem all_eight_join_time_records_store_one
    (f : FuelDispatchMachine.Exit) (h : MoveApplyMachine.FinalResult) (e : TreeEqualityMachine.Result)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (every_fuel_join_is_a_one_step_typed_value caller f D regs ctx).steps = 1 ∧
      (every_apply_join_is_a_one_step_typed_value caller h D regs ctx).steps = 1 ∧
      (every_equality_join_is_a_one_step_typed_value caller e D regs ctx).steps = 1 := ⟨rfl, rfl, rfl⟩

theorem global_and_component_typed_records_retain_exact_counts
    (q : Phase) (w : Resources.BinaryCounter.FixedWidthMachine.Phase)
    (h : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (start : Cfg Γ Λ R) :
    (exact_phase_timing caller q D regs ctx).steps = phaseSteps q D ∧
    (exact_configuration_timing caller start).steps = remainingSteps start ∧
    (exact_dirty_inspection_timing caller D regs ctx).steps = inspectSteps D ∧
    (exact_dirty_counter_stage_timing caller w D regs ctx).steps = (counterFinish w D).steps ∧
    (exact_dirty_inspection_stage_timing caller D regs ctx).steps = (inspectStageFinish D).steps ∧
    (exact_dirty_apply_stage_timing caller h D regs ctx).steps = (applyFinish h D).steps ∧
    (exact_raw_equality_stage_timing caller D regs ctx).steps = (equalityFinish D).steps :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end ComponentPrefixContracts

/-! ## Actual finite packages, installed configurations and the genuine input -/

def independentPackage (caller : ExampleCaller) (initial : Bool) : Turing.FinTM2 :=
  machine caller initial

def twoLabelPackage
    (caller : External (Fin 2) → Statement IndependentAlphabet (Fin 2) Bool)
    (initial : Bool) : Turing.FinTM2 := machine caller initial

theorem the_actual_unit_label_package_has_eleven_stacks_fortytwo_labels_and_612_registers
    (caller : ExampleCaller) (initial : Bool) :
    @Fintype.card (independentPackage caller initial).K (independentPackage caller initial).kFin = 11 ∧
      @Fintype.card (independentPackage caller initial).Λ (independentPackage caller initial).ΛFin = 42 ∧
      @Fintype.card (independentPackage caller initial).σ (independentPackage caller initial).σFin = 612 := by
  change @Fintype.card (machine caller initial).K (machine caller initial).kFin = 11 ∧
    @Fintype.card (machine caller initial).Λ (machine caller initial).ΛFin = 42 ∧
    @Fintype.card (machine caller initial).σ (machine caller initial).σFin = 612
  exact ⟨by simpa using machine_card_stackId caller initial,
    by simpa using machine_card_label caller initial,
    by simpa using machine_card_registers caller initial⟩

theorem the_actual_two_label_package_has_eleven_stacks_fortythree_labels_and_612_registers
    (caller : External (Fin 2) → Statement IndependentAlphabet (Fin 2) Bool)
    (initial : Bool) :
    @Fintype.card (twoLabelPackage caller initial).K (twoLabelPackage caller initial).kFin = 11 ∧
      @Fintype.card (twoLabelPackage caller initial).Λ (twoLabelPackage caller initial).ΛFin = 43 ∧
      @Fintype.card (twoLabelPackage caller initial).σ (twoLabelPackage caller initial).σFin = 612 := by
  change @Fintype.card (machine caller initial).K (machine caller initial).kFin = 11 ∧
    @Fintype.card (machine caller initial).Λ (machine caller initial).ΛFin = 43 ∧
    @Fintype.card (machine caller initial).σ (machine caller initial).σFin = 612
  exact ⟨by simpa using machine_card_stackId caller initial,
    by simpa using machine_card_label caller initial,
    by simpa using machine_card_registers caller initial⟩

section GenericPackageConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : External Λ → Statement Γ Λ R) (initial : R)

theorem actual_package_indices_and_alphabets_are_certificate_tag_and_fuel_bool :
    (machine caller initial).k₀ = Sum.inl LocalStack.certificate ∧
      (machine caller initial).k₁ = Sum.inl LocalStack.fuel ∧
      (machine caller initial).Γ (machine caller initial).k₀ = Tag ∧
      (machine caller initial).Γ (machine caller initial).k₁ = Bool :=
  ⟨rfl, rfl, rfl, rfl⟩

abbrev actual_package_every_physical_alphabet_is_finite (k : (machine caller initial).K) :
    Fintype ((machine caller initial).Γ k) := machineAlphabetFintype caller initial k

theorem actual_package_step_is_the_same_literal_runtime (c : Cfg Γ Λ R) :
    (machine caller initial).step c = step caller c := machine_step_eq caller initial c

theorem actual_package_retains_arbitrary_installed_registers_and_dirty_words
    (start : Cfg Γ Λ R) :
    FirstRun (machine caller initial).step start (remainingSteps start) (finalCfg start) :=
  machine_cfg_first_return caller initial start

theorem actual_package_first_result_converse_uses_the_complete_installed_endpoint
    (start finish : Cfg Γ Λ R) (ticks : Nat) :
    FirstRun (machine caller initial).step start ticks finish ↔
      ticks = remainingSteps start ∧ finish = finalCfg start :=
  machineFirstRun_iff caller initial start finish ticks

def actual_package_installed_timing (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (machine caller initial).step start
      (some (finalCfg start)) (remainingSteps start) := machineCfgInTime caller initial start

theorem actual_package_installed_timing_stores_the_exact_clock (start : Cfg Γ Λ R) :
    (actual_package_installed_timing caller initial start).steps = remainingSteps start := rfl

theorem the_genuine_initializer_installs_only_the_supplied_certificate (raw : Word) :
    Turing.initList (machine caller initial) raw =
      cfg (some (phaseLabel inspectPhase)) (initialRegisters initial)
        {certificate := raw} (fun _ => []) := initList_eq caller initial raw

theorem every_genuine_certificate_input_reaches_its_live_boolean_in_four_steps (raw : Word) :
    FirstRun (machine caller initial).step (Turing.initList (machine caller initial) raw) 4
      (cfg (some (resultLabel raw.isEmpty)) (initialRegisters initial)
        {certificate := raw} (fun _ => [])) := machine_init_first_return caller initial raw

theorem the_genuine_initializer_has_exact_rank_four_and_never_emits_a_fuel_output (raw : Word) :
    remainingSteps (Turing.initList (machine caller initial) raw) = 4 ∧
      (finalCfg (Turing.initList (machine caller initial) raw)).stk (machine caller initial).k₁ = [] ∧
      (finalCfg (Turing.initList (machine caller initial) raw)).stk (.inl .certificate) = raw ∧
      (finalCfg (Turing.initList (machine caller initial) raw)).l = some (resultLabel raw.isEmpty) :=
  ⟨machine_init_exact_rank caller initial raw, machine_init_final_output_empty caller initial raw,
    machine_init_final_certificate caller initial raw, machine_init_endpoint_live caller initial raw⟩

def actual_initializer_timing (raw : Word) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (Turing.initList (machine caller initial) raw)
      (some (cfg (some (resultLabel raw.isEmpty)) (initialRegisters initial)
        {certificate := raw} (fun _ => []))) 4 := machineInitInTimeExact caller initial raw

theorem actual_initializer_timing_stores_four (raw : Word) :
    (actual_initializer_timing caller initial raw).steps = 4 := rfl

theorem every_actual_initializer_prefix_has_exactly_the_input_cell_count
    (raw : Word) (n : Nat) (bound : n ≤ 4) (reached : Cfg Γ Λ R)
    (executed : Runs (machine caller initial).step
      (Turing.initList (machine caller initial) raw) n reached) :
    physicalCells reached = raw.length :=
  machine_init_prefix_cells caller initial raw n bound reached executed

theorem every_genuine_initializer_has_the_exact_inclusive_input_peak (raw : Word) :
    ExactPeak (machine caller initial).step
      (Turing.initList (machine caller initial) raw) 4 raw.length :=
  machine_init_exact_peak caller initial raw

end GenericPackageConnections

theorem both_literal_genuine_inputs_use_the_actual_package_initializer
    (caller : ExampleCaller) (initial : Bool) :
    FirstRun (independentPackage caller initial).step
      (Turing.initList (independentPackage caller initial) ([] : Word)) 4
      (cfg (some (resultLabel true)) (clean initial) {} (fun _ => [])) ∧
    FirstRun (independentPackage caller initial).step
      (Turing.initList (independentPackage caller initial) ([15] : Word)) 4
      (cfg (some (resultLabel false)) (clean initial) {certificate := [15]} (fun _ => [])) :=
  ⟨machine_init_first_return caller initial [], machine_init_first_return caller initial [15]⟩

theorem the_same_actual_package_runs_the_installed_rotation_input_for_twentyfive_steps
    (caller : ExampleCaller) (initial flag : Bool) :
    FirstRun (independentPackage caller initial).step (a12.start (stale flag) ordinaryContext)
      25 (a12.finish (stale flag) ordinaryContext) :=
  a12_actual_first_run caller (stale flag) ordinaryContext

/-! ## Complete FrontEnd physical compatibility and explicit installed entries -/

theorem all_front_end_physical_indices_and_symbols_have_complete_inverses
    {K : Type} {Γ : K → Type}
    (k : FrontEndMachine.StackId (NewBranchStores ⊕ K))
    (j : StackId (FrontEndProtected ⊕ K))
    (symbol : FrontEndMachine.alphabet (frontEndAddedAlphabet Γ) k) :
    frontEndStackEquiv.symm (frontEndStackEquiv k) = k ∧
      frontEndStackEquiv (frontEndStackEquiv.symm j) = j ∧
      (frontEndSymbolEquiv (Γ := Γ) k).symm (frontEndSymbolEquiv k symbol) = symbol :=
  ⟨frontEndStackEquiv.symm_apply_apply k, frontEndStackEquiv.apply_symm_apply j,
    (frontEndSymbolEquiv k).symm_apply_apply symbol⟩

theorem the_front_end_register_map_preserves_all_decoder_and_branch_fields
    {R : Type} (regs : FrontEndMachine.Registers (Option Branch × R)) :
    frontEndRegisterEquiv.symm (frontEndRegisterEquiv regs) = regs ∧
      (frontEndRegisterEquiv regs).1 = regs.2.1.b0 ∧
      (frontEndRegisterEquiv regs).2.1.1 = regs.2.2.1 ∧
      (frontEndRegisterEquiv regs).2.2.1 =
        (regs.2.1.b1, regs.2.1.b2, regs.2.1.b3, regs.2.1.tag) ∧
      (frontEndRegisterEquiv regs).2.2.2 = regs.2.2.2 :=
  ⟨frontEndRegisterEquiv.symm_apply_apply regs, rfl, rfl, rfl, rfl⟩

theorem front_end_reset_really_retains_the_incoming_branch_register
    {R : Type} (regs : FrontEndMachine.Registers (Option Branch × R)) :
    frontEndRegisterEquiv (FrontEndMachine.reset regs) =
      (none, ((regs.2.2.1, (none, none)), (frontEndDecoderZero, regs.2.2.2))) :=
  frontEndRegisterEquiv_reset regs

theorem complete_front_end_physical_cardinalities
    {K R : Type} [Fintype K] [Fintype R] :
    Fintype.card (FrontEndMachine.StackId (NewBranchStores ⊕ K)) = 16 + Fintype.card K ∧
      Fintype.card (StackId (FrontEndProtected ⊕ K)) = 16 + Fintype.card K ∧
      Fintype.card FrontEndDecoderComplement = 459 ∧
      Fintype.card (FrontEndMachine.Registers (Option Branch × R)) = 140454 * Fintype.card R ∧
      Fintype.card (Registers (FrontEndDecoderComplement × R)) = 140454 * Fintype.card R :=
  ⟨frontEnd_source_stack_card, frontEnd_stack_card, frontEnd_decoder_complement_card,
    frontEnd_source_register_card, frontEnd_register_card⟩

theorem the_front_end_map_preserves_the_sum_over_every_physical_stack
    {K : Type} {Γ : K → Type} [Fintype K]
    (allWords : ∀ k, List (FrontEndMachine.alphabet (frontEndAddedAlphabet Γ) k)) :
    ∑ k, (frontEndStacks allWords k).length = ∑ k, (allWords k).length :=
  frontEnd_stack_cells allWords

def frontEndInstalledEntry {K Λ R : Type} {Γ : K → Type}
    (regs : FrontEndMachine.Registers (Option Branch × R))
    (B O : List Branch) (ctx : ∀ k, List (Γ k))
    (source target : BinaryTree Unit) (fuel : Bits) (certificate : Word) :
    Cfg (frontEndProtectedAlphabet Γ) Λ (FrontEndDecoderComplement × R) :=
  cfg (some (phaseLabel inspectPhase)) (frontEndRegisterEquiv (FrontEndMachine.reset regs))
    (frontEndSuccessData source target fuel certificate B O) (frontEndSuccessContext ctx)

theorem the_actual_front_end_success_matches_the_installed_physical_data
    {K Λ R : Type} {Γ : K → Type}
    (regs : FrontEndMachine.Registers (Option Branch × R))
    (B O : List Branch) (ctx : ∀ k, List (Γ k))
    (source target : BinaryTree Unit) (fuel : Bits) (certificate : Word) :
    frontEndPhysicalData (FrontEndMachine.resultCfg (Λ := Λ) regs
      (frontEndAddedContext B O ctx) (.success source target fuel certificate)) =
      ((frontEndInstalledEntry (Λ := Λ) regs B O ctx source target fuel certificate).var,
        (frontEndInstalledEntry (Λ := Λ) regs B O ctx source target fuel certificate).stk) :=
  frontEnd_success_physical_data regs B O ctx source target fuel certificate

def staleFrontEndRegisters (flag : Bool) : FrontEndMachine.Registers (Option Branch × Bool) :=
  ((some 15, some ()),
    (⟨some true, some false, some true, some false, some 7⟩, (some .right, flag)))

def frontEndDirtyEntry (flag : Bool) :
    Cfg (frontEndProtectedAlphabet IndependentAlphabet) Unit (FrontEndDecoderComplement × Bool) :=
  frontEndInstalledEntry (staleFrontEndRegisters flag) [.right] [.left] ordinaryContext
    rightTwo leftTwo [true] [6, 10]

theorem front_end_dirty_entry_retains_both_physical_branch_words_and_stale_branch
    (flag : Bool) :
    frontEndDirtyEntry flag = r10.start
      (none, ((some .right, (none, none)), (frontEndDecoderZero, flag)))
      (frontEndSuccessContext ordinaryContext) := rfl

theorem the_actual_dirty_front_end_data_has_the_fixed_twenty_step_false_result
    (caller : External Unit → Statement (frontEndProtectedAlphabet IndependentAlphabet)
      Unit (FrontEndDecoderComplement × Bool)) (flag : Bool) :
    FirstRun (step caller) (frontEndDirtyEntry flag) 20
      (cfg (some (resultLabel false))
        (none, ((none, (none, none)), (frontEndDecoderZero, flag)))
        (data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0])
        (frontEndSuccessContext ordinaryContext)) ∧
    ExactPeak (step caller) (frontEndDirtyEntry flag) 20 20 := by
  have first := r10_actual_first_run caller
    (none, ((some .right, (none, none)), (frontEndDecoderZero, flag)))
    (frontEndSuccessContext ordinaryContext)
  have peak := r10_actual_exact_peak caller
    (none, ((some .right, (none, none)), (frontEndDecoderZero, flag)))
    (frontEndSuccessContext ordinaryContext)
  have external : externalCells (frontEndSuccessContext ordinaryContext) = 5 := by
    exact (frontEnd_success_context_cells ordinaryContext).trans
      ordinary_protected_context_has_five_physical_cells
  refine ⟨first, ?_⟩
  rw [front_end_dirty_entry_retains_both_physical_branch_words_and_stale_branch]
  have exactPeak : r10.peak + externalCells (frontEndSuccessContext ordinaryContext) = 20 := by
    rw [external]
    rfl
  rw [exactPeak] at peak
  exact peak

theorem the_dirty_front_end_selected_boundaries_use_the_same_actual_registers
    (caller : External Unit → Statement (frontEndProtectedAlphabet IndependentAlphabet)
      Unit (FrontEndDecoderComplement × Bool)) (flag : Bool) :
    ∀ b ∈ frontEndDirtyBoundaries,
      b.Expected (step caller) (frontEndDirtyEntry flag)
        (none, ((some .right, (none, none)), (frontEndDecoderZero, flag)))
        (frontEndSuccessContext ordinaryContext) :=
  all_five_dirty_branch_boundaries_have_their_actual_rank_and_cells caller
    (none, ((some .right, (none, none)), (frontEndDecoderZero, flag)))
    (frontEndSuccessContext ordinaryContext)

theorem explicitly_empty_added_branch_words_give_the_clean_front_end_example
    (caller : External Unit → Statement (frontEndProtectedAlphabet IndependentAlphabet)
      Unit (FrontEndDecoderComplement × Bool)) (flag : Bool) :
    FirstRun (step caller)
      (frontEndInstalledEntry (staleFrontEndRegisters flag) [] [] ordinaryContext
        rightTwo leftTwo [true] [6, 10]) 25
      (cfg (some (resultLabel true))
        (none, ((none, (none, none)), (frontEndDecoderZero, flag)))
        (data [] [] [] [] [] [] [] [false] []) (frontEndSuccessContext ordinaryContext)) :=
  a12_actual_first_run caller
    (frontEndRegisterEquiv (FrontEndMachine.reset (staleFrontEndRegisters flag)))
    (frontEndSuccessContext ordinaryContext)

/-! ## Further installation through complete carriers and owned body agreement -/

section FurtherCompleteInstallation
variable {K Λ R K' Λ' R' : Type} {Γ : K → Type} {Γ' : K' → Type}
variable (names : StackId K ≃ K') (symbols : ∀ k, alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')

theorem further_installation_has_a_complete_configuration_inverse
    (source : Cfg Γ Λ R) (target : Turing.TM2.Cfg Γ' Λ' R') :
    (installedCfgEquiv names symbols registers labels).symm
        (installedCfg names symbols registers labels source) = source ∧
    installedCfg names symbols registers labels
        ((installedCfgEquiv names symbols registers labels).symm target) = target :=
  ⟨(installedCfgEquiv names symbols registers labels).symm_apply_apply source,
    (installedCfgEquiv names symbols registers labels).apply_symm_apply target⟩

theorem further_installation_recovers_every_register_and_physical_word
    (source : Cfg Γ Λ R) :
    registers.symm (installedCfg names symbols registers labels source).var = source.var ∧
    ∀ k, ((installedCfg names symbols registers labels source).stk (names k)).map
      (symbols k).symm = source.stk k :=
  ⟨installedCfg_registers_readback names symbols registers labels source,
    installedCfg_stack_readback names symbols registers labels source⟩

theorem further_installation_preserves_the_complete_physical_sum
    [Fintype K] [Fintype K'] (source : Cfg Γ Λ R) :
    ∑ k, ((installedCfg names symbols registers labels source).stk k).length =
      physicalCells source := installed_stack_cells names symbols registers labels source

variable [DecidableEq K] [DecidableEq K']
variable (caller : External Λ → Statement Γ Λ R)
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')

theorem all_thirtynine_owned_bodies_suffice_for_each_actual_local_prefix
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) =
      ((next caller)^[n] (some start)).map (installedCfg names symbols registers labels) :=
  installed_owned_prefix names symbols registers labels caller ambient installed start n bound

theorem further_installation_fixes_the_first_time_and_the_entire_first_endpoint
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (finish : Turing.TM2.Cfg Γ' Λ' R') :
    ((FrontEndMachine.Transport.next ambient)^[n]
        (some (installedCfg names symbols registers labels start)) = some finish ∧
      ¬ Owned (finish.l.map labels.symm) ∧
      ∀ j, j < n → ∃ reached,
        (FrontEndMachine.Transport.next ambient)^[j]
          (some (installedCfg names symbols registers labels start)) = some reached ∧
        Owned (reached.l.map labels.symm)) ↔
    n = remainingSteps start ∧
      finish = installedCfg names symbols registers labels (finalCfg start) :=
  installed_firstRun_iff names symbols registers labels caller ambient installed start n finish

def exact_owned_installation_timing
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels start)
      (some (installedCfg names symbols registers labels (finalCfg start)))
      (remainingSteps start) :=
  installed_owned_timed names symbols registers labels caller ambient installed start

theorem exact_owned_installation_timing_stores_the_actual_clock
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) :
    (exact_owned_installation_timing names symbols registers labels caller ambient installed start).steps =
      remainingSteps start := rfl

theorem an_actual_installed_prefix_keeps_its_source_physical_bound
    [Fintype K] [Fintype K']
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) (budget : Nat)
    (estimate : ∀ source, Runs (step caller) start n source → physicalCells source ≤ budget)
    (reached : Turing.TM2.Cfg Γ' Λ' R')
    (executed : (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) = some reached) :
    ∑ k, (reached.stk k).length ≤ budget :=
  installed_prefix_cells_of_source_bound names symbols registers labels caller ambient installed
    start n bound budget estimate reached executed

theorem agreement_at_every_label_transports_arbitrary_later_caller_iterations
    (installed : ∀ label, ambient (labels label) =
      FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (n : Nat) (start : Option (Cfg Γ Λ R)) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (start.map (installedCfg names symbols registers labels)) =
      ((next caller)^[n] start).map (installedCfg names symbols registers labels) :=
  installed_iterate names symbols registers labels caller ambient installed n start

end FurtherCompleteInstallation


/-! ## Clean raw execution and represented source refinement -/

section CleanActualRuns
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem every_clean_raw_input_has_its_complete_actual_first_run
    (fuel : Bits) (certificate source target : Word) :
    FirstRun (step caller) (entry regs fuel certificate source target ctx)
      (runSteps fuel certificate source target) (runResult regs fuel certificate source target ctx) :=
  run_firstRun caller regs fuel certificate source target ctx

theorem clean_first_run_from_the_complete_evaluation
    (fuel : Bits) (certificate source target : Word) (result : Bool)
    (output : LocalData) (ticks : Nat)
    (evaluated : runEvaluation fuel certificate source target = ⟨result, output, ticks⟩) :
    FirstRun (step caller) (entry regs fuel certificate source target ctx) ticks
      (cfg (some (resultLabel result)) (resetAll regs) output ctx) := by
  change Resources.RotationCertificate.StreamMachine.FirstRun caller _ _ _
  have first := run_firstRun caller regs fuel certificate source target ctx
  simpa only [runSteps, runResult, evaluated, evaluationCfg] using first

theorem eof_uses_the_actual_raw_word_comparison_before_fuel
    (fuel : Bits) (source target : Word) :
    FirstRun (step caller) (entry regs fuel [] source target ctx)
      (TreeEqualityMachine.runSteps source target + 3)
      (cfg (some (resultLabel (decide (source = target)))) (resetAll regs)
        (cleanData fuel [] (source.drop (TreeEqualityMachine.runSteps source target))
          (target.drop (TreeEqualityMachine.runSteps source target))) ctx) :=
  clean_first_run_from_the_complete_evaluation caller regs ctx fuel [] source target _ _ _
    (runEvaluation_nil fuel source target)

theorem failed_fuel_stops_before_parsing_and_preserves_the_literal_certificate
    (fuel : Bits) (certificate source target : Word) (nonempty : certificate ≠ [])
    (failed : (Resources.BinaryCounter.decFixedRun fuel).1 = none) :
    FirstRun (step caller) (entry regs fuel certificate source target ctx)
      (Resources.BinaryCounter.FixedWidthMachine.runSteps fuel + 2)
      (cfg (some (resultLabel false)) (resetAll regs)
        (cleanData fuel certificate source target) ctx) :=
  clean_first_run_from_the_complete_evaluation caller regs ctx fuel certificate source target _ _ _
    (runEvaluation_no_fuel fuel certificate source target nonempty failed)

theorem failed_parsing_rolls_back_only_the_current_suffix_after_the_actual_decrement
    (fuel nextFuel : Bits) (certificate source target : Word) (nonempty : certificate ≠ [])
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (failed : (parseMoveRun certificate).1 = none) :
    FirstRun (step caller) (entry regs fuel certificate source target ctx)
      (Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
        MoveParserMachine.fullSteps certificate + 4)
      (cfg (some (resultLabel false)) (resetAll regs)
        (cleanData nextFuel certificate source target) ctx) :=
  clean_first_run_from_the_complete_evaluation caller regs ctx fuel certificate source target _ _ _
    (runEvaluation_parse_failure fuel nextFuel certificate source target nonempty decremented failed)

theorem represented_rotation_failure_retains_the_actual_remaining_physical_path
    (fuel nextFuel : Bits) (certificate rest : Word) (move : RotationMove)
    (source target : BinaryTree Unit)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (failed : (applyMoveRun move source).1 = none) :
    FirstRun (step caller) (entry regs fuel certificate (treeCode source) (treeCode target) ctx)
      (Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
        MoveApplyMachine.representedSteps move [] source [] + 3)
      (cfg (some (resultLabel false)) (resetAll regs)
        { (cleanData nextFuel rest (treeCode source) (treeCode target)) with
          path := PositionedRotationMachine.remainingPath move.position source } ctx) :=
  clean_first_run_from_the_complete_evaluation caller regs ctx fuel certificate
    (treeCode source) (treeCode target) _ _ _
    (represented_failure_step fuel nextFuel certificate rest move source target decremented parsed failed)

theorem every_represented_boolean_is_exactly_the_existing_source_boolean
    (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit) (result : Bool) :
    FirstResult (step caller) (entry regs fuel certificate (treeCode source) (treeCode target) ctx) result ↔
      (checkStreamRun fuel source target certificate).1 = result :=
  represented_firstResult_iff caller regs fuel certificate source target ctx result

theorem represented_acceptance_recognizes_the_literal_whole_certificate
    (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit) :
    FirstResult (step caller) (entry regs fuel certificate (treeCode source) (treeCode target) ctx) true ↔
      ∃ moves, certificate = certCode moves ∧ Trees.Rotations.applyMoves? moves source = some target ∧
        moves.length ≤ Resources.BinaryCounter.value fuel :=
  represented_accepts_iff caller regs fuel certificate source target ctx

theorem any_represented_first_output_fixes_the_clock_and_every_returned_word
    (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit)
    (ticks : Nat) (finish : Cfg Γ Λ R)
    (first : FirstRun (step caller)
      (entry regs fuel certificate (treeCode source) (treeCode target) ctx) ticks finish) :
    ticks = runSteps fuel certificate (treeCode source) (treeCode target) ∧
      finish = cfg (some (resultLabel (checkStreamRun fuel source target certificate).1))
        (resetAll regs) (runEvaluation fuel certificate (treeCode source) (treeCode target)).data ctx :=
  represented_complete_first_output caller regs fuel certificate source target ctx ticks finish first

theorem represented_acceptance_reaches_a_live_label_with_the_actual_remaining_fuel
    (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit)
    (accepted : (checkStreamRun fuel source target certificate).1 = true) :
    ∃ finalFuel,
      FirstRun (step caller) (entry regs fuel certificate (treeCode source) (treeCode target) ctx)
        (runSteps fuel certificate (treeCode source) (treeCode target))
        (cfg (some (resultLabel true)) (resetAll regs) (cleanData finalFuel [] [] []) ctx) ∧
      finalFuel.length = fuel.length :=
  represented_accepting_endpoint caller regs fuel certificate source target ctx accepted

def exact_raw_timing (fuel : Bits) (certificate source target : Word) :
    StateTransition.EvalsToInTime (step caller) (entry regs fuel certificate source target ctx)
      (some (runResult regs fuel certificate source target ctx))
      (runSteps fuel certificate source target) :=
  runInTimeExact caller regs fuel certificate source target ctx

def bounded_raw_timing (fuel : Bits) (certificate source target : Word) :
    StateTransition.EvalsToInTime (step caller) (entry regs fuel certificate source target ctx)
      (some (runResult regs fuel certificate source target ctx))
      ((2 * fuel.length + 3 * source.length + 7) * certificate.length + source.length + 4) :=
  runInPolynomialTime caller regs fuel certificate source target ctx

def exact_represented_timing (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit) :
    StateTransition.EvalsToInTime (step caller)
      (entry regs fuel certificate (treeCode source) (treeCode target) ctx)
      (some (runResult regs fuel certificate (treeCode source) (treeCode target) ctx))
      (runSteps fuel certificate (treeCode source) (treeCode target)) :=
  representedInTimeExact caller regs fuel certificate source target ctx

def bounded_represented_timing (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit) :
    StateTransition.EvalsToInTime (step caller)
      (entry regs fuel certificate (treeCode source) (treeCode target) ctx)
      (some (runResult regs fuel certificate (treeCode source) (treeCode target) ctx))
      ((2 * fuel.length + 6 * source.numNodes + 10) * certificate.length + 2 * source.numNodes + 5) :=
  representedInPolynomialTime caller regs fuel certificate source target ctx

theorem all_typed_clean_time_records_keep_the_actual_step_count
    (fuel : Bits) (certificate source target : Word) :
    (exact_raw_timing caller regs ctx fuel certificate source target).steps =
        runSteps fuel certificate source target ∧
      (bounded_raw_timing caller regs ctx fuel certificate source target).steps =
        runSteps fuel certificate source target := ⟨rfl, rfl⟩

theorem both_typed_represented_time_records_keep_machine_time
    (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit) :
    (exact_represented_timing caller regs ctx fuel certificate source target).steps =
        runSteps fuel certificate (treeCode source) (treeCode target) ∧
      (bounded_represented_timing caller regs ctx fuel certificate source target).steps =
        runSteps fuel certificate (treeCode source) (treeCode target) := ⟨rfl, rfl⟩

end CleanActualRuns

/-! The source tariff equations below retain their own measured observations. -/

theorem source_eof_tariff (fuel : Bits) (source target : BinaryTree Unit) :
    sourceObservation fuel source target [] =
      ((eqTreeRun source target).1, (eqTreeRun source target).2 + 1) :=
  sourceObservation_nil fuel source target

theorem source_fuel_failure_tariff (fuel : Bits) (source target : BinaryTree Unit)
    (tag : Tag) (raw : Word) (failed : (Resources.BinaryCounter.decFixedRun fuel).1 = none) :
    sourceObservation fuel source target (tag :: raw) =
      (false, (Resources.BinaryCounter.decFixedRun fuel).2 + 2) :=
  sourceObservation_no_fuel fuel source target tag raw failed

theorem source_parse_failure_tariff (fuel nextFuel : Bits) (source target : BinaryTree Unit)
    (tag : Tag) (raw : Word)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (failed : (parseMoveRun (tag :: raw)).1 = none) :
    sourceObservation fuel source target (tag :: raw) =
      (false, (Resources.BinaryCounter.decFixedRun fuel).2 + (parseMoveRun (tag :: raw)).2 + 2) :=
  sourceObservation_parse_failure fuel nextFuel source target tag raw decremented failed

theorem source_rotation_failure_tariff (fuel nextFuel : Bits) (source target : BinaryTree Unit)
    (certificate rest : Word) (move : RotationMove)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (failed : (applyMoveRun move source).1 = none) :
    sourceObservation fuel source target certificate =
      (false, (Resources.BinaryCounter.decFixedRun fuel).2 + (parseMoveRun certificate).2 +
        (applyMoveRun move source).2 + 2) :=
  sourceObservation_move_failure fuel nextFuel source target certificate rest move decremented parsed failed

theorem source_success_continues_at_the_literal_suffix_and_actual_next_tree
    (fuel nextFuel : Bits) (source nextTree target : BinaryTree Unit)
    (certificate rest : Word) (move : RotationMove)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (executed : (applyMoveRun move source).1 = some nextTree) :
    sourceObservation fuel source target certificate =
      ((sourceObservation nextFuel nextTree target rest).1,
        (Resources.BinaryCounter.decFixedRun fuel).2 + (parseMoveRun certificate).2 +
          (applyMoveRun move source).2 + (sourceObservation nextFuel nextTree target rest).2 + 1) ∧
    (applyMoveRun move source).2 = 3 * move.position.length + 5 ∧
    nextTree.numNodes = source.numNodes :=
  ⟨sourceObservation_step fuel nextFuel source nextTree target certificate rest move decremented parsed executed,
    source_success_application_cost move source nextTree executed,
    applyMoveRun_numNodes move source nextTree executed⟩

theorem the_source_budget_remains_a_distinct_observation_bound
    (fuel : Bits) (source target : BinaryTree Unit) (certificate : Word) :
    (sourceObservation fuel source target certificate).2 ≤
      (3 * fuel.length + 3 * source.numNodes + 12) * certificate.length + 3 * source.numNodes + 6 :=
  sourceObservation_cost_le fuel source target certificate


/-! ## Universal sharp families preserve the independently fixed expectations -/

section UniversalSharpConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)

theorem every_left_malformed_family_has_its_exact_actual_peak
    (rest : Word) (n : Nat) (target : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LeftSharpExpected (step caller) rest n target regs ctx := by
  have actual := left_nodes_run caller rest n target regs ctx
  change LocalRun caller (3 * n + 13) (sharpStart .left rest n target regs ctx)
    (sharpFinish rest n target regs ctx) at actual
  refine ⟨⟨LocalRun.iterate caller actual, not_owned_result false,
    LocalRun.owned_prefix caller actual⟩, ?_, ?_, ?_, ?_⟩
  · exact LocalRun.iterate caller (left_nodes_drop caller rest n target regs ctx)
  · exact left_nodes_drop_rank caller rest n target regs ctx
  · have cells := left_nodes_drop_cells (Λ := Λ) rest n target (resetAll regs) ctx
    change physicalCells (sharpDrop (Λ := Λ) rest n n target regs ctx) =
      2 * n + rest.length + 1 + target.length + externalCells ctx at cells
    omega
  · have peak := left_nodes_peak caller rest n target regs ctx
    change ExactPeak (step caller) (sharpStart .left rest n target regs ctx) (3 * n + 13)
      (max (n + 2) (2 * n) + rest.length + 1 + target.length + externalCells ctx) at peak
    have reorder : rest.length + max (n + 2) (2 * n) + 1 + target.length + externalCells ctx =
        max (n + 2) (2 * n) + rest.length + 1 + target.length + externalCells ctx := by omega
    rw [reorder]
    exact peak

theorem every_right_malformed_family_has_its_exact_actual_peak
    (rest : Word) (m : Nat) (target : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    RightSharpExpected (step caller) rest m target regs ctx := by
  have actual := right_nodes_run caller rest m target regs ctx
  change LocalRun caller (3 * m + 16) (sharpStart .right rest (m + 2) target regs ctx)
    (sharpFinish rest (m + 2) target regs ctx) at actual
  refine ⟨⟨LocalRun.iterate caller actual, not_owned_result false,
    LocalRun.owned_prefix caller actual⟩, ?_, ?_, ?_, ?_⟩
  · exact LocalRun.iterate caller (right_nodes_drop caller rest m target regs ctx)
  · exact right_nodes_drop_rank caller rest m target regs ctx
  · have cells := right_nodes_drop_cells (Λ := Λ) rest m target (resetAll regs) ctx
    change physicalCells (sharpDrop (Λ := Λ) rest (m + 2) (m + 1) target regs ctx) =
      2 * m + 3 + rest.length + 1 + target.length + externalCells ctx at cells
    omega
  · have peak := right_nodes_peak caller rest m target regs ctx
    change ExactPeak (step caller) (sharpStart .right rest (m + 2) target regs ctx) (3 * m + 16)
      (max (m + 4) (2 * m + 3) + rest.length + 1 + target.length + externalCells ctx) at peak
    have reorder : rest.length + max (m + 4) (2 * m + 3) + 1 + target.length + externalCells ctx =
        max (m + 4) (2 * m + 3) + rest.length + 1 + target.length + externalCells ctx := by omega
    rw [reorder]
    exact peak

theorem the_left_zero_case_keeps_its_initial_attained_maximum
    (rest target : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstRun (step caller) (sharpStart .left rest 0 target regs ctx) 13
      (sharpFinish rest 0 target regs ctx) ∧
      ExactPeak (step caller) (sharpStart .left rest 0 target regs ctx) 13
        (rest.length + 3 + target.length + externalCells ctx) := by
  have actual := every_left_malformed_family_has_its_exact_actual_peak caller rest 0 target regs ctx
  exact ⟨actual.1, actual.2.2.2.2⟩

theorem the_right_zero_case_has_a_distinct_clock_and_peak
    (rest target : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstRun (step caller) (sharpStart .right rest 2 target regs ctx) 16
      (sharpFinish rest 2 target regs ctx) ∧
      ExactPeak (step caller) (sharpStart .right rest 2 target regs ctx) 16
        (rest.length + 5 + target.length + externalCells ctx) := by
  have actual := every_right_malformed_family_has_its_exact_actual_peak caller rest 0 target regs ctx
  exact ⟨actual.1, actual.2.2.2.2⟩

end UniversalSharpConnections

theorem all_eighteen_sharp_instances_keep_their_literal_clocks_and_peaks
    (caller : External Unit → Statement IndependentAlphabet Unit Bool)
    (regs : Registers Bool) (c : SharpFixture) (listed : c ∈ sharpCases) :
    c.Expected (step caller) regs := by
  simp only [sharpCases, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      LeftSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_left_malformed_family_has_its_exact_actual_peak caller [15, 2] 0 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      LeftSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_left_malformed_family_has_its_exact_actual_peak caller [15, 2] 1 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      LeftSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_left_malformed_family_has_its_exact_actual_peak caller [15, 2] 2 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      LeftSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_left_malformed_family_has_its_exact_actual_peak caller [15, 2] 3 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      LeftSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_left_malformed_family_has_its_exact_actual_peak caller [15, 2] 4 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      LeftSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_left_malformed_family_has_its_exact_actual_peak caller [15, 2] 5 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      LeftSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_left_malformed_family_has_its_exact_actual_peak caller [15, 2] 6 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      LeftSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_left_malformed_family_has_its_exact_actual_peak caller [15, 2] 7 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      LeftSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_left_malformed_family_has_its_exact_actual_peak caller [15, 2] 8 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      RightSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_right_malformed_family_has_its_exact_actual_peak caller [15, 2] 0 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      RightSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_right_malformed_family_has_its_exact_actual_peak caller [15, 2] 1 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      RightSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_right_malformed_family_has_its_exact_actual_peak caller [15, 2] 2 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      RightSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_right_malformed_family_has_its_exact_actual_peak caller [15, 2] 3 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      RightSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_right_malformed_family_has_its_exact_actual_peak caller [15, 2] 4 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      RightSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_right_malformed_family_has_its_exact_actual_peak caller [15, 2] 5 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      RightSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_right_malformed_family_has_its_exact_actual_peak caller [15, 2] 6 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      RightSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_right_malformed_family_has_its_exact_actual_peak caller [15, 2] 7 [15] regs ordinaryContext
  · simpa [SharpFixture.Expected, SharpFixture.sourceCount, SharpFixture.pendingCount,
      RightSharpExpected, ordinary_protected_context_has_five_physical_cells] using
      every_right_malformed_family_has_its_exact_actual_peak caller [15, 2] 8 [15] regs ordinaryContext

/-! ## Explicit dirty allowances and a single complete actual prefix witness -/

section DirtyAllowanceEquations
variable {K : Type} {Γ : K → Type} [Fintype K]

theorem the_dirty_base_counts_all_nine_words_and_every_protected_word
    (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    mass D ctx = D.certificate.length + D.moveReverse.length + D.path.length +
      D.source.length + D.saved.length + D.scratch.length + D.units.length +
      D.fuel.length + D.target.length + externalCells ctx := rfl

theorem the_dirty_inspector_budget_uses_the_actual_fuel_and_apply_endpoints
    (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    inspectAllowance D ctx =
      if D.certificate = [] then mass D ctx else
        let borrowed := counterFinish .borrow D
        match borrowed.result with
        | .zero => mass D ctx
        | .positive =>
            let applied := applyFinish (MoveApplyMachine.movePhase .start) borrowed.data
            match applied.result with
            | .inl _ | .inr .failure =>
                max (mass D ctx) (hAllowance (MoveApplyMachine.movePhase .start) borrowed.data ctx)
            | .inr .success =>
                max (mass D ctx)
                  (max (hAllowance (MoveApplyMachine.movePhase .start) borrowed.data ctx)
                    (inspectAllowance applied.data ctx)) := by
  rw [inspectAllowance]
  by_cases empty : D.certificate = []
  · simp only [ite_eq_left empty]
  · simp only [ite_eq_right empty]
    cases fuelResult : (counterFinish .borrow D).result with
    | zero => simp_all only
    | positive =>
        cases applyResult :
            (applyFinish (MoveApplyMachine.movePhase .start) (counterFinish .borrow D).data).result with
        | inl token => simp_all only
        | inr result => cases result <;> simp_all only

theorem dirty_apply_phase_space_retains_debt_credit_and_the_actual_result_join
    (q : MoveApplyMachine.Phase) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    hPhaseAllowance q D ctx =
      max (mass D ctx + MoveApplyMachine.phaseDebt q +
        MoveApplyMachine.phaseCredit q (applyData D))
        (hJoinAllowance (applyFinish q D).result (applyFinish q D).data ctx) := rfl

theorem dirty_counter_phase_space_uses_its_actual_returned_words
    (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    counterAllowance q D ctx = max (mass D ctx)
      (fuelJoinAllowance (FuelDispatchMachine.exitOfResult (counterFinish q D).result)
        (counterFinish q D).data ctx) := rfl

theorem all_three_fuel_join_allowances_keep_their_distinct_continuations
    (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    fuelJoinAllowance .atEnd D ctx = mass D ctx ∧
      fuelJoinAllowance .zero D ctx = mass D ctx ∧
      fuelJoinAllowance .positive D ctx =
        max (mass D ctx) (hPhaseAllowance (MoveApplyMachine.movePhase .start) D ctx) :=
  ⟨rfl, rfl, rfl⟩

theorem all_three_apply_join_allowances_keep_dirty_success_reentry
    (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    hJoinAllowance MoveApplyMachine.parseFailure D ctx = mass D ctx ∧
      hJoinAllowance MoveApplyMachine.rotationFailure D ctx = mass D ctx ∧
      hJoinAllowance MoveApplyMachine.success D ctx =
        max (mass D ctx) (inspectAllowance D ctx) := ⟨rfl, rfl, rfl⟩

theorem equality_and_both_boolean_joins_have_no_extra_space_allowance
    (D : LocalData) (ctx : ∀ k, List (Γ k)) (r : TreeEqualityMachine.Result) :
    phaseAllowance comparePhase D ctx = mass D ctx ∧
      phaseAllowance (equalityJoinPhase r) D ctx = mass D ctx := ⟨rfl, rfl⟩

end DirtyAllowanceEquations

section DirtyActualPrefixSpace
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)

theorem every_dirty_configuration_bounds_every_actual_inclusive_prefix
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : Runs (step caller) start n reached) :
    physicalCells reached ≤ allowance start :=
  prefix_stackCells_le_dirty caller start n bound reached executed

theorem one_dirty_prefix_witness_has_execution_rank_stages_frame_and_space
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, Runs (step caller) start n reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧
      reached.var = registersAt start n ∧
      reached.var.2.2 = start.var.2.2 ∧
      (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧
      physicalCells reached ≤ allowance start := by
  obtain ⟨reached, executed, rank, path, owned, zero, registers, user, frame⟩ :=
    owned_prefix_frame caller start n bound
  exact ⟨reached, executed, rank, path, owned, zero, registers, user, frame,
    prefix_stackCells_le_dirty caller start n bound reached executed⟩

omit [Fintype K] in
theorem the_exact_stage_mask_applies_to_the_same_actual_reached_configuration
    (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : Runs (step caller) start n reached) :
    reached.var = registersAt start n := prefix_reset caller start reached n bound executed

omit [Fintype K] in
include caller in
theorem the_zero_step_stage_mask_is_the_original_register_tuple
    (start : Cfg Γ Λ R) : registersAt start 0 = start.var :=
  (prefix_reset caller start start 0 (Nat.zero_le _) rfl).symm

omit [DecidableEq K] in
theorem nonowned_live_configurations_use_exactly_their_existing_physical_mass
    (start : Cfg Γ Λ R) (outside : ¬ Owned start.l) :
    allowance start = physicalCells start := nonowned_allowance start outside

theorem nonowned_prefixes_are_only_the_original_state_at_zero
    (start reached : Cfg Γ Λ R) (outside : ¬ Owned start.l) (n : Nat)
    (bound : n ≤ remainingSteps start) (executed : Runs (step caller) start n reached) :
    n = 0 ∧ reached = start ∧ reached.var = start.var ∧
      physicalCells reached = physicalCells start := by
  have clock := nonowned_remaining start outside
  have zero : n = 0 := by omega
  subst n
  have same : reached = start := Option.some.inj executed.symm
  exact ⟨rfl, same, congrArg Turing.TM2.Cfg.var same, congrArg physicalCells same⟩

end DirtyActualPrefixSpace

/-! ## Clean, represented, finite-package and installed physical specializations -/

section CleanPhysicalConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)

theorem clean_raw_inputs_bound_every_actual_physical_prefix
    (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ runSteps fuel certificate source target)
    (reached : Cfg Γ Λ R)
    (executed : Runs (step caller) (entry regs fuel certificate source target ctx) n reached) :
    physicalCells reached ≤ certificate.length + 2 * source.length + fuel.length +
      target.length + externalCells ctx := by
  have bounded := prefix_stackCells_le_dirty caller
    (entry regs fuel certificate source target ctx) n bound reached executed
  rw [entry, allowance_phase_cfg] at bounded
  exact bounded.trans (inspectAllowance_clean_le fuel certificate source target ctx)

theorem one_clean_prefix_witness_has_every_contract_and_the_closed_physical_bound
    (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ runSteps fuel certificate source target) :
    ∃ reached, Runs (step caller) (entry regs fuel certificate source target ctx) n reached ∧
      remainingSteps reached = runSteps fuel certificate source target - n ∧
      Relation.ReflTransGen (LocalStep caller) (entry regs fuel certificate source target ctx) reached ∧
      (n < runSteps fuel certificate source target ↔ Owned reached.l) ∧
      (n = 0 → reached = entry regs fuel certificate source target ctx) ∧
      reached.var = registersAt (entry (Λ := Λ) regs fuel certificate source target ctx) n ∧
      reached.var.2.2 = regs.2.2 ∧
      (∀ k, reached.stk (.inr k) = ctx k) ∧
      physicalCells reached ≤ certificate.length + 2 * source.length + fuel.length +
        target.length + externalCells ctx := by
  obtain ⟨reached, executed, rank, path, owned, zero, registers, user, frame⟩ :=
    owned_prefix_frame caller (entry regs fuel certificate source target ctx) n bound
  exact ⟨reached, executed, rank, path, owned, zero, registers, user, frame,
    clean_raw_inputs_bound_every_actual_physical_prefix caller regs fuel certificate source target ctx
      n bound reached executed⟩

theorem represented_inputs_keep_the_same_physical_prefix_witness
    (regs : Registers R) (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit)
    (ctx : ∀ k, List (Γ k)) (n : Nat)
    (bound : n ≤ runSteps fuel certificate (treeCode source) (treeCode target)) :
    ∃ reached, Runs (step caller)
        (entry regs fuel certificate (treeCode source) (treeCode target) ctx) n reached ∧
      remainingSteps reached = runSteps fuel certificate (treeCode source) (treeCode target) - n ∧
      Relation.ReflTransGen (LocalStep caller)
        (entry regs fuel certificate (treeCode source) (treeCode target) ctx) reached ∧
      (n < runSteps fuel certificate (treeCode source) (treeCode target) ↔ Owned reached.l) ∧
      (n = 0 → reached = entry regs fuel certificate (treeCode source) (treeCode target) ctx) ∧
      reached.var = registersAt (entry (Λ := Λ) regs fuel certificate (treeCode source) (treeCode target) ctx) n ∧
      reached.var.2.2 = regs.2.2 ∧
      (∀ k, reached.stk (.inr k) = ctx k) ∧
      physicalCells reached ≤ certificate.length + 2 * (treeCode source).length + fuel.length +
        (treeCode target).length + externalCells ctx :=
  one_clean_prefix_witness_has_every_contract_and_the_closed_physical_bound caller regs fuel
    certificate (treeCode source) (treeCode target) ctx n bound

theorem exact_equality_prefixes_count_the_two_actually_consumed_word_tails
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ TreeEqualityMachine.runSteps D.source D.target)
    (reached : Cfg Γ Λ R)
    (executed : Runs (step caller) (cfg (some (phaseLabel comparePhase)) regs D ctx) n reached) :
    physicalCells reached =
      mass { D with source := D.source.drop n, target := D.target.drop n } ctx :=
  equality_prefix_stackCells_exact caller D regs ctx n bound reached executed

end CleanPhysicalConnections

section FinitePackagePhysicalConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : External Λ → Statement Γ Λ R)

theorem the_actual_finite_package_has_the_same_all_state_physical_bound
    (initial : R) (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : Runs (machine caller initial).step start n reached) :
    physicalCells reached ≤ allowance start :=
  prefix_stackCells_le_dirty caller start n bound reached executed

theorem the_actual_finite_package_has_one_clean_rank_frame_and_space_witness
    (initial : R) (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ runSteps fuel certificate source target) :
    ∃ reached, Runs (machine caller initial).step (entry regs fuel certificate source target ctx) n reached ∧
      remainingSteps reached = runSteps fuel certificate source target - n ∧
      Relation.ReflTransGen (LocalStep caller) (entry regs fuel certificate source target ctx) reached ∧
      (n < runSteps fuel certificate source target ↔ Owned reached.l) ∧
      (n = 0 → reached = entry regs fuel certificate source target ctx) ∧
      reached.var = registersAt (entry (Λ := Λ) regs fuel certificate source target ctx) n ∧
      reached.var.2.2 = regs.2.2 ∧
      (∀ k, reached.stk (.inr k) = ctx k) ∧
      physicalCells reached ≤ certificate.length + 2 * source.length + fuel.length +
        target.length + externalCells ctx :=
  one_clean_prefix_witness_has_every_contract_and_the_closed_physical_bound caller regs fuel
    certificate source target ctx n bound

end FinitePackagePhysicalConnections

section ExplicitFrontEndPhysicalSpace
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement (frontEndProtectedAlphabet Γ)
  Λ (FrontEndDecoderComplement × R))

theorem a_clean_explicit_front_end_entry_has_the_closed_physical_prefix_bound
    (regs : FrontEndMachine.Registers (Option Branch × R))
    (ctx : ∀ k, List (Γ k)) (source target : BinaryTree Unit) (fuel : Bits) (certificate : Word)
    (n : Nat) (bound : n ≤ runSteps fuel certificate (treeCode source) (treeCode target))
    (reached : Cfg (frontEndProtectedAlphabet Γ) Λ (FrontEndDecoderComplement × R))
    (executed : Runs (step caller)
      (frontEndInstalledEntry regs [] [] ctx source target fuel certificate) n reached) :
    physicalCells reached ≤ certificate.length + 2 * (treeCode source).length + fuel.length +
      (treeCode target).length + externalCells ctx := by
  have bounded := clean_raw_inputs_bound_every_actual_physical_prefix caller
    (frontEndRegisterEquiv (FrontEndMachine.reset regs)) fuel certificate
    (treeCode source) (treeCode target) (frontEndSuccessContext ctx) n bound reached executed
  have cells : externalCells (frontEndSuccessContext ctx) = externalCells ctx :=
    frontEnd_success_context_cells ctx
  simpa only [cells] using bounded

theorem arbitrary_dirty_front_end_branch_words_use_the_meaningful_dirty_allowance
    (regs : FrontEndMachine.Registers (Option Branch × R)) (B O : List Branch)
    (ctx : ∀ k, List (Γ k)) (source target : BinaryTree Unit) (fuel : Bits) (certificate : Word)
    (n : Nat)
    (bound : n ≤ remainingSteps (frontEndInstalledEntry (Λ := Λ) regs B O ctx source target fuel certificate))
    (reached : Cfg (frontEndProtectedAlphabet Γ) Λ (FrontEndDecoderComplement × R))
    (executed : Runs (step caller)
      (frontEndInstalledEntry regs B O ctx source target fuel certificate) n reached) :
    physicalCells reached ≤ inspectAllowance
      (frontEndSuccessData source target fuel certificate B O) (frontEndSuccessContext ctx) := by
  have bounded := prefix_stackCells_le_dirty caller
    (frontEndInstalledEntry regs B O ctx source target fuel certificate) n bound reached executed
  rw [frontEndInstalledEntry, allowance_phase_cfg] at bounded
  exact bounded

end ExplicitFrontEndPhysicalSpace

/-! ## Sharper physical bounds for the current parsed call -/

section CurrentCallPhysicalBounds
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)

theorem a_successfully_parsed_current_call_keeps_the_sharper_two_stage_bound
    (regs : Registers R) (fuel : Bits) (certificate source target rest : Word)
    (move : RotationMove) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (n : Nat) (bound : n ≤ MoveApplyMachine.runSteps certificate [] source [] [] [])
    (reached : Cfg Γ Λ R)
    (executed : Runs (step caller)
      (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start))))
        regs (cleanData fuel certificate source target) ctx) n reached) :
    physicalCells reached ≤
      max (certificate.length + source.length) (rest.length + move.position.length + 2 * source.length) +
        fuel.length + target.length + externalCells ctx :=
  apply_clean_prefix_cells_of_some caller fuel certificate source target move rest regs ctx
    parsed n bound reached executed

theorem a_failed_current_parse_does_not_charge_unused_tree_credit
    (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) (failed : (parseMoveRun certificate).1 = none)
    (n : Nat) (bound : n ≤ MoveApplyMachine.runSteps certificate [] source [] [] [])
    (reached : Cfg Γ Λ R)
    (executed : Runs (step caller)
      (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start))))
        regs (cleanData fuel certificate source target) ctx) n reached) :
    physicalCells reached ≤ certificate.length + source.length + fuel.length +
      target.length + externalCells ctx := by
  let D := cleanData fuel certificate source target
  let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  let start : ApplyCfg Γ Λ R := MoveApplyMachine.entry (applyRegisterEquiv.symm regs)
    certificate [] source [] [] [] (applyContext D ctx)
  have mapped : applyCfg start =
      cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start)))) regs D ctx := by
    simp only [start, MoveApplyMachine.entry, applyCfg_partial]
    rfl
  obtain ⟨middle, run, _, same⟩ := apply_prefix_lift caller localCaller start n bound reached
    (by rw [mapped]; exact executed)
  have cells := MoveApplyMachine.prefix_stackCells_le_of_none localCaller certificate
    [] source [] [] [] (applyRegisterEquiv.symm regs) (applyContext D ctx) failed n bound middle run
  change stackCells reached ≤ _
  rw [same, stackCells_applyCfg]
  rw [MoveApplyMachine.principalCells, applyContext_cells] at cells
  dsimp only [D, cleanData] at cells
  simp only [List.length_nil, Nat.add_zero] at cells
  change _ ≤ certificate.length + source.length + fuel.length + target.length + contextCells ctx
  omega

end CurrentCallPhysicalBounds

/-! ## Actual packaged clean and represented execution records -/

section PackagedSourceConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : External Λ → Statement Γ Λ R) (initial : R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem actual_packaged_clean_inputs_have_the_complete_first_handoff
    (fuel : Bits) (certificate source target : Word) :
    FirstRun (machine caller initial).step (entry regs fuel certificate source target ctx)
      (runSteps fuel certificate source target) (runResult regs fuel certificate source target ctx) :=
  run_firstRun caller regs fuel certificate source target ctx

theorem actual_packaged_represented_first_booleans_match_the_source_checker
    (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit) (result : Bool) :
    FirstResult (machine caller initial).step
      (entry regs fuel certificate (treeCode source) (treeCode target) ctx) result ↔
      (checkStreamRun fuel source target certificate).1 = result :=
  represented_firstResult_iff caller regs fuel certificate source target ctx result

def actual_packaged_exact_clean_timing (fuel : Bits) (certificate source target : Word) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (entry regs fuel certificate source target ctx)
      (some (runResult regs fuel certificate source target ctx))
      (runSteps fuel certificate source target) :=
  runInTimeExact caller regs fuel certificate source target ctx

def actual_packaged_polynomial_clean_timing (fuel : Bits) (certificate source target : Word) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (entry regs fuel certificate source target ctx)
      (some (runResult regs fuel certificate source target ctx))
      ((2 * fuel.length + 3 * source.length + 7) * certificate.length + source.length + 4) :=
  runInPolynomialTime caller regs fuel certificate source target ctx

def actual_packaged_exact_represented_timing
    (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (entry regs fuel certificate (treeCode source) (treeCode target) ctx)
      (some (runResult regs fuel certificate (treeCode source) (treeCode target) ctx))
      (runSteps fuel certificate (treeCode source) (treeCode target)) :=
  representedInTimeExact caller regs fuel certificate source target ctx

def actual_packaged_polynomial_represented_timing
    (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (entry regs fuel certificate (treeCode source) (treeCode target) ctx)
      (some (runResult regs fuel certificate (treeCode source) (treeCode target) ctx))
      ((2 * fuel.length + 6 * source.numNodes + 10) * certificate.length + 2 * source.numNodes + 5) :=
  representedInPolynomialTime caller regs fuel certificate source target ctx

theorem both_actual_packaged_clean_records_store_the_exact_machine_clock
    (fuel : Bits) (certificate source target : Word) :
    (actual_packaged_exact_clean_timing caller initial regs ctx fuel certificate source target).steps =
        runSteps fuel certificate source target ∧
      (actual_packaged_polynomial_clean_timing caller initial regs ctx fuel certificate source target).steps =
        runSteps fuel certificate source target := ⟨rfl, rfl⟩

theorem both_actual_packaged_represented_records_store_the_exact_machine_clock
    (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit) :
    (actual_packaged_exact_represented_timing caller initial regs ctx fuel certificate source target).steps =
        runSteps fuel certificate (treeCode source) (treeCode target) ∧
      (actual_packaged_polynomial_represented_timing caller initial regs ctx fuel certificate source target).steps =
        runSteps fuel certificate (treeCode source) (treeCode target) := ⟨rfl, rfl⟩

end PackagedSourceConnections

/-! ## The installed owned-prefix contract retains one actual configuration -/

section InstalledCompletePrefixConnections
variable {K Λ R K' Λ' R' : Type} {Γ : K → Type} {Γ' : K' → Type}
variable [DecidableEq K] [DecidableEq K']
variable (names : StackId K ≃ K') (symbols : ∀ k, alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')
variable (caller : External Λ → Statement Γ Λ R)
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
variable (installed : ∀ label, Owned (some label) →
  ambient (labels label) =
    FrontEndMachine.Transport.statement names symbols registers labels (program caller label))

include installed in
theorem one_installed_actual_prefix_has_the_complete_source_rank_stages_and_frame
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached : Turing.TM2.Cfg Γ' Λ' R',
      (FrontEndMachine.Transport.next ambient)^[n]
        (some (installedCfg names symbols registers labels start)) = some reached ∧
      let source := (installedCfgEquiv names symbols registers labels).symm reached
      Runs (step caller) start n source ∧
        remainingSteps source = remainingSteps start - n ∧
        Relation.ReflTransGen (LocalStep caller) start source ∧
        (n < remainingSteps start ↔ Owned source.l) ∧
        (n = 0 → source = start) ∧ source.var = registersAt start n ∧
        source.var.2.2 = start.var.2.2 ∧
        ∀ k, source.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨source, executed, rank, path, owned, zero, stage, user, frame⟩ :=
    owned_prefix_frame caller start n bound
  refine ⟨installedCfg names symbols registers labels source, ?_, ?_⟩
  · rw [installed_owned_prefix names symbols registers labels caller ambient installed start n bound,
      executed]
    rfl
  · have inverse : (installedCfgEquiv names symbols registers labels).symm
        (installedCfg names symbols registers labels source) = source :=
        (installedCfgEquiv names symbols registers labels).symm_apply_apply source
    dsimp only
    rw [inverse]
    exact ⟨executed, rank, path, owned, zero, stage, user, frame⟩

include installed in
theorem one_installed_actual_dirty_prefix_has_rank_stages_frame_and_space
    [Fintype K] [Fintype K']
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached : Turing.TM2.Cfg Γ' Λ' R',
      (FrontEndMachine.Transport.next ambient)^[n]
        (some (installedCfg names symbols registers labels start)) = some reached ∧
      (let source := (installedCfgEquiv names symbols registers labels).symm reached
       Runs (step caller) start n source ∧
         remainingSteps source = remainingSteps start - n ∧
         Relation.ReflTransGen (LocalStep caller) start source ∧
         (n < remainingSteps start ↔ Owned source.l) ∧
         (n = 0 → source = start) ∧ source.var = registersAt start n ∧
         source.var.2.2 = start.var.2.2 ∧
         ∀ k, source.stk (.inr k) = start.stk (.inr k)) ∧
      (∑ k, (reached.stk k).length) ≤ allowance start := by
  obtain ⟨reached, executed, properties⟩ :=
    one_installed_actual_prefix_has_the_complete_source_rank_stages_and_frame
      names symbols registers labels caller ambient installed start n bound
  refine ⟨reached, executed, properties, ?_⟩
  exact installed_prefix_cells_of_source_bound names symbols registers labels caller ambient installed
    start n bound (allowance start)
    (fun source run => prefix_stackCells_le_dirty caller start n bound source run) reached executed

def exact_installed_clean_timing (regs : Registers R) (fuel : Bits)
    (certificate source target : Word) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels (entry regs fuel certificate source target ctx))
      (some (installedCfg names symbols registers labels (runResult regs fuel certificate source target ctx)))
      (runSteps fuel certificate source target) :=
  installed_owned_timed names symbols registers labels caller ambient installed
    (entry regs fuel certificate source target ctx)

def polynomial_installed_clean_timing (regs : Registers R) (fuel : Bits)
    (certificate source target : Word) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels (entry regs fuel certificate source target ctx))
      (some (installedCfg names symbols registers labels (runResult regs fuel certificate source target ctx)))
      ((2 * fuel.length + 3 * source.length + 7) * certificate.length + source.length + 4) where
  steps := runSteps fuel certificate source target
  evals_in_steps := (exact_installed_clean_timing names symbols registers labels caller ambient installed
    regs fuel certificate source target ctx).evals_in_steps
  steps_le_m := runSteps_le fuel certificate source target

def exact_installed_represented_timing (regs : Registers R) (fuel : Bits)
    (certificate : Word) (source target : BinaryTree Unit) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels
        (entry regs fuel certificate (treeCode source) (treeCode target) ctx))
      (some (installedCfg names symbols registers labels
        (runResult regs fuel certificate (treeCode source) (treeCode target) ctx)))
      (runSteps fuel certificate (treeCode source) (treeCode target)) :=
  exact_installed_clean_timing names symbols registers labels caller ambient installed regs fuel
    certificate (treeCode source) (treeCode target) ctx

def polynomial_installed_represented_timing (regs : Registers R) (fuel : Bits)
    (certificate : Word) (source target : BinaryTree Unit) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels
        (entry regs fuel certificate (treeCode source) (treeCode target) ctx))
      (some (installedCfg names symbols registers labels
        (runResult regs fuel certificate (treeCode source) (treeCode target) ctx)))
      ((2 * fuel.length + 6 * source.numNodes + 10) * certificate.length + 2 * source.numNodes + 5) where
  steps := runSteps fuel certificate (treeCode source) (treeCode target)
  evals_in_steps := (exact_installed_represented_timing names symbols registers labels caller ambient installed
    regs fuel certificate source target ctx).evals_in_steps
  steps_le_m := runSteps_code_le fuel certificate source target

theorem both_installed_clean_time_records_store_the_exact_clock
    (regs : Registers R) (fuel : Bits) (certificate source target : Word) (ctx : ∀ k, List (Γ k)) :
    (exact_installed_clean_timing names symbols registers labels caller ambient installed
        regs fuel certificate source target ctx).steps = runSteps fuel certificate source target ∧
      (polynomial_installed_clean_timing names symbols registers labels caller ambient installed
        regs fuel certificate source target ctx).steps = runSteps fuel certificate source target := ⟨rfl, rfl⟩

theorem both_installed_represented_time_records_store_the_exact_clock
    (regs : Registers R) (fuel : Bits) (certificate : Word) (source target : BinaryTree Unit)
    (ctx : ∀ k, List (Γ k)) :
    (exact_installed_represented_timing names symbols registers labels caller ambient installed
        regs fuel certificate source target ctx).steps =
        runSteps fuel certificate (treeCode source) (treeCode target) ∧
      (polynomial_installed_represented_timing names symbols registers labels caller ambient installed
        regs fuel certificate source target ctx).steps =
        runSteps fuel certificate (treeCode source) (treeCode target) := ⟨rfl, rfl⟩

end InstalledCompletePrefixConnections


/-! ## Exact stage changes and all-prefix frames without finite caller labels -/

section GenericStageContracts
variable {K Λ R : Type} {Γ : K → Type}

theorem the_generic_phase_mask_distinguishes_zero_before_join_and_after_join
    (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) :
    phaseRegistersAt (Λ := Λ) q regs D ctx n =
      if n = 0 then regs else if n < firstJoinSteps q D
        then phaseRegistersBeforeJoin (Λ := Λ) q regs D ctx n else resetAll regs := rfl

theorem the_fuel_component_mask_preserves_all_apply_and_caller_registers
    (q : FuelDispatchMachine.Label Empty) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) :
    phaseRegistersBeforeJoin (Λ := Λ) (.inl q) regs D ctx n = (none, regs.2) := rfl

theorem the_apply_component_mask_uses_its_actual_parser_or_position_stage
    (q : MoveApplyMachine.Label Empty) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) :
    phaseRegistersBeforeJoin (Λ := Λ) (.inr (.inl q)) regs D ctx n =
      applyRegisterEquiv (MoveApplyMachine.registersAt
        (toApplyCfg (cfg (some (phaseLabel (Λ := Λ) (.inr (.inl q)))) regs D ctx)) n) := rfl

theorem the_equality_component_mask_preserves_fuel_branch_and_caller_registers
    (q : TreeEqualityMachine.Label Empty) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) :
    phaseRegistersBeforeJoin (Λ := Λ) (.inr (.inr q)) regs D ctx n =
      (regs.1, ((regs.2.1.1, (none, none)), regs.2.2)) := rfl

variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

theorem one_nonphysical_prefix_witness_has_exact_rank_stages_and_every_protected_word
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, Runs (step caller) start n reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧ reached.var = registersAt start n ∧
      reached.var.2.2 = start.var.2.2 ∧
      ∀ k, reached.stk (.inr k) = start.stk (.inr k) :=
  owned_prefix_frame caller start n bound

theorem every_actual_prefix_after_the_first_paid_join_has_all_four_temporaries_reset
    (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (afterJoin : firstJoinSteps q D ≤ n) (bound : n ≤ phaseSteps q D)
    (reached : Cfg Γ Λ R)
    (executed : Runs (step caller) (cfg (some (phaseLabel q)) regs D ctx) n reached) :
    reached.var = resetAll regs :=
  prefix_reset_after_firstJoin caller q D regs ctx n reached afterJoin bound executed

end GenericStageContracts

section PackagedSharedDirtyWitness
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : External Λ → Statement Γ Λ R)

theorem the_finite_package_has_one_dirty_execution_rank_stage_frame_and_space_witness
    (initial : R) (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, Runs (machine caller initial).step start n reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧ reached.var = registersAt start n ∧
      reached.var.2.2 = start.var.2.2 ∧
      (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧
      physicalCells reached ≤ allowance start :=
  one_dirty_prefix_witness_has_execution_rank_stages_frame_and_space caller start n bound

end PackagedSharedDirtyWitness

section InstalledSharedCleanWitness
variable {K Λ R K' Λ' R' : Type} {Γ : K → Type} {Γ' : K' → Type}
variable [DecidableEq K] [DecidableEq K'] [Fintype K] [Fintype K']
variable (names : StackId K ≃ K') (symbols : ∀ k, alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')
variable (caller : External Λ → Statement Γ Λ R)
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
variable (installed : ∀ label, Owned (some label) →
  ambient (labels label) =
    FrontEndMachine.Transport.statement names symbols registers labels (program caller label))

include installed in
theorem one_installed_clean_prefix_has_the_same_exact_rank_stages_frame_and_closed_space
    (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ runSteps fuel certificate source target) :
    ∃ reached : Turing.TM2.Cfg Γ' Λ' R',
      (FrontEndMachine.Transport.next ambient)^[n]
        (some (installedCfg names symbols registers labels (entry regs fuel certificate source target ctx))) =
          some reached ∧
      (let pulledBack := (installedCfgEquiv names symbols registers labels).symm reached
       Runs (step caller) (entry regs fuel certificate source target ctx) n pulledBack ∧
         remainingSteps pulledBack = runSteps fuel certificate source target - n ∧
         Relation.ReflTransGen (LocalStep caller) (entry regs fuel certificate source target ctx) pulledBack ∧
         (n < runSteps fuel certificate source target ↔ Owned pulledBack.l) ∧
         (n = 0 → pulledBack = entry regs fuel certificate source target ctx) ∧
         pulledBack.var = registersAt (entry (Λ := Λ) regs fuel certificate source target ctx) n ∧
         pulledBack.var.2.2 = regs.2.2 ∧ ∀ k, pulledBack.stk (.inr k) = ctx k) ∧
      (∑ k, (reached.stk k).length) ≤ certificate.length + 2 * source.length + fuel.length +
        target.length + externalCells ctx := by
  obtain ⟨reached, executed, properties⟩ :=
    one_installed_actual_prefix_has_the_complete_source_rank_stages_and_frame
      names symbols registers labels caller ambient installed
      (entry regs fuel certificate source target ctx) n bound
  refine ⟨reached, executed, properties, ?_⟩
  exact installed_prefix_cells_of_source_bound names symbols registers labels caller ambient installed
    (entry regs fuel certificate source target ctx) n bound
    (certificate.length + 2 * source.length + fuel.length + target.length + externalCells ctx)
    (fun pulledBack run => clean_raw_inputs_bound_every_actual_physical_prefix caller regs fuel certificate
      source target ctx n bound pulledBack run) reached executed

end InstalledSharedCleanWitness


/-! ## Parsed raw calls retain actual stopped paths and charged recursive runs -/

section ActualRawRecursion
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

theorem a_parsed_raw_call_has_its_literal_failure_or_actual_recursive_first_run
    (regs : Registers R) (fuel nextFuel : Bits) (certificate source target : Word)
    (move : RotationMove) (rest : Word) (ctx : ∀ k, List (Γ k))
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest)) :
    ∃ result output path,
      MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start) (moveCleanData certificate source) =
        ⟨.inr result, { certificate := rest, source := output, path := path },
          2 * move.position.length + 4 +
            PositionedRotationMachine.runSteps move.direction source move.position⟩ ∧
      output.length = source.length ∧
      (∃ consumed, move.position = consumed ++ path) ∧
      (result = .failure → output = source) ∧
      (result = .failure →
        FirstRun (step caller) (entry regs fuel certificate source target ctx)
          (Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
            (2 * move.position.length + 4 +
              PositionedRotationMachine.runSteps move.direction source move.position) + 3)
          (cfg (some (resultLabel false)) (resetAll regs)
            { (cleanData nextFuel rest source target) with path := path } ctx)) ∧
      (result = .success → path = [] ∧
        FirstRun (step caller) (entry regs fuel certificate source target ctx)
          (Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
            (2 * move.position.length + 4 +
              PositionedRotationMachine.runSteps move.direction source move.position) + 3 +
            runSteps nextFuel rest output target)
          (runResult (resetAll regs) nextFuel rest output target ctx)) := by
  obtain ⟨result, output, path, applied, length, suffix, restored, failed, succeeded⟩ :=
    runEvaluation_after_parse fuel nextFuel certificate source target move rest decremented parsed
  refine ⟨result, output, path, applied, length, suffix, restored, ?_, ?_⟩
  · intro failure
    exact clean_first_run_from_the_complete_evaluation caller regs ctx fuel certificate source target
      false _ _ (failed failure)
  · intro success
    subst result
    obtain ⟨empty, _⟩ := succeeded rfl
    subst path
    have actual := run_firstRun caller regs fuel certificate source target ctx
    rw [runSteps_step fuel nextFuel certificate source target move rest output decremented parsed applied,
      runResult_step regs fuel nextFuel certificate source target move rest output ctx decremented parsed applied] at actual
    exact ⟨rfl, actual⟩

end ActualRawRecursion


/-! The second finite label package uses its real one-input initializer too. -/
theorem both_literal_inputs_of_the_two_label_package_use_actual_initList
    (caller : External (Fin 2) → Statement IndependentAlphabet (Fin 2) Bool)
    (initial : Bool) :
    FirstRun (twoLabelPackage caller initial).step
      (Turing.initList (twoLabelPackage caller initial) ([] : Word)) 4
      (cfg (some (resultLabel true)) (clean initial) {} (fun _ => [])) ∧
    FirstRun (twoLabelPackage caller initial).step
      (Turing.initList (twoLabelPackage caller initial) ([15] : Word)) 4
      (cfg (some (resultLabel false)) (clean initial) {certificate := [15]} (fun _ => [])) :=
  ⟨machine_init_first_return caller initial [], machine_init_first_return caller initial [15]⟩

end Examples.RotationCertificateStreamMachine
