import Applications.Resources.RotationCertificate.FrontEndStreamMachine
import Examples.RotationCertificateStreamMachine
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Independent connected clients of the closed framed verifier

The literal records retain the 36 original raw inputs and the separately fixed
post-architecture cleanup, emitter, join, dirty-front-end and liveness cases.
Their complete endpoints, clocks and inclusive peaks come from the immutable
independent expectations. Expected values are not defined by the producer's
proof-side evaluator. The 96 owned domains are a separate universal obligation.

Validation and review evidence is recorded separately from these contracts.
-/

namespace Examples.RotationCertificateFrontEndStreamMachine

open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.FrontEndStreamMachine

def IndependentAlphabet : Fin 2 → Type := Fin.cases Bool (fun _ => Tag)

instance independentAlphabetFintype (k : Fin 2) : Fintype (IndependentAlphabet k) :=
  Fin.cases (motive := fun k : Fin 2 => Fintype (IndependentAlphabet k))
    (inferInstance : Fintype Bool) (fun _ => (inferInstance : Fintype Tag)) k

def independentWords (bits : Bits) (tags : Word) : ∀ k, List (IndependentAlphabet k) :=
  Fin.cases bits (fun _ => tags)

def ordinaryContext : ∀ k, List (IndependentAlphabet k) :=
  independentWords [true, false, true] [11, 15]

def emptyContext {K : Type} {Γ : K → Type} : ∀ k, List (Γ k) := fun _ => []

structure CommonFields where
  treeTag : Option Tag := none
  treeUnit : Option Unit := none
  b0 : Option Bool := none
  b1 : Option Bool := none
  b2 : Option Bool := none
  b3 : Option Bool := none
  decoderTag : Option Tag := none
  branch : Option Branch := none
  deriving DecidableEq

def CommonFields.withUser {R : Type} (fields : CommonFields) (value : R) : Registers R :=
  ((fields.treeTag, fields.treeUnit),
    ⟨fields.b0, fields.b1, fields.b2, fields.b3, fields.decoderTag⟩,
    (fields.branch, value))

def staleFields : CommonFields :=
  ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩

def stale (value : Bool) : Registers Bool := staleFields.withUser value

def clean {R : Type} (value : R) : Registers R := ({} : CommonFields).withUser value

abbrev ExampleCfg := Cfg IndependentAlphabet Unit Bool
abbrev ExampleCaller := Unit → Statement IndependentAlphabet Unit Bool
abbrev TwoLabelCfg := Cfg IndependentAlphabet (Fin 2) Bool
abbrev InfiniteLabelCfg := Cfg IndependentAlphabet Nat Bool

def localData (w0 w1 w2 w3 w4 : Bits) (w5 w6 w7 w8 w9 w10 : Word)
    (w11 : List Unit) (w12 : Bits) (w13 w14 : List Branch) (w15 : Bits) : LocalData :=
  { framedRaw := w0, frameFirstReverse := w1, frameCertReverse := w2,
    inputBits := w3, certificateBits := w4, inputRaw := w5, decodeReverse := w6,
    certificateWord := w7, sourceTree := w8, targetTree := w9, treeReverse := w10,
    pending := w11, bitsReverse := w12, moveReverse := w13, path := w14, fuel := w15 }

def rawEntryPhase : Phase := .inl (FrontEndMachine.framerLabel .scanPrefix)

/-- Actual optional iteration, including the separate outer-none state. -/
def Runs {K Λ R : Type} {Γ : K → Type}
    (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (start : Cfg Γ Λ R) (ticks : Nat) (finish : Cfg Γ Λ R) : Prop :=
  (fun state : Option (Cfg Γ Λ R) => state.bind transition)^[ticks] (some start) = some finish

/-- The first boundary can be a live halt or an initially external identity. -/
def FirstBoundary {K Λ R : Type} {Γ : K → Type}
    (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (start : Cfg Γ Λ R) (ticks : Nat) (finish : Cfg Γ Λ R) : Prop :=
  Runs transition start ticks finish ∧ ¬ Owned finish.l ∧
    ∀ n, n < ticks → ∃ reached, Runs transition start n reached ∧ Owned reached.l

/-- Actual live halt, with strict earlier ownership; no eventual-caller claim. -/
def FirstHalt {K Λ R : Type} {Γ : K → Type}
    (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (start : Cfg Γ Λ R) (ticks : Nat) (finish : Cfg Γ Λ R) : Prop :=
  Runs transition start ticks finish ∧ finish.l = none ∧
    ∀ n, n < ticks → ∃ reached, Runs transition start n reached ∧ Owned reached.l

def physicalCells {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (c : Cfg Γ Λ R) : Nat := ∑ k, (c.stk k).length

def externalCells {K : Type} {Γ : K → Type} [Fintype K]
    (ctx : ∀ k, List (Γ k)) : Nat := ∑ k, (ctx k).length

/-- Both the universal inclusive-prefix bound and an actual attained witness. -/
def ExactPeak {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (start : Cfg Γ Λ R) (ticks peak : Nat) : Prop :=
  (∀ n, n ≤ ticks → ∀ reached, Runs transition start n reached → physicalCells reached ≤ peak) ∧
  ∃ n reached, n ≤ ticks ∧ Runs transition start n reached ∧ physicalCells reached = peak

structure ClosedFixture where
  name : String
  phase : Phase
  fields : CommonFields
  before : LocalData
  after : LocalData
  ticks : Nat
  peak : Nat

def ClosedFixture.start {K Λ R : Type} {Γ : K → Type}
    (c : ClosedFixture) (value : R) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (phaseLabel c.phase)) (c.fields.withUser value) c.before ctx

def ClosedFixture.finish {K Λ R : Type} {Γ : K → Type}
    (c : ClosedFixture) (value : R) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg none (clean value) c.after ctx

def ClosedFixture.RunExpected {K Λ R : Type} {Γ : K → Type}
    (c : ClosedFixture) (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (value : R) (ctx : ∀ k, List (Γ k)) : Prop :=
  FirstHalt transition (c.start value ctx) c.ticks (c.finish value ctx)

def ClosedFixture.Expected {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (c : ClosedFixture) (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (value : R) (ctx : ∀ k, List (Γ k)) : Prop :=
  c.RunExpected transition value ctx ∧
  ExactPeak transition (c.start value ctx) c.ticks (c.peak + externalCells ctx)

inductive FrontEndKind
  | frameFailure | inputDecodeFailure | inputParseFailure | certificateDecodeFailure | success
  deriving DecidableEq

def FrontEndKind.registers {R : Type} : FrontEndKind → Registers R → Registers R
  | .frameFailure => FrontEndMachine.resetFramer
  | .inputDecodeFailure => FrontEndMachine.afterInputDecoder
  | .inputParseFailure | .certificateDecodeFailure | .success => FrontEndMachine.reset

structure StreamFixture where
  before : LocalData
  after : LocalData
  ticks : Nat
  peak : Nat
  result : Bool

structure RawFixture where
  name : String
  raw : Bits
  result : Bool
  frontEndKind : FrontEndKind
  frontEndTicks : Nat
  frontEndAfter : LocalData
  stream : Option StreamFixture
  joinTicks : Nat
  beforeClear : LocalData
  residualCells : Nat
  clearTicks : Nat
  after : LocalData
  ticks : Nat
  peak : Nat

def RawFixture.start {K Λ R : Type} {Γ : K → Type}
    (c : RawFixture) (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (phaseLabel rawEntryPhase)) regs { framedRaw := c.raw } ctx

def RawFixture.finish {K Λ R : Type} {Γ : K → Type}
    (c : RawFixture) (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg none (fullReset regs) c.after ctx

def RawFixture.frontEndFinish {K Λ R : Type} {Γ : K → Type}
    (c : RawFixture) (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (phaseLabel (if c.frontEndKind = .success then dispatchPhase else rejectPhase)))
    (c.frontEndKind.registers regs) c.frontEndAfter ctx

def RawFixture.IntermediateExpected {K Λ R : Type} {Γ : K → Type}
    (c : RawFixture) (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  Runs transition (c.start regs ctx) c.frontEndTicks (c.frontEndFinish regs ctx) ∧
  match c.stream with
  | none => Runs transition (c.start regs ctx) (c.frontEndTicks + 1)
      (cfg (some (clearLabel 0)) (answerRegisters false regs) c.beforeClear ctx)
  | some s =>
      Runs transition (c.start regs ctx) (c.frontEndTicks + 1)
        (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase)))
          (fullReset regs) s.before ctx) ∧
      Runs transition (c.start regs ctx) (c.frontEndTicks + 1 + s.ticks)
        (cfg (some (phaseLabel (resultPhase s.result))) (fullReset regs) s.after ctx) ∧
      Runs transition (c.start regs ctx) (c.frontEndTicks + 1 + s.ticks + 1)
        (cfg (some (clearLabel 0)) (answerRegisters s.result regs) c.beforeClear ctx)

def RawFixture.RunExpected {K Λ R : Type} {Γ : K → Type}
    (c : RawFixture) (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  FirstHalt transition (c.start regs ctx) c.ticks (c.finish regs ctx)

def RawFixture.StreamPeakExpected {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (c : RawFixture) (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  match c.stream with
  | none => True
  | some segment => ExactPeak transition
      (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase)))
        (fullReset regs) segment.before ctx) segment.ticks (segment.peak + externalCells ctx)

def RawFixture.Expected {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (c : RawFixture) (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  c.RunExpected transition regs ctx ∧ c.IntermediateExpected transition regs ctx ∧
  c.StreamPeakExpected transition regs ctx ∧
  ExactPeak transition (c.start regs ctx) c.ticks (c.peak + externalCells ctx)

def RawFixture.toClosed (c : RawFixture) : ClosedFixture :=
  ⟨c.name, rawEntryPhase, staleFields, { framedRaw := c.raw }, c.after, c.ticks, c.peak⟩

structure CleanupFixture extends ClosedFixture where
  index : Fin 16

structure EmitFixture extends ClosedFixture

structure JoinFixture extends ClosedFixture where
  nextPhase : Phase
  nextFields : CommonFields
  stream : Option StreamFixture

structure DirtyFrontEndFixture extends ClosedFixture where
  frontEndTicks : Nat
  frontEndAfter : LocalData
  stream : StreamFixture
  physicalPath : List Branch

structure Boundary where
  ticks : Nat
  phase : Option Phase
  fields : CommonFields
  words : LocalData
  cells : Nat

def Boundary.reached {K Λ R : Type} {Γ : K → Type}
    (boundary : Boundary) (value : R) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (boundary.phase.map phaseLabel) (boundary.fields.withUser value) boundary.words ctx

def Boundary.Expected {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (boundary : Boundary) (fixture : ClosedFixture)
    (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R)) (value : R) (ctx : ∀ k, List (Γ k)) : Prop :=
  Runs transition (fixture.start value ctx) boundary.ticks (boundary.reached value ctx) ∧
  physicalCells (boundary.reached (Λ := Λ) value ctx) = boundary.cells + externalCells ctx

inductive LivenessFixture
  | liveHalt (name : String) (fields : CommonFields) (words : LocalData) (peak : Nat)
  | outerNone (name : String)
  | externalAllocator (name : String) (label : Nat) (fields : CommonFields)
      (words : LocalData) (afterBits : Bits) (afterTags : Word) (afterCells : Nat)

/-! ## Literal fixed raw cases -/
def raw_F01 : RawFixture where
  name := "raw/F01"
  raw := []
  result := false
  frontEndKind := .frameFailure
  frontEndTicks := 2
  frontEndAfter := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []
  stream := none
  joinTicks := 1
  beforeClear := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []
  residualCells := 0
  clearTicks := 17
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 20
  peak := 1

def raw_F02 : RawFixture where
  name := "raw/F02"
  raw := [false]
  result := false
  frontEndKind := .frameFailure
  frontEndTicks := 2
  frontEndAfter := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []
  stream := none
  joinTicks := 1
  beforeClear := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []
  residualCells := 0
  clearTicks := 17
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 20
  peak := 1

def raw_F03 : RawFixture where
  name := "raw/F03"
  raw := [false, true]
  result := false
  frontEndKind := .frameFailure
  frontEndTicks := 4
  frontEndAfter := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []
  stream := none
  joinTicks := 1
  beforeClear := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []
  residualCells := 0
  clearTicks := 17
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 22
  peak := 2

def raw_F04 : RawFixture where
  name := "raw/F04"
  raw := [false, true, false]
  result := false
  frontEndKind := .frameFailure
  frontEndTicks := 4
  frontEndAfter := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []
  stream := none
  joinTicks := 1
  beforeClear := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []
  residualCells := 0
  clearTicks := 17
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 22
  peak := 3

def raw_F05 : RawFixture where
  name := "raw/F05"
  raw := [true]
  result := false
  frontEndKind := .inputParseFailure
  frontEndTicks := 11
  frontEndAfter := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []
  stream := none
  joinTicks := 1
  beforeClear := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []
  residualCells := 0
  clearTicks := 17
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 29
  peak := 1

def raw_F06 : RawFixture where
  name := "raw/F06"
  raw := [true, true]
  result := false
  frontEndKind := .inputParseFailure
  frontEndTicks := 13
  frontEndAfter := localData [] [] [] [] [true] [] [] [] [] [] [] [] [] [] [] []
  stream := none
  joinTicks := 1
  beforeClear := localData [] [] [] [] [true] [] [] [] [] [] [] [] [] [] [] []
  residualCells := 1
  clearTicks := 18
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 32
  peak := 2

def raw_F07 : RawFixture where
  name := "raw/F07"
  raw := [false, true, true]
  result := false
  frontEndKind := .inputDecodeFailure
  frontEndTicks := 8
  frontEndAfter := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []
  stream := none
  joinTicks := 1
  beforeClear := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []
  residualCells := 0
  clearTicks := 17
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 26
  peak := 3

def raw_F08 : RawFixture where
  name := "raw/F08"
  raw := [false, true, true, false, true, true]
  result := false
  frontEndKind := .inputDecodeFailure
  frontEndTicks := 14
  frontEndAfter := localData [] [] [] [] [false, true, true] [] [] [] [] [] [] [] [] [] [] []
  stream := none
  joinTicks := 1
  beforeClear := localData [] [] [] [] [false, true, true] [] [] [] [] [] [] [] [] [] [] []
  residualCells := 3
  clearTicks := 20
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 35
  peak := 6

def raw_I01 : RawFixture where
  name := "raw/I01"
  raw := [false, false, false, false, false, false, false, false, true]
  result := false
  frontEndKind := .inputParseFailure
  frontEndTicks := 25
  frontEndAfter := localData [] [] [] [] [] [0] [] [] [] [] [] [] [] [] [] []
  stream := none
  joinTicks := 1
  beforeClear := localData [] [] [] [] [] [0] [] [] [] [] [] [] [] [] [] []
  residualCells := 1
  clearTicks := 18
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 44
  peak := 9

def raw_I02 : RawFixture where
  name := "raw/I02"
  raw := [false, true, false, true, false, true, false, true, true, true]
  result := false
  frontEndKind := .inputParseFailure
  frontEndTicks := 23
  frontEndAfter := localData [] [] [] [] [true] [15] [] [] [] [] [] [] [] [] [] []
  stream := none
  joinTicks := 1
  beforeClear := localData [] [] [] [] [true] [15] [] [] [] [] [] [] [] [] [] []
  residualCells := 2
  clearTicks := 19
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 43
  peak := 10

def raw_I03 : RawFixture where
  name := "raw/I03"
  raw := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, true, false, false, true]
  result := false
  frontEndKind := .inputParseFailure
  frontEndTicks := 55
  frontEndAfter := localData [] [] [] [] [] [0, 0, 2, 5] [] [] [] [] [] [] [] [] [] []
  stream := none
  joinTicks := 1
  beforeClear := localData [] [] [] [] [] [0, 0, 2, 5] [] [] [] [] [] [] [] [] [] []
  residualCells := 4
  clearTicks := 21
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 77
  peak := 33

def raw_I04 : RawFixture where
  name := "raw/I04"
  raw := [false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, false, true]
  result := false
  frontEndKind := .inputParseFailure
  frontEndTicks := 92
  frontEndAfter := localData [] [] [] [] [] [0, 2, 0, 2, 5, 0] [] [] [] [] [] [] [] [] [] []
  stream := none
  joinTicks := 1
  beforeClear := localData [] [] [] [] [] [0, 2, 0, 2, 5, 0] [] [] [] [] [] [] [] [] [] []
  residualCells := 6
  clearTicks := 23
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 116
  peak := 49

def raw_I05 : RawFixture where
  name := "raw/I05"
  raw := [false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, true, false, true, false, true, false, true, false, false, false, true, false, false, true]
  result := false
  frontEndKind := .inputParseFailure
  frontEndTicks := 88
  frontEndAfter := localData [] [] [] [] [] [0, 2, 0, 2, 15, 5] [] [] [] [] [] [] [] [] [] []
  stream := none
  joinTicks := 1
  beforeClear := localData [] [] [] [] [] [0, 2, 0, 2, 15, 5] [] [] [] [] [] [] [] [] [] []
  residualCells := 6
  clearTicks := 23
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 112
  peak := 49

def raw_I06 : RawFixture where
  name := "raw/I06"
  raw := [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, true, false, true, false, true, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, true, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, true, false, true, true, false, false, true, false, true]
  result := false
  frontEndKind := .inputParseFailure
  frontEndTicks := 154
  frontEndAfter := localData [] [] [] [] [false, true, true, false, false, true, false, true] [1, 0, 1, 15, 2, 1, 1, 0, 15, 2, 4, 5] [] [] [] [] [] [] [] [] [] []
  stream := none
  joinTicks := 1
  beforeClear := localData [] [] [] [] [false, true, true, false, false, true, false, true] [1, 0, 1, 15, 2, 1, 1, 0, 15, 2, 4, 5] [] [] [] [] [] [] [] [] [] []
  residualCells := 20
  clearTicks := 37
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 192
  peak := 105

def raw_I07 : RawFixture where
  name := "raw/I07"
  raw := [false, true, false, true, false, true, false, true, false, false, false, true, false, false, false, false, false, true, false, true, false, true, false, true, false, false, false, true, false, false, false, false, false, true, false, false, false, true, false, false, true]
  result := false
  frontEndKind := .inputParseFailure
  frontEndTicks := 61
  frontEndAfter := localData [] [] [] [] [] [15, 2, 15, 2, 5] [] [] [] [] [] [] [] [] [] []
  stream := none
  joinTicks := 1
  beforeClear := localData [] [] [] [] [] [15, 2, 15, 2, 5] [] [] [] [] [] [] [] [] [] []
  residualCells := 5
  clearTicks := 22
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 84
  peak := 41

def raw_C01 : RawFixture where
  name := "raw/C01"
  raw := [false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, true, false, false, true, true]
  result := false
  frontEndKind := .certificateDecodeFailure
  frontEndTicks := 73
  frontEndAfter := localData [] [] [] [] [] [] [] [] [0] [0] [] [] [] [] [] []
  stream := none
  joinTicks := 1
  beforeClear := localData [] [] [] [] [] [] [] [] [0] [0] [] [] [] [] [] []
  residualCells := 2
  clearTicks := 19
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 93
  peak := 42

def raw_C02 : RawFixture where
  name := "raw/C02"
  raw := [false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, true, false, false, false, false, false, true, false, true, false, false, false, false, false, true, false, false, false, true, false, false, true, true, true, true, true, true]
  result := false
  frontEndKind := .certificateDecodeFailure
  frontEndTicks := 107
  frontEndAfter := localData [] [] [] [] [] [] [] [] [0] [0] [] [] [] [] [] [false, false]
  stream := none
  joinTicks := 1
  beforeClear := localData [] [] [] [] [] [] [] [] [0] [0] [] [] [] [] [] [false, false]
  residualCells := 4
  clearTicks := 21
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 129
  peak := 62

def raw_C03 : RawFixture where
  name := "raw/C03"
  raw := [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, true, false, true, true, false, false, true, false, true, false]
  result := false
  frontEndKind := .certificateDecodeFailure
  frontEndTicks := 201
  frontEndAfter := localData [] [] [] [] [] [] [] [] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [true]
  stream := none
  joinTicks := 1
  beforeClear := localData [] [] [] [] [] [] [] [] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [true]
  residualCells := 11
  clearTicks := 28
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 230
  peak := 122

def raw_V01 : RawFixture where
  name := "raw/V01"
  raw := [false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, true, false, false, true]
  result := true
  frontEndKind := .success
  frontEndTicks := 71
  frontEndAfter := localData [] [] [] [] [] [] [] [] [0] [0] [] [] [] [] [] []
  stream := some { before := localData [] [] [] [] [] [] [] [] [0] [0] [] [] [] [] [] [], after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [], ticks := 5, peak := 2, result := true }
  joinTicks := 2
  beforeClear := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []
  residualCells := 0
  clearTicks := 17
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 95
  peak := 41

def raw_V02 : RawFixture where
  name := "raw/V02"
  raw := [false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, true, false, false, true]
  result := false
  frontEndKind := .success
  frontEndTicks := 95
  frontEndAfter := localData [] [] [] [] [] [] [] [] [0] [1, 0, 0] [] [] [] [] [] []
  stream := some { before := localData [] [] [] [] [] [] [] [] [0] [1, 0, 0] [] [] [] [] [] [], after := localData [] [] [] [] [] [] [] [] [] [0, 0] [] [] [] [] [] [], ticks := 4, peak := 4, result := false }
  joinTicks := 2
  beforeClear := localData [] [] [] [] [] [] [] [] [] [0, 0] [] [] [] [] [] []
  residualCells := 2
  clearTicks := 19
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 120
  peak := 57

def raw_V03 : RawFixture where
  name := "raw/V03"
  raw := [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, true, false, true, true, false, false, true, false, true]
  result := true
  frontEndKind := .success
  frontEndTicks := 199
  frontEndAfter := localData [] [] [] [] [] [] [] [6, 10] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [true]
  stream := some { before := localData [] [] [] [] [] [] [] [6, 10] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [true], after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false], ticks := 25, peak := 13, result := true }
  joinTicks := 2
  beforeClear := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  residualCells := 1
  clearTicks := 18
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 244
  peak := 121

def raw_V04 : RawFixture where
  name := "raw/V04"
  raw := [false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, true, true, true, true, false, false, true, false, true]
  result := true
  frontEndKind := .success
  frontEndTicks := 199
  frontEndAfter := localData [] [] [] [] [] [] [] [7, 10] [1, 1, 0, 0, 0] [1, 0, 1, 0, 0] [] [] [] [] [] [true]
  stream := some { before := localData [] [] [] [] [] [] [] [7, 10] [1, 1, 0, 0, 0] [1, 0, 1, 0, 0] [] [] [] [] [] [true], after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false], ticks := 24, peak := 13, result := true }
  joinTicks := 2
  beforeClear := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  residualCells := 1
  clearTicks := 18
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 243
  peak := 121

def raw_V05 : RawFixture where
  name := "raw/V05"
  raw := [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, true, false, true, true, false, false, true, false, true, true, true, true, false, false, true, false, true]
  result := true
  frontEndKind := .success
  frontEndTicks := 231
  frontEndAfter := localData [] [] [] [] [] [] [] [6, 10, 7, 10] [1, 0, 1, 0, 0] [1, 0, 1, 0, 0] [] [] [] [] [] [false, true]
  stream := some { before := localData [] [] [] [] [] [] [] [6, 10, 7, 10] [1, 0, 1, 0, 0] [1, 0, 1, 0, 0] [] [] [] [] [] [false, true], after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false, false], ticks := 42, peak := 16, result := true }
  joinTicks := 2
  beforeClear := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false, false]
  residualCells := 2
  clearTicks := 19
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 294
  peak := 137

def raw_V06 : RawFixture where
  name := "raw/V06"
  raw := [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, true, false, true, true, false, false, true, false, true, true, true, true, false, false, true, false, true]
  result := false
  frontEndKind := .success
  frontEndTicks := 219
  frontEndAfter := localData [] [] [] [] [] [] [] [6, 10, 7, 10] [1, 0, 1, 0, 0] [1, 0, 1, 0, 0] [] [] [] [] [] [true]
  stream := some { before := localData [] [] [] [] [] [] [] [6, 10, 7, 10] [1, 0, 1, 0, 0] [1, 0, 1, 0, 0] [] [] [] [] [] [true], after := localData [] [] [] [] [] [] [] [7, 10] [1, 1, 0, 0, 0] [1, 0, 1, 0, 0] [] [] [] [] [] [false], ticks := 22, peak := 15, result := false }
  joinTicks := 2
  beforeClear := localData [] [] [] [] [] [] [] [7, 10] [1, 1, 0, 0, 0] [1, 0, 1, 0, 0] [] [] [] [] [] [false]
  residualCells := 13
  clearTicks := 30
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 273
  peak := 129

def raw_V07 : RawFixture where
  name := "raw/V07"
  raw := [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, true, false, false, false, false, false, true, false, true, false, false, false, false, false, true, false, false, false, true, false, false, true, false, true, true, false, false, true, false, true]
  result := false
  frontEndKind := .success
  frontEndTicks := 211
  frontEndAfter := localData [] [] [] [] [] [] [] [6, 10] [1, 0, 1, 0, 0] [1, 0, 1, 0, 0] [] [] [] [] [] [false, false]
  stream := some { before := localData [] [] [] [] [] [] [] [6, 10] [1, 0, 1, 0, 0] [1, 0, 1, 0, 0] [] [] [] [] [] [false, false], after := localData [] [] [] [] [] [] [] [6, 10] [1, 0, 1, 0, 0] [1, 0, 1, 0, 0] [] [] [] [] [] [false, false], ticks := 8, peak := 14, result := false }
  joinTicks := 2
  beforeClear := localData [] [] [] [] [] [] [] [6, 10] [1, 0, 1, 0, 0] [1, 0, 1, 0, 0] [] [] [] [] [] [false, false]
  residualCells := 14
  clearTicks := 31
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 252
  peak := 129

def raw_V08 : RawFixture where
  name := "raw/V08"
  raw := [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, true, false, false, false, false, false, true, false, true, false, false, false, false, false, true, false, false, false, true, false, false, true, false, true, true, false, false, true, false, true]
  result := true
  frontEndKind := .success
  frontEndTicks := 223
  frontEndAfter := localData [] [] [] [] [] [] [] [6, 10] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [true, false, false]
  stream := some { before := localData [] [] [] [] [] [] [] [6, 10] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [true, false, false], after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false, false, false], ticks := 25, peak := 15, result := true }
  joinTicks := 2
  beforeClear := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false, false, false]
  residualCells := 3
  clearTicks := 20
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 270
  peak := 137

def raw_V09 : RawFixture where
  name := "raw/V09"
  raw := [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, true, false, true, true, false]
  result := false
  frontEndKind := .success
  frontEndTicks := 189
  frontEndAfter := localData [] [] [] [] [] [] [] [6] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [true]
  stream := some { before := localData [] [] [] [] [] [] [] [6] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [true], after := localData [] [] [] [] [] [] [] [6] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [false], ticks := 9, peak := 12, result := false }
  joinTicks := 2
  beforeClear := localData [] [] [] [] [] [] [] [6] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [false]
  residualCells := 12
  clearTicks := 29
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 229
  peak := 117

def raw_V10 : RawFixture where
  name := "raw/V10"
  raw := [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, true, false, true, true, false, true, true, true, true, false, true, false, true]
  result := false
  frontEndKind := .success
  frontEndTicks := 209
  frontEndAfter := localData [] [] [] [] [] [] [] [6, 15, 10] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [true]
  stream := some { before := localData [] [] [] [] [] [] [] [6, 15, 10] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [true], after := localData [] [] [] [] [] [] [] [6, 15, 10] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [false], ticks := 9, peak := 14, result := false }
  joinTicks := 2
  beforeClear := localData [] [] [] [] [] [] [] [6, 15, 10] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [false]
  residualCells := 14
  clearTicks := 31
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 251
  peak := 125

def raw_V11 : RawFixture where
  name := "raw/V11"
  raw := [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, true, false, true, true, false, false, false, false, true, false, true, false, true]
  result := false
  frontEndKind := .success
  frontEndTicks := 209
  frontEndAfter := localData [] [] [] [] [] [] [] [6, 8, 10] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [true]
  stream := some { before := localData [] [] [] [] [] [] [] [6, 8, 10] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [true], after := localData [] [] [] [] [] [] [] [] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [false], ticks := 17, peak := 14, result := false }
  joinTicks := 2
  beforeClear := localData [] [] [] [] [] [] [] [] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [false]
  residualCells := 11
  clearTicks := 28
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 256
  peak := 125

def raw_V12 : RawFixture where
  name := "raw/V12"
  raw := [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, true, true, true, true, false, false, true, false, true]
  result := false
  frontEndKind := .success
  frontEndTicks := 199
  frontEndAfter := localData [] [] [] [] [] [] [] [7, 10] [1, 0, 1, 0, 0] [1, 0, 1, 0, 0] [] [] [] [] [] [true]
  stream := some { before := localData [] [] [] [] [] [] [] [7, 10] [1, 0, 1, 0, 0] [1, 0, 1, 0, 0] [] [] [] [] [] [true], after := localData [] [] [] [] [] [] [] [] [1, 0, 1, 0, 0] [1, 0, 1, 0, 0] [] [] [] [] [] [false], ticks := 13, peak := 13, result := false }
  joinTicks := 2
  beforeClear := localData [] [] [] [] [] [] [] [] [1, 0, 1, 0, 0] [1, 0, 1, 0, 0] [] [] [] [] [] [false]
  residualCells := 11
  clearTicks := 28
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 242
  peak := 121

def raw_V13 : RawFixture where
  name := "raw/V13"
  raw := [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, false, true]
  result := true
  frontEndKind := .success
  frontEndTicks := 257
  frontEndAfter := localData [] [] [] [] [] [] [] [6, 9, 10] [1, 0, 1, 0, 1, 0, 0] [1, 0, 1, 1, 0, 0, 0] [] [] [] [] [] [true]
  stream := some { before := localData [] [] [] [] [] [] [] [6, 9, 10] [1, 0, 1, 0, 1, 0, 0] [1, 0, 1, 1, 0, 0, 0] [] [] [] [] [] [true], after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false], ticks := 33, peak := 18, result := true }
  joinTicks := 2
  beforeClear := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  residualCells := 1
  clearTicks := 18
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 310
  peak := 157

def raw_V14 : RawFixture where
  name := "raw/V14"
  raw := [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, true, false, true, true, false, false, true, false, true, true, true, true, true]
  result := false
  frontEndKind := .success
  frontEndTicks := 209
  frontEndAfter := localData [] [] [] [] [] [] [] [6, 10, 15] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [true]
  stream := some { before := localData [] [] [] [] [] [] [] [6, 10, 15] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [true], after := localData [] [] [] [] [] [] [] [15] [1, 1, 0, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [false], ticks := 22, peak := 14, result := false }
  joinTicks := 2
  beforeClear := localData [] [] [] [] [] [] [] [15] [1, 1, 0, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [false]
  residualCells := 12
  clearTicks := 29
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 262
  peak := 125

def raw_V15 : RawFixture where
  name := "raw/V15"
  raw := [false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, true, false, false, false, false, false, true, false, true, false, false, false, false, false, true, false, false, false, true, false, false, true]
  result := true
  frontEndKind := .success
  frontEndTicks := 95
  frontEndAfter := localData [] [] [] [] [] [] [] [] [0] [0] [] [] [] [] [] [false, false]
  stream := some { before := localData [] [] [] [] [] [] [] [] [0] [0] [] [] [] [] [] [false, false], after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false, false], ticks := 5, peak := 4, result := true }
  joinTicks := 2
  beforeClear := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false, false]
  residualCells := 2
  clearTicks := 19
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 121
  peak := 57

def raw_V16 : RawFixture where
  name := "raw/V16"
  raw := [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, true, true, true, true, true]
  result := false
  frontEndKind := .success
  frontEndTicks := 189
  frontEndAfter := localData [] [] [] [] [] [] [] [15] [1, 0, 1, 0, 0] [1, 0, 1, 0, 0] [] [] [] [] [] [true]
  stream := some { before := localData [] [] [] [] [] [] [] [15] [1, 0, 1, 0, 0] [1, 0, 1, 0, 0] [] [] [] [] [] [true], after := localData [] [] [] [] [] [] [] [15] [1, 0, 1, 0, 0] [1, 0, 1, 0, 0] [] [] [] [] [] [false], ticks := 7, peak := 12, result := false }
  joinTicks := 2
  beforeClear := localData [] [] [] [] [] [] [] [15] [1, 0, 1, 0, 0] [1, 0, 1, 0, 0] [] [] [] [] [] [false]
  residualCells := 12
  clearTicks := 29
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 227
  peak := 117

def raw_V17 : RawFixture where
  name := "raw/V17"
  raw := [false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, true, false, true, true, false, false, true, false, true]
  result := false
  frontEndKind := .success
  frontEndTicks := 103
  frontEndAfter := localData [] [] [] [] [] [] [] [6, 10] [0] [0] [] [] [] [] [] [true]
  stream := some { before := localData [] [] [] [] [] [] [] [6, 10] [0] [0] [] [] [] [] [] [true], after := localData [] [] [] [] [] [] [] [] [0] [0] [] [] [] [] [] [false], ticks := 13, peak := 5, result := false }
  joinTicks := 2
  beforeClear := localData [] [] [] [] [] [] [] [] [0] [0] [] [] [] [] [] [false]
  residualCells := 3
  clearTicks := 20
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 138
  peak := 57

def raw_V18 : RawFixture where
  name := "raw/V18"
  raw := [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, true, false, false, true, false, true, true, false, false, true, false, true]
  result := false
  frontEndKind := .success
  frontEndTicks := 187
  frontEndAfter := localData [] [] [] [] [] [] [] [6, 10] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] []
  stream := some { before := localData [] [] [] [] [] [] [] [6, 10] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [], after := localData [] [] [] [] [] [] [] [6, 10] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [], ticks := 4, peak := 12, result := false }
  joinTicks := 2
  beforeClear := localData [] [] [] [] [] [] [] [6, 10] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] []
  residualCells := 12
  clearTicks := 29
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 222
  peak := 113

def rawCases : List RawFixture :=
  [raw_F01, raw_F02, raw_F03, raw_F04, raw_F05, raw_F06, raw_F07, raw_F08, raw_I01, raw_I02, raw_I03, raw_I04, raw_I05, raw_I06, raw_I07, raw_C01, raw_C02, raw_C03, raw_V01, raw_V02, raw_V03, raw_V04, raw_V05, raw_V06, raw_V07, raw_V08, raw_V09, raw_V10, raw_V11, raw_V12, raw_V13, raw_V14, raw_V15, raw_V16, raw_V17, raw_V18]

theorem raw_cases_count : rawCases.length = 36 := rfl

/-! ## Literal partial cleaners, emitters, joins and dirty FrontEnd starts -/

def dirtyData : LocalData :=
  localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]

def clear_C00 : CleanupFixture where
  name := "additional/C00"
  phase := clearPhase 0
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 49
  peak := 32
  index := 0

def clear_C00_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 0), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 2, phase := some (clearPhase 0), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 3, phase := some (clearPhase 1), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 48, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [], cells := 0 },
   { ticks := 49, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [true], cells := 1 }]

def clear_C00E : CleanupFixture where
  name := "additional/C00E"
  phase := clearPhase 0
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 47
  peak := 30
  index := 0

def clear_C00E_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 0), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 1, phase := some (clearPhase 1), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 46, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [], cells := 0 },
   { ticks := 47, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false], cells := 1 }]

def clear_C01 : CleanupFixture where
  name := "additional/C01"
  phase := clearPhase 1
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 46
  peak := 32
  index := 1

def clear_C01_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 1), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 1, phase := some (clearPhase 1), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 2, phase := some (clearPhase 2), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 45, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [], cells := 2 },
   { ticks := 46, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [true], cells := 3 }]

def clear_C01E : CleanupFixture where
  name := "additional/C01E"
  phase := clearPhase 1
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 45
  peak := 31
  index := 1

def clear_C01E_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 1), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 1, phase := some (clearPhase 2), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 44, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [], cells := 2 },
   { ticks := 45, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false], cells := 3 }]

def clear_C02 : CleanupFixture where
  name := "additional/C02"
  phase := clearPhase 2
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [] [] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 44
  peak := 32
  index := 2

def clear_C02_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 2), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 2, phase := some (clearPhase 2), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 3, phase := some (clearPhase 3), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 43, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [] [] [] [] [] [] [] [] [] [] [] [] [] [], cells := 3 },
   { ticks := 44, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [] [] [] [] [] [] [] [] [] [] [] [] [] [true], cells := 4 }]

def clear_C02E : CleanupFixture where
  name := "additional/C02E"
  phase := clearPhase 2
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 42
  peak := 30
  index := 2

def clear_C02E_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 2), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 1, phase := some (clearPhase 3), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 41, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [] [] [] [] [] [] [] [] [] [] [] [] [] [], cells := 3 },
   { ticks := 42, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [] [] [] [] [] [] [] [] [] [] [] [] [] [false], cells := 4 }]

def clear_C03 : CleanupFixture where
  name := "additional/C03"
  phase := clearPhase 3
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 41
  peak := 32
  index := 3

def clear_C03_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 3), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 1, phase := some (clearPhase 3), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 2, phase := some (clearPhase 4), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 40, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [] [] [] [] [] [] [] [] [] [] [] [] [], cells := 5 },
   { ticks := 41, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [] [] [] [] [] [] [] [] [] [] [] [] [true], cells := 6 }]

def clear_C03E : CleanupFixture where
  name := "additional/C03E"
  phase := clearPhase 3
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 40
  peak := 31
  index := 3

def clear_C03E_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 3), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 1, phase := some (clearPhase 4), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 39, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [] [] [] [] [] [] [] [] [] [] [] [] [], cells := 5 },
   { ticks := 40, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [] [] [] [] [] [] [] [] [] [] [] [] [false], cells := 6 }]

def clear_C04 : CleanupFixture where
  name := "additional/C04"
  phase := clearPhase 4
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 39
  peak := 32
  index := 4

def clear_C04_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 4), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 3, phase := some (clearPhase 4), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 4, phase := some (clearPhase 5), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 38, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [] [] [] [] [] [] [] [] [] [] [] [], cells := 6 },
   { ticks := 39, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [] [] [] [] [] [] [] [] [] [] [] [true], cells := 7 }]

def clear_C04E : CleanupFixture where
  name := "additional/C04E"
  phase := clearPhase 4
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 36
  peak := 29
  index := 4

def clear_C04E_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 4), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 1, phase := some (clearPhase 5), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 35, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [] [] [] [] [] [] [] [] [] [] [] [], cells := 6 },
   { ticks := 36, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [] [] [] [] [] [] [] [] [] [] [] [false], cells := 7 }]

def clear_C05 : CleanupFixture where
  name := "additional/C05"
  phase := clearPhase 5
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 35
  peak := 32
  index := 5

def clear_C05_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 5), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 2, phase := some (clearPhase 5), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 3, phase := some (clearPhase 6), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 34, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [] [] [] [] [] [] [] [] [] [] [], cells := 9 },
   { ticks := 35, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [] [] [] [] [] [] [] [] [] [] [true], cells := 10 }]

def clear_C05E : CleanupFixture where
  name := "additional/C05E"
  phase := clearPhase 5
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 33
  peak := 30
  index := 5

def clear_C05E_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 5), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 1, phase := some (clearPhase 6), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 32, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [] [] [] [] [] [] [] [] [] [] [], cells := 9 },
   { ticks := 33, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [] [] [] [] [] [] [] [] [] [] [false], cells := 10 }]

def clear_C06 : CleanupFixture where
  name := "additional/C06"
  phase := clearPhase 6
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [] [] [] [] [] [] [] [] [] [true]
  ticks := 32
  peak := 32
  index := 6

def clear_C06_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 6), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 1, phase := some (clearPhase 6), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 2, phase := some (clearPhase 7), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 31, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [] [] [] [] [] [] [] [] [] [], cells := 11 },
   { ticks := 32, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [] [] [] [] [] [] [] [] [] [true], cells := 12 }]

def clear_C06E : CleanupFixture where
  name := "additional/C06E"
  phase := clearPhase 6
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [] [] [] [] [] [] [] [] [] [false]
  ticks := 31
  peak := 31
  index := 6

def clear_C06E_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 6), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 1, phase := some (clearPhase 7), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 30, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [] [] [] [] [] [] [] [] [] [], cells := 11 },
   { ticks := 31, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [] [] [] [] [] [] [] [] [] [false], cells := 12 }]

def clear_C07 : CleanupFixture where
  name := "additional/C07"
  phase := clearPhase 7
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [] [] [] [] [] [] [] [] [true]
  ticks := 30
  peak := 32
  index := 7

def clear_C07_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 7), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 2, phase := some (clearPhase 7), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 3, phase := some (clearPhase 8), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 29, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [] [] [] [] [] [] [] [] [], cells := 12 },
   { ticks := 30, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [] [] [] [] [] [] [] [] [true], cells := 13 }]

def clear_C07E : CleanupFixture where
  name := "additional/C07E"
  phase := clearPhase 7
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [] [] [] [] [] [] [] [] [false]
  ticks := 28
  peak := 30
  index := 7

def clear_C07E_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 7), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 1, phase := some (clearPhase 8), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 27, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [] [] [] [] [] [] [] [] [], cells := 12 },
   { ticks := 28, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [] [] [] [] [] [] [] [] [false], cells := 13 }]

def clear_C08 : CleanupFixture where
  name := "additional/C08"
  phase := clearPhase 8
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [] [] [] [] [] [] [] [true]
  ticks := 27
  peak := 32
  index := 8

def clear_C08_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 8), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 3, phase := some (clearPhase 8), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 4, phase := some (clearPhase 9), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 26, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [] [] [] [] [] [] [] [], cells := 14 },
   { ticks := 27, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [] [] [] [] [] [] [] [true], cells := 15 }]

def clear_C08E : CleanupFixture where
  name := "additional/C08E"
  phase := clearPhase 8
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [] [] [] [] [] [] [] [false]
  ticks := 24
  peak := 29
  index := 8

def clear_C08E_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 8), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 1, phase := some (clearPhase 9), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 23, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [] [] [] [] [] [] [] [], cells := 14 },
   { ticks := 24, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [] [] [] [] [] [] [] [false], cells := 15 }]

def clear_C09 : CleanupFixture where
  name := "additional/C09"
  phase := clearPhase 9
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [] [] [] [] [] [] [true]
  ticks := 23
  peak := 32
  index := 9

def clear_C09_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 9), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 1, phase := some (clearPhase 9), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 2, phase := some (clearPhase 10), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 22, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [] [] [] [] [] [] [], cells := 17 },
   { ticks := 23, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [] [] [] [] [] [] [true], cells := 18 }]

def clear_C09E : CleanupFixture where
  name := "additional/C09E"
  phase := clearPhase 9
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [] [] [] [] [] [] [false]
  ticks := 22
  peak := 31
  index := 9

def clear_C09E_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 9), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 1, phase := some (clearPhase 10), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 21, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [] [] [] [] [] [] [], cells := 17 },
   { ticks := 22, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [] [] [] [] [] [] [false], cells := 18 }]

def clear_C10 : CleanupFixture where
  name := "additional/C10"
  phase := clearPhase 10
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [] [] [] [] [] [true]
  ticks := 21
  peak := 32
  index := 10

def clear_C10_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 10), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 2, phase := some (clearPhase 10), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 3, phase := some (clearPhase 11), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 20, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [] [] [] [] [] [], cells := 18 },
   { ticks := 21, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [] [] [] [] [] [true], cells := 19 }]

def clear_C10E : CleanupFixture where
  name := "additional/C10E"
  phase := clearPhase 10
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [] [] [] [] [] [false]
  ticks := 19
  peak := 30
  index := 10

def clear_C10E_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 10), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 1, phase := some (clearPhase 11), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 18, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [] [] [] [] [] [], cells := 18 },
   { ticks := 19, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [] [] [] [] [] [false], cells := 19 }]

def clear_C11 : CleanupFixture where
  name := "additional/C11"
  phase := clearPhase 11
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [] [] [] [] [true]
  ticks := 18
  peak := 32
  index := 11

def clear_C11_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 11), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 2, phase := some (clearPhase 11), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 3, phase := some (clearPhase 12), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 17, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [] [] [] [] [], cells := 20 },
   { ticks := 18, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [] [] [] [] [true], cells := 21 }]

def clear_C11E : CleanupFixture where
  name := "additional/C11E"
  phase := clearPhase 11
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [] [] [] [] [false]
  ticks := 16
  peak := 30
  index := 11

def clear_C11E_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 11), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 1, phase := some (clearPhase 12), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 15, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [] [] [] [] [], cells := 20 },
   { ticks := 16, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [] [] [] [] [false], cells := 21 }]

def clear_C12 : CleanupFixture where
  name := "additional/C12"
  phase := clearPhase 12
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [] [] [] [true]
  ticks := 15
  peak := 32
  index := 12

def clear_C12_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 12), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 3, phase := some (clearPhase 12), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 4, phase := some (clearPhase 13), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 14, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [] [] [] [], cells := 22 },
   { ticks := 15, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [] [] [] [true], cells := 23 }]

def clear_C12E : CleanupFixture where
  name := "additional/C12E"
  phase := clearPhase 12
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [] [] [] [false]
  ticks := 12
  peak := 29
  index := 12

def clear_C12E_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 12), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 1, phase := some (clearPhase 13), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 11, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [] [] [] [], cells := 22 },
   { ticks := 12, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [] [] [] [false], cells := 23 }]

def clear_C13 : CleanupFixture where
  name := "additional/C13"
  phase := clearPhase 13
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [] [] [true]
  ticks := 11
  peak := 32
  index := 13

def clear_C13_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 13), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 2, phase := some (clearPhase 13), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 3, phase := some (clearPhase 14), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 10, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [] [] [], cells := 25 },
   { ticks := 11, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [] [] [true], cells := 26 }]

def clear_C13E : CleanupFixture where
  name := "additional/C13E"
  phase := clearPhase 13
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [] [] [false]
  ticks := 9
  peak := 30
  index := 13

def clear_C13E_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 13), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 1, phase := some (clearPhase 14), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 8, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [] [] [], cells := 25 },
   { ticks := 9, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [] [] [false], cells := 26 }]

def clear_C14 : CleanupFixture where
  name := "additional/C14"
  phase := clearPhase 14
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [] [true]
  ticks := 8
  peak := 32
  index := 14

def clear_C14_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 14), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 3, phase := some (clearPhase 14), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [] [false, true], cells := 29 },
   { ticks := 4, phase := some (clearPhase 15), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [] [false, true], cells := 29 },
   { ticks := 7, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [] [], cells := 27 },
   { ticks := 8, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [] [true], cells := 28 }]

def clear_C14E : CleanupFixture where
  name := "additional/C14E"
  phase := clearPhase 14
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [] [false]
  ticks := 5
  peak := 29
  index := 14

def clear_C14E_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 14), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [] [false, true], cells := 29 },
   { ticks := 1, phase := some (clearPhase 15), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [] [false, true], cells := 29 },
   { ticks := 4, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [] [], cells := 27 },
   { ticks := 5, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [] [false], cells := 28 }]

def clear_C15 : CleanupFixture where
  name := "additional/C15"
  phase := clearPhase 15
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [true]
  ticks := 4
  peak := 32
  index := 15

def clear_C15_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 15), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 2, phase := some (clearPhase 15), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [], cells := 30 },
   { ticks := 3, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [], cells := 30 },
   { ticks := 4, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [true], cells := 31 }]

def clear_C15E : CleanupFixture where
  name := "additional/C15E"
  phase := clearPhase 15
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] []
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false]
  ticks := 2
  peak := 31
  index := 15

def clear_C15E_boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 15), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [], cells := 30 },
   { ticks := 1, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [], cells := 30 },
   { ticks := 2, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false], cells := 31 }]

def emit_E00 : EmitFixture where
  name := "additional/E00"
  phase := emitPhase
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, false, true]
  ticks := 1
  peak := 33

def emit_E01 : EmitFixture where
  name := "additional/E01"
  phase := emitPhase
  fields := ⟨some 15, some (), some false, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, false, true]
  ticks := 1
  peak := 33

def emit_E02 : EmitFixture where
  name := "additional/E02"
  phase := emitPhase
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [true, false, true]
  ticks := 1
  peak := 33

def emit_E03 : EmitFixture where
  name := "additional/E03"
  phase := emitPhase
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 1
  peak := 1

def join_J00 : JoinFixture where
  name := "additional/J00"
  phase := rejectPhase
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 50
  peak := 32
  nextPhase := clearPhase 0
  nextFields := ⟨none, none, some false, none, none, none, none, none⟩
  stream := none

def join_J01 : JoinFixture where
  name := "additional/J01"
  phase := resultPhase false
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 50
  peak := 32
  nextPhase := clearPhase 0
  nextFields := ⟨none, none, some false, none, none, none, none, none⟩
  stream := none

def join_J02 : JoinFixture where
  name := "additional/J02"
  phase := resultPhase true
  fields := ⟨some 15, some (), some false, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 50
  peak := 32
  nextPhase := clearPhase 0
  nextFields := ⟨none, none, some true, none, none, none, none, none⟩
  stream := none

def join_J03 : JoinFixture where
  name := "additional/J03"
  phase := dispatchPhase
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [] [] [true] [11] [3] [] [] [] [12] [(), ()] [false, true] [.right, .left] [.right] [true]
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 38
  peak := 15
  nextPhase := streamPhase StreamMachine.inspectPhase
  nextFields := ⟨none, none, none, none, none, none, none, none⟩
  stream := some { before := localData [true, false] [false] [] [] [true] [11] [3] [] [] [] [12] [(), ()] [false, true] [.right, .left] [.right] [true], after := localData [true, false] [false] [] [] [true] [11] [3] [] [] [] [12] [(), ()] [false, true] [.right, .left] [.right] [true], ticks := 4, peak := 15, result := true }

def dirty_D00 : DirtyFrontEndFixture where
  name := "additional/D00"
  phase := .inl (FrontEndMachine.certificateDecoderLabel .emit)
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [] [] [] [false, true] [11] [10, 6] [7, 10] [1, 0, 1, 0, 0] [1, 0, 1, 0, 0] [] [] [true] [] [] [false, true]
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 72
  peak := 22
  frontEndTicks := 3
  frontEndAfter := localData [true, false] [] [] [] [false, true] [11] [] [6, 10, 7, 10] [1, 0, 1, 0, 0] [1, 0, 1, 0, 0] [] [] [true] [] [] [false, true]
  stream := { before := localData [true, false] [] [] [] [false, true] [11] [] [6, 10, 7, 10] [1, 0, 1, 0, 0] [1, 0, 1, 0, 0] [] [] [true] [] [] [false, true], after := localData [true, false] [] [] [] [false, true] [11] [] [] [] [] [] [] [true] [] [] [false, false], ticks := 42, peak := 22, result := true }
  physicalPath := []

def dirty_D01 : DirtyFrontEndFixture where
  name := "additional/D01"
  phase := rawEntryPhase
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, true, false, true, true, false, false, true, false, true] [] [] [] [] [] [] [] [] [] [] [] [] [.right] [.left] []
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 249
  peak := 123
  frontEndTicks := 199
  frontEndAfter := localData [] [] [] [] [] [] [] [6, 10] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [.right] [.left] [true]
  stream := { before := localData [] [] [] [] [] [] [] [6, 10] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [.right] [.left] [true], after := localData [] [] [] [] [] [] [] [] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [false], ticks := 20, peak := 15, result := false }
  physicalPath := [.right, .left]

def dirty_D02 : DirtyFrontEndFixture where
  name := "additional/D02"
  phase := rawEntryPhase
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, false, true] [] [] [] [] [] [] [] [] [] [] [] [] [.right, .left] [.left, .right] []
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 312
  peak := 161
  frontEndTicks := 257
  frontEndAfter := localData [] [] [] [] [] [] [] [6, 9, 10] [1, 0, 1, 0, 1, 0, 0] [1, 0, 1, 1, 0, 0, 0] [] [] [] [.right, .left] [.left, .right] [true]
  stream := { before := localData [] [] [] [] [] [] [] [6, 9, 10] [1, 0, 1, 0, 1, 0, 0] [1, 0, 1, 1, 0, 0, 0] [] [] [] [.right, .left] [.left, .right] [true], after := localData [] [] [] [] [] [] [] [] [1, 0, 1, 0, 1, 0, 0] [1, 0, 1, 1, 0, 0, 0] [] [] [] [] [.right, .left, .right] [false], ticks := 18, peak := 22, result := false }
  physicalPath := [.left, .right, .right, .left, .right]

def dirty_D03 : DirtyFrontEndFixture where
  name := "additional/D03"
  phase := rawEntryPhase
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, true, false, true, true, false, false, true, false, true] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 244
  peak := 121
  frontEndTicks := 199
  frontEndAfter := localData [] [] [] [] [] [] [] [6, 10] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [true]
  stream := { before := localData [] [] [] [] [] [] [] [6, 10] [1, 0, 1, 0, 0] [1, 1, 0, 0, 0] [] [] [] [] [] [true], after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false], ticks := 25, peak := 13, result := true }
  physicalPath := []

def clear_CZERO : CleanupFixture where
  name := "additional/CZERO"
  phase := clearPhase 0
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 17
  peak := 1
  index := 0

def partialClearCases : List CleanupFixture :=
  [clear_C00, clear_C00E, clear_C01, clear_C01E, clear_C02, clear_C02E, clear_C03, clear_C03E, clear_C04, clear_C04E, clear_C05, clear_C05E, clear_C06, clear_C06E, clear_C07, clear_C07E, clear_C08, clear_C08E, clear_C09, clear_C09E, clear_C10, clear_C10E, clear_C11, clear_C11E, clear_C12, clear_C12E, clear_C13, clear_C13E, clear_C14, clear_C14E, clear_C15, clear_C15E]

theorem partialClearCases_count : partialClearCases.length = 32 := rfl

def emitCases : List EmitFixture :=
  [emit_E00, emit_E01, emit_E02, emit_E03]

theorem emitCases_count : emitCases.length = 4 := rfl

def joinCases : List JoinFixture :=
  [join_J00, join_J01, join_J02, join_J03]

theorem joinCases_count : joinCases.length = 4 := rfl

def dirtyFrontEndCases : List DirtyFrontEndFixture :=
  [dirty_D00, dirty_D01, dirty_D02, dirty_D03]

theorem dirtyFrontEndCases_count : dirtyFrontEndCases.length = 4 := rfl

def partialClearBoundaries : List (CleanupFixture × List Boundary) :=
  [(clear_C00, clear_C00_boundaries),
   (clear_C00E, clear_C00E_boundaries),
   (clear_C01, clear_C01_boundaries),
   (clear_C01E, clear_C01E_boundaries),
   (clear_C02, clear_C02_boundaries),
   (clear_C02E, clear_C02E_boundaries),
   (clear_C03, clear_C03_boundaries),
   (clear_C03E, clear_C03E_boundaries),
   (clear_C04, clear_C04_boundaries),
   (clear_C04E, clear_C04E_boundaries),
   (clear_C05, clear_C05_boundaries),
   (clear_C05E, clear_C05E_boundaries),
   (clear_C06, clear_C06_boundaries),
   (clear_C06E, clear_C06E_boundaries),
   (clear_C07, clear_C07_boundaries),
   (clear_C07E, clear_C07E_boundaries),
   (clear_C08, clear_C08_boundaries),
   (clear_C08E, clear_C08E_boundaries),
   (clear_C09, clear_C09_boundaries),
   (clear_C09E, clear_C09E_boundaries),
   (clear_C10, clear_C10_boundaries),
   (clear_C10E, clear_C10E_boundaries),
   (clear_C11, clear_C11_boundaries),
   (clear_C11E, clear_C11E_boundaries),
   (clear_C12, clear_C12_boundaries),
   (clear_C12E, clear_C12E_boundaries),
   (clear_C13, clear_C13_boundaries),
   (clear_C13E, clear_C13E_boundaries),
   (clear_C14, clear_C14_boundaries),
   (clear_C14E, clear_C14E_boundaries),
   (clear_C15, clear_C15_boundaries),
   (clear_C15E, clear_C15E_boundaries)]

theorem partial_clear_boundary_count : (partialClearBoundaries.map (fun p => p.2.length)).sum = 142 := rfl

/-! ## Three distinct liveness records -/

def liveness_L00 : LivenessFixture :=
  .liveHalt "liveness/L00" (⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩) (localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]) 32

def liveness_L01 : LivenessFixture :=
  .outerNone "liveness/L01"

def liveness_L02 : LivenessFixture :=
  .externalAllocator "liveness/L02" 42 (⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩) (localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]) [true, true, false, true] [11, 15] 38

def livenessCases : List LivenessFixture := [liveness_L00, liveness_L01, liveness_L02]

theorem liveness_cases_count : livenessCases.length = 3 := rfl

def allClosedCases : List ClosedFixture :=
  rawCases.map RawFixture.toClosed ++ partialClearCases.map CleanupFixture.toClosedFixture ++
    emitCases.map EmitFixture.toClosedFixture ++ joinCases.map JoinFixture.toClosedFixture ++
    dirtyFrontEndCases.map DirtyFrontEndFixture.toClosedFixture ++ [clear_CZERO.toClosedFixture]

theorem all_positive_closed_cases_count : allClosedCases.length = 81 := rfl

theorem all_frozen_case_records_count : allClosedCases.length + livenessCases.length = 84 := rfl

/-! ## All 96 owned control domains, independently listed -/

def frontend_framer_scanPrefix : Phase := .inl (FrontEndMachine.framerLabel .scanPrefix)
def frontend_framer_copyCert : Phase := .inl (FrontEndMachine.framerLabel .copyCert)
def frontend_framer_emitCert : Phase := .inl (FrontEndMachine.framerLabel .emitCert)
def frontend_framer_emitFirst : Phase := .inl (FrontEndMachine.framerLabel .emitFirst)
def frontend_framer_clearFirst : Phase := .inl (FrontEndMachine.framerLabel .clearFirst)
def frontend_inputDecoder_scan : Phase := .inl (FrontEndMachine.inputDecoderLabel .scan)
def frontend_inputDecoder_emit : Phase := .inl (FrontEndMachine.inputDecoderLabel .emit)
def frontend_inputDecoder_clear : Phase := .inl (FrontEndMachine.inputDecoderLabel .clear)
def frontend_sourceTree_init : Phase := .inl (InputParserMachine.treeLabel .source .init)
def frontend_sourceTree_scan : Phase := .inl (InputParserMachine.treeLabel .source .scan)
def frontend_sourceTree_emit : Phase := .inl (InputParserMachine.treeLabel .source .emit)
def frontend_sourceTree_undo : Phase := .inl (InputParserMachine.treeLabel .source .undo)
def frontend_sourceTree_dropPending : Phase := .inl (InputParserMachine.treeLabel .source .dropPending)
def frontend_targetTree_init : Phase := .inl (InputParserMachine.treeLabel .target .init)
def frontend_targetTree_scan : Phase := .inl (InputParserMachine.treeLabel .target .scan)
def frontend_targetTree_emit : Phase := .inl (InputParserMachine.treeLabel .target .emit)
def frontend_targetTree_undo : Phase := .inl (InputParserMachine.treeLabel .target .undo)
def frontend_targetTree_dropPending : Phase := .inl (InputParserMachine.treeLabel .target .dropPending)
def frontend_input_bitsScan : Phase := .inl (InputParserMachine.phaseLabel .bitsScan)
def frontend_input_bitsEmit : Phase := .inl (InputParserMachine.phaseLabel .bitsEmit)
def frontend_input_eof : Phase := .inl (InputParserMachine.phaseLabel .eof)
def frontend_input_restoreEnd : Phase := .inl (InputParserMachine.phaseLabel .restoreEnd)
def frontend_input_fuelUndo : Phase := .inl (InputParserMachine.phaseLabel .fuelUndo)
def frontend_input_bitsUndo : Phase := .inl (InputParserMachine.phaseLabel .bitsUndo)
def frontend_input_restoreSep2 : Phase := .inl (InputParserMachine.phaseLabel .restoreSep2)
def frontend_input_targetToReverse : Phase := .inl (InputParserMachine.phaseLabel .targetToReverse)
def frontend_input_targetToRaw : Phase := .inl (InputParserMachine.phaseLabel .targetToRaw)
def frontend_input_restoreSep1 : Phase := .inl (InputParserMachine.phaseLabel .restoreSep1)
def frontend_input_sourceToReverse : Phase := .inl (InputParserMachine.phaseLabel .sourceToReverse)
def frontend_input_sourceToRaw : Phase := .inl (InputParserMachine.phaseLabel .sourceToRaw)
def frontend_source_success : Phase := .inl (InputParserMachine.treeResultLabel .source .success)
def frontend_target_success : Phase := .inl (InputParserMachine.treeResultLabel .target .success)
def frontend_target_failure : Phase := .inl (InputParserMachine.treeResultLabel .target .failure)
def frontend_certificateDecoder_scan : Phase := .inl (FrontEndMachine.certificateDecoderLabel .scan)
def frontend_certificateDecoder_emit : Phase := .inl (FrontEndMachine.certificateDecoderLabel .emit)
def frontend_certificateDecoder_clear : Phase := .inl (FrontEndMachine.certificateDecoderLabel .clear)
def frontend_dispatch : Phase := .inl (FrontEndMachine.dispatchLabel)
def frontend_reject : Phase := .inl (FrontEndMachine.rejectLabel)
def stream_inspect : Phase := streamPhase (StreamMachine.inspectPhase)
def stream_counter_borrow : Phase := streamPhase (StreamMachine.counterPhase .borrow)
def stream_counter_restoreTrue : Phase := streamPhase (StreamMachine.counterPhase .restoreTrue)
def stream_counter_restoreFalse : Phase := streamPhase (StreamMachine.counterPhase .restoreFalse)
def stream_fuelJoin_atEnd : Phase := streamPhase (StreamMachine.fuelJoinPhase .atEnd)
def stream_fuelJoin_positive : Phase := streamPhase (StreamMachine.fuelJoinPhase .positive)
def stream_fuelJoin_zero : Phase := streamPhase (StreamMachine.fuelJoinPhase .zero)
def stream_move_start : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.movePhase (.start)))
def stream_move_scan_left : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.movePhase (.scan .left)))
def stream_move_scan_right : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.movePhase (.scan .right)))
def stream_move_emit_left : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.movePhase (.emit .left)))
def stream_move_emit_right : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.movePhase (.emit .right)))
def stream_move_undo_left : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.movePhase (.undo .left)))
def stream_move_undo_right : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.movePhase (.undo .right)))
def stream_moveDispatch_success_left : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.dispatchPhase (.success .left)))
def stream_moveDispatch_success_right : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.dispatchPhase (.success .right)))
def stream_moveDispatch_failure : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.dispatchPhase (.failure)))
def stream_position_seek_left : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.seek .left)))
def stream_position_seek_right : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.seek .right)))
def stream_position_scanPrefix_left : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.scanPrefix .left)))
def stream_position_scanPrefix_right : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.scanPrefix .right)))
def stream_position_start_left : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.start .left)))
def stream_position_start_right : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.start .right)))
def stream_position_scanScratch_left : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left)))
def stream_position_scanScratch_right : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.scanScratch .right)))
def stream_position_checkRight : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.checkRight)))
def stream_position_restoreScratch_successLeft : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft)))
def stream_position_restoreScratch_successRight : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successRight)))
def stream_position_restoreScratch_failureLeft : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .failureLeft)))
def stream_position_restoreScratch_failureRight : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .failureRight)))
def stream_position_dropPending : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.dropPending)))
def stream_position_restorePrefix_success : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success)))
def stream_position_restorePrefix_failure : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure)))
def stream_applyJoin_parseFailure : Phase := streamPhase (StreamMachine.applyJoinPhase MoveApplyMachine.parseFailure)
def stream_applyJoin_rotationFailure : Phase := streamPhase (StreamMachine.applyJoinPhase MoveApplyMachine.rotationFailure)
def stream_applyJoin_success : Phase := streamPhase (StreamMachine.applyJoinPhase MoveApplyMachine.success)
def stream_compare : Phase := streamPhase (StreamMachine.comparePhase)
def stream_equalityJoin_equal : Phase := streamPhase (StreamMachine.equalityJoinPhase .equal)
def stream_equalityJoin_different : Phase := streamPhase (StreamMachine.equalityJoinPhase .different)
def stream_result_false : Phase := resultPhase false
def stream_result_true : Phase := resultPhase true
def clear_00 : Phase := clearPhase 0
def clear_01 : Phase := clearPhase 1
def clear_02 : Phase := clearPhase 2
def clear_03 : Phase := clearPhase 3
def clear_04 : Phase := clearPhase 4
def clear_05 : Phase := clearPhase 5
def clear_06 : Phase := clearPhase 6
def clear_07 : Phase := clearPhase 7
def clear_08 : Phase := clearPhase 8
def clear_09 : Phase := clearPhase 9
def clear_10 : Phase := clearPhase 10
def clear_11 : Phase := clearPhase 11
def clear_12 : Phase := clearPhase 12
def clear_13 : Phase := clearPhase 13
def clear_14 : Phase := clearPhase 14
def clear_15 : Phase := clearPhase 15
def emit : Phase := emitPhase

def phaseDomains : List Phase :=
  [frontend_framer_scanPrefix,
   frontend_framer_copyCert,
   frontend_framer_emitCert,
   frontend_framer_emitFirst,
   frontend_framer_clearFirst,
   frontend_inputDecoder_scan,
   frontend_inputDecoder_emit,
   frontend_inputDecoder_clear,
   frontend_sourceTree_init,
   frontend_sourceTree_scan,
   frontend_sourceTree_emit,
   frontend_sourceTree_undo,
   frontend_sourceTree_dropPending,
   frontend_targetTree_init,
   frontend_targetTree_scan,
   frontend_targetTree_emit,
   frontend_targetTree_undo,
   frontend_targetTree_dropPending,
   frontend_input_bitsScan,
   frontend_input_bitsEmit,
   frontend_input_eof,
   frontend_input_restoreEnd,
   frontend_input_fuelUndo,
   frontend_input_bitsUndo,
   frontend_input_restoreSep2,
   frontend_input_targetToReverse,
   frontend_input_targetToRaw,
   frontend_input_restoreSep1,
   frontend_input_sourceToReverse,
   frontend_input_sourceToRaw,
   frontend_source_success,
   frontend_target_success,
   frontend_target_failure,
   frontend_certificateDecoder_scan,
   frontend_certificateDecoder_emit,
   frontend_certificateDecoder_clear,
   frontend_dispatch,
   frontend_reject,
   stream_inspect,
   stream_counter_borrow,
   stream_counter_restoreTrue,
   stream_counter_restoreFalse,
   stream_fuelJoin_atEnd,
   stream_fuelJoin_positive,
   stream_fuelJoin_zero,
   stream_move_start,
   stream_move_scan_left,
   stream_move_scan_right,
   stream_move_emit_left,
   stream_move_emit_right,
   stream_move_undo_left,
   stream_move_undo_right,
   stream_moveDispatch_success_left,
   stream_moveDispatch_success_right,
   stream_moveDispatch_failure,
   stream_position_seek_left,
   stream_position_seek_right,
   stream_position_scanPrefix_left,
   stream_position_scanPrefix_right,
   stream_position_start_left,
   stream_position_start_right,
   stream_position_scanScratch_left,
   stream_position_scanScratch_right,
   stream_position_checkRight,
   stream_position_restoreScratch_successLeft,
   stream_position_restoreScratch_successRight,
   stream_position_restoreScratch_failureLeft,
   stream_position_restoreScratch_failureRight,
   stream_position_dropPending,
   stream_position_restorePrefix_success,
   stream_position_restorePrefix_failure,
   stream_applyJoin_parseFailure,
   stream_applyJoin_rotationFailure,
   stream_applyJoin_success,
   stream_compare,
   stream_equalityJoin_equal,
   stream_equalityJoin_different,
   stream_result_false,
   stream_result_true,
   clear_00,
   clear_01,
   clear_02,
   clear_03,
   clear_04,
   clear_05,
   clear_06,
   clear_07,
   clear_08,
   clear_09,
   clear_10,
   clear_11,
   clear_12,
   clear_13,
   clear_14,
   clear_15,
   emit]

theorem phase_domains_count : phaseDomains.length = 96 := rfl

/-! ## Complete finite carriers and physical maps -/

theorem cleanup_phase_count : Fintype.card CleanupPhase = 17 := by
  rw [← Fintype.card_congr cleanupPhaseEquiv]
  simp

theorem finite_dimensions_unit :
    Fintype.card (StackId (Fin 2)) = 18 ∧
    Fintype.card (Label Unit) = 97 ∧
    Fintype.card (Registers Bool) = 280908 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using card_stackId (K := Fin 2)
  · simpa only [Fintype.card_unit] using card_label (Λ := Unit)
  · simpa only [Fintype.card_bool] using card_registers (R := Bool)

theorem finite_dimensions_two :
    Fintype.card (StackId (Fin 2)) = 18 ∧
    Fintype.card (Label (Fin 2)) = 98 ∧
    Fintype.card (Registers Bool) = 280908 := by
  refine ⟨finite_dimensions_unit.1, ?_, finite_dimensions_unit.2.2⟩
  simpa only [Fintype.card_fin] using card_label (Λ := Fin 2)

theorem owned_dimensions_with_infinite_labels :
    Fintype.card (OwnedLabel Nat) = 96 := card_ownedLabel

theorem standalone_dimensions :
    Fintype.card (StackId Empty) = 16 ∧
    Fintype.card (Label Empty) = 96 ∧
    Fintype.card (Registers Unit) = 140454 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Fintype.card_empty, Nat.add_zero] using card_stackId (K := Empty)
  · simpa only [Fintype.card_empty, Nat.add_zero] using card_label (Λ := Empty)
  · simpa only [Fintype.card_unit, Nat.mul_one] using card_registers (R := Unit)

theorem all_reset_callbacks_preserve_the_exact_fields {R α : Type}
    (regs : Registers R) (bit : Bool) (head : Option α) :
    (fullReset regs).1 = (none, none) ∧
    (fullReset regs).2.1 = BitDecoderMachine.zeroRegisters ∧
    (fullReset regs).2.2 = (none, user regs) ∧
    answer (answerRegisters bit regs) = bit ∧
    (answerRegisters bit regs).2.2 = (none, user regs) ∧
    (observeOccupied regs head).1 = regs.1 ∧
    (observeOccupied regs head).2.1.b0 = regs.2.1.b0 ∧
    (observeOccupied regs head).2.1.b1 = some head.isSome ∧
    (observeOccupied regs head).2.1.b2 = regs.2.1.b2 ∧
    (observeOccupied regs head).2.1.b3 = regs.2.1.b3 ∧
    (observeOccupied regs head).2.1.tag = regs.2.1.tag ∧
    (observeOccupied regs head).2.2 = regs.2.2 := by
  exact ⟨rfl, rfl, rfl, answer_answerRegisters bit regs, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem front_end_reset_preserves_stale_branch_but_closed_reset_clears_it {R : Type}
    (regs : Registers R) :
    (FrontEndMachine.reset regs).2.2.1 = regs.2.2.1 ∧
    (fullReset regs).2.2.1 = none ∧
    (FrontEndMachine.reset regs).2.2.2 = user regs ∧
    (fullReset regs).2.2.2 = user regs := ⟨rfl, rfl, rfl, rfl⟩

theorem complete_cfg_keeps_all_local_and_original_words {K Λ R : Type} {Γ : K → Type}
    (label : Option (Label Λ)) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    dataOfCfg (cfg label regs D ctx) = D ∧
    contextOfCfg (cfg label regs D ctx) = ctx ∧
    (cfg label regs D ctx).var = regs ∧ (cfg label regs D ctx).l = label :=
  ⟨dataOfCfg_cfg label regs D ctx, contextOfCfg_cfg label regs D ctx, rfl, rfl⟩

theorem complete_component_label_maps_roundtrip {Λ : Type} (label : Label Λ) :
    frontEndLabelEquiv (frontEndLabelEquiv.symm label) = label ∧
    streamLabelEquiv (streamLabelEquiv.symm label) = label :=
  ⟨frontEndLabelEquiv.apply_symm_apply label, streamLabelEquiv.apply_symm_apply label⟩

theorem complete_stream_stack_and_register_maps_roundtrip {K R : Type}
    (k : StackId K) (regs : Registers R) :
    streamStackEquiv (streamStackEquiv.symm k) = k ∧
    streamRegisterEquiv (streamRegisterEquiv.symm regs) = regs :=
  ⟨streamStackEquiv.apply_symm_apply k, streamRegisterEquiv.apply_symm_apply regs⟩

theorem every_listed_domain_is_owned {Λ : Type} (q : Phase) (_member : q ∈ phaseDomains) :
    Owned (some (phaseLabel (Λ := Λ) q)) := owned_phase q

theorem ordinary_context_has_five_cells : externalCells ordinaryContext = 5 := by
  simp only [externalCells, Fin.sum_univ_two, ordinaryContext, independentWords]
  rfl

/-- Complete physical sum; no label or register finiteness is required. -/
theorem actual_physical_cells_of_cfg {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (label : Option (Label Λ)) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    physicalCells (cfg label regs D ctx) = localCells D + externalCells ctx := by
  have base := FrontEndMachine.stackCells_cfg (Λ := Empty) none regs
    (frontEndData D) (frontEndContext D ctx)
  have branchWords : (Finset.univ : Finset StreamMachine.NewBranchStores) =
      {.moveReverse, .path} := by
    ext k
    cases k <;> simp
  change FrontEndMachine.stackCells (FrontEndMachine.cfg (Λ := Empty) none regs
    (frontEndData D) (frontEndContext D ctx)) = _
  rw [base]
  simp only [FrontEndMachine.contextCells, Fintype.sum_sum_type, branchWords]
  simp only [Finset.sum_insert, Finset.mem_singleton, reduceCtorEq, not_false_eq_true,
    Finset.sum_singleton]
  change FrontEndMachine.localCells (frontEndData D) +
    (D.moveReverse.length + D.path.length + externalCells ctx) = _
  simp only [FrontEndMachine.localCells, frontEndData, localCells]
  omega

section ActualRuntimeConnections

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
  (caller : Λ → Statement Γ Λ R)

theorem first_halt_of_actual_local_run {n : Nat} {start finish : Cfg Γ Λ R}
    (executed : LocalRun caller n start finish) (halted : finish.l = none) :
    FirstHalt (step caller) start n finish := by
  exact ⟨executed.iterate caller, halted, executed.owned_prefix caller⟩

theorem first_boundary_of_actual_local_run {n : Nat} {start finish : Cfg Γ Λ R}
    (executed : LocalRun caller n start finish) (external : ¬ Owned finish.l) :
    FirstBoundary (step caller) start n finish := by
  exact ⟨executed.iterate caller, external, executed.owned_prefix caller⟩

theorem first_halt_is_a_first_boundary {n : Nat} {start finish : Cfg Γ Λ R}
    (first : FirstHalt (step caller) start n finish) :
    FirstBoundary (step caller) start n finish := by
  refine ⟨first.1, ?_, first.2.2⟩
  rw [first.2.1]
  exact not_owned_none

theorem actual_first_boundaries_fix_both_time_and_every_field
    {n m : Nat} {start finish other : Cfg Γ Λ R}
    (first : FirstBoundary (step caller) start n finish)
    (second : FirstBoundary (step caller) start m other) : n = m ∧ finish = other :=
  LocalRun.first_unique caller (LocalRun.of_iterate caller first.1 first.2.2)
    (LocalRun.of_iterate caller second.1 second.2.2) first.2.1 second.2.1

theorem all_four_new_joins_execute_one_actual_step (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel rejectPhase)) regs D ctx) =
      some (cfg (some (clearLabel 0)) (answerRegisters false regs) D ctx) ∧
    step caller (cfg (some (phaseLabel dispatchPhase)) regs D ctx) =
      some (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase))) (fullReset regs) D ctx) ∧
    step caller (cfg (some (phaseLabel (resultPhase false))) regs D ctx) =
      some (cfg (some (clearLabel 0)) (answerRegisters false regs) D ctx) ∧
    step caller (cfg (some (phaseLabel (resultPhase true))) regs D ctx) =
      some (cfg (some (clearLabel 0)) (answerRegisters true regs) D ctx) :=
  ⟨reject_step caller D regs ctx, dispatch_step caller D regs ctx,
    result_step caller false D regs ctx, result_step caller true D regs ctx⟩

theorem direct_emit_preserves_other_words_and_pushes_old_fuel
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstHalt (step caller) (cfg (some emitLabel) regs D ctx) 1
      (cfg none (fullReset regs) { D with fuel := answer regs :: D.fuel } ctx) :=
  first_halt_of_actual_local_run caller
    (phase_step_localRun caller (q := emitPhase) (emit_step caller D regs ctx)) rfl

theorem live_halt_has_zero_first_halt_and_keeps_all_dirty_fields
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstHalt (step caller) (cfg none regs D ctx) 0 (cfg none regs D ctx) ∧
    next caller (some (cfg none regs D ctx)) = none := by
  refine ⟨⟨rfl, rfl, ?_⟩, rfl⟩
  intro n strict
  omega

theorem external_first_boundary_is_zero_identity
    (label : Λ) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstBoundary (step caller) (cfg (some (callerLabel label)) regs D ctx) 0
      (cfg (some (callerLabel label)) regs D ctx) := by
  refine ⟨rfl, not_owned_caller label, ?_⟩
  intro n strict
  omega

theorem outer_none_stays_none (n : Nat) : (next caller)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, next_none]

end ActualRuntimeConnections

section EmitPhysicalPeak

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
  (caller : Λ → Statement Γ Λ R)

theorem direct_emitter_has_exact_inclusive_peak
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cfg (some emitLabel) regs D ctx) 1
      (localCells D + 1 + externalCells ctx) := by
  let start : Cfg Γ Λ R := cfg (some emitLabel) regs D ctx
  let finish : Cfg Γ Λ R := cfg none (fullReset regs) (emitData (answer regs) D) ctx
  have one : Runs (step caller) start 1 finish := (direct_emit_preserves_other_words_and_pushes_old_fuel
    caller D regs ctx).1
  have startCells : physicalCells start = localCells D + externalCells ctx :=
    actual_physical_cells_of_cfg _ _ _ _
  have endCells : physicalCells finish = localCells D + 1 + externalCells ctx := by
    rw [show finish = cfg none (fullReset regs) (emitData (answer regs) D) ctx from rfl,
      actual_physical_cells_of_cfg]
    simp only [localCells, emitData, List.length_cons]
    omega
  constructor
  · intro n bound reached executed
    have which : n = 0 ∨ n = 1 := by omega
    rcases which with rfl | rfl
    · have same : start = reached := Option.some.inj executed
      subst reached
      rw [startCells]
      omega
    · have same : finish = reached := Option.some.inj (one.symm.trans executed)
      subst reached
      exact Nat.le_of_eq endCells
  · exact ⟨1, finish, by omega, one, endCells⟩

end EmitPhysicalPeak

/-! ## The exact arbitrary suffix cleaner -/

/-- Independent suffix formula: every earlier word is literal and fuel is one bit. -/
def expectedCleanupData (i : Fin 16) (bit : Bool) (D : LocalData) : LocalData where
  framedRaw := if 0 < i.val then D.framedRaw else []
  frameFirstReverse := if 1 < i.val then D.frameFirstReverse else []
  frameCertReverse := if 2 < i.val then D.frameCertReverse else []
  inputBits := if 3 < i.val then D.inputBits else []
  certificateBits := if 4 < i.val then D.certificateBits else []
  inputRaw := if 5 < i.val then D.inputRaw else []
  decodeReverse := if 6 < i.val then D.decodeReverse else []
  certificateWord := if 7 < i.val then D.certificateWord else []
  sourceTree := if 8 < i.val then D.sourceTree else []
  targetTree := if 9 < i.val then D.targetTree else []
  treeReverse := if 10 < i.val then D.treeReverse else []
  pending := if 11 < i.val then D.pending else []
  bitsReverse := if 12 < i.val then D.bitsReverse else []
  moveReverse := if 13 < i.val then D.moveReverse else []
  path := if 14 < i.val then D.path else []
  fuel := [bit]

theorem actual_cleanup_data_is_the_independent_suffix_formula
    (i : Fin 16) (bit : Bool) (D : LocalData) :
    cleanupData i bit D = expectedCleanupData i bit D := by
  fin_cases i <;> rfl

section CleanupActualRuns

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
  (caller : Λ → Statement Γ Λ R)

theorem cleanup_all_suffixes_execute (i : Fin 16) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstHalt (step caller) (cfg (some (clearLabel i)) regs D ctx)
      (suffixCells i D + (16 - i.val) + 1)
      (cfg none (fullReset regs) (expectedCleanupData i (answer regs) D) ctx) := by
  have run := first_halt_of_actual_local_run caller (cleanup_localRun caller i D regs ctx) rfl
  rw [actual_cleanup_data_is_the_independent_suffix_formula] at run
  exact run

theorem cleanup_current_word_positive_prefix_preserves_the_original_registers_at_zero
    (i : Fin 16) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ slotLength i D) :
    Runs (step caller) (cfg (some (clearLabel i)) regs D ctx) n
      (cfg (some (clearLabel i)) (if n = 0 then regs else occupancyRegisters true regs)
        (dropData i n D) ctx) :=
  (drain_slot_localRun caller i D regs ctx n bound).iterate caller

theorem cleanup_last_occupied_pop_and_the_empty_probe_are_distinct
    (i : Fin 16) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (nonempty : slotLength i D ≠ 0) :
    Runs (step caller) (cfg (some (clearLabel i)) regs D ctx) (slotLength i D)
      (cfg (some (clearLabel i)) (occupancyRegisters true regs) (emptySlot i D) ctx) ∧
    Runs (step caller) (cfg (some (clearLabel i)) regs D ctx) (slotLength i D + 1)
      (cfg (some (nextClear i)) (occupancyRegisters false regs) (emptySlot i D) ctx) := by
  constructor
  · change (next caller)^[slotLength i D]
      (some (cfg (some (clearLabel i)) regs D ctx)) =
      some (cfg (some (clearLabel i)) (occupancyRegisters true regs) (emptySlot i D) ctx)
    simpa only [emptySlot, drainRegisters, nonempty, ite_false] using
      (drain_slot_localRun caller i D regs ctx (slotLength i D) (Nat.le_refl _)).iterate caller
  · exact (clear_slot_localRun caller i D regs ctx).iterate caller

theorem rejecting_join_has_its_whole_halt_after_the_paid_activation
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstHalt (step caller) (cfg (some (phaseLabel rejectPhase)) regs D ctx)
      (1 + cleanupSteps 0 D)
      (cfg none (fullReset regs) (cleanupData 0 false D) ctx) := by
  have head := phase_step_localRun caller (reject_step caller D regs ctx)
  have tail := cleanup_localRun caller 0 D (answerRegisters false regs) ctx
  have run := LocalRun.trans caller head tail
  simp only [fullReset_answerRegisters, answer_answerRegisters] at run
  exact first_halt_of_actual_local_run caller run rfl

theorem boolean_join_has_its_whole_halt_after_the_paid_activation
    (bit : Bool) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstHalt (step caller) (cfg (some (phaseLabel (resultPhase bit))) regs D ctx)
      (1 + cleanupSteps 0 D)
      (cfg none (fullReset regs) (cleanupData 0 bit D) ctx) := by
  have head := phase_step_localRun caller (result_step caller bit D regs ctx)
  have tail := cleanup_localRun caller 0 D (answerRegisters bit regs) ctx
  have run := LocalRun.trans caller head tail
  simp only [fullReset_answerRegisters, answer_answerRegisters] at run
  exact first_halt_of_actual_local_run caller run rfl

theorem clear_C00_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C00.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 0 clear_C00.before (clear_C00.fields.withUser value) ctx

theorem clear_C00E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C00E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 0 clear_C00E.before (clear_C00E.fields.withUser value) ctx

theorem clear_C01_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C01.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 1 clear_C01.before (clear_C01.fields.withUser value) ctx

theorem clear_C01E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C01E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 1 clear_C01E.before (clear_C01E.fields.withUser value) ctx

theorem clear_C02_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C02.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 2 clear_C02.before (clear_C02.fields.withUser value) ctx

theorem clear_C02E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C02E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 2 clear_C02E.before (clear_C02E.fields.withUser value) ctx

theorem clear_C03_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C03.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 3 clear_C03.before (clear_C03.fields.withUser value) ctx

theorem clear_C03E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C03E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 3 clear_C03E.before (clear_C03E.fields.withUser value) ctx

theorem clear_C04_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C04.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 4 clear_C04.before (clear_C04.fields.withUser value) ctx

theorem clear_C04E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C04E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 4 clear_C04E.before (clear_C04E.fields.withUser value) ctx

theorem clear_C05_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C05.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 5 clear_C05.before (clear_C05.fields.withUser value) ctx

theorem clear_C05E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C05E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 5 clear_C05E.before (clear_C05E.fields.withUser value) ctx

theorem clear_C06_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C06.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 6 clear_C06.before (clear_C06.fields.withUser value) ctx

theorem clear_C06E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C06E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 6 clear_C06E.before (clear_C06E.fields.withUser value) ctx

theorem clear_C07_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C07.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 7 clear_C07.before (clear_C07.fields.withUser value) ctx

theorem clear_C07E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C07E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 7 clear_C07E.before (clear_C07E.fields.withUser value) ctx

theorem clear_C08_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C08.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 8 clear_C08.before (clear_C08.fields.withUser value) ctx

theorem clear_C08E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C08E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 8 clear_C08E.before (clear_C08E.fields.withUser value) ctx

theorem clear_C09_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C09.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 9 clear_C09.before (clear_C09.fields.withUser value) ctx

theorem clear_C09E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C09E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 9 clear_C09E.before (clear_C09E.fields.withUser value) ctx

theorem clear_C10_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C10.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 10 clear_C10.before (clear_C10.fields.withUser value) ctx

theorem clear_C10E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C10E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 10 clear_C10E.before (clear_C10E.fields.withUser value) ctx

theorem clear_C11_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C11.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 11 clear_C11.before (clear_C11.fields.withUser value) ctx

theorem clear_C11E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C11E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 11 clear_C11E.before (clear_C11E.fields.withUser value) ctx

theorem clear_C12_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C12.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 12 clear_C12.before (clear_C12.fields.withUser value) ctx

theorem clear_C12E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C12E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 12 clear_C12E.before (clear_C12E.fields.withUser value) ctx

theorem clear_C13_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C13.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 13 clear_C13.before (clear_C13.fields.withUser value) ctx

theorem clear_C13E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C13E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 13 clear_C13E.before (clear_C13E.fields.withUser value) ctx

theorem clear_C14_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C14.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 14 clear_C14.before (clear_C14.fields.withUser value) ctx

theorem clear_C14E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C14E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 14 clear_C14E.before (clear_C14E.fields.withUser value) ctx

theorem clear_C15_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C15.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 15 clear_C15.before (clear_C15.fields.withUser value) ctx

theorem clear_C15E_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C15E.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 15 clear_C15E.before (clear_C15E.fields.withUser value) ctx

theorem emit_E00_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    emit_E00.toClosedFixture.RunExpected (step caller) value ctx :=
  direct_emit_preserves_other_words_and_pushes_old_fuel caller emit_E00.before (emit_E00.fields.withUser value) ctx

theorem emit_E01_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    emit_E01.toClosedFixture.RunExpected (step caller) value ctx :=
  direct_emit_preserves_other_words_and_pushes_old_fuel caller emit_E01.before (emit_E01.fields.withUser value) ctx

theorem emit_E02_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    emit_E02.toClosedFixture.RunExpected (step caller) value ctx :=
  direct_emit_preserves_other_words_and_pushes_old_fuel caller emit_E02.before (emit_E02.fields.withUser value) ctx

theorem emit_E03_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    emit_E03.toClosedFixture.RunExpected (step caller) value ctx :=
  direct_emit_preserves_other_words_and_pushes_old_fuel caller emit_E03.before (emit_E03.fields.withUser value) ctx

theorem join_J00_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    join_J00.toClosedFixture.RunExpected (step caller) value ctx :=
  rejecting_join_has_its_whole_halt_after_the_paid_activation caller join_J00.before (join_J00.fields.withUser value) ctx

theorem join_J01_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    join_J01.toClosedFixture.RunExpected (step caller) value ctx :=
  boolean_join_has_its_whole_halt_after_the_paid_activation caller false join_J01.before (join_J01.fields.withUser value) ctx

theorem join_J02_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    join_J02.toClosedFixture.RunExpected (step caller) value ctx :=
  boolean_join_has_its_whole_halt_after_the_paid_activation caller true join_J02.before (join_J02.fields.withUser value) ctx

theorem clear_CZERO_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_CZERO.toClosedFixture.RunExpected (step caller) value ctx :=
  cleanup_all_suffixes_execute caller 0 clear_CZERO.before (clear_CZERO.fields.withUser value) ctx

theorem all_partial_clear_cases_execute (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ fixture ∈ partialClearCases, fixture.toClosedFixture.RunExpected (step caller) value ctx := by
  intro fixture member
  simp only [partialClearCases, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact clear_C00_actual_first_halt caller value ctx
  · exact clear_C00E_actual_first_halt caller value ctx
  · exact clear_C01_actual_first_halt caller value ctx
  · exact clear_C01E_actual_first_halt caller value ctx
  · exact clear_C02_actual_first_halt caller value ctx
  · exact clear_C02E_actual_first_halt caller value ctx
  · exact clear_C03_actual_first_halt caller value ctx
  · exact clear_C03E_actual_first_halt caller value ctx
  · exact clear_C04_actual_first_halt caller value ctx
  · exact clear_C04E_actual_first_halt caller value ctx
  · exact clear_C05_actual_first_halt caller value ctx
  · exact clear_C05E_actual_first_halt caller value ctx
  · exact clear_C06_actual_first_halt caller value ctx
  · exact clear_C06E_actual_first_halt caller value ctx
  · exact clear_C07_actual_first_halt caller value ctx
  · exact clear_C07E_actual_first_halt caller value ctx
  · exact clear_C08_actual_first_halt caller value ctx
  · exact clear_C08E_actual_first_halt caller value ctx
  · exact clear_C09_actual_first_halt caller value ctx
  · exact clear_C09E_actual_first_halt caller value ctx
  · exact clear_C10_actual_first_halt caller value ctx
  · exact clear_C10E_actual_first_halt caller value ctx
  · exact clear_C11_actual_first_halt caller value ctx
  · exact clear_C11E_actual_first_halt caller value ctx
  · exact clear_C12_actual_first_halt caller value ctx
  · exact clear_C12E_actual_first_halt caller value ctx
  · exact clear_C13_actual_first_halt caller value ctx
  · exact clear_C13E_actual_first_halt caller value ctx
  · exact clear_C14_actual_first_halt caller value ctx
  · exact clear_C14E_actual_first_halt caller value ctx
  · exact clear_C15_actual_first_halt caller value ctx
  · exact clear_C15E_actual_first_halt caller value ctx

end CleanupActualRuns

/-! ## The original FE measurements keep source costs separate from machine time -/

structure FrontEndMeasurements where
  framingTicks : Nat
  inputDecoderTicks : Option Nat
  inputParserTicks : Option Nat
  certificateDecoderTicks : Option Nat
  inputUnpackCost : Option Nat
  inputParseCost : Option Nat
  certificateUnpackCost : Option Nat
  totalFrontEndTicks : Nat
  deriving DecidableEq

/-- Observations of the existing component definitions; this is not controller execution. -/
def observeFrontEndMeasurements (raw : Bits) : FrontEndMeasurements :=
  let f := BitPairFraming.runSteps raw
  match BitPairFraming.unframe raw with
  | none => ⟨f, none, none, none, none, none, none, FrontEndMachine.runSteps raw⟩
  | some (input, cert) =>
    let dI := OpenDecoderMachine.runSteps input
    let cI := (unpackWordRun input).2
    match (unpackWordRun input).1 with
    | none => ⟨f, some dI, none, none, some cI, none, none, FrontEndMachine.runSteps raw⟩
    | some word =>
      let pI := InputParserMachine.inputSteps word
      let cP := (parseInputRun word).2
      match (parseInputRun word).1 with
      | none => ⟨f, some dI, some pI, none, some cI, some cP, none,
          FrontEndMachine.runSteps raw⟩
      | some _ => ⟨f, some dI, some pI, some (OpenDecoderMachine.runSteps cert),
          some cI, some cP, some (unpackWordRun cert).2, FrontEndMachine.runSteps raw⟩

structure SourceObservation where
  fixture : RawFixture
  measurements : FrontEndMeasurements

def SourceObservation.Expected (observation : SourceObservation) : Prop :=
  observeFrontEndMeasurements observation.fixture.raw = observation.measurements ∧
  BitPairFraming.verifyFramed observation.fixture.raw = observation.fixture.result

def source_F01 : SourceObservation :=
  ⟨raw_F01, ⟨2, none, none, none, none, none, none, 2⟩⟩

theorem source_F01_has_its_original_component_tariffs : source_F01.Expected := by
  constructor <;> rfl

def source_F02 : SourceObservation :=
  ⟨raw_F02, ⟨2, none, none, none, none, none, none, 2⟩⟩

theorem source_F02_has_its_original_component_tariffs : source_F02.Expected := by
  constructor <;> rfl

def source_F03 : SourceObservation :=
  ⟨raw_F03, ⟨4, none, none, none, none, none, none, 4⟩⟩

theorem source_F03_has_its_original_component_tariffs : source_F03.Expected := by
  constructor <;> rfl

def source_F04 : SourceObservation :=
  ⟨raw_F04, ⟨4, none, none, none, none, none, none, 4⟩⟩

theorem source_F04_has_its_original_component_tariffs : source_F04.Expected := by
  constructor <;> rfl

def source_F05 : SourceObservation :=
  ⟨raw_F05, ⟨4, some 2, some 5, none, some 2, some 4, none, 11⟩⟩

theorem source_F05_has_its_original_component_tariffs : source_F05.Expected := by
  constructor <;> rfl

def source_F06 : SourceObservation :=
  ⟨raw_F06, ⟨6, some 2, some 5, none, some 2, some 4, none, 13⟩⟩

theorem source_F06_has_its_original_component_tariffs : source_F06.Expected := by
  constructor <;> rfl

def source_F07 : SourceObservation :=
  ⟨raw_F07, ⟨6, some 2, none, none, some 2, none, none, 8⟩⟩

theorem source_F07_has_its_original_component_tariffs : source_F07.Expected := by
  constructor <;> rfl

def source_F08 : SourceObservation :=
  ⟨raw_F08, ⟨12, some 2, none, none, some 2, none, none, 14⟩⟩

theorem source_F08_has_its_original_component_tariffs : source_F08.Expected := by
  constructor <;> rfl

def source_I01 : SourceObservation :=
  ⟨raw_I01, ⟨12, some 4, some 9, none, some 6, some 7, none, 25⟩⟩

theorem source_I01_has_its_original_component_tariffs : source_I01.Expected := by
  constructor <;> rfl

def source_I02 : SourceObservation :=
  ⟨raw_I02, ⟨14, some 4, some 5, none, some 6, some 4, none, 23⟩⟩

theorem source_I02_has_its_original_component_tariffs : source_I02.Expected := by
  constructor <;> rfl

def source_I03 : SourceObservation :=
  ⟨raw_I03, ⟨36, some 10, some 9, none, some 18, some 7, none, 55⟩⟩

theorem source_I03_has_its_original_component_tariffs : source_I03.Expected := by
  constructor <;> rfl

def source_I04 : SourceObservation :=
  ⟨raw_I04, ⟨52, some 14, some 26, none, some 26, some 15, none, 92⟩⟩

theorem source_I04_has_its_original_component_tariffs : source_I04.Expected := by
  constructor <;> rfl

def source_I05 : SourceObservation :=
  ⟨raw_I05, ⟨52, some 14, some 22, none, some 26, some 14, none, 88⟩⟩

theorem source_I05_has_its_original_component_tariffs : source_I05.Expected := by
  constructor <;> rfl

def source_I06 : SourceObservation :=
  ⟨raw_I06, ⟨116, some 26, some 12, none, some 50, some 11, none, 154⟩⟩

theorem source_I06_has_its_original_component_tariffs : source_I06.Expected := by
  constructor <;> rfl

def source_I07 : SourceObservation :=
  ⟨raw_I07, ⟨44, some 12, some 5, none, some 22, some 4, none, 61⟩⟩

theorem source_I07_has_its_original_component_tariffs : source_I07.Expected := by
  constructor <;> rfl

def source_C01 : SourceObservation :=
  ⟨raw_C01, ⟨46, some 12, some 13, some 2, some 22, some 15, some 2, 73⟩⟩

theorem source_C01_has_its_original_component_tariffs : source_C01.Expected := by
  constructor <;> rfl

def source_C02 : SourceObservation :=
  ⟨raw_C02, ⟨70, some 16, some 17, some 4, some 30, some 21, some 4, 107⟩⟩

theorem source_C02_has_its_original_component_tariffs : source_C02.Expected := by
  constructor <;> rfl

def source_C03 : SourceObservation :=
  ⟨raw_C03, ⟨134, some 30, some 31, some 6, some 58, some 46, some 6, 201⟩⟩

theorem source_C03_has_its_original_component_tariffs : source_C03.Expected := by
  constructor <;> rfl

def source_V01 : SourceObservation :=
  ⟨raw_V01, ⟨44, some 12, some 13, some 2, some 22, some 15, some 2, 71⟩⟩

theorem source_V01_has_its_original_component_tariffs : source_V01.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [] (.nil : BinaryTree Unit)
      (.nil : BinaryTree Unit) []).1 = true
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V02 : SourceObservation :=
  ⟨raw_V02, ⟨60, some 16, some 17, some 2, some 30, some 22, some 2, 95⟩⟩

theorem source_V02_has_its_original_component_tariffs : source_V02.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [] (.nil : BinaryTree Unit)
      (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) []).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V03 : SourceObservation :=
  ⟨raw_V03, ⟨132, some 30, some 31, some 6, some 58, some 46, some 10, 199⟩⟩

theorem source_V03_has_its_original_component_tariffs : source_V03.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit)) [6, 10]).1 = true
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V04 : SourceObservation :=
  ⟨raw_V04, ⟨132, some 30, some 31, some 6, some 58, some 46, some 10, 199⟩⟩

theorem source_V04_has_its_original_component_tariffs : source_V04.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit))
      (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit))) [7, 10]).1 = true
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V05 : SourceObservation :=
  ⟨raw_V05, ⟨156, some 32, some 33, some 10, some 62, some 49, some 18, 231⟩⟩

theorem source_V05_has_its_original_component_tariffs : source_V05.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [false, true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit))) [6, 10, 7, 10]).1 = true
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V06 : SourceObservation :=
  ⟨raw_V06, ⟨148, some 30, some 31, some 10, some 58, some 46, some 18, 219⟩⟩

theorem source_V06_has_its_original_component_tariffs : source_V06.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit))) [6, 10, 7, 10]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V07 : SourceObservation :=
  ⟨raw_V07, ⟨140, some 32, some 33, some 6, some 62, some 49, some 10, 211⟩⟩

theorem source_V07_has_its_original_component_tariffs : source_V07.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [false, false] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit))) [6, 10]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V08 : SourceObservation :=
  ⟨raw_V08, ⟨148, some 34, some 35, some 6, some 66, some 52, some 10, 223⟩⟩

theorem source_V08_has_its_original_component_tariffs : source_V08.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true, false, false] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit)) [6, 10]).1 = true
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V09 : SourceObservation :=
  ⟨raw_V09, ⟨124, some 30, some 31, some 4, some 58, some 46, some 6, 189⟩⟩

theorem source_V09_has_its_original_component_tariffs : source_V09.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit)) [6]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V10 : SourceObservation :=
  ⟨raw_V10, ⟨140, some 30, some 31, some 8, some 58, some 46, some 14, 209⟩⟩

theorem source_V10_has_its_original_component_tariffs : source_V10.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit)) [6, 15, 10]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V11 : SourceObservation :=
  ⟨raw_V11, ⟨140, some 30, some 31, some 8, some 58, some 46, some 14, 209⟩⟩

theorem source_V11_has_its_original_component_tariffs : source_V11.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit)) [6, 8, 10]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V12 : SourceObservation :=
  ⟨raw_V12, ⟨132, some 30, some 31, some 6, some 58, some 46, some 10, 199⟩⟩

theorem source_V12_has_its_original_component_tariffs : source_V12.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit))) [7, 10]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V13 : SourceObservation :=
  ⟨raw_V13, ⟨172, some 38, some 39, some 8, some 74, some 60, some 14, 257⟩⟩

theorem source_V13_has_its_original_component_tariffs : source_V13.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit))))
      (.node () (.nil : BinaryTree Unit) (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit))) [6, 9, 10]).1 = true
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V14 : SourceObservation :=
  ⟨raw_V14, ⟨140, some 30, some 31, some 8, some 58, some 46, some 14, 209⟩⟩

theorem source_V14_has_its_original_component_tariffs : source_V14.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit)) [6, 10, 15]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V15 : SourceObservation :=
  ⟨raw_V15, ⟨60, some 16, some 17, some 2, some 30, some 21, some 2, 95⟩⟩

theorem source_V15_has_its_original_component_tariffs : source_V15.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [false, false] (.nil : BinaryTree Unit)
      (.nil : BinaryTree Unit) []).1 = true
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V16 : SourceObservation :=
  ⟨raw_V16, ⟨124, some 30, some 31, some 4, some 58, some 46, some 6, 189⟩⟩

theorem source_V16_has_its_original_component_tariffs : source_V16.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit))) [15]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V17 : SourceObservation :=
  ⟨raw_V17, ⟨68, some 14, some 15, some 6, some 26, some 18, some 10, 103⟩⟩

theorem source_V17_has_its_original_component_tariffs : source_V17.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [true] (.nil : BinaryTree Unit)
      (.nil : BinaryTree Unit) [6, 10]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def source_V18 : SourceObservation :=
  ⟨raw_V18, ⟨124, some 28, some 29, some 6, some 54, some 43, some 10, 187⟩⟩

theorem source_V18_has_its_original_component_tariffs : source_V18.Expected := by
  constructor
  · rfl
  · change (checkStreamRun [] (.node () (.nil : BinaryTree Unit) (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)))
      (.node () (.node () (.nil : BinaryTree Unit) (.nil : BinaryTree Unit)) (.nil : BinaryTree Unit)) [6, 10]).1 = false
    norm_num [checkStreamRun_nil, checkStreamRun_cons,
      Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
      applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
      rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
      Resources.bind, Resources.CallCount.tick]

def originalSourceObservations : List SourceObservation :=
  [source_F01, source_F02, source_F03, source_F04, source_F05, source_F06, source_F07, source_F08, source_I01, source_I02, source_I03, source_I04, source_I05, source_I06, source_I07, source_C01, source_C02, source_C03, source_V01, source_V02, source_V03, source_V04, source_V05, source_V06, source_V07, source_V08, source_V09, source_V10, source_V11, source_V12, source_V13, source_V14, source_V15, source_V16, source_V17, source_V18]

theorem original_source_observations_count : originalSourceObservations.length = 36 := rfl

theorem original_source_observations_keep_their_own_tariffs :
    ∀ observation ∈ originalSourceObservations, observation.Expected := by
  intro observation member
  simp only [originalSourceObservations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact source_F01_has_its_original_component_tariffs
  · exact source_F02_has_its_original_component_tariffs
  · exact source_F03_has_its_original_component_tariffs
  · exact source_F04_has_its_original_component_tariffs
  · exact source_F05_has_its_original_component_tariffs
  · exact source_F06_has_its_original_component_tariffs
  · exact source_F07_has_its_original_component_tariffs
  · exact source_F08_has_its_original_component_tariffs
  · exact source_I01_has_its_original_component_tariffs
  · exact source_I02_has_its_original_component_tariffs
  · exact source_I03_has_its_original_component_tariffs
  · exact source_I04_has_its_original_component_tariffs
  · exact source_I05_has_its_original_component_tariffs
  · exact source_I06_has_its_original_component_tariffs
  · exact source_I07_has_its_original_component_tariffs
  · exact source_C01_has_its_original_component_tariffs
  · exact source_C02_has_its_original_component_tariffs
  · exact source_C03_has_its_original_component_tariffs
  · exact source_V01_has_its_original_component_tariffs
  · exact source_V02_has_its_original_component_tariffs
  · exact source_V03_has_its_original_component_tariffs
  · exact source_V04_has_its_original_component_tariffs
  · exact source_V05_has_its_original_component_tariffs
  · exact source_V06_has_its_original_component_tariffs
  · exact source_V07_has_its_original_component_tariffs
  · exact source_V08_has_its_original_component_tariffs
  · exact source_V09_has_its_original_component_tariffs
  · exact source_V10_has_its_original_component_tariffs
  · exact source_V11_has_its_original_component_tariffs
  · exact source_V12_has_its_original_component_tariffs
  · exact source_V13_has_its_original_component_tariffs
  · exact source_V14_has_its_original_component_tariffs
  · exact source_V15_has_its_original_component_tariffs
  · exact source_V16_has_its_original_component_tariffs
  · exact source_V17_has_its_original_component_tariffs
  · exact source_V18_has_its_original_component_tariffs

/-- These tariffs refer to the unframed source verifier, not the physical closed clock. -/
theorem all_four_source_tariffs_keep_their_original_priority
    (input cert : Bits) :
    ((unpackWordRun input).1 = none →
      verifyBitsRun input cert = (false, (unpackWordRun input).2 + 2)) ∧
    (∀ word, (unpackWordRun input).1 = some word → (parseInputRun word).1 = none →
      verifyBitsRun input cert = (false, (unpackWordRun input).2 + (parseInputRun word).2 + 2)) ∧
    (∀ word source target fuel, (unpackWordRun input).1 = some word →
      (parseInputRun word).1 = some (source, target, fuel) → (unpackWordRun cert).1 = none →
      verifyBitsRun input cert =
        (false, (unpackWordRun input).2 + (parseInputRun word).2 + (unpackWordRun cert).2 + 2)) ∧
    (∀ word moves source target fuel, (unpackWordRun input).1 = some word →
      (parseInputRun word).1 = some (source, target, fuel) → (unpackWordRun cert).1 = some moves →
      verifyBitsRun input cert =
        ((checkStreamRun fuel source target moves).1,
          (unpackWordRun input).2 + (parseInputRun word).2 + (unpackWordRun cert).2 +
            (checkStreamRun fuel source target moves).2 + 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact verifyBitsRun_input_none input cert
  · intro word decoded parsed
    exact verifyBitsRun_parse_none input cert word decoded parsed
  · intro word source target fuel decoded parsed failed
    exact verifyBitsRun_certificate_none input cert word source target fuel decoded parsed failed
  · intro word moves source target fuel decoded parsed certificate
    exact verifyBitsRun_success input cert word moves source target fuel decoded parsed certificate

/-! ## Exhaustive domains and exact physical cleanup contracts -/

-- Name the component decisions so the complete finite sum is synthesized at defaults.
local instance : DecidableEq (FrontEndMachine.ExtraLabel Empty) := inferInstance
local instance : DecidableEq (FrontEndMachine.Label Empty) := inferInstance
local instance : DecidableEq (FuelDispatchMachine.Label Empty) := inferInstance
local instance : DecidableEq (MoveApplyMachine.External Empty) := inferInstance
local instance : DecidableEq (MoveApplyMachine.Label Empty) := inferInstance
local instance : DecidableEq (TreeEqualityMachine.Label Empty) := inferInstance
local instance : DecidableEq (StreamMachine.Label Empty) := inferInstance
local instance : DecidableEq Phase := inferInstance

theorem the_96_phase_domains_are_distinct : phaseDomains.Nodup := by decide

theorem the_96_phase_domains_are_complete (phase : Phase) : phase ∈ phaseDomains := by
  have cardinality : phaseDomains.toFinset.card = Fintype.card Phase := by
    rw [List.toFinset_card_of_nodup the_96_phase_domains_are_distinct,
      phase_domains_count, card_phase]
  have complete := Finset.eq_univ_of_card phaseDomains.toFinset cardinality
  exact List.mem_toFinset.mp (complete ▸ Finset.mem_univ phase)

section ExactPhysicalConnections

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
  (caller : Λ → Statement Γ Λ R)

theorem exact_peak_from_the_actual_public_prefix_contract
    {start : Cfg Γ Λ R} {ticks peak : Nat}
    (checked : Resources.RotationCertificate.FrontEndStreamMachine.ExactPeak caller start ticks peak) :
    ExactPeak (step caller) start ticks peak := by
  constructor
  · exact checked.1
  · obtain ⟨n, bound, reached, executed, cells⟩ := checked.2
    exact ⟨n, reached, bound, executed, cells⟩

theorem arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak
    (index : Fin 16) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cfg (some (clearLabel index)) regs D ctx)
      (suffixCells index D + (16 - index.val) + 1)
      (max (prefixCells index D + suffixCells index D) (prefixCells index D + 1) + externalCells ctx) :=
  exact_peak_from_the_actual_public_prefix_contract caller (cleanup_peak caller index D regs ctx)

/-- Compose actual inclusive prefixes; the peak is attained in one of the two segments. -/
theorem exact_peaks_compose
    {start middle : Cfg Γ Λ R} {m n firstPeak secondPeak : Nat}
    (executed : Runs (step caller) start m middle)
    (first : ExactPeak (step caller) start m firstPeak)
    (second : ExactPeak (step caller) middle n secondPeak) :
    ExactPeak (step caller) start (m + n) (max firstPeak secondPeak) := by
  constructor
  · exact PrefixProperty.trans caller executed
      (fun j bound reached run => (first.1 j bound reached run).trans (Nat.le_max_left _ _))
      (fun j bound reached run => (second.1 j bound reached run).trans (Nat.le_max_right _ _))
  · by_cases larger : secondPeak ≤ firstPeak
    · obtain ⟨j, reached, bound, run, cells⟩ := first.2
      exact ⟨j, reached, by omega, run, cells.trans (Nat.max_eq_left larger).symm⟩
    · obtain ⟨j, reached, bound, run, cells⟩ := second.2
      refine ⟨j + m, reached, by omega, ?_, cells.trans (Nat.max_eq_right (by omega)).symm⟩
      change (next caller)^[j + m] (some start) = some reached
      change (next caller)^[m] (some start) = some middle at executed
      rw [Function.iterate_add_apply, executed]
      exact run

/-- A load-and-goto join changes no physical word, including at its endpoint. -/
theorem one_step_with_unchanged_words_has_its_initial_mass_as_peak
    {start finish : Cfg Γ Λ R} (executed : step caller start = some finish)
    (same : physicalCells finish = physicalCells start) :
    ExactPeak (step caller) start 1 (physicalCells start) := by
  have run : Runs (step caller) start 1 finish := executed
  constructor
  · intro n bound reached arrived
    have cases : n = 0 ∨ n = 1 := by omega
    rcases cases with rfl | rfl
    · have equal := Option.some.inj arrived
      subst reached
      exact Nat.le_refl _
    · have equal := Option.some.inj (run.symm.trans arrived)
      subst reached
      exact Nat.le_of_eq same
  · exact ⟨0, start, by omega, rfl, rfl⟩

theorem rejecting_join_has_the_exact_cleanup_peak
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cfg (some (phaseLabel rejectPhase)) regs D ctx)
      (1 + cleanupSteps 0 D) (max (localCells D) 1 + externalCells ctx) := by
  have first := one_step_with_unchanged_words_has_its_initial_mass_as_peak caller
    (reject_step caller D regs ctx) (by rw [actual_physical_cells_of_cfg, actual_physical_cells_of_cfg])
  have second := arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller
    0 D (answerRegisters false regs) ctx
  have joined := exact_peaks_compose caller ((phase_step_localRun caller (reject_step caller D regs ctx)).iterate caller)
    first second
  rw [actual_physical_cells_of_cfg] at joined
  have prefixZero : prefixCells 0 D = 0 := by
    simp [prefixCells, suffixCells, localCells]
  rw [prefixZero, Nat.zero_add, Nat.zero_add] at joined
  have suffixZero : suffixCells 0 D = localCells D := by
    simpa only [prefixZero, Nat.zero_add] using prefixCells_add_suffixCells 0 D
  rw [suffixZero] at joined
  have equation : max (localCells D + externalCells ctx)
      (max (localCells D) 1 + externalCells ctx) = max (localCells D) 1 + externalCells ctx :=
    Nat.max_eq_right (Nat.add_le_add_right (Nat.le_max_left _ _) _)
  exact equation ▸ joined

theorem boolean_join_has_the_exact_cleanup_peak
    (bit : Bool) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (cfg (some (phaseLabel (resultPhase bit))) regs D ctx)
      (1 + cleanupSteps 0 D) (max (localCells D) 1 + externalCells ctx) := by
  have first := one_step_with_unchanged_words_has_its_initial_mass_as_peak caller
    (result_step caller bit D regs ctx) (by rw [actual_physical_cells_of_cfg, actual_physical_cells_of_cfg])
  have second := arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller
    0 D (answerRegisters bit regs) ctx
  have joined := exact_peaks_compose caller ((phase_step_localRun caller (result_step caller bit D regs ctx)).iterate caller)
    first second
  rw [actual_physical_cells_of_cfg] at joined
  have prefixZero : prefixCells 0 D = 0 := by
    simp [prefixCells, suffixCells, localCells]
  rw [prefixZero, Nat.zero_add, Nat.zero_add] at joined
  have suffixZero : suffixCells 0 D = localCells D := by
    simpa only [prefixZero, Nat.zero_add] using prefixCells_add_suffixCells 0 D
  rw [suffixZero] at joined
  have equation : max (localCells D + externalCells ctx)
      (max (localCells D) 1 + externalCells ctx) = max (localCells D) 1 + externalCells ctx :=
    Nat.max_eq_right (Nat.add_le_add_right (Nat.le_max_left _ _) _)
  exact equation ▸ joined

theorem clear_C00_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C00.toClosedFixture.start value ctx) clear_C00.ticks
      (clear_C00.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 0
    clear_C00.before (clear_C00.fields.withUser value) ctx

theorem clear_C00_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C00.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C00_actual_first_halt caller value ctx, clear_C00_actual_exact_peak caller value ctx⟩

theorem clear_C00E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C00E.toClosedFixture.start value ctx) clear_C00E.ticks
      (clear_C00E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 0
    clear_C00E.before (clear_C00E.fields.withUser value) ctx

theorem clear_C00E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C00E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C00E_actual_first_halt caller value ctx, clear_C00E_actual_exact_peak caller value ctx⟩

theorem clear_C01_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C01.toClosedFixture.start value ctx) clear_C01.ticks
      (clear_C01.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 1
    clear_C01.before (clear_C01.fields.withUser value) ctx

theorem clear_C01_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C01.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C01_actual_first_halt caller value ctx, clear_C01_actual_exact_peak caller value ctx⟩

theorem clear_C01E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C01E.toClosedFixture.start value ctx) clear_C01E.ticks
      (clear_C01E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 1
    clear_C01E.before (clear_C01E.fields.withUser value) ctx

theorem clear_C01E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C01E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C01E_actual_first_halt caller value ctx, clear_C01E_actual_exact_peak caller value ctx⟩

theorem clear_C02_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C02.toClosedFixture.start value ctx) clear_C02.ticks
      (clear_C02.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 2
    clear_C02.before (clear_C02.fields.withUser value) ctx

theorem clear_C02_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C02.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C02_actual_first_halt caller value ctx, clear_C02_actual_exact_peak caller value ctx⟩

theorem clear_C02E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C02E.toClosedFixture.start value ctx) clear_C02E.ticks
      (clear_C02E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 2
    clear_C02E.before (clear_C02E.fields.withUser value) ctx

theorem clear_C02E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C02E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C02E_actual_first_halt caller value ctx, clear_C02E_actual_exact_peak caller value ctx⟩

theorem clear_C03_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C03.toClosedFixture.start value ctx) clear_C03.ticks
      (clear_C03.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 3
    clear_C03.before (clear_C03.fields.withUser value) ctx

theorem clear_C03_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C03.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C03_actual_first_halt caller value ctx, clear_C03_actual_exact_peak caller value ctx⟩

theorem clear_C03E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C03E.toClosedFixture.start value ctx) clear_C03E.ticks
      (clear_C03E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 3
    clear_C03E.before (clear_C03E.fields.withUser value) ctx

theorem clear_C03E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C03E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C03E_actual_first_halt caller value ctx, clear_C03E_actual_exact_peak caller value ctx⟩

theorem clear_C04_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C04.toClosedFixture.start value ctx) clear_C04.ticks
      (clear_C04.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 4
    clear_C04.before (clear_C04.fields.withUser value) ctx

theorem clear_C04_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C04.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C04_actual_first_halt caller value ctx, clear_C04_actual_exact_peak caller value ctx⟩

theorem clear_C04E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C04E.toClosedFixture.start value ctx) clear_C04E.ticks
      (clear_C04E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 4
    clear_C04E.before (clear_C04E.fields.withUser value) ctx

theorem clear_C04E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C04E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C04E_actual_first_halt caller value ctx, clear_C04E_actual_exact_peak caller value ctx⟩

theorem clear_C05_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C05.toClosedFixture.start value ctx) clear_C05.ticks
      (clear_C05.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 5
    clear_C05.before (clear_C05.fields.withUser value) ctx

theorem clear_C05_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C05.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C05_actual_first_halt caller value ctx, clear_C05_actual_exact_peak caller value ctx⟩

theorem clear_C05E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C05E.toClosedFixture.start value ctx) clear_C05E.ticks
      (clear_C05E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 5
    clear_C05E.before (clear_C05E.fields.withUser value) ctx

theorem clear_C05E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C05E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C05E_actual_first_halt caller value ctx, clear_C05E_actual_exact_peak caller value ctx⟩

theorem clear_C06_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C06.toClosedFixture.start value ctx) clear_C06.ticks
      (clear_C06.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 6
    clear_C06.before (clear_C06.fields.withUser value) ctx

theorem clear_C06_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C06.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C06_actual_first_halt caller value ctx, clear_C06_actual_exact_peak caller value ctx⟩

theorem clear_C06E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C06E.toClosedFixture.start value ctx) clear_C06E.ticks
      (clear_C06E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 6
    clear_C06E.before (clear_C06E.fields.withUser value) ctx

theorem clear_C06E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C06E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C06E_actual_first_halt caller value ctx, clear_C06E_actual_exact_peak caller value ctx⟩

theorem clear_C07_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C07.toClosedFixture.start value ctx) clear_C07.ticks
      (clear_C07.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 7
    clear_C07.before (clear_C07.fields.withUser value) ctx

theorem clear_C07_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C07.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C07_actual_first_halt caller value ctx, clear_C07_actual_exact_peak caller value ctx⟩

theorem clear_C07E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C07E.toClosedFixture.start value ctx) clear_C07E.ticks
      (clear_C07E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 7
    clear_C07E.before (clear_C07E.fields.withUser value) ctx

theorem clear_C07E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C07E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C07E_actual_first_halt caller value ctx, clear_C07E_actual_exact_peak caller value ctx⟩

theorem clear_C08_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C08.toClosedFixture.start value ctx) clear_C08.ticks
      (clear_C08.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 8
    clear_C08.before (clear_C08.fields.withUser value) ctx

theorem clear_C08_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C08.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C08_actual_first_halt caller value ctx, clear_C08_actual_exact_peak caller value ctx⟩

theorem clear_C08E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C08E.toClosedFixture.start value ctx) clear_C08E.ticks
      (clear_C08E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 8
    clear_C08E.before (clear_C08E.fields.withUser value) ctx

theorem clear_C08E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C08E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C08E_actual_first_halt caller value ctx, clear_C08E_actual_exact_peak caller value ctx⟩

theorem clear_C09_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C09.toClosedFixture.start value ctx) clear_C09.ticks
      (clear_C09.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 9
    clear_C09.before (clear_C09.fields.withUser value) ctx

theorem clear_C09_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C09.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C09_actual_first_halt caller value ctx, clear_C09_actual_exact_peak caller value ctx⟩

theorem clear_C09E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C09E.toClosedFixture.start value ctx) clear_C09E.ticks
      (clear_C09E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 9
    clear_C09E.before (clear_C09E.fields.withUser value) ctx

theorem clear_C09E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C09E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C09E_actual_first_halt caller value ctx, clear_C09E_actual_exact_peak caller value ctx⟩

theorem clear_C10_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C10.toClosedFixture.start value ctx) clear_C10.ticks
      (clear_C10.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 10
    clear_C10.before (clear_C10.fields.withUser value) ctx

theorem clear_C10_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C10.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C10_actual_first_halt caller value ctx, clear_C10_actual_exact_peak caller value ctx⟩

theorem clear_C10E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C10E.toClosedFixture.start value ctx) clear_C10E.ticks
      (clear_C10E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 10
    clear_C10E.before (clear_C10E.fields.withUser value) ctx

theorem clear_C10E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C10E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C10E_actual_first_halt caller value ctx, clear_C10E_actual_exact_peak caller value ctx⟩

theorem clear_C11_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C11.toClosedFixture.start value ctx) clear_C11.ticks
      (clear_C11.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 11
    clear_C11.before (clear_C11.fields.withUser value) ctx

theorem clear_C11_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C11.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C11_actual_first_halt caller value ctx, clear_C11_actual_exact_peak caller value ctx⟩

theorem clear_C11E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C11E.toClosedFixture.start value ctx) clear_C11E.ticks
      (clear_C11E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 11
    clear_C11E.before (clear_C11E.fields.withUser value) ctx

theorem clear_C11E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C11E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C11E_actual_first_halt caller value ctx, clear_C11E_actual_exact_peak caller value ctx⟩

theorem clear_C12_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C12.toClosedFixture.start value ctx) clear_C12.ticks
      (clear_C12.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 12
    clear_C12.before (clear_C12.fields.withUser value) ctx

theorem clear_C12_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C12.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C12_actual_first_halt caller value ctx, clear_C12_actual_exact_peak caller value ctx⟩

theorem clear_C12E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C12E.toClosedFixture.start value ctx) clear_C12E.ticks
      (clear_C12E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 12
    clear_C12E.before (clear_C12E.fields.withUser value) ctx

theorem clear_C12E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C12E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C12E_actual_first_halt caller value ctx, clear_C12E_actual_exact_peak caller value ctx⟩

theorem clear_C13_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C13.toClosedFixture.start value ctx) clear_C13.ticks
      (clear_C13.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 13
    clear_C13.before (clear_C13.fields.withUser value) ctx

theorem clear_C13_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C13.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C13_actual_first_halt caller value ctx, clear_C13_actual_exact_peak caller value ctx⟩

theorem clear_C13E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C13E.toClosedFixture.start value ctx) clear_C13E.ticks
      (clear_C13E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 13
    clear_C13E.before (clear_C13E.fields.withUser value) ctx

theorem clear_C13E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C13E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C13E_actual_first_halt caller value ctx, clear_C13E_actual_exact_peak caller value ctx⟩

theorem clear_C14_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C14.toClosedFixture.start value ctx) clear_C14.ticks
      (clear_C14.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 14
    clear_C14.before (clear_C14.fields.withUser value) ctx

theorem clear_C14_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C14.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C14_actual_first_halt caller value ctx, clear_C14_actual_exact_peak caller value ctx⟩

theorem clear_C14E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C14E.toClosedFixture.start value ctx) clear_C14E.ticks
      (clear_C14E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 14
    clear_C14E.before (clear_C14E.fields.withUser value) ctx

theorem clear_C14E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C14E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C14E_actual_first_halt caller value ctx, clear_C14E_actual_exact_peak caller value ctx⟩

theorem clear_C15_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C15.toClosedFixture.start value ctx) clear_C15.ticks
      (clear_C15.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 15
    clear_C15.before (clear_C15.fields.withUser value) ctx

theorem clear_C15_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C15.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C15_actual_first_halt caller value ctx, clear_C15_actual_exact_peak caller value ctx⟩

theorem clear_C15E_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_C15E.toClosedFixture.start value ctx) clear_C15E.ticks
      (clear_C15E.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 15
    clear_C15E.before (clear_C15E.fields.withUser value) ctx

theorem clear_C15E_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_C15E.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_C15E_actual_first_halt caller value ctx, clear_C15E_actual_exact_peak caller value ctx⟩

theorem emit_E00_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (emit_E00.toClosedFixture.start value ctx) emit_E00.ticks
      (emit_E00.peak + externalCells ctx) :=
  direct_emitter_has_exact_inclusive_peak caller emit_E00.before (emit_E00.fields.withUser value) ctx

theorem emit_E00_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    emit_E00.toClosedFixture.Expected (step caller) value ctx :=
  ⟨emit_E00_actual_first_halt caller value ctx, emit_E00_actual_exact_peak caller value ctx⟩

theorem emit_E01_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (emit_E01.toClosedFixture.start value ctx) emit_E01.ticks
      (emit_E01.peak + externalCells ctx) :=
  direct_emitter_has_exact_inclusive_peak caller emit_E01.before (emit_E01.fields.withUser value) ctx

theorem emit_E01_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    emit_E01.toClosedFixture.Expected (step caller) value ctx :=
  ⟨emit_E01_actual_first_halt caller value ctx, emit_E01_actual_exact_peak caller value ctx⟩

theorem emit_E02_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (emit_E02.toClosedFixture.start value ctx) emit_E02.ticks
      (emit_E02.peak + externalCells ctx) :=
  direct_emitter_has_exact_inclusive_peak caller emit_E02.before (emit_E02.fields.withUser value) ctx

theorem emit_E02_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    emit_E02.toClosedFixture.Expected (step caller) value ctx :=
  ⟨emit_E02_actual_first_halt caller value ctx, emit_E02_actual_exact_peak caller value ctx⟩

theorem emit_E03_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (emit_E03.toClosedFixture.start value ctx) emit_E03.ticks
      (emit_E03.peak + externalCells ctx) :=
  direct_emitter_has_exact_inclusive_peak caller emit_E03.before (emit_E03.fields.withUser value) ctx

theorem emit_E03_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    emit_E03.toClosedFixture.Expected (step caller) value ctx :=
  ⟨emit_E03_actual_first_halt caller value ctx, emit_E03_actual_exact_peak caller value ctx⟩

theorem join_J00_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (join_J00.toClosedFixture.start value ctx) join_J00.ticks
      (join_J00.peak + externalCells ctx) :=
  rejecting_join_has_the_exact_cleanup_peak caller join_J00.before (join_J00.fields.withUser value) ctx

theorem join_J00_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    join_J00.toClosedFixture.Expected (step caller) value ctx :=
  ⟨join_J00_actual_first_halt caller value ctx, join_J00_actual_exact_peak caller value ctx⟩

theorem join_J01_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (join_J01.toClosedFixture.start value ctx) join_J01.ticks
      (join_J01.peak + externalCells ctx) :=
  boolean_join_has_the_exact_cleanup_peak caller false join_J01.before (join_J01.fields.withUser value) ctx

theorem join_J01_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    join_J01.toClosedFixture.Expected (step caller) value ctx :=
  ⟨join_J01_actual_first_halt caller value ctx, join_J01_actual_exact_peak caller value ctx⟩

theorem join_J02_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (join_J02.toClosedFixture.start value ctx) join_J02.ticks
      (join_J02.peak + externalCells ctx) :=
  boolean_join_has_the_exact_cleanup_peak caller true join_J02.before (join_J02.fields.withUser value) ctx

theorem join_J02_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    join_J02.toClosedFixture.Expected (step caller) value ctx :=
  ⟨join_J02_actual_first_halt caller value ctx, join_J02_actual_exact_peak caller value ctx⟩

theorem clear_CZERO_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (clear_CZERO.toClosedFixture.start value ctx) clear_CZERO.ticks
      (clear_CZERO.peak + externalCells ctx) :=
  arbitrary_cleanup_has_both_its_upper_bound_and_an_attained_peak caller 0
    clear_CZERO.before (clear_CZERO.fields.withUser value) ctx

theorem clear_CZERO_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    clear_CZERO.toClosedFixture.Expected (step caller) value ctx :=
  ⟨clear_CZERO_actual_first_halt caller value ctx, clear_CZERO_actual_exact_peak caller value ctx⟩

end ExactPhysicalConnections

/-! ## The fixed selected cleanup boundaries are actual configurations -/

section CleanupBoundaryConnections

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
  (caller : Λ → Statement Γ Λ R)

omit [Fintype K] in
/-- All intermediate slot prefixes use the real transported finite cleaner. -/
theorem every_indexed_cleanup_prefix_retains_all_nonactive_words
    (i j : Fin 16) (t : Nat) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (ordered : i.val ≤ j.val) (within : t ≤ slotLength j D) :
    Runs (step caller) (cfg (some (clearLabel i)) regs D ctx)
      ((∑ k : Fin 16, if i.val ≤ k.val ∧ k.val < j.val then slotLength k D + 1 else 0) + t)
      (cfg (some (clearLabel j))
        (if t = 0 then (if i = j then regs else occupancyRegisters false regs)
          else occupancyRegisters true regs)
        (dropData j t (boundaryData i j D)) ctx) := by
  have run := cleanup_prefix_iterate caller i j t D regs ctx ordered within
  have registers := cleanupPrefixCfg_registers (Λ := Λ) i j t regs D ctx
  change (drainRegisters (boundaryRegisters i j regs) t) = _ at registers
  change (next caller)^[boundarySteps i j D + t]
    (some (cfg (some (clearLabel i)) regs D ctx)) = _
  simpa only [cleanupPrefixCfg, registers] using run

theorem clear_C00_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C00_boundaries,
      point.Expected clear_C00.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C00_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 0 clear_C00.before (clear_C00.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 0 clear_C00.before (clear_C00.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 0 15 clear_C00.before (clear_C00.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 0 15 clear_C00.before)
          (boundaryRegisters 0 15 (clear_C00.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C00_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C00E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C00E_boundaries,
      point.Expected clear_C00E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C00E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 0 clear_C00E.before (clear_C00E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 0 15 clear_C00E.before (clear_C00E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 0 15 clear_C00E.before)
          (boundaryRegisters 0 15 (clear_C00E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C00E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C01_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C01_boundaries,
      point.Expected clear_C01.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C01_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 1 clear_C01.before (clear_C01.fields.withUser value) ctx 1 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 1 clear_C01.before (clear_C01.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 1 15 clear_C01.before (clear_C01.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 1 15 clear_C01.before)
          (boundaryRegisters 1 15 (clear_C01.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C01_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C01E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C01E_boundaries,
      point.Expected clear_C01E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C01E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 1 clear_C01E.before (clear_C01E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 1 15 clear_C01E.before (clear_C01E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 1 15 clear_C01E.before)
          (boundaryRegisters 1 15 (clear_C01E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C01E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C02_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C02_boundaries,
      point.Expected clear_C02.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C02_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 2 clear_C02.before (clear_C02.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 2 clear_C02.before (clear_C02.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 2 15 clear_C02.before (clear_C02.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 2 15 clear_C02.before)
          (boundaryRegisters 2 15 (clear_C02.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C02_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C02E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C02E_boundaries,
      point.Expected clear_C02E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C02E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 2 clear_C02E.before (clear_C02E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 2 15 clear_C02E.before (clear_C02E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 2 15 clear_C02E.before)
          (boundaryRegisters 2 15 (clear_C02E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C02E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C03_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C03_boundaries,
      point.Expected clear_C03.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C03_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 3 clear_C03.before (clear_C03.fields.withUser value) ctx 1 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 3 clear_C03.before (clear_C03.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 3 15 clear_C03.before (clear_C03.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 3 15 clear_C03.before)
          (boundaryRegisters 3 15 (clear_C03.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C03_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C03E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C03E_boundaries,
      point.Expected clear_C03E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C03E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 3 clear_C03E.before (clear_C03E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 3 15 clear_C03E.before (clear_C03E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 3 15 clear_C03E.before)
          (boundaryRegisters 3 15 (clear_C03E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C03E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C04_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C04_boundaries,
      point.Expected clear_C04.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C04_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 4 clear_C04.before (clear_C04.fields.withUser value) ctx 3 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 4 clear_C04.before (clear_C04.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 4 15 clear_C04.before (clear_C04.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 4 15 clear_C04.before)
          (boundaryRegisters 4 15 (clear_C04.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C04_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C04E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C04E_boundaries,
      point.Expected clear_C04E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C04E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 4 clear_C04E.before (clear_C04E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 4 15 clear_C04E.before (clear_C04E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 4 15 clear_C04E.before)
          (boundaryRegisters 4 15 (clear_C04E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C04E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C05_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C05_boundaries,
      point.Expected clear_C05.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C05_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 5 clear_C05.before (clear_C05.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 5 clear_C05.before (clear_C05.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 5 15 clear_C05.before (clear_C05.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 5 15 clear_C05.before)
          (boundaryRegisters 5 15 (clear_C05.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C05_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C05E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C05E_boundaries,
      point.Expected clear_C05E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C05E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 5 clear_C05E.before (clear_C05E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 5 15 clear_C05E.before (clear_C05E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 5 15 clear_C05E.before)
          (boundaryRegisters 5 15 (clear_C05E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C05E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C06_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C06_boundaries,
      point.Expected clear_C06.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C06_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 6 clear_C06.before (clear_C06.fields.withUser value) ctx 1 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 6 clear_C06.before (clear_C06.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 6 15 clear_C06.before (clear_C06.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 6 15 clear_C06.before)
          (boundaryRegisters 6 15 (clear_C06.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C06_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C06E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C06E_boundaries,
      point.Expected clear_C06E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C06E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 6 clear_C06E.before (clear_C06E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 6 15 clear_C06E.before (clear_C06E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 6 15 clear_C06E.before)
          (boundaryRegisters 6 15 (clear_C06E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C06E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C07_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C07_boundaries,
      point.Expected clear_C07.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C07_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 7 clear_C07.before (clear_C07.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 7 clear_C07.before (clear_C07.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 7 15 clear_C07.before (clear_C07.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 7 15 clear_C07.before)
          (boundaryRegisters 7 15 (clear_C07.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C07_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C07E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C07E_boundaries,
      point.Expected clear_C07E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C07E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 7 clear_C07E.before (clear_C07E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 7 15 clear_C07E.before (clear_C07E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 7 15 clear_C07E.before)
          (boundaryRegisters 7 15 (clear_C07E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C07E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C08_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C08_boundaries,
      point.Expected clear_C08.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C08_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 8 clear_C08.before (clear_C08.fields.withUser value) ctx 3 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 8 clear_C08.before (clear_C08.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 8 15 clear_C08.before (clear_C08.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 8 15 clear_C08.before)
          (boundaryRegisters 8 15 (clear_C08.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C08_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C08E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C08E_boundaries,
      point.Expected clear_C08E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C08E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 8 clear_C08E.before (clear_C08E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 8 15 clear_C08E.before (clear_C08E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 8 15 clear_C08E.before)
          (boundaryRegisters 8 15 (clear_C08E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C08E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C09_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C09_boundaries,
      point.Expected clear_C09.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C09_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 9 clear_C09.before (clear_C09.fields.withUser value) ctx 1 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 9 clear_C09.before (clear_C09.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 9 15 clear_C09.before (clear_C09.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 9 15 clear_C09.before)
          (boundaryRegisters 9 15 (clear_C09.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C09_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C09E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C09E_boundaries,
      point.Expected clear_C09E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C09E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 9 clear_C09E.before (clear_C09E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 9 15 clear_C09E.before (clear_C09E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 9 15 clear_C09E.before)
          (boundaryRegisters 9 15 (clear_C09E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C09E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C10_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C10_boundaries,
      point.Expected clear_C10.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C10_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 10 clear_C10.before (clear_C10.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 10 clear_C10.before (clear_C10.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 10 15 clear_C10.before (clear_C10.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 10 15 clear_C10.before)
          (boundaryRegisters 10 15 (clear_C10.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C10_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C10E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C10E_boundaries,
      point.Expected clear_C10E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C10E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 10 clear_C10E.before (clear_C10E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 10 15 clear_C10E.before (clear_C10E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 10 15 clear_C10E.before)
          (boundaryRegisters 10 15 (clear_C10E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C10E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C11_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C11_boundaries,
      point.Expected clear_C11.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C11_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 11 clear_C11.before (clear_C11.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 11 clear_C11.before (clear_C11.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 11 15 clear_C11.before (clear_C11.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 11 15 clear_C11.before)
          (boundaryRegisters 11 15 (clear_C11.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C11_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C11E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C11E_boundaries,
      point.Expected clear_C11E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C11E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 11 clear_C11E.before (clear_C11E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 11 15 clear_C11E.before (clear_C11E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 11 15 clear_C11E.before)
          (boundaryRegisters 11 15 (clear_C11E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C11E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C12_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C12_boundaries,
      point.Expected clear_C12.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C12_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 12 clear_C12.before (clear_C12.fields.withUser value) ctx 3 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 12 clear_C12.before (clear_C12.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 12 15 clear_C12.before (clear_C12.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 12 15 clear_C12.before)
          (boundaryRegisters 12 15 (clear_C12.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C12_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C12E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C12E_boundaries,
      point.Expected clear_C12E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C12E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 12 clear_C12E.before (clear_C12E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 12 15 clear_C12E.before (clear_C12E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 12 15 clear_C12E.before)
          (boundaryRegisters 12 15 (clear_C12E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C12E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C13_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C13_boundaries,
      point.Expected clear_C13.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C13_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 13 clear_C13.before (clear_C13.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 13 clear_C13.before (clear_C13.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 13 15 clear_C13.before (clear_C13.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 13 15 clear_C13.before)
          (boundaryRegisters 13 15 (clear_C13.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C13_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C13E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C13E_boundaries,
      point.Expected clear_C13E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C13E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 13 clear_C13E.before (clear_C13E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 13 15 clear_C13E.before (clear_C13E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 13 15 clear_C13E.before)
          (boundaryRegisters 13 15 (clear_C13E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C13E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C14_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C14_boundaries,
      point.Expected clear_C14.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C14_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 14 clear_C14.before (clear_C14.fields.withUser value) ctx 3 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 14 clear_C14.before (clear_C14.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 14 15 clear_C14.before (clear_C14.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 14 15 clear_C14.before)
          (boundaryRegisters 14 15 (clear_C14.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C14_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C14E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C14E_boundaries,
      point.Expected clear_C14E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C14E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_slot_localRun caller 14 clear_C14E.before (clear_C14E.fields.withUser value) ctx).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 14 15 clear_C14E.before (clear_C14E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 14 15 clear_C14E.before)
          (boundaryRegisters 14 15 (clear_C14E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C14E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C15_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C15_boundaries,
      point.Expected clear_C15.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C15_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (drain_slot_localRun caller 15 clear_C15.before (clear_C15.fields.withUser value) ctx 2 (by decide)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 15 15 clear_C15.before (clear_C15.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 15 15 clear_C15.before)
          (boundaryRegisters 15 15 (clear_C15.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C15_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem clear_C15E_boundaries_are_actual (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ point ∈ clear_C15E_boundaries,
      point.Expected clear_C15E.toClosedFixture (step caller) value ctx := by
  intro point member
  simp only [clear_C15E_boundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · constructor
    · rfl
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (LocalRun.trans caller
        (boundary_localRun caller 15 15 clear_C15E.before (clear_C15E.fields.withUser value) ctx (by decide))
        (clear_slot_localRun caller 15 (boundaryData 15 15 clear_C15E.before)
          (boundaryRegisters 15 15 (clear_C15E.fields.withUser value)) ctx)).iterate caller
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl
  · constructor
    · exact (clear_C15E_actual_first_halt caller value ctx).1
    · change physicalCells (cfg _ _ _ _) = _
      rw [actual_physical_cells_of_cfg]
      rfl

theorem all_partial_clear_boundaries_are_literal (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ pair ∈ partialClearBoundaries, ∀ point ∈ pair.2,
      point.Expected pair.1.toClosedFixture (step caller) value ctx := by
  intro pair member
  simp only [partialClearBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact clear_C00_boundaries_are_actual caller value ctx
  · exact clear_C00E_boundaries_are_actual caller value ctx
  · exact clear_C01_boundaries_are_actual caller value ctx
  · exact clear_C01E_boundaries_are_actual caller value ctx
  · exact clear_C02_boundaries_are_actual caller value ctx
  · exact clear_C02E_boundaries_are_actual caller value ctx
  · exact clear_C03_boundaries_are_actual caller value ctx
  · exact clear_C03E_boundaries_are_actual caller value ctx
  · exact clear_C04_boundaries_are_actual caller value ctx
  · exact clear_C04E_boundaries_are_actual caller value ctx
  · exact clear_C05_boundaries_are_actual caller value ctx
  · exact clear_C05E_boundaries_are_actual caller value ctx
  · exact clear_C06_boundaries_are_actual caller value ctx
  · exact clear_C06E_boundaries_are_actual caller value ctx
  · exact clear_C07_boundaries_are_actual caller value ctx
  · exact clear_C07E_boundaries_are_actual caller value ctx
  · exact clear_C08_boundaries_are_actual caller value ctx
  · exact clear_C08E_boundaries_are_actual caller value ctx
  · exact clear_C09_boundaries_are_actual caller value ctx
  · exact clear_C09E_boundaries_are_actual caller value ctx
  · exact clear_C10_boundaries_are_actual caller value ctx
  · exact clear_C10E_boundaries_are_actual caller value ctx
  · exact clear_C11_boundaries_are_actual caller value ctx
  · exact clear_C11E_boundaries_are_actual caller value ctx
  · exact clear_C12_boundaries_are_actual caller value ctx
  · exact clear_C12E_boundaries_are_actual caller value ctx
  · exact clear_C13_boundaries_are_actual caller value ctx
  · exact clear_C13E_boundaries_are_actual caller value ctx
  · exact clear_C14_boundaries_are_actual caller value ctx
  · exact clear_C14E_boundaries_are_actual caller value ctx
  · exact clear_C15_boundaries_are_actual caller value ctx
  · exact clear_C15E_boundaries_are_actual caller value ctx

end CleanupBoundaryConnections

end Examples.RotationCertificateFrontEndStreamMachine

namespace Examples.RotationCertificateFrontEndStreamMachine.StreamCertificates

open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.StreamMachine
open Examples.RotationCertificateStreamMachine

/-! Small Stream certificates for fixed closed-controller segments.
Each adjacent configuration is checked against the actual existing S program.
The expected endpoints and peaks were fixed before this certificate derivation. -/

def segment_v02 : RunFixture where
  name := "closed-controller/segment_v02"
  phase := inspectPhase
  before := data [] [] [] [0] [] [] [] [] [1, 0, 0]
  result := false
  after := data [] [] [] [] [] [] [] [] [0, 0]
  ticks := 4
  peak := 4

def trace_segment_v02 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [0] [] [] [] [] [1, 0, 0], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [0] [] [] [] [] [1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [] [1, 0, 0], .complete⟩
  | 3 => ⟨.inl (equalityJoinPhase .different), data [] [] [] [] [] [] [] [] [0, 0], .complete⟩
  | _ => ⟨.inr false, data [] [] [] [] [] [] [] [] [0, 0], .complete⟩

def segment_v07 : RunFixture where
  name := "closed-controller/segment_v07"
  phase := inspectPhase
  before := data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0]
  result := false
  after := data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0]
  ticks := 8
  peak := 14

def trace_segment_v07 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [()] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 3 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [] [1, 0, 1, 0, 0], .fuel⟩
  | 4 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [(), ()] [] [1, 0, 1, 0, 0], .fuel⟩
  | 5 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [()] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 6 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .fuel⟩
  | 7 => ⟨.inl (fuelJoinPhase .zero), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .fuel⟩
  | _ => ⟨.inr false, data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false] [1, 0, 1, 0, 0], .complete⟩

def segment_v08 : RunFixture where
  name := "closed-controller/segment_v08"
  phase := inspectPhase
  before := data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false, false] [1, 1, 0, 0, 0]
  result := true
  after := data [] [] [] [] [] [] [] [false, false, false] []
  ticks := 25
  peak := 15

def trace_segment_v08 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false, false] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true, false, false] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left))), data [] [] [] [0, 1, 0, 0] [] [] [()] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .checkRight)), data [] [] [] [1, 0, 0] [] [0] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0] [] [0] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft))), data [] [] [] [0, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success))), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyJoinPhase MoveApplyMachine.success), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (inspectPhase), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 17 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 18 => ⟨.inl (comparePhase), data [] [] [] [1, 1, 0, 0, 0] [] [] [] [false, false, false] [1, 1, 0, 0, 0], .complete⟩
  | 19 => ⟨.inl (comparePhase), data [] [] [] [1, 0, 0, 0] [] [] [] [false, false, false] [1, 0, 0, 0], .complete⟩
  | 20 => ⟨.inl (comparePhase), data [] [] [] [0, 0, 0] [] [] [] [false, false, false] [0, 0, 0], .complete⟩
  | 21 => ⟨.inl (comparePhase), data [] [] [] [0, 0] [] [] [] [false, false, false] [0, 0], .complete⟩
  | 22 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false, false, false] [0], .complete⟩
  | 23 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false, false, false] [], .complete⟩
  | 24 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false, false, false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false, false, false] [], .complete⟩

def segment_v09 : RunFixture where
  name := "closed-controller/segment_v09"
  phase := inspectPhase
  before := data [6] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0]
  result := false
  after := data [6] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0]
  ticks := 9
  peak := 12

def trace_segment_v09 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.undo .left))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [6] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [6] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [6] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩

def segment_v10 : RunFixture where
  name := "closed-controller/segment_v10"
  phase := inspectPhase
  before := data [6, 15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0]
  result := false
  after := data [6, 15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0]
  ticks := 9
  peak := 14

def trace_segment_v10 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.undo .left))), data [15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [6, 15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [6, 15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [6, 15, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩

def segment_v11 : RunFixture where
  name := "closed-controller/segment_v11"
  phase := inspectPhase
  before := data [6, 8, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0]
  result := false
  after := data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0]
  ticks := 17
  peak := 14

def trace_segment_v11 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 8, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 8, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 8, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 8, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 8, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [8, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [.left] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [.left] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [.left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [.left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [.left] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [] [0, 1, 0, 0] [1] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .left))), data [] [] [] [0, 1, 0, 0] [1] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .dropPending)), data [] [] [] [0, 1, 0, 0] [1] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure))), data [] [] [] [0, 1, 0, 0] [1] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (applyJoinPhase MoveApplyMachine.rotationFailure), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 1, 0, 0, 0], .complete⟩

def segment_v12 : RunFixture where
  name := "closed-controller/segment_v12"
  phase := inspectPhase
  before := data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0]
  result := false
  after := data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0]
  ticks := 13
  peak := 13

def trace_segment_v12 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [7, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .right))), data [10] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .right))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .right))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .right))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.start .right))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .dropPending)), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure))), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyJoinPhase MoveApplyMachine.rotationFailure), data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩

def segment_v15 : RunFixture where
  name := "closed-controller/segment_v15"
  phase := inspectPhase
  before := data [] [] [] [0] [] [] [] [false, false] [0]
  result := true
  after := data [] [] [] [] [] [] [] [false, false] []
  ticks := 5
  peak := 4

def trace_segment_v15 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [] [] [0] [] [] [] [false, false] [0], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [] [] [0] [] [] [] [false, false] [0], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [] [] [0] [] [] [] [false, false] [0], .complete⟩
  | 3 => ⟨.inl (comparePhase), data [] [] [] [] [] [] [] [false, false] [], .complete⟩
  | 4 => ⟨.inl (equalityJoinPhase .equal), data [] [] [] [] [] [] [] [false, false] [], .complete⟩
  | _ => ⟨.inr true, data [] [] [] [] [] [] [] [false, false] [], .complete⟩

def segment_v16 : RunFixture where
  name := "closed-controller/segment_v16"
  phase := inspectPhase
  before := data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0]
  result := false
  after := data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0]
  ticks := 7
  peak := 12

def trace_segment_v16 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase .failure)), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyJoinPhase MoveApplyMachine.parseFailure), data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [15] [] [] [1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 0, 0], .complete⟩

def segment_v18 : RunFixture where
  name := "closed-controller/segment_v18"
  phase := inspectPhase
  before := data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [] [1, 1, 0, 0, 0]
  result := false
  after := data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [] [1, 1, 0, 0, 0]
  ticks := 4
  peak := 12

def trace_segment_v18 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [] [1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [] [1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreFalse), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [] [1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .zero), data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [] [1, 1, 0, 0, 0], .fuel⟩
  | _ => ⟨.inr false, data [6, 10] [] [] [1, 0, 1, 0, 0] [] [] [] [] [1, 1, 0, 0, 0], .complete⟩

def segment_j03 : RunFixture where
  name := "closed-controller/segment_j03"
  phase := inspectPhase
  before := data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] []
  result := true
  after := data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] []
  ticks := 4
  peak := 8

def trace_segment_j03 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .original⟩
  | 1 => ⟨.inl (fuelJoinPhase .atEnd), data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .fuel⟩
  | 2 => ⟨.inl (comparePhase), data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .complete⟩
  | 3 => ⟨.inl (equalityJoinPhase .equal), data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .complete⟩
  | _ => ⟨.inr true, data [] [.right, .left] [.right] [] [12] [3] [(), ()] [true] [], .complete⟩

def segment_d02 : RunFixture where
  name := "closed-controller/segment_d02"
  phase := inspectPhase
  before := data [6, 9, 10] [.right, .left] [.left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 1, 0, 0, 0]
  result := false
  after := data [] [] [.right, .left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0]
  ticks := 18
  peak := 22

def trace_segment_d02 : Nat → TracePoint
  | 0 => ⟨.inl (inspectPhase), data [6, 9, 10] [.right, .left] [.left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 1, 0, 0, 0], .original⟩
  | 1 => ⟨.inl (counterPhase .borrow), data [6, 9, 10] [.right, .left] [.left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [true] [1, 0, 1, 1, 0, 0, 0], .fuel⟩
  | 2 => ⟨.inl (counterPhase .restoreTrue), data [6, 9, 10] [.right, .left] [.left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .fuel⟩
  | 3 => ⟨.inl (fuelJoinPhase .positive), data [6, 9, 10] [.right, .left] [.left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .fuel⟩
  | 4 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase .start)), data [6, 9, 10] [.right, .left] [.left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 5 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [9, 10] [.right, .left] [.left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 6 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.scan .left))), data [10] [.right, .right, .left] [.left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 7 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [.right, .right, .left] [.left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 8 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [.right, .left] [.right, .left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 9 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [.left] [.right, .right, .left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 10 => ⟨.inl (applyPhase (MoveApplyMachine.movePhase (.emit .left))), data [] [] [.left, .right, .right, .left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 11 => ⟨.inl (applyPhase (MoveApplyMachine.dispatchPhase (.success .left))), data [] [] [.left, .right, .right, .left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 12 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [.left, .right, .right, .left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 13 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.seek .left))), data [] [] [.right, .right, .left, .right] [0, 1, 0, 1, 0, 0] [1] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 14 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase .dropPending)), data [] [] [.right, .left, .right] [0, 1, 0, 1, 0, 0] [1] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 15 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure))), data [] [] [.right, .left, .right] [0, 1, 0, 1, 0, 0] [1] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 16 => ⟨.inl (applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure))), data [] [] [.right, .left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | 17 => ⟨.inl (applyJoinPhase MoveApplyMachine.rotationFailure), data [] [] [.right, .left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩
  | _ => ⟨.inr false, data [] [] [.right, .left, .right] [1, 0, 1, 0, 1, 0, 0] [] [] [] [false] [1, 0, 1, 1, 0, 0, 0], .complete⟩

section ActualEdges
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem trace_segment_v02_steps (n : Nat) (bound : n < 4) :
    step caller ((trace_segment_v02 n).reached regs ctx) =
      some ((trace_segment_v02 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_segment_v02 0).stores rfl ((trace_segment_v02 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_segment_v02 1).stores ((trace_segment_v02 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_segment_v02 2).stores ((trace_segment_v02 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_different (fun _ => .halt) 0 1 [] [0, 0] (equalityRegisterEquiv.symm ((trace_segment_v02 2).stage.apply regs)) (equalityContext (trace_segment_v02 2).stores ctx) (by decide))
  · exact equality_join_step caller .different (trace_segment_v02 3).stores ((trace_segment_v02 3).stage.apply regs) ctx

theorem trace_segment_v07_steps (n : Nat) (bound : n < 8) :
    step caller ((trace_segment_v07 n).reached regs ctx) =
      some ((trace_segment_v07 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_segment_v07 0).stores 6 [10] rfl ((trace_segment_v07 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_segment_v07 1).stores ((trace_segment_v07 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_segment_v07 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_segment_v07 1).stores.certificate) (fuelContext (trace_segment_v07 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_segment_v07 2).stores ((trace_segment_v07 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_segment_v07 2).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_segment_v07 2).stores.certificate) (fuelContext (trace_segment_v07 2).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_segment_v07 3).stores ((trace_segment_v07 3).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((trace_segment_v07 3).stage.apply regs) [(), ()] (FuelDispatchMachine.stores ((trace_segment_v07 3).stores.certificate) (fuelContext (trace_segment_v07 3).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_segment_v07 4).stores ((trace_segment_v07 4).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_segment_v07 4).stage.apply regs) [()] (FuelDispatchMachine.stores ((trace_segment_v07 4).stores.certificate) (fuelContext (trace_segment_v07 4).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_segment_v07 5).stores ((trace_segment_v07 5).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_segment_v07 5).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_segment_v07 5).stores.certificate) (fuelContext (trace_segment_v07 5).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_segment_v07 6).stores ((trace_segment_v07 6).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((trace_segment_v07 6).stage.apply regs) (FuelDispatchMachine.stores ((trace_segment_v07 6).stores.certificate) (fuelContext (trace_segment_v07 6).stores ctx)))
  · exact fuel_join_step caller .zero (trace_segment_v07 7).stores ((trace_segment_v07 7).stage.apply regs) ctx

theorem trace_segment_v08_steps (n : Nat) (bound : n < 25) :
    step caller ((trace_segment_v08 n).reached regs ctx) =
      some ((trace_segment_v08 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_segment_v08 0).stores 6 [10] rfl ((trace_segment_v08 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_segment_v08 1).stores ((trace_segment_v08 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false] ((trace_segment_v08 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_segment_v08 1).stores.certificate) (fuelContext (trace_segment_v08 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_segment_v08 2).stores ((trace_segment_v08 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false, false, false] ((trace_segment_v08 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_segment_v08 2).stores.certificate) (fuelContext (trace_segment_v08 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_segment_v08 3).stores ((trace_segment_v08 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_segment_v08 4).stores ((trace_segment_v08 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v08 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v08 4).stores) (applyContext (trace_segment_v08 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_segment_v08 5).stores ((trace_segment_v08 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v08 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v08 5).stores) (applyContext (trace_segment_v08 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_segment_v08 6).stores ((trace_segment_v08 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v08 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v08 6).stores) (applyContext (trace_segment_v08 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_segment_v08 7).stores ((trace_segment_v08 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_segment_v08 7).stores)
        (applyRegisterEquiv.symm ((trace_segment_v08 7).stage.apply regs)) (applyContext (trace_segment_v08 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_segment_v08 8).stores ((trace_segment_v08 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_segment_v08 9).stores ((trace_segment_v08 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.scanScratch .left) (trace_segment_v08 10).stores ((trace_segment_v08 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller .checkRight (trace_segment_v08 11).stores ((trace_segment_v08 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_segment_v08 12).stores ((trace_segment_v08 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restoreScratch .successLeft) (trace_segment_v08 13).stores ((trace_segment_v08 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .success) (trace_segment_v08 14).stores ((trace_segment_v08 14).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.success (trace_segment_v08 15).stores ((trace_segment_v08 15).stage.apply regs) ctx
  · exact inspect_step_nil caller (trace_segment_v08 16).stores rfl ((trace_segment_v08 16).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_segment_v08 17).stores ((trace_segment_v08 17).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_segment_v08 18).stores ((trace_segment_v08 18).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [1, 0, 0, 0] [1, 0, 0, 0] (equalityRegisterEquiv.symm ((trace_segment_v08 18).stage.apply regs)) (equalityContext (trace_segment_v08 18).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_segment_v08 19).stores ((trace_segment_v08 19).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 1 [0, 0, 0] [0, 0, 0] (equalityRegisterEquiv.symm ((trace_segment_v08 19).stage.apply regs)) (equalityContext (trace_segment_v08 19).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_segment_v08 20).stores ((trace_segment_v08 20).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0, 0] [0, 0] (equalityRegisterEquiv.symm ((trace_segment_v08 20).stage.apply regs)) (equalityContext (trace_segment_v08 20).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_segment_v08 21).stores ((trace_segment_v08 21).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [0] [0] (equalityRegisterEquiv.symm ((trace_segment_v08 21).stage.apply regs)) (equalityContext (trace_segment_v08 21).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_segment_v08 22).stores ((trace_segment_v08 22).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_segment_v08 22).stage.apply regs)) (equalityContext (trace_segment_v08 22).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_segment_v08 23).stores ((trace_segment_v08 23).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_segment_v08 23).stage.apply regs)) (equalityContext (trace_segment_v08 23).stores ctx))
  · exact equality_join_step caller .equal (trace_segment_v08 24).stores ((trace_segment_v08 24).stage.apply regs) ctx

theorem trace_segment_v09_steps (n : Nat) (bound : n < 9) :
    step caller ((trace_segment_v09 n).reached regs ctx) =
      some ((trace_segment_v09 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_segment_v09 0).stores 6 [] rfl ((trace_segment_v09 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_segment_v09 1).stores ((trace_segment_v09 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_segment_v09 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_segment_v09 1).stores.certificate) (fuelContext (trace_segment_v09 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_segment_v09 2).stores ((trace_segment_v09 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_segment_v09 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_segment_v09 2).stores.certificate) (fuelContext (trace_segment_v09 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_segment_v09 3).stores ((trace_segment_v09 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_segment_v09 4).stores ((trace_segment_v09 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v09 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v09 4).stores) (applyContext (trace_segment_v09 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_segment_v09 5).stores ((trace_segment_v09 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_nil (fun _ => .halt) .left [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v09 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v09 5).stores) (applyContext (trace_segment_v09 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (trace_segment_v09 6).stores ((trace_segment_v09 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_nil (fun _ => .halt) .left [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v09 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v09 6).stores) (applyContext (trace_segment_v09 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_segment_v09 7).stores ((trace_segment_v09 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_segment_v09 7).stores)
        (applyRegisterEquiv.symm ((trace_segment_v09 7).stage.apply regs)) (applyContext (trace_segment_v09 7).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_segment_v09 8).stores ((trace_segment_v09 8).stage.apply regs) ctx

theorem trace_segment_v10_steps (n : Nat) (bound : n < 9) :
    step caller ((trace_segment_v10 n).reached regs ctx) =
      some ((trace_segment_v10 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_segment_v10 0).stores 6 [15, 10] rfl ((trace_segment_v10 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_segment_v10 1).stores ((trace_segment_v10 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_segment_v10 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_segment_v10 1).stores.certificate) (fuelContext (trace_segment_v10 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_segment_v10 2).stores ((trace_segment_v10 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_segment_v10 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_segment_v10 2).stores.certificate) (fuelContext (trace_segment_v10 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_segment_v10 3).stores ((trace_segment_v10 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_segment_v10 4).stores ((trace_segment_v10 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [15, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v10 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v10 4).stores) (applyContext (trace_segment_v10 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_segment_v10 5).stores ((trace_segment_v10 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_foreign (fun _ => .halt) .left 15 [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v10 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v10 5).stores) (applyContext (trace_segment_v10 5).stores ctx)) (by decide) (by decide) (by decide))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.undo .left) (trace_segment_v10 6).stores ((trace_segment_v10 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.undo_step_nil (fun _ => .halt) .left [15, 10] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v10 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v10 6).stores) (applyContext (trace_segment_v10 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_segment_v10 7).stores ((trace_segment_v10 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_segment_v10 7).stores)
        (applyRegisterEquiv.symm ((trace_segment_v10 7).stage.apply regs)) (applyContext (trace_segment_v10 7).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_segment_v10 8).stores ((trace_segment_v10 8).stage.apply regs) ctx

theorem trace_segment_v11_steps (n : Nat) (bound : n < 17) :
    step caller ((trace_segment_v11 n).reached regs ctx) =
      some ((trace_segment_v11 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_segment_v11 0).stores 6 [8, 10] rfl ((trace_segment_v11 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_segment_v11 1).stores ((trace_segment_v11 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_segment_v11 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_segment_v11 1).stores.certificate) (fuelContext (trace_segment_v11 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_segment_v11 2).stores ((trace_segment_v11 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_segment_v11 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_segment_v11 2).stores.certificate) (fuelContext (trace_segment_v11 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_segment_v11 3).stores ((trace_segment_v11 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_segment_v11 4).stores ((trace_segment_v11 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [8, 10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v11 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v11 4).stores) (applyContext (trace_segment_v11 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_segment_v11 5).stores ((trace_segment_v11 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v11 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v11 5).stores) (applyContext (trace_segment_v11 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_segment_v11 6).stores ((trace_segment_v11 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [.left] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v11 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v11 6).stores) (applyContext (trace_segment_v11 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_segment_v11 7).stores ((trace_segment_v11 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .left [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v11 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v11 7).stores) (applyContext (trace_segment_v11 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_segment_v11 8).stores ((trace_segment_v11 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.left] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v11 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v11 8).stores) (applyContext (trace_segment_v11 8).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_segment_v11 9).stores ((trace_segment_v11 9).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_segment_v11 9).stores)
        (applyRegisterEquiv.symm ((trace_segment_v11 9).stage.apply regs)) (applyContext (trace_segment_v11 9).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_segment_v11 10).stores ((trace_segment_v11 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (trace_segment_v11 11).stores ((trace_segment_v11 11).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .left) (trace_segment_v11 12).stores ((trace_segment_v11 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller .dropPending (trace_segment_v11 13).stores ((trace_segment_v11 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (trace_segment_v11 14).stores ((trace_segment_v11 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (trace_segment_v11 15).stores ((trace_segment_v11 15).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.rotationFailure (trace_segment_v11 16).stores ((trace_segment_v11 16).stage.apply regs) ctx

theorem trace_segment_v12_steps (n : Nat) (bound : n < 13) :
    step caller ((trace_segment_v12 n).reached regs ctx) =
      some ((trace_segment_v12 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_segment_v12 0).stores 7 [10] rfl ((trace_segment_v12 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_segment_v12 1).stores ((trace_segment_v12 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_segment_v12 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_segment_v12 1).stores.certificate) (fuelContext (trace_segment_v12 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_segment_v12 2).stores ((trace_segment_v12 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_segment_v12 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_segment_v12 2).stores.certificate) (fuelContext (trace_segment_v12 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_segment_v12 3).stores ((trace_segment_v12 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_segment_v12 4).stores ((trace_segment_v12 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .right [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v12 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v12 4).stores) (applyContext (trace_segment_v12 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .right) (trace_segment_v12 5).stores ((trace_segment_v12 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .right [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v12 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v12 5).stores) (applyContext (trace_segment_v12 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .right) (trace_segment_v12 6).stores ((trace_segment_v12 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .right [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v12 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v12 6).stores) (applyContext (trace_segment_v12 6).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .right)) (trace_segment_v12 7).stores ((trace_segment_v12 7).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .right) (applyData (trace_segment_v12 7).stores)
        (applyRegisterEquiv.symm ((trace_segment_v12 7).stage.apply regs)) (applyContext (trace_segment_v12 7).stores ctx))
  · exact apply_position_advance_step caller (.seek .right) (trace_segment_v12 8).stores ((trace_segment_v12 8).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.start .right) (trace_segment_v12 9).stores ((trace_segment_v12 9).stage.apply regs) ctx
  · exact apply_position_advance_step caller .dropPending (trace_segment_v12 10).stores ((trace_segment_v12 10).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (trace_segment_v12 11).stores ((trace_segment_v12 11).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.rotationFailure (trace_segment_v12 12).stores ((trace_segment_v12 12).stage.apply regs) ctx

theorem trace_segment_v15_steps (n : Nat) (bound : n < 5) :
    step caller ((trace_segment_v15 n).reached regs ctx) =
      some ((trace_segment_v15 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_segment_v15 0).stores rfl ((trace_segment_v15 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_segment_v15 1).stores ((trace_segment_v15 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_segment_v15 2).stores ((trace_segment_v15 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 0 [] [] (equalityRegisterEquiv.symm ((trace_segment_v15 2).stage.apply regs)) (equalityContext (trace_segment_v15 2).stores ctx))
  · exact equality_step_of_step caller (fun _ => .halt) (trace_segment_v15 3).stores ((trace_segment_v15 3).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_segment_v15 3).stage.apply regs)) (equalityContext (trace_segment_v15 3).stores ctx))
  · exact equality_join_step caller .equal (trace_segment_v15 4).stores ((trace_segment_v15 4).stage.apply regs) ctx

theorem trace_segment_v16_steps (n : Nat) (bound : n < 7) :
    step caller ((trace_segment_v16 n).reached regs ctx) =
      some ((trace_segment_v16 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_segment_v16 0).stores 15 [] rfl ((trace_segment_v16 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_segment_v16 1).stores ((trace_segment_v16 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_segment_v16 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_segment_v16 1).stores.certificate) (fuelContext (trace_segment_v16 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_segment_v16 2).stores ((trace_segment_v16 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_segment_v16 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_segment_v16 2).stores.certificate) (fuelContext (trace_segment_v16 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_segment_v16 3).stores ((trace_segment_v16 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_segment_v16 4).stores ((trace_segment_v16 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_foreign (fun _ => .halt) 15 [] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_v16 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_v16 4).stores) (applyContext (trace_segment_v16 4).stores ctx)) (by decide) (by decide))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase .failure) (trace_segment_v16 5).stores ((trace_segment_v16 5).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) .failure (applyData (trace_segment_v16 5).stores)
        (applyRegisterEquiv.symm ((trace_segment_v16 5).stage.apply regs)) (applyContext (trace_segment_v16 5).stores ctx))
  · exact apply_join_step caller MoveApplyMachine.parseFailure (trace_segment_v16 6).stores ((trace_segment_v16 6).stage.apply regs) ctx

theorem trace_segment_v18_steps (n : Nat) (bound : n < 4) :
    step caller ((trace_segment_v18 n).reached regs ctx) =
      some ((trace_segment_v18 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_segment_v18 0).stores 6 [10] rfl ((trace_segment_v18 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_segment_v18 1).stores ((trace_segment_v18 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) ((trace_segment_v18 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_segment_v18 1).stores.certificate) (fuelContext (trace_segment_v18 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse (trace_segment_v18 2).stores ((trace_segment_v18 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_segment_v18 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_segment_v18 2).stores.certificate) (fuelContext (trace_segment_v18 2).stores ctx)))
  · exact fuel_join_step caller .zero (trace_segment_v18 3).stores ((trace_segment_v18 3).stage.apply regs) ctx

theorem trace_segment_j03_steps (n : Nat) (bound : n < 4) :
    step caller ((trace_segment_j03 n).reached regs ctx) =
      some ((trace_segment_j03 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_nil caller (trace_segment_j03 0).stores rfl ((trace_segment_j03 0).stage.apply regs) ctx
  · exact fuel_join_step caller .atEnd (trace_segment_j03 1).stores ((trace_segment_j03 1).stage.apply regs) ctx
  · exact equality_step_of_step caller (fun _ => .halt) (trace_segment_j03 2).stores ((trace_segment_j03 2).stage.apply regs) ctx _ _ _ _
      (TreeEqualityMachine.compare_step_nil_nil (fun _ => .halt) (equalityRegisterEquiv.symm ((trace_segment_j03 2).stage.apply regs)) (equalityContext (trace_segment_j03 2).stores ctx))
  · exact equality_join_step caller .equal (trace_segment_j03 3).stores ((trace_segment_j03 3).stage.apply regs) ctx

theorem trace_segment_d02_steps (n : Nat) (bound : n < 18) :
    step caller ((trace_segment_d02 n).reached regs ctx) =
      some ((trace_segment_d02 (n + 1)).reached regs ctx) := by
  interval_cases n
  · exact inspect_step_cons caller (trace_segment_d02 0).stores 6 [9, 10] rfl ((trace_segment_d02 0).stage.apply regs) ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow (trace_segment_d02 1).stores ((trace_segment_d02 1).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] ((trace_segment_d02 1).stage.apply regs) [] (FuelDispatchMachine.stores ((trace_segment_d02 1).stores.certificate) (fuelContext (trace_segment_d02 1).stores ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue (trace_segment_d02 2).stores ((trace_segment_d02 2).stage.apply regs) ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [false] ((trace_segment_d02 2).stage.apply regs) (FuelDispatchMachine.stores ((trace_segment_d02 2).stores.certificate) (fuelContext (trace_segment_d02 2).stores ctx)))
  · exact fuel_join_step caller .positive (trace_segment_d02 3).stores ((trace_segment_d02 3).stage.apply regs) ctx
  · exact apply_move_step_of_step caller (fun _ => .halt) .start (trace_segment_d02 4).stores ((trace_segment_d02 4).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [9, 10] [.right, .left] [.left, .right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_d02 4).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_d02 4).stores) (applyContext (trace_segment_d02 4).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_segment_d02 5).stores ((trace_segment_d02 5).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_branch (fun _ => .halt) .left .right [10] [.right, .left] [.left, .right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_d02 5).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_d02 5).stores) (applyContext (trace_segment_d02 5).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.scan .left) (trace_segment_d02 6).stores ((trace_segment_d02 6).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.scan_step_end (fun _ => .halt) .left [] [.right, .right, .left] [.left, .right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_d02 6).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_d02 6).stores) (applyContext (trace_segment_d02 6).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_segment_d02 7).stores ((trace_segment_d02 7).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .right [] [.right, .left] [.left, .right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_d02 7).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_d02 7).stores) (applyContext (trace_segment_d02 7).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_segment_d02 8).stores ((trace_segment_d02 8).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .right [] [.left] [.right, .left, .right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_d02 8).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_d02 8).stores) (applyContext (trace_segment_d02 8).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_segment_d02 9).stores ((trace_segment_d02 9).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_cons (fun _ => .halt) .left .left [] [] [.right, .right, .left, .right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_d02 9).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_d02 9).stores) (applyContext (trace_segment_d02 9).stores ctx)))
  · exact apply_move_step_of_step caller (fun _ => .halt) (.emit .left) (trace_segment_d02 10).stores ((trace_segment_d02 10).stage.apply regs) ctx _ _ _ _ _
      (MoveParserMachine.emit_step_nil (fun _ => .halt) .left [] [.left, .right, .right, .left, .right] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm ((trace_segment_d02 10).stage.apply regs))) (MoveApplyMachine.moveContext (applyData (trace_segment_d02 10).stores) (applyContext (trace_segment_d02 10).stores ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) (trace_segment_d02 11).stores ((trace_segment_d02 11).stage.apply regs) ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData (trace_segment_d02 11).stores)
        (applyRegisterEquiv.symm ((trace_segment_d02 11).stage.apply regs)) (applyContext (trace_segment_d02 11).stores ctx))
  · exact apply_position_advance_step caller (.seek .left) (trace_segment_d02 12).stores ((trace_segment_d02 12).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.seek .left) (trace_segment_d02 13).stores ((trace_segment_d02 13).stage.apply regs) ctx
  · exact apply_position_advance_step caller .dropPending (trace_segment_d02 14).stores ((trace_segment_d02 14).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (trace_segment_d02 15).stores ((trace_segment_d02 15).stage.apply regs) ctx
  · exact apply_position_advance_step caller (.restorePrefix .failure) (trace_segment_d02 16).stores ((trace_segment_d02 16).stage.apply regs) ctx
  · exact apply_join_step caller MoveApplyMachine.rotationFailure (trace_segment_d02 17).stores ((trace_segment_d02 17).stage.apply regs) ctx

end ActualEdges

theorem trace_segment_v02_owned (n : Nat) (bound : n < 4) :
    (trace_segment_v02 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_v02_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (trace_segment_v02 n).stores ≤ 4 := by
  interval_cases n <;> decide

theorem segment_v02_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_v02.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_v02 trace_segment_v02 rfl rfl
    (trace_segment_v02_steps caller regs ctx) trace_segment_v02_owned

theorem segment_v02_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_v02.start regs ctx)
      segment_v02.ticks (segment_v02.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_v02
    4 4 (trace_segment_v02_steps caller regs ctx) trace_segment_v02_cells rfl

theorem trace_segment_v07_owned (n : Nat) (bound : n < 8) :
    (trace_segment_v07 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_v07_cells (n : Nat) (bound : n ≤ 8) :
    fixtureCells (trace_segment_v07 n).stores ≤ 14 := by
  interval_cases n <;> decide

theorem segment_v07_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_v07.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_v07 trace_segment_v07 rfl rfl
    (trace_segment_v07_steps caller regs ctx) trace_segment_v07_owned

theorem segment_v07_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_v07.start regs ctx)
      segment_v07.ticks (segment_v07.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_v07
    8 14 (trace_segment_v07_steps caller regs ctx) trace_segment_v07_cells rfl

theorem trace_segment_v08_owned (n : Nat) (bound : n < 25) :
    (trace_segment_v08 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_v08_cells (n : Nat) (bound : n ≤ 25) :
    fixtureCells (trace_segment_v08 n).stores ≤ 15 := by
  interval_cases n <;> decide

theorem segment_v08_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_v08.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_v08 trace_segment_v08 rfl rfl
    (trace_segment_v08_steps caller regs ctx) trace_segment_v08_owned

theorem segment_v08_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_v08.start regs ctx)
      segment_v08.ticks (segment_v08.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_v08
    25 15 (trace_segment_v08_steps caller regs ctx) trace_segment_v08_cells rfl

theorem trace_segment_v09_owned (n : Nat) (bound : n < 9) :
    (trace_segment_v09 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_v09_cells (n : Nat) (bound : n ≤ 9) :
    fixtureCells (trace_segment_v09 n).stores ≤ 12 := by
  interval_cases n <;> decide

theorem segment_v09_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_v09.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_v09 trace_segment_v09 rfl rfl
    (trace_segment_v09_steps caller regs ctx) trace_segment_v09_owned

theorem segment_v09_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_v09.start regs ctx)
      segment_v09.ticks (segment_v09.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_v09
    9 12 (trace_segment_v09_steps caller regs ctx) trace_segment_v09_cells rfl

theorem trace_segment_v10_owned (n : Nat) (bound : n < 9) :
    (trace_segment_v10 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_v10_cells (n : Nat) (bound : n ≤ 9) :
    fixtureCells (trace_segment_v10 n).stores ≤ 14 := by
  interval_cases n <;> decide

theorem segment_v10_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_v10.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_v10 trace_segment_v10 rfl rfl
    (trace_segment_v10_steps caller regs ctx) trace_segment_v10_owned

theorem segment_v10_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_v10.start regs ctx)
      segment_v10.ticks (segment_v10.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_v10
    9 14 (trace_segment_v10_steps caller regs ctx) trace_segment_v10_cells rfl

theorem trace_segment_v11_owned (n : Nat) (bound : n < 17) :
    (trace_segment_v11 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_v11_cells (n : Nat) (bound : n ≤ 17) :
    fixtureCells (trace_segment_v11 n).stores ≤ 14 := by
  interval_cases n <;> decide

theorem segment_v11_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_v11.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_v11 trace_segment_v11 rfl rfl
    (trace_segment_v11_steps caller regs ctx) trace_segment_v11_owned

theorem segment_v11_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_v11.start regs ctx)
      segment_v11.ticks (segment_v11.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_v11
    17 14 (trace_segment_v11_steps caller regs ctx) trace_segment_v11_cells rfl

theorem trace_segment_v12_owned (n : Nat) (bound : n < 13) :
    (trace_segment_v12 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_v12_cells (n : Nat) (bound : n ≤ 13) :
    fixtureCells (trace_segment_v12 n).stores ≤ 13 := by
  interval_cases n <;> decide

theorem segment_v12_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_v12.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_v12 trace_segment_v12 rfl rfl
    (trace_segment_v12_steps caller regs ctx) trace_segment_v12_owned

theorem segment_v12_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_v12.start regs ctx)
      segment_v12.ticks (segment_v12.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_v12
    13 13 (trace_segment_v12_steps caller regs ctx) trace_segment_v12_cells rfl

theorem trace_segment_v15_owned (n : Nat) (bound : n < 5) :
    (trace_segment_v15 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_v15_cells (n : Nat) (bound : n ≤ 5) :
    fixtureCells (trace_segment_v15 n).stores ≤ 4 := by
  interval_cases n <;> decide

theorem segment_v15_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_v15.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_v15 trace_segment_v15 rfl rfl
    (trace_segment_v15_steps caller regs ctx) trace_segment_v15_owned

theorem segment_v15_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_v15.start regs ctx)
      segment_v15.ticks (segment_v15.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_v15
    5 4 (trace_segment_v15_steps caller regs ctx) trace_segment_v15_cells rfl

theorem trace_segment_v16_owned (n : Nat) (bound : n < 7) :
    (trace_segment_v16 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_v16_cells (n : Nat) (bound : n ≤ 7) :
    fixtureCells (trace_segment_v16 n).stores ≤ 12 := by
  interval_cases n <;> decide

theorem segment_v16_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_v16.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_v16 trace_segment_v16 rfl rfl
    (trace_segment_v16_steps caller regs ctx) trace_segment_v16_owned

theorem segment_v16_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_v16.start regs ctx)
      segment_v16.ticks (segment_v16.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_v16
    7 12 (trace_segment_v16_steps caller regs ctx) trace_segment_v16_cells rfl

theorem trace_segment_v18_owned (n : Nat) (bound : n < 4) :
    (trace_segment_v18 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_v18_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (trace_segment_v18 n).stores ≤ 12 := by
  interval_cases n <;> decide

theorem segment_v18_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_v18.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_v18 trace_segment_v18 rfl rfl
    (trace_segment_v18_steps caller regs ctx) trace_segment_v18_owned

theorem segment_v18_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_v18.start regs ctx)
      segment_v18.ticks (segment_v18.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_v18
    4 12 (trace_segment_v18_steps caller regs ctx) trace_segment_v18_cells rfl

theorem trace_segment_j03_owned (n : Nat) (bound : n < 4) :
    (trace_segment_j03 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_j03_cells (n : Nat) (bound : n ≤ 4) :
    fixtureCells (trace_segment_j03 n).stores ≤ 8 := by
  interval_cases n <;> decide

theorem segment_j03_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_j03.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_j03 trace_segment_j03 rfl rfl
    (trace_segment_j03_steps caller regs ctx) trace_segment_j03_owned

theorem segment_j03_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_j03.start regs ctx)
      segment_j03.ticks (segment_j03.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_j03
    4 8 (trace_segment_j03_steps caller regs ctx) trace_segment_j03_cells rfl

theorem trace_segment_d02_owned (n : Nat) (bound : n < 18) :
    (trace_segment_d02 n).control.isLeft = true := by
  interval_cases n <;> rfl

theorem trace_segment_d02_cells (n : Nat) (bound : n ≤ 18) :
    fixtureCells (trace_segment_d02 n).stores ≤ 22 := by
  interval_cases n <;> decide

theorem segment_d02_first_run
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    segment_d02.RunExpected (step caller) regs ctx :=
  literal_trace_is_an_actual_first_run caller regs ctx segment_d02 trace_segment_d02 rfl rfl
    (trace_segment_d02_steps caller regs ctx) trace_segment_d02_owned

theorem segment_d02_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Examples.RotationCertificateStreamMachine.ExactPeak (step caller) (segment_d02.start regs ctx)
      segment_d02.ticks (segment_d02.peak + Examples.RotationCertificateStreamMachine.externalCells ctx) :=
  finite_trace_has_its_exact_inclusive_peak caller regs ctx trace_segment_d02
    18 22 (trace_segment_d02_steps caller regs ctx) trace_segment_d02_cells rfl

end Examples.RotationCertificateFrontEndStreamMachine.StreamCertificates

namespace Examples.RotationCertificateFrontEndStreamMachine

open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.FrontEndStreamMachine

/-! ## Exact actual Stream segments inside the common physical carrier -/

def StreamFixture.LocalRunExpected {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (fixture : StreamFixture) (caller : Λ → Statement Γ Λ R)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  LocalRun caller fixture.ticks
    (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase)))
      (fullReset regs) fixture.before ctx)
    (cfg (some (phaseLabel (resultPhase fixture.result))) (fullReset regs) fixture.after ctx)

def StreamFixture.RunExpected {K Λ R : Type} {Γ : K → Type}
    (fixture : StreamFixture) (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  Runs transition
    (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase)))
      (fullReset regs) fixture.before ctx) fixture.ticks
    (cfg (some (phaseLabel (resultPhase fixture.result))) (fullReset regs) fixture.after ctx)

def StreamFixture.PeakExpected {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (fixture : StreamFixture) (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  ExactPeak transition
    (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase)))
      (fullReset regs) fixture.before ctx) fixture.ticks (fixture.peak + externalCells ctx)

def streamProtectedCells (D : LocalData) : Nat :=
  D.framedRaw.length + D.frameFirstReverse.length + D.frameCertReverse.length +
    D.inputBits.length + D.certificateBits.length + D.inputRaw.length + D.bitsReverse.length

section ActualStreamTransport

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
  (caller : Λ → Statement Γ Λ R)

omit caller [DecidableEq K] in
theorem common_stream_start_is_the_complete_view
    (q : StreamMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    streamCfg (Λ := Λ) (StreamMachine.cfg (some (StreamMachine.phaseLabel q))
      (StreamMachine.frontEndRegisterEquiv regs) (streamData D) (streamContext D ctx)) =
      cfg (some (phaseLabel (streamPhase q))) regs D ctx := by
  simpa only [streamView, Option.map_some, streamLabelEquiv_phase] using
    streamCfg_view (Λ := Λ) (some (StreamMachine.phaseLabel q)) regs D ctx

omit caller [DecidableEq K] in
theorem common_stream_end_keeps_every_complement_word
    (bit : Bool) (D : LocalData) (E : StreamMachine.LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    streamCfg (Λ := Λ) (StreamMachine.cfg (some (StreamMachine.resultLabel bit))
      (StreamMachine.resetAll (StreamMachine.frontEndRegisterEquiv regs)) E (streamContext D ctx)) =
      cfg (some (phaseLabel (resultPhase bit))) (streamReset regs) (withStream D E) ctx := by
  simpa only [streamView, streamData_withStream, streamContext_withStream,
    frontEndRegisterEquiv_streamReset, Option.map_some, streamLabelEquiv_result] using
      streamCfg_view (Λ := Λ) (some (StreamMachine.resultLabel bit))
        (streamReset regs) (withStream D E) ctx

theorem an_existing_actual_stream_run_is_an_actual_common_carrier_run
    (fixture : Examples.RotationCertificateStreamMachine.RunFixture)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (localCaller : StreamMachine.External (StreamCallerLabel Λ) → StreamStatement Γ Λ R)
    (sameInput : streamData D = fixture.before)
    (checked : fixture.RunExpected (StreamMachine.step localCaller)
      (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx)) :
    LocalRun caller fixture.ticks
      (cfg (some (phaseLabel (streamPhase fixture.phase))) regs D ctx)
      (cfg (some (phaseLabel (resultPhase fixture.result)))
        (streamReset regs) (withStream D fixture.after) ctx) := by
  have original := StreamMachine.LocalRun.of_iterate localCaller checked.1 checked.2.2
  have transported := stream_localRun caller localCaller original
  change LocalRun caller fixture.ticks
    (streamCfg (StreamMachine.cfg (some (StreamMachine.phaseLabel fixture.phase))
      (StreamMachine.frontEndRegisterEquiv regs) fixture.before (streamContext D ctx)))
    (streamCfg (StreamMachine.cfg (some (StreamMachine.resultLabel fixture.result))
      (StreamMachine.resetAll (StreamMachine.frontEndRegisterEquiv regs)) fixture.after
      (streamContext D ctx))) at transported
  rw [← sameInput, common_stream_start_is_the_complete_view,
    common_stream_end_keeps_every_complement_word] at transported
  exact transported

variable [Fintype K]

/-- Transport all actual inclusive prefixes and the same attained peak witness. -/
theorem an_actual_stream_peak_is_preserved_by_the_full_stack_equivalence
    (localCaller : StreamMachine.External (StreamCallerLabel Λ) → StreamStatement Γ Λ R)
    {start finish : StreamCfg Γ Λ R} {ticks peak : Nat}
    (run : StreamMachine.LocalRun localCaller ticks start finish)
    (checked : Examples.RotationCertificateStreamMachine.ExactPeak
      (StreamMachine.step localCaller) start ticks peak) :
    ExactPeak (step caller) (streamCfg start) ticks peak := by
  have transport (n : Nat) (bound : n ≤ ticks) (reached : StreamCfg Γ Λ R)
      (executed : (StreamMachine.next localCaller)^[n] (some start) = some reached) :
      Runs (step caller) (streamCfg start) n (streamCfg reached) := by
    have equality := stream_prefix_transport caller localCaller n start
      (fun j strict => run.owned_prefix localCaller j (by omega))
    change (next caller)^[n] (some (streamCfg start)) = some (streamCfg reached)
    simpa only [executed, Option.map_some] using equality
  constructor
  · intro n bound reached executed
    obtain ⟨original, arrived⟩ : ∃ original,
        (StreamMachine.next localCaller)^[n] (some start) = some original := by
      by_cases last : n = ticks
      · subst n
        exact ⟨finish, run.iterate localCaller⟩
      · obtain ⟨original, arrived, _⟩ := run.owned_prefix localCaller n (by omega)
        exact ⟨original, arrived⟩
    have actual := transport n bound original arrived
    have same := Option.some.inj (executed.symm.trans actual)
    subst reached
    change Resources.RotationCertificate.FrontEndStreamMachine.stackCells (streamCfg original) ≤ peak
    rw [stackCells_streamCfg]
    exact checked.1 n bound original arrived
  · obtain ⟨n, original, bound, arrived, cells⟩ := checked.2
    refine ⟨n, streamCfg original, bound, transport n bound original arrived, ?_⟩
    change Resources.RotationCertificate.FrontEndStreamMachine.stackCells (streamCfg original) = peak
    rw [stackCells_streamCfg]
    exact cells

theorem a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells
    (fixture : Examples.RotationCertificateStreamMachine.RunFixture)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (localCaller : StreamMachine.External (StreamCallerLabel Λ) → StreamStatement Γ Λ R)
    (sameInput : streamData D = fixture.before)
    (checkedRun : fixture.RunExpected (StreamMachine.step localCaller)
      (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx))
    (checkedPeak : Examples.RotationCertificateStreamMachine.ExactPeak
      (StreamMachine.step localCaller)
      (fixture.start (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx))
      fixture.ticks (fixture.peak + Examples.RotationCertificateStreamMachine.externalCells (streamContext D ctx))) :
    ExactPeak (step caller) (cfg (some (phaseLabel (streamPhase fixture.phase))) regs D ctx)
      fixture.ticks (fixture.peak + streamProtectedCells D + externalCells ctx) := by
  have run := StreamMachine.LocalRun.of_iterate localCaller checkedRun.1 checkedRun.2.2
  have peak := an_actual_stream_peak_is_preserved_by_the_full_stack_equivalence caller localCaller run checkedPeak
  change ExactPeak (step caller)
    (streamCfg (StreamMachine.cfg (some (StreamMachine.phaseLabel fixture.phase))
      (StreamMachine.frontEndRegisterEquiv regs) fixture.before (streamContext D ctx)))
    fixture.ticks (fixture.peak + Examples.RotationCertificateStreamMachine.externalCells (streamContext D ctx)) at peak
  rw [← sameInput, common_stream_start_is_the_complete_view] at peak
  have mass : Examples.RotationCertificateStreamMachine.externalCells (streamContext D ctx) =
      streamProtectedCells D + externalCells ctx := streamContext_cells D ctx
  simpa only [mass, Nat.add_assoc] using peak

end ActualStreamTransport

section LiteralStreamConnections

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
  (caller : Λ → Statement Γ Λ R)

theorem raw_V01_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V01.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a03
    raw_V01.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a03_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V01.frontEndAfter ctx))

theorem raw_V01_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V01.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V01_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V02_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V02.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_v02
    raw_V02.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v02_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V02.frontEndAfter ctx))

theorem raw_V02_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V02.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V02_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V03_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V03.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a12
    raw_V03.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a12_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V03.frontEndAfter ctx))

theorem raw_V03_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V03.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V03_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V04_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V04.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a13
    raw_V04.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a13_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V04.frontEndAfter ctx))

theorem raw_V04_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V04.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V04_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V05_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V05.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a18
    raw_V05.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a18_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V05.frontEndAfter ctx))

theorem raw_V05_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V05.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V05_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V06_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V06.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a19
    raw_V06.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a19_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V06.frontEndAfter ctx))

theorem raw_V06_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V06.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V06_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V07_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V07.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_v07
    raw_V07.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v07_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V07.frontEndAfter ctx))

theorem raw_V07_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V07.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V07_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V08_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V08.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_v08
    raw_V08.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v08_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V08.frontEndAfter ctx))

theorem raw_V08_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V08.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V08_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V09_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V09.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_v09
    raw_V09.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v09_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V09.frontEndAfter ctx))

theorem raw_V09_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V09.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V09_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V10_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V10.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_v10
    raw_V10.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v10_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V10.frontEndAfter ctx))

theorem raw_V10_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V10.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V10_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V11_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V11.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_v11
    raw_V11.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v11_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V11.frontEndAfter ctx))

theorem raw_V11_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V11.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V11_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V12_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V12.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_v12
    raw_V12.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v12_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V12.frontEndAfter ctx))

theorem raw_V12_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V12.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V12_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V13_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V13.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a17
    raw_V13.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a17_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V13.frontEndAfter ctx))

theorem raw_V13_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V13.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V13_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V14_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V14.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.r07
    raw_V14.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.r07_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V14.frontEndAfter ctx))

theorem raw_V14_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V14.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V14_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V15_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V15.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_v15
    raw_V15.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v15_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V15.frontEndAfter ctx))

theorem raw_V15_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V15.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V15_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V16_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V16.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_v16
    raw_V16.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v16_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V16.frontEndAfter ctx))

theorem raw_V16_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V16.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V16_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V17_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V17.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a14
    raw_V17.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a14_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V17.frontEndAfter ctx))

theorem raw_V17_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V17.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V17_stream_actual_local_run caller regs ctx).iterate caller

theorem raw_V18_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V18.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_v18
    raw_V18.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v18_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V18.frontEndAfter ctx))

theorem raw_V18_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match raw_V18.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (raw_V18_stream_actual_local_run caller regs ctx).iterate caller

theorem dirty_D00_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D00.stream.LocalRunExpected caller regs ctx :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a18
    dirty_D00.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a18_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D00.stream.before ctx))

theorem dirty_D00_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D00.stream.RunExpected (step caller) regs ctx :=
  (dirty_D00_stream_actual_local_run caller regs ctx).iterate caller

theorem dirty_D01_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D01.stream.LocalRunExpected caller regs ctx :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.r10
    dirty_D01.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.r10_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D01.stream.before ctx))

theorem dirty_D01_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D01.stream.RunExpected (step caller) regs ctx :=
  (dirty_D01_stream_actual_local_run caller regs ctx).iterate caller

theorem dirty_D02_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D02.stream.LocalRunExpected caller regs ctx :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_d02
    dirty_D02.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_d02_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D02.stream.before ctx))

theorem dirty_D02_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D02.stream.RunExpected (step caller) regs ctx :=
  (dirty_D02_stream_actual_local_run caller regs ctx).iterate caller

theorem dirty_D03_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D03.stream.LocalRunExpected caller regs ctx :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller Examples.RotationCertificateStreamMachine.a12
    dirty_D03.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a12_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D03.stream.before ctx))

theorem dirty_D03_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D03.stream.RunExpected (step caller) regs ctx :=
  (dirty_D03_stream_actual_local_run caller regs ctx).iterate caller

theorem join_J03_stream_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match join_J03.stream with | none => True | some segment => segment.LocalRunExpected caller regs ctx) :=
  an_existing_actual_stream_run_is_an_actual_common_carrier_run caller StreamCertificates.segment_j03
    join_J03.before (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_j03_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext join_J03.before ctx))

theorem join_J03_stream_actual_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match join_J03.stream with | none => True | some segment => segment.RunExpected (step caller) regs ctx) :=
  (join_J03_stream_actual_local_run caller regs ctx).iterate caller

variable [Fintype K]

theorem raw_V01_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V01.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a03
    raw_V01.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a03_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V01.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.a03_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V01.frontEndAfter ctx))

theorem raw_V02_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V02.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_v02
    raw_V02.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v02_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V02.frontEndAfter ctx))
    (StreamCertificates.segment_v02_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V02.frontEndAfter ctx))

theorem raw_V03_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V03.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a12
    raw_V03.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a12_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V03.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.a12_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V03.frontEndAfter ctx))

theorem raw_V04_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V04.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a13
    raw_V04.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a13_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V04.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.a13_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V04.frontEndAfter ctx))

theorem raw_V05_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V05.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a18
    raw_V05.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a18_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V05.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.a18_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V05.frontEndAfter ctx))

theorem raw_V06_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V06.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a19
    raw_V06.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a19_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V06.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.a19_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V06.frontEndAfter ctx))

theorem raw_V07_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V07.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_v07
    raw_V07.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v07_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V07.frontEndAfter ctx))
    (StreamCertificates.segment_v07_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V07.frontEndAfter ctx))

theorem raw_V08_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V08.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_v08
    raw_V08.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v08_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V08.frontEndAfter ctx))
    (StreamCertificates.segment_v08_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V08.frontEndAfter ctx))

theorem raw_V09_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V09.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_v09
    raw_V09.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v09_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V09.frontEndAfter ctx))
    (StreamCertificates.segment_v09_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V09.frontEndAfter ctx))

theorem raw_V10_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V10.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_v10
    raw_V10.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v10_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V10.frontEndAfter ctx))
    (StreamCertificates.segment_v10_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V10.frontEndAfter ctx))

theorem raw_V11_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V11.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_v11
    raw_V11.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v11_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V11.frontEndAfter ctx))
    (StreamCertificates.segment_v11_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V11.frontEndAfter ctx))

theorem raw_V12_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V12.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_v12
    raw_V12.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v12_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V12.frontEndAfter ctx))
    (StreamCertificates.segment_v12_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V12.frontEndAfter ctx))

theorem raw_V13_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V13.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a17
    raw_V13.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a17_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V13.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.a17_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V13.frontEndAfter ctx))

theorem raw_V14_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V14.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.r07
    raw_V14.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.r07_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V14.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.r07_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V14.frontEndAfter ctx))

theorem raw_V15_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V15.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_v15
    raw_V15.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v15_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V15.frontEndAfter ctx))
    (StreamCertificates.segment_v15_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V15.frontEndAfter ctx))

theorem raw_V16_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V16.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_v16
    raw_V16.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v16_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V16.frontEndAfter ctx))
    (StreamCertificates.segment_v16_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V16.frontEndAfter ctx))

theorem raw_V17_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V17.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a14
    raw_V17.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a14_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V17.frontEndAfter ctx))
    (Examples.RotationCertificateStreamMachine.a14_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V17.frontEndAfter ctx))

theorem raw_V18_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V18.StreamPeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_v18
    raw_V18.frontEndAfter (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_v18_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V18.frontEndAfter ctx))
    (StreamCertificates.segment_v18_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext raw_V18.frontEndAfter ctx))

theorem dirty_D00_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D00.stream.PeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a18
    dirty_D00.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a18_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D00.stream.before ctx))
    (Examples.RotationCertificateStreamMachine.a18_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D00.stream.before ctx))

theorem dirty_D01_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D01.stream.PeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.r10
    dirty_D01.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.r10_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D01.stream.before ctx))
    (Examples.RotationCertificateStreamMachine.r10_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D01.stream.before ctx))

theorem dirty_D02_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D02.stream.PeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_d02
    dirty_D02.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_d02_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D02.stream.before ctx))
    (StreamCertificates.segment_d02_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D02.stream.before ctx))

theorem dirty_D03_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    dirty_D03.stream.PeakExpected (step caller) regs ctx :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller Examples.RotationCertificateStreamMachine.a12
    dirty_D03.stream.before (fullReset regs) ctx (fun _ => .halt) rfl
    (Examples.RotationCertificateStreamMachine.a12_actual_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D03.stream.before ctx))
    (Examples.RotationCertificateStreamMachine.a12_actual_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext dirty_D03.stream.before ctx))

theorem join_J03_stream_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (match join_J03.stream with | none => True | some segment => segment.PeakExpected (step caller) regs ctx) :=
  a_checked_stream_fixture_preserves_its_exact_peak_and_all_context_cells caller StreamCertificates.segment_j03
    join_J03.before (fullReset regs) ctx (fun _ => .halt) rfl
    (StreamCertificates.segment_j03_first_run (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext join_J03.before ctx))
    (StreamCertificates.segment_j03_exact_peak (fun _ => .halt)
      (StreamMachine.frontEndRegisterEquiv (fullReset regs)) (streamContext join_J03.before ctx))

end LiteralStreamConnections

/-! ## All 36 raw inputs compose the actual front end, stream and cleanup -/

@[simp] theorem full_reset_after_any_front_end_outcome {R : Type}
    (kind : FrontEndKind) (regs : Registers R) :
    fullReset (kind.registers regs) = fullReset regs := by cases kind <;> rfl

@[simp] theorem answer_after_any_front_end_outcome {R : Type}
    (kind : FrontEndKind) (bit : Bool) (regs : Registers R) :
    answerRegisters bit (kind.registers regs) = answerRegisters bit regs := by cases kind <;> rfl

section LiteralRawRuns

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
  (caller : Λ → Statement Γ Λ R)

theorem raw_F01_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_F01.frontEndTicks (raw_F01.start regs ctx) (raw_F01.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_F01.raw ctx

theorem raw_F01_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F01.IntermediateExpected (step caller) regs ctx := by
  have first := raw_F01_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F01.frontEndAfter (raw_F01.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_F01.frontEndTicks + 1] (some (raw_F01.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_F01.beforeClear ctx)
  have sameData : raw_F01.frontEndAfter = raw_F01.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_F01_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F01.RunExpected (step caller) regs ctx := by
  have first := raw_F01_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F01.frontEndAfter (raw_F01.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_F01.frontEndAfter
    (answerRegisters false (raw_F01.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_F02_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_F02.frontEndTicks (raw_F02.start regs ctx) (raw_F02.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_F02.raw ctx

theorem raw_F02_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F02.IntermediateExpected (step caller) regs ctx := by
  have first := raw_F02_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F02.frontEndAfter (raw_F02.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_F02.frontEndTicks + 1] (some (raw_F02.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_F02.beforeClear ctx)
  have sameData : raw_F02.frontEndAfter = raw_F02.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_F02_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F02.RunExpected (step caller) regs ctx := by
  have first := raw_F02_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F02.frontEndAfter (raw_F02.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_F02.frontEndAfter
    (answerRegisters false (raw_F02.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_F03_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_F03.frontEndTicks (raw_F03.start regs ctx) (raw_F03.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_F03.raw ctx

theorem raw_F03_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F03.IntermediateExpected (step caller) regs ctx := by
  have first := raw_F03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F03.frontEndAfter (raw_F03.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_F03.frontEndTicks + 1] (some (raw_F03.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_F03.beforeClear ctx)
  have sameData : raw_F03.frontEndAfter = raw_F03.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_F03_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F03.RunExpected (step caller) regs ctx := by
  have first := raw_F03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F03.frontEndAfter (raw_F03.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_F03.frontEndAfter
    (answerRegisters false (raw_F03.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_F04_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_F04.frontEndTicks (raw_F04.start regs ctx) (raw_F04.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_F04.raw ctx

theorem raw_F04_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F04.IntermediateExpected (step caller) regs ctx := by
  have first := raw_F04_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F04.frontEndAfter (raw_F04.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_F04.frontEndTicks + 1] (some (raw_F04.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_F04.beforeClear ctx)
  have sameData : raw_F04.frontEndAfter = raw_F04.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_F04_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F04.RunExpected (step caller) regs ctx := by
  have first := raw_F04_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F04.frontEndAfter (raw_F04.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_F04.frontEndAfter
    (answerRegisters false (raw_F04.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_F05_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_F05.frontEndTicks (raw_F05.start regs ctx) (raw_F05.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_F05.raw ctx

theorem raw_F05_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F05.IntermediateExpected (step caller) regs ctx := by
  have first := raw_F05_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F05.frontEndAfter (raw_F05.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_F05.frontEndTicks + 1] (some (raw_F05.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_F05.beforeClear ctx)
  have sameData : raw_F05.frontEndAfter = raw_F05.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_F05_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F05.RunExpected (step caller) regs ctx := by
  have first := raw_F05_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F05.frontEndAfter (raw_F05.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_F05.frontEndAfter
    (answerRegisters false (raw_F05.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_F06_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_F06.frontEndTicks (raw_F06.start regs ctx) (raw_F06.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_F06.raw ctx

theorem raw_F06_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F06.IntermediateExpected (step caller) regs ctx := by
  have first := raw_F06_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F06.frontEndAfter (raw_F06.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_F06.frontEndTicks + 1] (some (raw_F06.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_F06.beforeClear ctx)
  have sameData : raw_F06.frontEndAfter = raw_F06.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_F06_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F06.RunExpected (step caller) regs ctx := by
  have first := raw_F06_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F06.frontEndAfter (raw_F06.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_F06.frontEndAfter
    (answerRegisters false (raw_F06.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_F07_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_F07.frontEndTicks (raw_F07.start regs ctx) (raw_F07.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_F07.raw ctx

theorem raw_F07_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F07.IntermediateExpected (step caller) regs ctx := by
  have first := raw_F07_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F07.frontEndAfter (raw_F07.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_F07.frontEndTicks + 1] (some (raw_F07.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_F07.beforeClear ctx)
  have sameData : raw_F07.frontEndAfter = raw_F07.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_F07_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F07.RunExpected (step caller) regs ctx := by
  have first := raw_F07_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F07.frontEndAfter (raw_F07.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_F07.frontEndAfter
    (answerRegisters false (raw_F07.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_F08_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_F08.frontEndTicks (raw_F08.start regs ctx) (raw_F08.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_F08.raw ctx

theorem raw_F08_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F08.IntermediateExpected (step caller) regs ctx := by
  have first := raw_F08_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F08.frontEndAfter (raw_F08.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_F08.frontEndTicks + 1] (some (raw_F08.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_F08.beforeClear ctx)
  have sameData : raw_F08.frontEndAfter = raw_F08.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_F08_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F08.RunExpected (step caller) regs ctx := by
  have first := raw_F08_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_F08.frontEndAfter (raw_F08.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_F08.frontEndAfter
    (answerRegisters false (raw_F08.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_I01_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_I01.frontEndTicks (raw_I01.start regs ctx) (raw_I01.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_I01.raw ctx

theorem raw_I01_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I01.IntermediateExpected (step caller) regs ctx := by
  have first := raw_I01_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I01.frontEndAfter (raw_I01.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_I01.frontEndTicks + 1] (some (raw_I01.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_I01.beforeClear ctx)
  have sameData : raw_I01.frontEndAfter = raw_I01.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_I01_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I01.RunExpected (step caller) regs ctx := by
  have first := raw_I01_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I01.frontEndAfter (raw_I01.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_I01.frontEndAfter
    (answerRegisters false (raw_I01.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_I02_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_I02.frontEndTicks (raw_I02.start regs ctx) (raw_I02.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_I02.raw ctx

theorem raw_I02_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I02.IntermediateExpected (step caller) regs ctx := by
  have first := raw_I02_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I02.frontEndAfter (raw_I02.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_I02.frontEndTicks + 1] (some (raw_I02.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_I02.beforeClear ctx)
  have sameData : raw_I02.frontEndAfter = raw_I02.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_I02_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I02.RunExpected (step caller) regs ctx := by
  have first := raw_I02_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I02.frontEndAfter (raw_I02.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_I02.frontEndAfter
    (answerRegisters false (raw_I02.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_I03_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_I03.frontEndTicks (raw_I03.start regs ctx) (raw_I03.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_I03.raw ctx

theorem raw_I03_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I03.IntermediateExpected (step caller) regs ctx := by
  have first := raw_I03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I03.frontEndAfter (raw_I03.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_I03.frontEndTicks + 1] (some (raw_I03.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_I03.beforeClear ctx)
  have sameData : raw_I03.frontEndAfter = raw_I03.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_I03_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I03.RunExpected (step caller) regs ctx := by
  have first := raw_I03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I03.frontEndAfter (raw_I03.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_I03.frontEndAfter
    (answerRegisters false (raw_I03.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_I04_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_I04.frontEndTicks (raw_I04.start regs ctx) (raw_I04.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_I04.raw ctx

theorem raw_I04_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I04.IntermediateExpected (step caller) regs ctx := by
  have first := raw_I04_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I04.frontEndAfter (raw_I04.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_I04.frontEndTicks + 1] (some (raw_I04.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_I04.beforeClear ctx)
  have sameData : raw_I04.frontEndAfter = raw_I04.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_I04_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I04.RunExpected (step caller) regs ctx := by
  have first := raw_I04_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I04.frontEndAfter (raw_I04.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_I04.frontEndAfter
    (answerRegisters false (raw_I04.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_I05_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_I05.frontEndTicks (raw_I05.start regs ctx) (raw_I05.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_I05.raw ctx

theorem raw_I05_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I05.IntermediateExpected (step caller) regs ctx := by
  have first := raw_I05_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I05.frontEndAfter (raw_I05.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_I05.frontEndTicks + 1] (some (raw_I05.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_I05.beforeClear ctx)
  have sameData : raw_I05.frontEndAfter = raw_I05.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_I05_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I05.RunExpected (step caller) regs ctx := by
  have first := raw_I05_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I05.frontEndAfter (raw_I05.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_I05.frontEndAfter
    (answerRegisters false (raw_I05.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_I06_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_I06.frontEndTicks (raw_I06.start regs ctx) (raw_I06.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_I06.raw ctx

theorem raw_I06_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I06.IntermediateExpected (step caller) regs ctx := by
  have first := raw_I06_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I06.frontEndAfter (raw_I06.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_I06.frontEndTicks + 1] (some (raw_I06.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_I06.beforeClear ctx)
  have sameData : raw_I06.frontEndAfter = raw_I06.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_I06_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I06.RunExpected (step caller) regs ctx := by
  have first := raw_I06_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I06.frontEndAfter (raw_I06.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_I06.frontEndAfter
    (answerRegisters false (raw_I06.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_I07_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_I07.frontEndTicks (raw_I07.start regs ctx) (raw_I07.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_I07.raw ctx

theorem raw_I07_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I07.IntermediateExpected (step caller) regs ctx := by
  have first := raw_I07_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I07.frontEndAfter (raw_I07.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_I07.frontEndTicks + 1] (some (raw_I07.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_I07.beforeClear ctx)
  have sameData : raw_I07.frontEndAfter = raw_I07.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_I07_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I07.RunExpected (step caller) regs ctx := by
  have first := raw_I07_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_I07.frontEndAfter (raw_I07.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_I07.frontEndAfter
    (answerRegisters false (raw_I07.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_C01_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_C01.frontEndTicks (raw_C01.start regs ctx) (raw_C01.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_C01.raw ctx

theorem raw_C01_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_C01.IntermediateExpected (step caller) regs ctx := by
  have first := raw_C01_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_C01.frontEndAfter (raw_C01.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_C01.frontEndTicks + 1] (some (raw_C01.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_C01.beforeClear ctx)
  have sameData : raw_C01.frontEndAfter = raw_C01.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_C01_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_C01.RunExpected (step caller) regs ctx := by
  have first := raw_C01_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_C01.frontEndAfter (raw_C01.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_C01.frontEndAfter
    (answerRegisters false (raw_C01.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_C02_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_C02.frontEndTicks (raw_C02.start regs ctx) (raw_C02.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_C02.raw ctx

theorem raw_C02_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_C02.IntermediateExpected (step caller) regs ctx := by
  have first := raw_C02_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_C02.frontEndAfter (raw_C02.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_C02.frontEndTicks + 1] (some (raw_C02.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_C02.beforeClear ctx)
  have sameData : raw_C02.frontEndAfter = raw_C02.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_C02_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_C02.RunExpected (step caller) regs ctx := by
  have first := raw_C02_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_C02.frontEndAfter (raw_C02.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_C02.frontEndAfter
    (answerRegisters false (raw_C02.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_C03_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_C03.frontEndTicks (raw_C03.start regs ctx) (raw_C03.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_C03.raw ctx

theorem raw_C03_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_C03.IntermediateExpected (step caller) regs ctx := by
  have first := raw_C03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_C03.frontEndAfter (raw_C03.frontEndKind.registers regs) ctx)
  refine ⟨first.iterate caller, ?_⟩
  have joined := LocalRun.trans caller first join
  change (next caller)^[raw_C03.frontEndTicks + 1] (some (raw_C03.start regs ctx)) =
    some (cfg (some (clearLabel 0)) (answerRegisters false regs) raw_C03.beforeClear ctx)
  have sameData : raw_C03.frontEndAfter = raw_C03.beforeClear := rfl
  simpa only [answer_after_any_front_end_outcome, sameData] using joined.iterate caller

theorem raw_C03_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_C03.RunExpected (step caller) regs ctx := by
  have first := raw_C03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (reject_step caller raw_C03.frontEndAfter (raw_C03.frontEndKind.registers regs) ctx)
  have tail := cleanup_localRun caller 0 raw_C03.frontEndAfter
    (answerRegisters false (raw_C03.frontEndKind.registers regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first join) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters,
    full_reset_after_any_front_end_outcome] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V01_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V01.frontEndTicks (raw_V01.start regs ctx) (raw_V01.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V01.raw ctx

theorem raw_V01_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V01.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V01_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V01.frontEndAfter (raw_V01.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V01_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V01.result raw_V01.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V01_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V01.RunExpected (step caller) regs ctx := by
  have first := raw_V01_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V01.frontEndAfter (raw_V01.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V01_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V01.result raw_V01.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V01.beforeClear
    (answerRegisters raw_V01.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V02_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V02.frontEndTicks (raw_V02.start regs ctx) (raw_V02.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V02.raw ctx

theorem raw_V02_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V02.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V02_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V02.frontEndAfter (raw_V02.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V02_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V02.result raw_V02.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V02_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V02.RunExpected (step caller) regs ctx := by
  have first := raw_V02_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V02.frontEndAfter (raw_V02.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V02_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V02.result raw_V02.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V02.beforeClear
    (answerRegisters raw_V02.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V03_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V03.frontEndTicks (raw_V03.start regs ctx) (raw_V03.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V03.raw ctx

theorem raw_V03_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V03.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V03.frontEndAfter (raw_V03.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V03_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V03.result raw_V03.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V03_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V03.RunExpected (step caller) regs ctx := by
  have first := raw_V03_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V03.frontEndAfter (raw_V03.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V03_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V03.result raw_V03.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V03.beforeClear
    (answerRegisters raw_V03.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V04_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V04.frontEndTicks (raw_V04.start regs ctx) (raw_V04.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V04.raw ctx

theorem raw_V04_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V04.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V04_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V04.frontEndAfter (raw_V04.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V04_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V04.result raw_V04.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V04_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V04.RunExpected (step caller) regs ctx := by
  have first := raw_V04_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V04.frontEndAfter (raw_V04.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V04_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V04.result raw_V04.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V04.beforeClear
    (answerRegisters raw_V04.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V05_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V05.frontEndTicks (raw_V05.start regs ctx) (raw_V05.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V05.raw ctx

theorem raw_V05_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V05.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V05_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V05.frontEndAfter (raw_V05.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V05_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V05.result raw_V05.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V05_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V05.RunExpected (step caller) regs ctx := by
  have first := raw_V05_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V05.frontEndAfter (raw_V05.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V05_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V05.result raw_V05.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V05.beforeClear
    (answerRegisters raw_V05.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V06_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V06.frontEndTicks (raw_V06.start regs ctx) (raw_V06.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V06.raw ctx

theorem raw_V06_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V06.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V06_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V06.frontEndAfter (raw_V06.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V06_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V06.result raw_V06.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V06_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V06.RunExpected (step caller) regs ctx := by
  have first := raw_V06_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V06.frontEndAfter (raw_V06.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V06_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V06.result raw_V06.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V06.beforeClear
    (answerRegisters raw_V06.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V07_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V07.frontEndTicks (raw_V07.start regs ctx) (raw_V07.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V07.raw ctx

theorem raw_V07_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V07.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V07_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V07.frontEndAfter (raw_V07.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V07_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V07.result raw_V07.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V07_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V07.RunExpected (step caller) regs ctx := by
  have first := raw_V07_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V07.frontEndAfter (raw_V07.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V07_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V07.result raw_V07.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V07.beforeClear
    (answerRegisters raw_V07.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V08_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V08.frontEndTicks (raw_V08.start regs ctx) (raw_V08.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V08.raw ctx

theorem raw_V08_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V08.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V08_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V08.frontEndAfter (raw_V08.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V08_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V08.result raw_V08.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V08_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V08.RunExpected (step caller) regs ctx := by
  have first := raw_V08_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V08.frontEndAfter (raw_V08.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V08_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V08.result raw_V08.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V08.beforeClear
    (answerRegisters raw_V08.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V09_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V09.frontEndTicks (raw_V09.start regs ctx) (raw_V09.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V09.raw ctx

theorem raw_V09_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V09.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V09_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V09.frontEndAfter (raw_V09.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V09_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V09.result raw_V09.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V09_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V09.RunExpected (step caller) regs ctx := by
  have first := raw_V09_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V09.frontEndAfter (raw_V09.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V09_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V09.result raw_V09.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V09.beforeClear
    (answerRegisters raw_V09.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V10_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V10.frontEndTicks (raw_V10.start regs ctx) (raw_V10.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V10.raw ctx

theorem raw_V10_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V10.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V10_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V10.frontEndAfter (raw_V10.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V10_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V10.result raw_V10.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V10_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V10.RunExpected (step caller) regs ctx := by
  have first := raw_V10_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V10.frontEndAfter (raw_V10.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V10_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V10.result raw_V10.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V10.beforeClear
    (answerRegisters raw_V10.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V11_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V11.frontEndTicks (raw_V11.start regs ctx) (raw_V11.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V11.raw ctx

theorem raw_V11_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V11.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V11_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V11.frontEndAfter (raw_V11.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V11_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V11.result raw_V11.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V11_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V11.RunExpected (step caller) regs ctx := by
  have first := raw_V11_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V11.frontEndAfter (raw_V11.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V11_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V11.result raw_V11.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V11.beforeClear
    (answerRegisters raw_V11.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V12_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V12.frontEndTicks (raw_V12.start regs ctx) (raw_V12.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V12.raw ctx

theorem raw_V12_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V12.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V12_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V12.frontEndAfter (raw_V12.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V12_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V12.result raw_V12.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V12_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V12.RunExpected (step caller) regs ctx := by
  have first := raw_V12_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V12.frontEndAfter (raw_V12.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V12_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V12.result raw_V12.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V12.beforeClear
    (answerRegisters raw_V12.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V13_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V13.frontEndTicks (raw_V13.start regs ctx) (raw_V13.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V13.raw ctx

theorem raw_V13_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V13.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V13_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V13.frontEndAfter (raw_V13.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V13_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V13.result raw_V13.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V13_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V13.RunExpected (step caller) regs ctx := by
  have first := raw_V13_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V13.frontEndAfter (raw_V13.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V13_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V13.result raw_V13.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V13.beforeClear
    (answerRegisters raw_V13.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V14_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V14.frontEndTicks (raw_V14.start regs ctx) (raw_V14.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V14.raw ctx

theorem raw_V14_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V14.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V14_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V14.frontEndAfter (raw_V14.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V14_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V14.result raw_V14.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V14_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V14.RunExpected (step caller) regs ctx := by
  have first := raw_V14_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V14.frontEndAfter (raw_V14.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V14_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V14.result raw_V14.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V14.beforeClear
    (answerRegisters raw_V14.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V15_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V15.frontEndTicks (raw_V15.start regs ctx) (raw_V15.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V15.raw ctx

theorem raw_V15_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V15.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V15_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V15.frontEndAfter (raw_V15.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V15_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V15.result raw_V15.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V15_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V15.RunExpected (step caller) regs ctx := by
  have first := raw_V15_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V15.frontEndAfter (raw_V15.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V15_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V15.result raw_V15.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V15.beforeClear
    (answerRegisters raw_V15.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V16_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V16.frontEndTicks (raw_V16.start regs ctx) (raw_V16.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V16.raw ctx

theorem raw_V16_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V16.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V16_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V16.frontEndAfter (raw_V16.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V16_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V16.result raw_V16.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V16_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V16.RunExpected (step caller) regs ctx := by
  have first := raw_V16_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V16.frontEndAfter (raw_V16.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V16_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V16.result raw_V16.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V16.beforeClear
    (answerRegisters raw_V16.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V17_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V17.frontEndTicks (raw_V17.start regs ctx) (raw_V17.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V17.raw ctx

theorem raw_V17_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V17.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V17_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V17.frontEndAfter (raw_V17.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V17_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V17.result raw_V17.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V17_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V17.RunExpected (step caller) regs ctx := by
  have first := raw_V17_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V17.frontEndAfter (raw_V17.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V17_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V17.result raw_V17.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V17.beforeClear
    (answerRegisters raw_V17.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

theorem raw_V18_frontend_actual_local_run (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller raw_V18.frontEndTicks (raw_V18.start regs ctx) (raw_V18.frontEndFinish regs ctx) :=
  frontEnd_clean_localRun caller regs raw_V18.raw ctx

theorem raw_V18_actual_intermediates (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V18.IntermediateExpected (step caller) regs ctx := by
  have first := raw_V18_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V18.frontEndAfter (raw_V18.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V18_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V18.result raw_V18.beforeClear (fullReset regs) ctx)
  have answered := LocalRun.trans caller streamed answerJoin
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, answered.iterate caller⟩

theorem raw_V18_actual_first_halt (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V18.RunExpected (step caller) regs ctx := by
  have first := raw_V18_frontend_actual_local_run caller regs ctx
  have join := phase_step_localRun caller
    (dispatch_step caller raw_V18.frontEndAfter (raw_V18.frontEndKind.registers regs) ctx)
  simp only [full_reset_after_any_front_end_outcome] at join
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before (raw_V18_stream_actual_local_run caller regs ctx)
  have answerJoin := phase_step_localRun caller
    (result_step caller raw_V18.result raw_V18.beforeClear (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 raw_V18.beforeClear
    (answerRegisters raw_V18.result (fullReset regs)) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller streamed answerJoin) tail
  simp only [fullReset_answerRegisters, answer_answerRegisters, fullReset_fullReset] at joined
  exact first_halt_of_actual_local_run caller joined rfl

/-- Actual first-halt uniqueness identifies the proof-side clock without defining a fixture by it. -/
theorem an_actual_raw_fixture_has_the_canonical_clock
    (fixture : RawFixture) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (checked : fixture.RunExpected (step caller) regs ctx) : fixture.ticks = runSteps fixture.raw := by
  have first := LocalRun.of_iterate caller checked.1 checked.2.2
  have canonical := run_localRun caller regs fixture.raw ctx
  apply (LocalRun.first_unique caller first canonical ?_ ?_).1
  · rw [checked.2.1]
    exact not_owned_none
  · rw [runResult_eq]
    exact not_owned_none

variable [Fintype K]

theorem raw_F01_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_F01.start regs ctx) raw_F01.ticks (raw_F01.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_F01 regs ctx
    (raw_F01_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_F01.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_F01_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F01.Expected (step caller) regs ctx :=
  ⟨raw_F01_actual_first_halt caller regs ctx, raw_F01_actual_intermediates caller regs ctx,
    by trivial, raw_F01_actual_exact_peak caller regs ctx⟩

theorem raw_F02_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_F02.start regs ctx) raw_F02.ticks (raw_F02.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_F02 regs ctx
    (raw_F02_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_F02.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_F02_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F02.Expected (step caller) regs ctx :=
  ⟨raw_F02_actual_first_halt caller regs ctx, raw_F02_actual_intermediates caller regs ctx,
    by trivial, raw_F02_actual_exact_peak caller regs ctx⟩

theorem raw_F03_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_F03.start regs ctx) raw_F03.ticks (raw_F03.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_F03 regs ctx
    (raw_F03_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_F03.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_F03_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F03.Expected (step caller) regs ctx :=
  ⟨raw_F03_actual_first_halt caller regs ctx, raw_F03_actual_intermediates caller regs ctx,
    by trivial, raw_F03_actual_exact_peak caller regs ctx⟩

theorem raw_F04_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_F04.start regs ctx) raw_F04.ticks (raw_F04.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_F04 regs ctx
    (raw_F04_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_F04.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_F04_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F04.Expected (step caller) regs ctx :=
  ⟨raw_F04_actual_first_halt caller regs ctx, raw_F04_actual_intermediates caller regs ctx,
    by trivial, raw_F04_actual_exact_peak caller regs ctx⟩

theorem raw_F05_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_F05.start regs ctx) raw_F05.ticks (raw_F05.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_F05 regs ctx
    (raw_F05_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_F05.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_F05_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F05.Expected (step caller) regs ctx :=
  ⟨raw_F05_actual_first_halt caller regs ctx, raw_F05_actual_intermediates caller regs ctx,
    by trivial, raw_F05_actual_exact_peak caller regs ctx⟩

theorem raw_F06_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_F06.start regs ctx) raw_F06.ticks (raw_F06.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_F06 regs ctx
    (raw_F06_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_F06.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_F06_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F06.Expected (step caller) regs ctx :=
  ⟨raw_F06_actual_first_halt caller regs ctx, raw_F06_actual_intermediates caller regs ctx,
    by trivial, raw_F06_actual_exact_peak caller regs ctx⟩

theorem raw_F07_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_F07.start regs ctx) raw_F07.ticks (raw_F07.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_F07 regs ctx
    (raw_F07_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_F07.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_F07_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F07.Expected (step caller) regs ctx :=
  ⟨raw_F07_actual_first_halt caller regs ctx, raw_F07_actual_intermediates caller regs ctx,
    by trivial, raw_F07_actual_exact_peak caller regs ctx⟩

theorem raw_F08_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_F08.start regs ctx) raw_F08.ticks (raw_F08.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_F08 regs ctx
    (raw_F08_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_F08.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_F08_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_F08.Expected (step caller) regs ctx :=
  ⟨raw_F08_actual_first_halt caller regs ctx, raw_F08_actual_intermediates caller regs ctx,
    by trivial, raw_F08_actual_exact_peak caller regs ctx⟩

theorem raw_I01_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_I01.start regs ctx) raw_I01.ticks (raw_I01.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_I01 regs ctx
    (raw_I01_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_I01.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_I01_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I01.Expected (step caller) regs ctx :=
  ⟨raw_I01_actual_first_halt caller regs ctx, raw_I01_actual_intermediates caller regs ctx,
    by trivial, raw_I01_actual_exact_peak caller regs ctx⟩

theorem raw_I02_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_I02.start regs ctx) raw_I02.ticks (raw_I02.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_I02 regs ctx
    (raw_I02_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_I02.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_I02_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I02.Expected (step caller) regs ctx :=
  ⟨raw_I02_actual_first_halt caller regs ctx, raw_I02_actual_intermediates caller regs ctx,
    by trivial, raw_I02_actual_exact_peak caller regs ctx⟩

theorem raw_I03_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_I03.start regs ctx) raw_I03.ticks (raw_I03.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_I03 regs ctx
    (raw_I03_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_I03.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_I03_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I03.Expected (step caller) regs ctx :=
  ⟨raw_I03_actual_first_halt caller regs ctx, raw_I03_actual_intermediates caller regs ctx,
    by trivial, raw_I03_actual_exact_peak caller regs ctx⟩

theorem raw_I04_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_I04.start regs ctx) raw_I04.ticks (raw_I04.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_I04 regs ctx
    (raw_I04_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_I04.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_I04_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I04.Expected (step caller) regs ctx :=
  ⟨raw_I04_actual_first_halt caller regs ctx, raw_I04_actual_intermediates caller regs ctx,
    by trivial, raw_I04_actual_exact_peak caller regs ctx⟩

theorem raw_I05_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_I05.start regs ctx) raw_I05.ticks (raw_I05.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_I05 regs ctx
    (raw_I05_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_I05.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_I05_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I05.Expected (step caller) regs ctx :=
  ⟨raw_I05_actual_first_halt caller regs ctx, raw_I05_actual_intermediates caller regs ctx,
    by trivial, raw_I05_actual_exact_peak caller regs ctx⟩

theorem raw_I06_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_I06.start regs ctx) raw_I06.ticks (raw_I06.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_I06 regs ctx
    (raw_I06_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_I06.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_I06_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I06.Expected (step caller) regs ctx :=
  ⟨raw_I06_actual_first_halt caller regs ctx, raw_I06_actual_intermediates caller regs ctx,
    by trivial, raw_I06_actual_exact_peak caller regs ctx⟩

theorem raw_I07_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_I07.start regs ctx) raw_I07.ticks (raw_I07.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_I07 regs ctx
    (raw_I07_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_I07.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_I07_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_I07.Expected (step caller) regs ctx :=
  ⟨raw_I07_actual_first_halt caller regs ctx, raw_I07_actual_intermediates caller regs ctx,
    by trivial, raw_I07_actual_exact_peak caller regs ctx⟩

theorem raw_C01_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_C01.start regs ctx) raw_C01.ticks (raw_C01.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_C01 regs ctx
    (raw_C01_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_C01.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_C01_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_C01.Expected (step caller) regs ctx :=
  ⟨raw_C01_actual_first_halt caller regs ctx, raw_C01_actual_intermediates caller regs ctx,
    by trivial, raw_C01_actual_exact_peak caller regs ctx⟩

theorem raw_C02_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_C02.start regs ctx) raw_C02.ticks (raw_C02.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_C02 regs ctx
    (raw_C02_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_C02.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_C02_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_C02.Expected (step caller) regs ctx :=
  ⟨raw_C02_actual_first_halt caller regs ctx, raw_C02_actual_intermediates caller regs ctx,
    by trivial, raw_C02_actual_exact_peak caller regs ctx⟩

theorem raw_C03_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_C03.start regs ctx) raw_C03.ticks (raw_C03.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_C03 regs ctx
    (raw_C03_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_C03.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_C03.raw.length 1 = raw_C03.peak := by
    norm_num [raw_C03]
  rw [literalPeak] at peak
  exact peak

theorem raw_C03_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_C03.Expected (step caller) regs ctx :=
  ⟨raw_C03_actual_first_halt caller regs ctx, raw_C03_actual_intermediates caller regs ctx,
    by trivial, raw_C03_actual_exact_peak caller regs ctx⟩

theorem raw_V01_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V01.start regs ctx) raw_V01.ticks (raw_V01.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V01 regs ctx
    (raw_V01_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V01.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_V01_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V01.Expected (step caller) regs ctx :=
  ⟨raw_V01_actual_first_halt caller regs ctx, raw_V01_actual_intermediates caller regs ctx,
    raw_V01_stream_actual_exact_peak caller regs ctx, raw_V01_actual_exact_peak caller regs ctx⟩

theorem raw_V02_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V02.start regs ctx) raw_V02.ticks (raw_V02.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V02 regs ctx
    (raw_V02_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V02.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_V02_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V02.Expected (step caller) regs ctx :=
  ⟨raw_V02_actual_first_halt caller regs ctx, raw_V02_actual_intermediates caller regs ctx,
    raw_V02_stream_actual_exact_peak caller regs ctx, raw_V02_actual_exact_peak caller regs ctx⟩

theorem raw_V03_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V03.start regs ctx) raw_V03.ticks (raw_V03.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V03 regs ctx
    (raw_V03_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V03.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_V03.raw.length 1 = raw_V03.peak := by
    norm_num [raw_V03]
  rw [literalPeak] at peak
  exact peak

theorem raw_V03_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V03.Expected (step caller) regs ctx :=
  ⟨raw_V03_actual_first_halt caller regs ctx, raw_V03_actual_intermediates caller regs ctx,
    raw_V03_stream_actual_exact_peak caller regs ctx, raw_V03_actual_exact_peak caller regs ctx⟩

theorem raw_V04_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V04.start regs ctx) raw_V04.ticks (raw_V04.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V04 regs ctx
    (raw_V04_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V04.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_V04.raw.length 1 = raw_V04.peak := by
    norm_num [raw_V04]
  rw [literalPeak] at peak
  exact peak

theorem raw_V04_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V04.Expected (step caller) regs ctx :=
  ⟨raw_V04_actual_first_halt caller regs ctx, raw_V04_actual_intermediates caller regs ctx,
    raw_V04_stream_actual_exact_peak caller regs ctx, raw_V04_actual_exact_peak caller regs ctx⟩

theorem raw_V05_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V05.start regs ctx) raw_V05.ticks (raw_V05.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V05 regs ctx
    (raw_V05_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V05.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_V05.raw.length 1 = raw_V05.peak := by
    norm_num [raw_V05]
  rw [literalPeak] at peak
  exact peak

theorem raw_V05_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V05.Expected (step caller) regs ctx :=
  ⟨raw_V05_actual_first_halt caller regs ctx, raw_V05_actual_intermediates caller regs ctx,
    raw_V05_stream_actual_exact_peak caller regs ctx, raw_V05_actual_exact_peak caller regs ctx⟩

theorem raw_V06_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V06.start regs ctx) raw_V06.ticks (raw_V06.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V06 regs ctx
    (raw_V06_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V06.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_V06.raw.length 1 = raw_V06.peak := by
    norm_num [raw_V06]
  rw [literalPeak] at peak
  exact peak

theorem raw_V06_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V06.Expected (step caller) regs ctx :=
  ⟨raw_V06_actual_first_halt caller regs ctx, raw_V06_actual_intermediates caller regs ctx,
    raw_V06_stream_actual_exact_peak caller regs ctx, raw_V06_actual_exact_peak caller regs ctx⟩

theorem raw_V07_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V07.start regs ctx) raw_V07.ticks (raw_V07.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V07 regs ctx
    (raw_V07_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V07.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_V07.raw.length 1 = raw_V07.peak := by
    norm_num [raw_V07]
  rw [literalPeak] at peak
  exact peak

theorem raw_V07_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V07.Expected (step caller) regs ctx :=
  ⟨raw_V07_actual_first_halt caller regs ctx, raw_V07_actual_intermediates caller regs ctx,
    raw_V07_stream_actual_exact_peak caller regs ctx, raw_V07_actual_exact_peak caller regs ctx⟩

theorem raw_V08_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V08.start regs ctx) raw_V08.ticks (raw_V08.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V08 regs ctx
    (raw_V08_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V08.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_V08.raw.length 1 = raw_V08.peak := by
    norm_num [raw_V08]
  rw [literalPeak] at peak
  exact peak

theorem raw_V08_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V08.Expected (step caller) regs ctx :=
  ⟨raw_V08_actual_first_halt caller regs ctx, raw_V08_actual_intermediates caller regs ctx,
    raw_V08_stream_actual_exact_peak caller regs ctx, raw_V08_actual_exact_peak caller regs ctx⟩

theorem raw_V09_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V09.start regs ctx) raw_V09.ticks (raw_V09.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V09 regs ctx
    (raw_V09_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V09.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_V09_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V09.Expected (step caller) regs ctx :=
  ⟨raw_V09_actual_first_halt caller regs ctx, raw_V09_actual_intermediates caller regs ctx,
    raw_V09_stream_actual_exact_peak caller regs ctx, raw_V09_actual_exact_peak caller regs ctx⟩

theorem raw_V10_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V10.start regs ctx) raw_V10.ticks (raw_V10.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V10 regs ctx
    (raw_V10_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V10.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_V10.raw.length 1 = raw_V10.peak := by
    norm_num [raw_V10]
  rw [literalPeak] at peak
  exact peak

theorem raw_V10_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V10.Expected (step caller) regs ctx :=
  ⟨raw_V10_actual_first_halt caller regs ctx, raw_V10_actual_intermediates caller regs ctx,
    raw_V10_stream_actual_exact_peak caller regs ctx, raw_V10_actual_exact_peak caller regs ctx⟩

theorem raw_V11_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V11.start regs ctx) raw_V11.ticks (raw_V11.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V11 regs ctx
    (raw_V11_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V11.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_V11.raw.length 1 = raw_V11.peak := by
    norm_num [raw_V11]
  rw [literalPeak] at peak
  exact peak

theorem raw_V11_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V11.Expected (step caller) regs ctx :=
  ⟨raw_V11_actual_first_halt caller regs ctx, raw_V11_actual_intermediates caller regs ctx,
    raw_V11_stream_actual_exact_peak caller regs ctx, raw_V11_actual_exact_peak caller regs ctx⟩

theorem raw_V12_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V12.start regs ctx) raw_V12.ticks (raw_V12.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V12 regs ctx
    (raw_V12_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V12.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_V12.raw.length 1 = raw_V12.peak := by
    norm_num [raw_V12]
  rw [literalPeak] at peak
  exact peak

theorem raw_V12_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V12.Expected (step caller) regs ctx :=
  ⟨raw_V12_actual_first_halt caller regs ctx, raw_V12_actual_intermediates caller regs ctx,
    raw_V12_stream_actual_exact_peak caller regs ctx, raw_V12_actual_exact_peak caller regs ctx⟩

theorem raw_V13_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V13.start regs ctx) raw_V13.ticks (raw_V13.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V13 regs ctx
    (raw_V13_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V13.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_V13.raw.length 1 = raw_V13.peak := by
    norm_num [raw_V13]
  rw [literalPeak] at peak
  exact peak

theorem raw_V13_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V13.Expected (step caller) regs ctx :=
  ⟨raw_V13_actual_first_halt caller regs ctx, raw_V13_actual_intermediates caller regs ctx,
    raw_V13_stream_actual_exact_peak caller regs ctx, raw_V13_actual_exact_peak caller regs ctx⟩

theorem raw_V14_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V14.start regs ctx) raw_V14.ticks (raw_V14.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V14 regs ctx
    (raw_V14_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V14.raw ctx)
  rw [← clock] at peak
  have literalPeak : max raw_V14.raw.length 1 = raw_V14.peak := by
    norm_num [raw_V14]
  rw [literalPeak] at peak
  exact peak

theorem raw_V14_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V14.Expected (step caller) regs ctx :=
  ⟨raw_V14_actual_first_halt caller regs ctx, raw_V14_actual_intermediates caller regs ctx,
    raw_V14_stream_actual_exact_peak caller regs ctx, raw_V14_actual_exact_peak caller regs ctx⟩

theorem raw_V15_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V15.start regs ctx) raw_V15.ticks (raw_V15.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V15 regs ctx
    (raw_V15_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V15.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_V15_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V15.Expected (step caller) regs ctx :=
  ⟨raw_V15_actual_first_halt caller regs ctx, raw_V15_actual_intermediates caller regs ctx,
    raw_V15_stream_actual_exact_peak caller regs ctx, raw_V15_actual_exact_peak caller regs ctx⟩

theorem raw_V16_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V16.start regs ctx) raw_V16.ticks (raw_V16.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V16 regs ctx
    (raw_V16_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V16.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_V16_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V16.Expected (step caller) regs ctx :=
  ⟨raw_V16_actual_first_halt caller regs ctx, raw_V16_actual_intermediates caller regs ctx,
    raw_V16_stream_actual_exact_peak caller regs ctx, raw_V16_actual_exact_peak caller regs ctx⟩

theorem raw_V17_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V17.start regs ctx) raw_V17.ticks (raw_V17.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V17 regs ctx
    (raw_V17_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V17.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_V17_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V17.Expected (step caller) regs ctx :=
  ⟨raw_V17_actual_first_halt caller regs ctx, raw_V17_actual_intermediates caller regs ctx,
    raw_V17_stream_actual_exact_peak caller regs ctx, raw_V17_actual_exact_peak caller regs ctx⟩

theorem raw_V18_actual_exact_peak (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (raw_V18.start regs ctx) raw_V18.ticks (raw_V18.peak + externalCells ctx) := by
  have clock := an_actual_raw_fixture_has_the_canonical_clock caller raw_V18 regs ctx
    (raw_V18_actual_first_halt caller regs ctx)
  have peak := exact_peak_from_the_actual_public_prefix_contract caller (run_peak caller regs raw_V18.raw ctx)
  rw [← clock] at peak
  exact peak

theorem raw_V18_expected (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    raw_V18.Expected (step caller) regs ctx :=
  ⟨raw_V18_actual_first_halt caller regs ctx, raw_V18_actual_intermediates caller regs ctx,
    raw_V18_stream_actual_exact_peak caller regs ctx, raw_V18_actual_exact_peak caller regs ctx⟩

theorem all_original_raw_rows_execute_with_their_complete_endpoints_and_peaks
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ∀ fixture ∈ rawCases, fixture.Expected (step caller) regs ctx := by
  intro fixture member
  simp only [rawCases, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact raw_F01_expected caller regs ctx
  · exact raw_F02_expected caller regs ctx
  · exact raw_F03_expected caller regs ctx
  · exact raw_F04_expected caller regs ctx
  · exact raw_F05_expected caller regs ctx
  · exact raw_F06_expected caller regs ctx
  · exact raw_F07_expected caller regs ctx
  · exact raw_F08_expected caller regs ctx
  · exact raw_I01_expected caller regs ctx
  · exact raw_I02_expected caller regs ctx
  · exact raw_I03_expected caller regs ctx
  · exact raw_I04_expected caller regs ctx
  · exact raw_I05_expected caller regs ctx
  · exact raw_I06_expected caller regs ctx
  · exact raw_I07_expected caller regs ctx
  · exact raw_C01_expected caller regs ctx
  · exact raw_C02_expected caller regs ctx
  · exact raw_C03_expected caller regs ctx
  · exact raw_V01_expected caller regs ctx
  · exact raw_V02_expected caller regs ctx
  · exact raw_V03_expected caller regs ctx
  · exact raw_V04_expected caller regs ctx
  · exact raw_V05_expected caller regs ctx
  · exact raw_V06_expected caller regs ctx
  · exact raw_V07_expected caller regs ctx
  · exact raw_V08_expected caller regs ctx
  · exact raw_V09_expected caller regs ctx
  · exact raw_V10_expected caller regs ctx
  · exact raw_V11_expected caller regs ctx
  · exact raw_V12_expected caller regs ctx
  · exact raw_V13_expected caller regs ctx
  · exact raw_V14_expected caller regs ctx
  · exact raw_V15_expected caller regs ctx
  · exact raw_V16_expected caller regs ctx
  · exact raw_V17_expected caller regs ctx
  · exact raw_V18_expected caller regs ctx

end LiteralRawRuns

/-! The operational raw-case aggregate has no finite-context hypothesis. -/

theorem all_original_raw_rows_have_their_actual_first_halt
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : Λ → Statement Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (fixture : RawFixture) (member : fixture ∈ rawCases) :
    fixture.RunExpected (step caller) regs ctx := by
  simp only [rawCases, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact raw_F01_actual_first_halt caller regs ctx
  · exact raw_F02_actual_first_halt caller regs ctx
  · exact raw_F03_actual_first_halt caller regs ctx
  · exact raw_F04_actual_first_halt caller regs ctx
  · exact raw_F05_actual_first_halt caller regs ctx
  · exact raw_F06_actual_first_halt caller regs ctx
  · exact raw_F07_actual_first_halt caller regs ctx
  · exact raw_F08_actual_first_halt caller regs ctx
  · exact raw_I01_actual_first_halt caller regs ctx
  · exact raw_I02_actual_first_halt caller regs ctx
  · exact raw_I03_actual_first_halt caller regs ctx
  · exact raw_I04_actual_first_halt caller regs ctx
  · exact raw_I05_actual_first_halt caller regs ctx
  · exact raw_I06_actual_first_halt caller regs ctx
  · exact raw_I07_actual_first_halt caller regs ctx
  · exact raw_C01_actual_first_halt caller regs ctx
  · exact raw_C02_actual_first_halt caller regs ctx
  · exact raw_C03_actual_first_halt caller regs ctx
  · exact raw_V01_actual_first_halt caller regs ctx
  · exact raw_V02_actual_first_halt caller regs ctx
  · exact raw_V03_actual_first_halt caller regs ctx
  · exact raw_V04_actual_first_halt caller regs ctx
  · exact raw_V05_actual_first_halt caller regs ctx
  · exact raw_V06_actual_first_halt caller regs ctx
  · exact raw_V07_actual_first_halt caller regs ctx
  · exact raw_V08_actual_first_halt caller regs ctx
  · exact raw_V09_actual_first_halt caller regs ctx
  · exact raw_V10_actual_first_halt caller regs ctx
  · exact raw_V11_actual_first_halt caller regs ctx
  · exact raw_V12_actual_first_halt caller regs ctx
  · exact raw_V13_actual_first_halt caller regs ctx
  · exact raw_V14_actual_first_halt caller regs ctx
  · exact raw_V15_actual_first_halt caller regs ctx
  · exact raw_V16_actual_first_halt caller regs ctx
  · exact raw_V17_actual_first_halt caller regs ctx
  · exact raw_V18_actual_first_halt caller regs ctx

/-! ## Genuine finite packages, with exact initialization and halt conventions -/

def independentPackage (caller : ExampleCaller) (initial : Bool) : Turing.FinTM2 :=
  machine caller initial

def twoLabelPackage (caller : Fin 2 → Statement IndependentAlphabet (Fin 2) Bool)
    (initial : Bool) : Turing.FinTM2 := machine caller initial

theorem independent_package_has_the_actual_bundled_dimensions
    (caller : ExampleCaller) (initial : Bool) :
    @Fintype.card (independentPackage caller initial).K
        (independentPackage caller initial).kFin = 18 ∧
    @Fintype.card (independentPackage caller initial).Λ
        (independentPackage caller initial).ΛFin = 97 ∧
    @Fintype.card (independentPackage caller initial).σ
        (independentPackage caller initial).σFin = 280908 := by
  change @Fintype.card (machine caller initial).K (machine caller initial).kFin = 18 ∧
    @Fintype.card (machine caller initial).Λ (machine caller initial).ΛFin = 97 ∧
    @Fintype.card (machine caller initial).σ (machine caller initial).σFin = 280908
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using machine_card_stackId caller initial
  · simpa only [Fintype.card_unit] using machine_card_label caller initial
  · simpa only [Fintype.card_bool] using machine_card_registers caller initial

theorem two_label_package_has_the_actual_bundled_dimensions
    (caller : Fin 2 → Statement IndependentAlphabet (Fin 2) Bool) (initial : Bool) :
    @Fintype.card (twoLabelPackage caller initial).K
        (twoLabelPackage caller initial).kFin = 18 ∧
    @Fintype.card (twoLabelPackage caller initial).Λ
        (twoLabelPackage caller initial).ΛFin = 98 ∧
    @Fintype.card (twoLabelPackage caller initial).σ
        (twoLabelPackage caller initial).σFin = 280908 := by
  change @Fintype.card (machine caller initial).K (machine caller initial).kFin = 18 ∧
    @Fintype.card (machine caller initial).Λ (machine caller initial).ΛFin = 98 ∧
    @Fintype.card (machine caller initial).σ (machine caller initial).σFin = 280908
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using machine_card_stackId caller initial
  · simpa only [Fintype.card_fin] using machine_card_label caller initial
  · simpa only [Fintype.card_bool] using machine_card_registers caller initial

section ActualFinitePackage

variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R]
  [∀ k, Fintype (Γ k)]
variable (caller : Λ → Statement Γ Λ R) (initial : R)

theorem the_actual_package_uses_distinct_existing_boolean_input_and_output_stores :
    (machine caller initial).k₀ = Sum.inl FrontEndMachine.LocalStack.framedRaw ∧
    (machine caller initial).k₁ = Sum.inl FrontEndMachine.LocalStack.fuel ∧
    (machine caller initial).k₀ ≠ (machine caller initial).k₁ ∧
    (machine caller initial).Γ (machine caller initial).k₀ = Bool ∧
    (machine caller initial).Γ (machine caller initial).k₁ = Bool ∧
    (machine caller initial).main = phaseLabel rawEntryPhase ∧
    (machine caller initial).initialState = initialRegisters initial :=
  ⟨machine_inputIndex caller initial, machine_outputIndex caller initial,
    machine_input_ne_output caller initial, machine_inputAlphabet caller initial,
    machine_outputAlphabet caller initial, machine_main caller initial,
    machine_initialState caller initial⟩

theorem every_actual_physical_alphabet_has_a_finite_type
    (k : (machine caller initial).K) : Finite ((machine caller initial).Γ k) :=
  machine_alphabet_finite caller initial k

theorem genuine_initialization_supplies_only_the_framed_raw_word (raw : Bits) :
    Turing.initList (machine caller initial) raw =
      cfg (some (phaseLabel rawEntryPhase)) (initialRegisters initial)
        { framedRaw := raw } (fun _ => []) := machine_initList_eq caller initial raw

theorem genuine_halt_is_a_live_none_label_with_only_its_output_word (out : Bits) :
    Turing.haltList (machine caller initial) out =
      cfg none (initialRegisters initial) { fuel := out } (fun _ => []) :=
  machine_haltList_eq caller initial out

theorem a_cleaned_endpoint_is_the_literal_package_halt_exactly_for_the_initial_user_and_empty_context
    (out : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    cfg none (fullReset regs) { fuel := out } ctx =
      Turing.haltList (machine caller initial) out ↔
      user regs = initial ∧ ctx = (fun _ => []) :=
  machine_haltList_eq_iff caller initial out regs ctx

def RawFixture.PackageExpected (fixture : RawFixture) : Prop :=
  FirstHalt (machine caller initial).step
      (Turing.initList (machine caller initial) fixture.raw) fixture.ticks
      (Turing.haltList (machine caller initial) [fixture.result]) ∧
  ExactPeak (machine caller initial).step
      (Turing.initList (machine caller initial) fixture.raw) fixture.ticks fixture.peak ∧
  (fun state : Option (Cfg Γ Λ R) => state.bind (machine caller initial).step)^[fixture.ticks + 1]
      (some (Turing.initList (machine caller initial) fixture.raw)) = none

theorem a_connected_literal_run_connects_to_actual_initList_and_haltList
    (fixture : RawFixture)
    (output : fixture.after = ({ fuel := [fixture.result] } : LocalData))
    (connected : fixture.Expected (step caller) (initialRegisters initial) (fun _ => [])) :
    fixture.PackageExpected caller initial := by
  have startEq : (Turing.initList (machine caller initial) fixture.raw : Cfg Γ Λ R) =
      fixture.start (initialRegisters initial) (fun _ => []) :=
    machine_initList_eq caller initial fixture.raw
  have finishEq :
      (Turing.haltList (machine caller initial) [fixture.result] : Cfg Γ Λ R) =
        fixture.finish (initialRegisters initial) (fun _ => []) := by
    refine (machine_haltList_eq caller initial [fixture.result]).trans ?_
    change cfg none (initialRegisters initial) { fuel := [fixture.result] } (fun _ => []) =
      cfg none (fullReset (initialRegisters initial)) fixture.after (fun _ => [])
    rw [fullReset_initialRegisters, output]
  have first : FirstHalt (machine caller initial).step
      (Turing.initList (machine caller initial) fixture.raw) fixture.ticks
      (Turing.haltList (machine caller initial) [fixture.result]) := by
    change FirstHalt (step caller)
      (Turing.initList (machine caller initial) fixture.raw) fixture.ticks
      (Turing.haltList (machine caller initial) [fixture.result])
    exact (congrArg₂ (fun start finish : Cfg Γ Λ R =>
      FirstHalt (step caller) start fixture.ticks finish) startEq finishEq).mpr connected.1
  have actualPeak : ExactPeak (step caller)
      (fixture.start (initialRegisters initial) (fun _ => [])) fixture.ticks fixture.peak := by
    simpa only [externalCells, List.length_nil, Finset.sum_const_zero, Nat.add_zero]
      using connected.2.2.2
  have peak : ExactPeak (machine caller initial).step
      (Turing.initList (machine caller initial) fixture.raw) fixture.ticks fixture.peak := by
    change ExactPeak (step caller)
      (Turing.initList (machine caller initial) fixture.raw) fixture.ticks fixture.peak
    exact (congrArg (fun start : Cfg Γ Λ R =>
      ExactPeak (step caller) start fixture.ticks fixture.peak) startEq).mpr actualPeak
  refine ⟨first, peak, ?_⟩
  change (fun state : Option (Cfg Γ Λ R) => state.bind (step caller))^[fixture.ticks + 1]
    (some (Turing.initList (machine caller initial) fixture.raw)) = none
  have reached :
      (fun state : Option (Cfg Γ Λ R) => state.bind (step caller))^[fixture.ticks]
          (some (Turing.initList (machine caller initial) fixture.raw)) =
        some (Turing.haltList (machine caller initial) [fixture.result]) := first.1
  rw [Function.iterate_succ_apply', reached]
  rfl

theorem all_36_literal_rows_use_the_real_finite_package
    (fixture : RawFixture) (member : fixture ∈ rawCases) :
    fixture.PackageExpected caller initial := by
  have connected := all_original_raw_rows_execute_with_their_complete_endpoints_and_peaks
    caller (initialRegisters initial) (fun _ => []) fixture member
  apply a_connected_literal_run_connects_to_actual_initList_and_haltList caller initial
    fixture ?_ connected
  simp only [rawCases, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

end ActualFinitePackage

theorem both_concrete_packages_execute_every_original_raw_row
    (unitCaller : ExampleCaller)
    (twoCaller : Fin 2 → Statement IndependentAlphabet (Fin 2) Bool)
    (initial : Bool) (fixture : RawFixture) (member : fixture ∈ rawCases) :
    fixture.PackageExpected unitCaller initial ∧
    fixture.PackageExpected twoCaller initial :=
  ⟨all_36_literal_rows_use_the_real_finite_package unitCaller initial fixture member,
    all_36_literal_rows_use_the_real_finite_package twoCaller initial fixture member⟩

theorem a_preserved_nonempty_installed_context_is_not_the_genuine_package_halt
    (caller : ExampleCaller) (initial : Bool) (out : Bits) (regs : Registers Bool) :
    cfg none (fullReset regs) { fuel := out } ordinaryContext ≠
      Turing.haltList (independentPackage caller initial) out := by
  intro equal
  obtain ⟨_, empty⟩ := (machine_haltList_eq_iff caller initial out regs ordinaryContext).1 equal
  have impossible := congrFun empty (0 : Fin 2)
  change [true, false, true] = [] at impossible
  cases impossible

theorem the_preserved_user_register_can_also_separate_a_cleaned_endpoint_from_haltList
    (caller : ExampleCaller) (initial : Bool) (out : Bits) :
    cfg none (fullReset (stale (!initial))) { fuel := out }
        (emptyContext : ∀ k, List (IndependentAlphabet k)) ≠
      Turing.haltList (independentPackage caller initial) out := by
  intro equal
  have impossible := (machine_haltList_eq_iff caller initial out (stale (!initial)) emptyContext).1 equal
  have userEqual : (!initial) = initial := impossible.1
  cases initial <;> cases userEqual

theorem a_late_partial_clear_keeps_lower_slots_and_is_not_a_package_halt
    (caller : ExampleCaller) (initial : Bool) :
    clear_C15.toClosedFixture.finish initial emptyContext ≠
      Turing.haltList (independentPackage caller initial) [true] := by
  intro equal
  have wordEqual := congrArg (fun c : ExampleCfg => c.stk (.inl .framedRaw)) equal
  change [true, false] = [] at wordEqual
  cases wordEqual

theorem dirty_direct_emit_pushes_onto_old_fuel_and_is_not_a_singleton_package_halt
    (caller : ExampleCaller) (initial : Bool) :
    emit_E02.toClosedFixture.finish initial emptyContext ≠
      Turing.haltList (independentPackage caller initial) [true] := by
  intro equal
  have wordEqual := congrArg (fun c : ExampleCfg => c.stk (.inl .fuel)) equal
  change [true, false, true] = [true] at wordEqual
  cases wordEqual

theorem the_empty_direct_emit_fixture_has_the_package_output_without_using_its_initializer
    (caller : ExampleCaller) (initial : Bool) :
    emit_E03.toClosedFixture.finish initial emptyContext =
      Turing.haltList (independentPackage caller initial) [false] := by
  exact (machine_haltList_eq caller initial [false]).symm

/-! ## Complete-carrier installations and the owned halt tail -/

section CompleteInstallationMaps

variable {K Λ R K' Λ' R' : Type} {Γ : K → Type} {Γ' : K' → Type}
variable (names : StackId K ≃ K') (symbols : ∀ k, alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')

theorem complete_installation_reads_back_every_label_register_and_stack_word
    (c : Cfg Γ Λ R) :
    (installedCfgEquiv names symbols registers labels).symm
        (installedCfg names symbols registers labels c) = c ∧
    (installedCfg names symbols registers labels c).l = c.l.map labels ∧
    registers.symm (installedCfg names symbols registers labels c).var = c.var ∧
    ∀ k, ((installedCfg names symbols registers labels c).stk (names k)).map
        (symbols k).symm = c.stk k :=
  ⟨installedCfg_readback names symbols registers labels c,
    installedCfg_label names symbols registers labels c,
    installedCfg_registers_readback names symbols registers labels c,
    installedCfg_stack_readback names symbols registers labels c⟩

theorem complete_installation_preserves_the_full_physical_sum
    [Fintype K] [Fintype K'] (c : Cfg Γ Λ R) :
    (∑ k, ((installedCfg names symbols registers labels c).stk k).length) = physicalCells c :=
  installed_stack_cells names symbols registers labels c

end CompleteInstallationMaps

section OwnedInstallationExecution

variable {K Λ R K' Λ' R' : Type} {Γ : K → Type} {Γ' : K' → Type}
variable [DecidableEq K] [DecidableEq K']
variable (names : StackId K ≃ K') (symbols : ∀ k, alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')
variable (caller : Λ → Statement Γ Λ R)
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
variable (installed : ∀ label, Owned (some label) →
  ambient (labels label) =
    FrontEndMachine.Transport.statement names symbols registers labels (program caller label))

omit names symbols registers labels caller installed [DecidableEq K] in
theorem any_live_halt_configuration_takes_one_step_to_outer_none
    (halted : Turing.TM2.Cfg Γ' Λ' R') (label : halted.l = none) :
    Turing.TM2.step ambient halted = none := by
  rcases halted with ⟨l, regs, words⟩
  cases label
  rfl

omit names symbols registers labels caller installed [DecidableEq K] in
theorem any_ambient_optional_iterator_keeps_outer_none (n : Nat) :
    (FrontEndMachine.Transport.next ambient)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

include installed in
theorem an_actual_owned_first_halt_transports_its_complete_endpoint_and_every_later_none
    (start finish : Cfg Γ Λ R) (ticks : Nat)
    (first : FirstHalt (step caller) start ticks finish) :
    (FrontEndMachine.Transport.next ambient)^[ticks]
        (some (installedCfg names symbols registers labels start)) =
      some (installedCfg names symbols registers labels finish) ∧
    (installedCfg names symbols registers labels finish).l = none ∧
    (∀ n, n < ticks → ∃ reached,
      (FrontEndMachine.Transport.next ambient)^[n]
          (some (installedCfg names symbols registers labels start)) = some reached ∧
      installedOwned labels reached.l) ∧
    ∀ extra, (FrontEndMachine.Transport.next ambient)^[ticks + 1 + extra]
        (some (installedCfg names symbols registers labels start)) = none := by
  have localRun : LocalRun caller ticks start finish :=
    LocalRun.of_iterate caller first.1 first.2.2
  have executed := installed_localRun names symbols registers labels caller ambient installed localRun
  have halted : (installedCfg names symbols registers labels finish).l = none := by
    rw [installedCfg_label, first.2.1]
    rfl
  refine ⟨executed, halted, ?_, ?_⟩
  · intro n strict
    exact installed_localRun_owned_prefix names symbols registers labels caller ambient
      installed localRun n strict
  · intro extra
    have vanished : (FrontEndMachine.Transport.next ambient)^[ticks + 1]
        (some (installedCfg names symbols registers labels start)) = none := by
      rw [Function.iterate_succ_apply', executed]
      exact any_live_halt_configuration_takes_one_step_to_outer_none ambient _ halted
    rw [Nat.add_comm (ticks + 1) extra, Function.iterate_add_apply, vanished]
    exact any_ambient_optional_iterator_keeps_outer_none ambient extra

include installed in
theorem every_actual_owned_prefix_uses_the_same_complete_installation
    (start finish : Cfg Γ Λ R) (ticks : Nat)
    (first : FirstHalt (step caller) start ticks finish) (n : Nat) (bound : n ≤ ticks) :
    (FrontEndMachine.Transport.next ambient)^[n]
        (some (installedCfg names symbols registers labels start)) =
      ((next caller)^[n] (some start)).map (installedCfg names symbols registers labels) := by
  exact installed_prefix_of_owned names symbols registers labels caller ambient installed n start
    (fun j earlier => first.2.2 j (Nat.lt_of_lt_of_le earlier bound))

include installed in
theorem every_literal_raw_case_has_the_same_installed_first_halt_and_halt_tail
    (fixture : RawFixture) (member : fixture ∈ rawCases)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (FrontEndMachine.Transport.next ambient)^[fixture.ticks]
        (some (installedCfg names symbols registers labels (fixture.start regs ctx))) =
      some (installedCfg names symbols registers labels (fixture.finish regs ctx)) ∧
    (installedCfg names symbols registers labels (fixture.finish regs ctx)).l = none ∧
    (∀ n, n < fixture.ticks → ∃ reached,
      (FrontEndMachine.Transport.next ambient)^[n]
          (some (installedCfg names symbols registers labels (fixture.start regs ctx))) = some reached ∧
      installedOwned labels reached.l) ∧
    ∀ extra, (FrontEndMachine.Transport.next ambient)^[fixture.ticks + 1 + extra]
        (some (installedCfg names symbols registers labels (fixture.start regs ctx))) = none := by
  have actual := all_original_raw_rows_have_their_actual_first_halt caller regs ctx fixture member
  exact an_actual_owned_first_halt_transports_its_complete_endpoint_and_every_later_none
    names symbols registers labels caller ambient installed _ _ _ actual

section InstalledPhysicalSpace

variable [Fintype K] [Fintype K']

include installed in
theorem actual_installed_prefixes_preserve_both_the_exact_peak_bound_and_its_attained_witness
    (start finish : Cfg Γ Λ R) (ticks peak : Nat)
    (first : FirstHalt (step caller) start ticks finish)
    (maximum : ExactPeak (step caller) start ticks peak) :
    (∀ n, n ≤ ticks → ∀ reached,
      (FrontEndMachine.Transport.next ambient)^[n]
          (some (installedCfg names symbols registers labels start)) = some reached →
      (∑ k, (reached.stk k).length) ≤ peak) ∧
    ∃ n reached, n ≤ ticks ∧
      (FrontEndMachine.Transport.next ambient)^[n]
          (some (installedCfg names symbols registers labels start)) = some reached ∧
      (∑ k, (reached.stk k).length) = peak := by
  constructor
  · intro n bound reached executed
    obtain ⟨source, sourceRun⟩ : ∃ source, (next caller)^[n] (some start) = some source := by
      by_cases last : n = ticks
      · subst n
        exact ⟨finish, first.1⟩
      · obtain ⟨source, sourceRun, _⟩ := first.2.2 n (by omega)
        exact ⟨source, sourceRun⟩
    have mapped := every_actual_owned_prefix_uses_the_same_complete_installation
      names symbols registers labels caller ambient installed start finish ticks first n bound
    rw [sourceRun] at mapped
    have same : reached = installedCfg names symbols registers labels source :=
      Option.some.inj (executed.symm.trans mapped)
    subst reached
    rw [installed_stack_cells]
    exact maximum.1 n bound source sourceRun
  · obtain ⟨n, source, bound, sourceRun, cells⟩ := maximum.2
    refine ⟨n, installedCfg names symbols registers labels source, bound, ?_, ?_⟩
    · have sourceIteration : (next caller)^[n] (some start) = some source := by
        change Runs (step caller) start n source
        exact sourceRun
      rw [every_actual_owned_prefix_uses_the_same_complete_installation names symbols registers
        labels caller ambient installed start finish ticks first n bound, sourceIteration]
      rfl
    · rw [installed_stack_cells]
      exact cells

end InstalledPhysicalSpace

omit installed in
theorem arbitrary_external_iterations_use_the_distinct_all_label_agreement_hypothesis
    (allLabels : ∀ label, ambient (labels label) =
      FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (n : Nat) (start : Option (Cfg Γ Λ R)) :
    (FrontEndMachine.Transport.next ambient)^[n]
        (start.map (installedCfg names symbols registers labels)) =
      ((next caller)^[n] start).map (installedCfg names symbols registers labels) :=
  installed_iterate names symbols registers labels caller ambient allLabels n start

end OwnedInstallationExecution

/-! ## Every owned domain and every actual configuration -/

section UniversalOwnedExecution

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : Λ → Statement Γ Λ R)

theorem every_owned_phase_has_its_exact_live_first_halt
    (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    0 < phaseSteps q D ∧
    FirstHalt (step caller) (cfg (some (phaseLabel q)) regs D ctx)
      (phaseSteps q D) (phaseResult q regs D ctx) :=
  ⟨phaseSteps_pos q D, phase_first_halt caller q D regs ctx⟩

theorem the_independently_listed_96_domains_all_have_the_full_arbitrary_state_contract
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ∀ q ∈ phaseDomains,
      0 < phaseSteps q D ∧
      FirstHalt (step caller) (cfg (some (phaseLabel q)) regs D ctx)
        (phaseSteps q D) (phaseResult q regs D ctx) := by
  intro q _
  exact every_owned_phase_has_its_exact_live_first_halt caller q D regs ctx

theorem any_actual_first_boundary_fixes_the_entire_canonical_endpoint
    (start finish : Cfg Γ Λ R) (n : Nat) :
    FirstBoundary (step caller) start n finish ↔
      n = remainingSteps start ∧ finish = finalCfg start :=
  first_boundary_iff caller start finish n

theorem any_actual_first_halt_requires_the_canonical_endpoint_itself_to_be_halted
    (start finish : Cfg Γ Λ R) (n : Nat) :
    FirstHalt (step caller) start n finish ↔
      n = remainingSteps start ∧ finish = finalCfg start ∧ (finalCfg start).l = none :=
  first_halt_iff caller start finish n

theorem every_configuration_has_an_exact_boundary_but_only_owned_starts_force_halt
    (start : Cfg Γ Λ R) :
    FirstBoundary (step caller) start (remainingSteps start) (finalCfg start) ∧
    (Owned start.l → FirstHalt (step caller) start (remainingSteps start) (finalCfg start)) :=
  ⟨cfg_first_return caller start, cfg_first_halt caller start⟩

theorem every_actual_owned_step_decreases_the_exact_natural_rank_and_keeps_the_complete_endpoint
    (before after : Cfg Γ Λ R) (transition : LocalStep caller before after) :
    remainingSteps before = remainingSteps after + 1 ∧ finalCfg before = finalCfg after :=
  ⟨local_step_remaining caller transition, finalCfg_step caller transition⟩

theorem every_positive_rank_has_an_actual_successor
    (start : Cfg Γ Λ R) (positive : 0 < remainingSteps start) :
    ∃ reached, step caller start = some reached ∧
      remainingSteps start = remainingSteps reached + 1 := local_progress caller start positive

theorem one_actual_prefix_witness_carries_rank_registers_context_and_final_state
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, Runs (step caller) start n reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧ reached.var = registersAt start n ∧
      user reached.var = user start.var ∧
      (∀ k, reached.stk (.inr (.inr k)) = start.stk (.inr (.inr k))) ∧
      finalCfg reached = finalCfg start := owned_prefix_frame caller start n bound

theorem arbitrary_protected_registers_and_words_are_preserved_along_the_actual_local_relation
    (start reached : Cfg Γ Λ R)
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    user reached.var = user start.var ∧
      ∀ k, reached.stk (.inr (.inr k)) = start.stk (.inr (.inr k)) :=
  local_reaches_frame caller path

theorem every_owned_run_is_independent_of_later_caller_bodies_at_all_times
    (other : Λ → Statement Γ Λ R) (start : Cfg Γ Λ R)
    (owned : Owned start.l) (n : Nat) :
    (next caller)^[n] (some start) = (next other)^[n] (some start) :=
  owned_iterate_caller_independent caller other start owned n

theorem an_ambient_program_needs_only_owned_body_agreement_even_after_the_halt
    (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ q, ambient (phaseLabel q) = program (fun _ => .halt) (phaseLabel q))
    (start : Cfg Γ Λ R) (owned : Owned start.l) (n : Nat) :
    (fun state : Option (Cfg Γ Λ R) => state.bind (Turing.TM2.step ambient))^[n] (some start) =
      (next caller)^[n] (some start) := ambient_owned_iterate_eq caller ambient agrees start owned n

theorem the_live_halt_time_and_outer_none_time_differ_by_one
    (start : Cfg Γ Λ R) (owned : Owned start.l) :
    FirstHalt (step caller) start (remainingSteps start) (finalCfg start) ∧
    (next caller)^[remainingSteps start + 1] (some start) = none ∧
    ∀ n, remainingSteps start < n → (next caller)^[n] (some start) = none :=
  ⟨cfg_first_halt caller start owned,
    cfg_halt_then_none caller start (finalCfg_halted_of_owned start owned),
    cfg_after_halt caller start (finalCfg_halted_of_owned start owned)⟩

def phaseExactTime (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel q)) regs D ctx)
      (some (phaseResult q regs D ctx)) (phaseSteps q D) := phaseInTime caller q D regs ctx

def configurationExactTime (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (step caller) start (some (finalCfg start)) (remainingSteps start) :=
  cfgInTime caller start

def ownedOuterNoneTime (start : Cfg Γ Λ R) (owned : Owned start.l) :
    StateTransition.EvalsToInTime (step caller) start none (remainingSteps start + 1) :=
  haltNoneInTime caller start (finalCfg_halted_of_owned start owned)

theorem exact_type_valued_times_retain_the_actual_activation_counts
    (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (start : Cfg Γ Λ R) (owned : Owned start.l) :
    (phaseExactTime caller q D regs ctx).steps = phaseSteps q D ∧
    (configurationExactTime caller start).steps = remainingSteps start ∧
    (ownedOuterNoneTime caller start owned).steps = remainingSteps start + 1 := ⟨rfl, rfl, rfl⟩

def rejectPrimitiveTime (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel rejectPhase)) regs D ctx)
      (some (cfg (some (clearLabel 0)) (answerRegisters false regs) D ctx)) 1 where
  steps := 1
  evals_in_steps := reject_step caller D regs ctx
  steps_le_m := Nat.le_refl _

def dispatchPrimitiveTime (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel dispatchPhase)) regs D ctx)
      (some (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase))) (fullReset regs) D ctx)) 1 where
  steps := 1
  evals_in_steps := dispatch_step caller D regs ctx
  steps_le_m := Nat.le_refl _

def resultPrimitiveTime (bit : Bool) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel (resultPhase bit))) regs D ctx)
      (some (cfg (some (clearLabel 0)) (answerRegisters bit regs) D ctx)) 1 where
  steps := 1
  evals_in_steps := result_step caller bit D regs ctx
  steps_le_m := Nat.le_refl _

theorem all_four_primitive_join_records_count_only_the_paid_immediate_activation
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (rejectPrimitiveTime caller D regs ctx).steps = 1 ∧
    (dispatchPrimitiveTime caller D regs ctx).steps = 1 ∧
    (resultPrimitiveTime caller false D regs ctx).steps = 1 ∧
    (resultPrimitiveTime caller true D regs ctx).steps = 1 := ⟨rfl, rfl, rfl, rfl⟩

end UniversalOwnedExecution

section UniversalPhysicalSpace

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : Λ → Statement Γ Λ R)

theorem the_dirty_allowance_bounds_the_same_actual_prefix_witness
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, Runs (step caller) start n reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧ reached.var = registersAt start n ∧
      user reached.var = user start.var ∧
      (∀ k, reached.stk (.inr (.inr k)) = start.stk (.inr (.inr k))) ∧
      finalCfg reached = finalCfg start ∧ physicalCells reached ≤ allowance start :=
  owned_prefix_space caller start n bound

theorem every_actual_rank_bounded_prefix_has_the_total_physical_bound
    (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : Runs (step caller) start n reached) :
    physicalCells reached ≤ allowance start :=
  prefix_stackCells_le_dirty caller start n bound reached executed

theorem the_clean_input_bound_shares_its_rank_register_frame_and_clock_witness
    (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ runSteps raw) :
    ∃ reached, Runs (step caller) (entry regs raw ctx) n reached ∧
      remainingSteps reached = runSteps raw - n ∧
      Relation.ReflTransGen (LocalStep caller) (entry regs raw ctx) reached ∧
      (n < runSteps raw ↔ Owned reached.l) ∧
      (n = 0 → reached = entry regs raw ctx) ∧
      reached.var = registersAt (entry (Λ := Λ) regs raw ctx) n ∧ user reached.var = user regs ∧
      (∀ k, reached.stk (.inr (.inr k)) = ctx k) ∧
      finalCfg reached = runResult regs raw ctx ∧
      physicalCells reached ≤ max raw.length 1 + externalCells ctx ∧
      runSteps raw ≤ raw.length * raw.length + 10 * raw.length + 36 :=
  run_owned_prefix caller regs raw ctx n bound

end UniversalPhysicalSpace

/-! ## Complete clean outputs, source recognition, and distinct time tariffs -/

section CompleteCleanOutputs

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : Λ → Statement Γ Λ R)

theorem the_complete_first_output_is_fixed_for_both_boolean_results
    (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (finish : Cfg Γ Λ R) :
    FirstHalt (step caller) (entry regs raw ctx) n finish ↔
      n = runSteps raw ∧
      finish = cfg none (fullReset regs) { fuel := [BitPairFraming.verifyFramed raw] } ctx :=
  run_first_halt_iff caller regs raw ctx n finish

theorem a_specified_singleton_boolean_first_output_fixes_the_clock_and_source_boolean
    (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (bit : Bool) :
    FirstHalt (step caller) (entry regs raw ctx) n
        (cfg none (fullReset regs) { fuel := [bit] } ctx) ↔
      n = runSteps raw ∧ BitPairFraming.verifyFramed raw = bit := by
  rw [the_complete_first_output_is_fixed_for_both_boolean_results caller]
  constructor
  · rintro ⟨count, endpoint⟩
    have output := congrArg (fun c : Cfg Γ Λ R => c.stk (.inl .fuel)) endpoint
    change [bit] = [BitPairFraming.verifyFramed raw] at output
    exact ⟨count, (List.cons.inj output).1.symm⟩
  · rintro ⟨count, value⟩
    exact ⟨count, by rw [value]⟩

open Trees.Rotations (applyMoves?)

theorem actual_true_first_output_is_exactly_the_complete_framed_rotation_language
    (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (∃ n finish, FirstHalt (step caller) (entry regs raw ctx) n finish ∧
      finish.stk (.inl .fuel) = [true]) ↔
      ∃ (source target : BinaryTree Unit) (fuel : Bits) (moves : List RotationMove),
        raw = BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits (certCode moves)) ∧
        applyMoves? moves source = some target ∧ moves.length ≤ Resources.BinaryCounter.value fuel :=
  run_accept_iff caller regs raw ctx

theorem actual_false_first_output_is_the_complete_complement_for_every_raw_word
    (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (∃ n, FirstHalt (step caller) (entry regs raw ctx) n
      (cfg none (fullReset regs) { fuel := [false] } ctx)) ↔
      ¬ ∃ (source target : BinaryTree Unit) (fuel : Bits) (moves : List RotationMove),
        raw = BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits (certCode moves)) ∧
        applyMoves? moves source = some target ∧ moves.length ≤ Resources.BinaryCounter.value fuel := by
  rw [← BitPairFraming.verifyFramed_accept_iff_trace]
  constructor
  · rintro ⟨n, first⟩ accepted
    have value := (a_specified_singleton_boolean_first_output_fixes_the_clock_and_source_boolean
      caller raw regs ctx n false).1 first
    rw [accepted] at value
    cases value.2
  · intro rejected
    have value : BitPairFraming.verifyFramed raw = false := by
      cases result : BitPairFraming.verifyFramed raw
      · rfl
      · exact False.elim (rejected result)
    exact ⟨runSteps raw,
      (a_specified_singleton_boolean_first_output_fixes_the_clock_and_source_boolean
        caller raw regs ctx (runSteps raw) false).2 ⟨rfl, value⟩⟩

def rawExactTime (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry regs raw ctx)
      (some (runResult regs raw ctx)) (runSteps raw) := runInTimeExact caller regs raw ctx

def rawPolynomialTime (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry regs raw ctx)
      (some (runResult regs raw ctx)) (raw.length * raw.length + 10 * raw.length + 36) :=
  runInTimePolynomial caller regs raw ctx

theorem the_polynomial_time_record_still_records_the_exact_executed_count
    (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (rawExactTime caller raw regs ctx).steps = runSteps raw ∧
    (rawPolynomialTime caller raw regs ctx).steps = runSteps raw := ⟨rfl, rfl⟩

end CompleteCleanOutputs

theorem each_front_end_failure_priority_has_its_own_literal_cleanup_cost
    (raw cert : Bits) (input : Word) (source target : BinaryTree Unit) (fuel : Bits) :
    (FrontEndMachine.sourceOutcome raw = .frameFailure →
      runSteps raw = FrontEndMachine.runSteps raw + 18) ∧
    (FrontEndMachine.sourceOutcome raw = .inputDecodeFailure cert →
      runSteps raw = FrontEndMachine.runSteps raw + cert.length + 18) ∧
    (FrontEndMachine.sourceOutcome raw = .inputParseFailure input cert →
      runSteps raw = FrontEndMachine.runSteps raw + input.length + cert.length + 18) ∧
    (FrontEndMachine.sourceOutcome raw = .certificateDecodeFailure source target fuel →
      runSteps raw = FrontEndMachine.runSteps raw + (treeCode source).length +
        (treeCode target).length + fuel.length + 18) :=
  ⟨runSteps_frameFailure raw, runSteps_inputDecodeFailure raw cert,
    runSteps_inputParseFailure raw input cert,
    runSteps_certificateDecodeFailure raw source target fuel⟩

theorem successful_front_end_syntax_charges_the_actual_stream_endpoint_mass
    (raw : Bits) (source target : BinaryTree Unit) (fuel : Bits) (cert : Word)
    (returned : FrontEndMachine.sourceOutcome raw = .success source target fuel cert) :
    runSteps raw = FrontEndMachine.runSteps raw +
      StreamMachine.runSteps fuel cert (treeCode source) (treeCode target) +
      StreamMachine.localCells (StreamMachine.runEvaluation fuel cert (treeCode source) (treeCode target)).data + 19 :=
  runSteps_success raw source target fuel cert returned

theorem represented_inputs_retain_the_full_machine_clock_on_success_or_rejection
    (source target : BinaryTree Unit) (fuel : Bits) (cert : Word) :
    runSteps (BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits cert)) =
      12 * (inputCode source target fuel).length + 10 * cert.length +
      StreamMachine.runSteps fuel cert (treeCode source) (treeCode target) +
      StreamMachine.localCells (StreamMachine.runEvaluation fuel cert (treeCode source) (treeCode target)).data + 30 :=
  runSteps_code source target fuel cert

theorem only_the_accepting_stream_premise_reduces_final_mass_to_the_fuel_width
    (source target : BinaryTree Unit) (fuel : Bits) (cert : Word)
    (accepted : (checkStreamRun fuel source target cert).1 = true) :
    runSteps (BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits cert)) =
      12 * (inputCode source target fuel).length + 10 * cert.length +
      StreamMachine.runSteps fuel cert (treeCode source) (treeCode target) + fuel.length + 30 :=
  runSteps_accepting_code source target fuel cert accepted

theorem represented_raw_boolean_agrees_with_the_measured_stream_source
    (source target : BinaryTree Unit) (fuel : Bits) (cert : Word) :
    BitPairFraming.verifyFramed
        (BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits cert)) =
      (checkStreamRun fuel source target cert).1 := by
  rw [BitPairFraming.verifyFramed_frame, verifyBitsRun_code_value, verifyRun_code]

section RepresentedCompleteOutputs

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : Λ → Statement Γ Λ R)

theorem represented_first_halt_keeps_both_outcomes_and_all_final_fields
    (source target : BinaryTree Unit) (fuel : Bits) (cert : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (finish : Cfg Γ Λ R) :
    FirstHalt (step caller)
        (entry regs (BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits cert)) ctx)
        n finish ↔
      n = 12 * (inputCode source target fuel).length + 10 * cert.length +
        StreamMachine.runSteps fuel cert (treeCode source) (treeCode target) +
        StreamMachine.localCells (StreamMachine.runEvaluation fuel cert (treeCode source) (treeCode target)).data + 30 ∧
      finish = cfg none (fullReset regs) { fuel := [(checkStreamRun fuel source target cert).1] } ctx := by
  rw [the_complete_first_output_is_fixed_for_both_boolean_results caller,
    runSteps_code, represented_raw_boolean_agrees_with_the_measured_stream_source]

def representedExactTime (source target : BinaryTree Unit) (fuel : Bits) (cert : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (entry regs (BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits cert)) ctx)
      (some (cfg none (fullReset regs) { fuel := [(checkStreamRun fuel source target cert).1] } ctx))
      (12 * (inputCode source target fuel).length + 10 * cert.length +
        StreamMachine.runSteps fuel cert (treeCode source) (treeCode target) +
        StreamMachine.localCells (StreamMachine.runEvaluation fuel cert (treeCode source) (treeCode target)).data + 30) where
  steps := 12 * (inputCode source target fuel).length + 10 * cert.length +
    StreamMachine.runSteps fuel cert (treeCode source) (treeCode target) +
    StreamMachine.localCells (StreamMachine.runEvaluation fuel cert (treeCode source) (treeCode target)).data + 30
  evals_in_steps := by
    rw [← runSteps_code]
    change (next caller)^[runSteps
      (BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits cert))]
        (some (entry regs
          (BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits cert)) ctx)) = _
    simpa only [represented_raw_boolean_agrees_with_the_measured_stream_source] using
      (run_verifyFramed caller regs
        (BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits cert)) ctx).1
  steps_le_m := Nat.le_refl _

theorem represented_type_valued_time_retains_the_actual_endpoint_mass
    (source target : BinaryTree Unit) (fuel : Bits) (cert : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (representedExactTime caller source target fuel cert regs ctx).steps =
      12 * (inputCode source target fuel).length + 10 * cert.length +
      StreamMachine.runSteps fuel cert (treeCode source) (treeCode target) +
      StreamMachine.localCells (StreamMachine.runEvaluation fuel cert (treeCode source) (treeCode target)).data + 30 := rfl

end RepresentedCompleteOutputs

theorem framing_failure_has_no_invented_bit_verifier_observation
    (raw : Bits) (failed : BitPairFraming.unframe raw = none) : sourceObservation raw = none :=
  sourceObservation_frameFailure raw failed

theorem input_decoder_failure_retains_its_existing_source_tariff
    (raw input cert : Bits) (framed : BitPairFraming.unframe raw = some (input, cert))
    (failed : (unpackWordRun input).1 = none) :
    sourceObservation raw = some (false, (unpackWordRun input).2 + 2) :=
  sourceObservation_inputDecodeFailure raw input cert framed failed

theorem input_parser_failure_retains_its_existing_source_tariff
    (raw input cert : Bits) (word : Word)
    (framed : BitPairFraming.unframe raw = some (input, cert))
    (decoded : (unpackWordRun input).1 = some word) (failed : (parseInputRun word).1 = none) :
    sourceObservation raw = some (false, (unpackWordRun input).2 + (parseInputRun word).2 + 2) :=
  sourceObservation_inputParseFailure raw input cert word framed decoded failed

theorem certificate_decoder_failure_retains_its_existing_source_tariff
    (raw input cert : Bits) (word : Word) (source target : BinaryTree Unit) (fuel : Bits)
    (framed : BitPairFraming.unframe raw = some (input, cert))
    (decoded : (unpackWordRun input).1 = some word)
    (parsed : (parseInputRun word).1 = some (source, target, fuel))
    (failed : (unpackWordRun cert).1 = none) :
    sourceObservation raw = some (false, (unpackWordRun input).2 + (parseInputRun word).2 +
      (unpackWordRun cert).2 + 2) :=
  sourceObservation_certificateDecodeFailure raw input cert word source target fuel framed decoded parsed failed

theorem successful_decoding_retains_the_actual_stream_source_tariff
    (raw input cert : Bits) (word moves : Word) (source target : BinaryTree Unit) (fuel : Bits)
    (framed : BitPairFraming.unframe raw = some (input, cert))
    (decoded : (unpackWordRun input).1 = some word)
    (parsed : (parseInputRun word).1 = some (source, target, fuel))
    (certificate : (unpackWordRun cert).1 = some moves) :
    sourceObservation raw = some ((checkStreamRun fuel source target moves).1,
      (unpackWordRun input).2 + (parseInputRun word).2 + (unpackWordRun cert).2 +
        (checkStreamRun fuel source target moves).2 + 1) :=
  sourceObservation_success raw input cert word moves source target fuel framed decoded parsed certificate

/-! ## Dirty FrontEnd and dispatch fixtures, composed through actual stages -/

def branchRawData (raw : Bits) (reverse path : List Branch) : LocalData :=
  { framedRaw := raw, moveReverse := reverse, path := path }

def branchOutcomeData (outcome : FrontEndMachine.Outcome) (reverse path : List Branch) : LocalData :=
  { frontEndOutcomeData outcome with moveReverse := reverse, path := path }

section DirtyFrontEndConnections

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : Λ → Statement Γ Λ R)

omit caller [DecidableEq K] in
theorem the_front_end_entry_view_preserves_arbitrary_old_branch_words
    (raw : Bits) (reverse path : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    frontEndCfg (FrontEndMachine.entry (Λ := FrontEndCallerLabel Λ) regs raw
      (frontEndContext (branchRawData raw reverse path) ctx)) =
      cfg (some (phaseLabel rawEntryPhase)) regs (branchRawData raw reverse path) ctx :=
  frontEndCfg_view (some (FrontEndMachine.framerLabel .scanPrefix)) regs
    (branchRawData raw reverse path) ctx

omit caller [DecidableEq K] in
theorem the_front_end_result_view_preserves_arbitrary_old_branch_words
    (outcome : FrontEndMachine.Outcome) (raw : Bits) (reverse path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    frontEndCfg (FrontEndMachine.resultCfg (Λ := FrontEndCallerLabel Λ) regs
      (frontEndContext (branchRawData raw reverse path) ctx) outcome) =
      cfg (some (phaseLabel (frontEndOutcomePhase outcome)))
        (frontEndOutcomeRegisters outcome regs) (branchOutcomeData outcome reverse path) ctx := by
  cases outcome with
  | frameFailure =>
      exact frontEndCfg_view (some FrontEndMachine.rejectLabel) (FrontEndMachine.resetFramer regs)
        (branchOutcomeData .frameFailure reverse path) ctx
  | inputDecodeFailure cert =>
      exact frontEndCfg_view (some FrontEndMachine.rejectLabel) (FrontEndMachine.afterInputDecoder regs)
        (branchOutcomeData (.inputDecodeFailure cert) reverse path) ctx
  | inputParseFailure input cert =>
      exact frontEndCfg_view (some FrontEndMachine.rejectLabel) (FrontEndMachine.reset regs)
        (branchOutcomeData (.inputParseFailure input cert) reverse path) ctx
  | certificateDecodeFailure source target fuel =>
      exact frontEndCfg_view (some FrontEndMachine.rejectLabel) (FrontEndMachine.reset regs)
        (branchOutcomeData (.certificateDecodeFailure source target fuel) reverse path) ctx
  | success source target fuel cert =>
      exact frontEndCfg_view (some FrontEndMachine.dispatchLabel) (FrontEndMachine.reset regs)
        (branchOutcomeData (.success source target fuel cert) reverse path) ctx

theorem actual_front_end_processing_does_not_clean_the_old_branch_words
    (raw : Bits) (reverse path : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (FrontEndMachine.runSteps raw)
      (cfg (some (phaseLabel rawEntryPhase)) regs (branchRawData raw reverse path) ctx)
      (cfg (some (phaseLabel (frontEndOutcomePhase (FrontEndMachine.sourceOutcome raw))))
        (frontEndOutcomeRegisters (FrontEndMachine.sourceOutcome raw) regs)
        (branchOutcomeData (FrontEndMachine.sourceOutcome raw) reverse path) ctx) := by
  have source := FrontEndMachine.run_source_trace
    (Γ := StreamMachine.frontEndAddedAlphabet Γ) (Λ := FrontEndCallerLabel Λ)
    (fun _ => .halt) regs raw (frontEndContext (branchRawData raw reverse path) ctx)
  have actual := frontEnd_trace_localRun caller (fun _ => .halt) source
  rw [the_front_end_entry_view_preserves_arbitrary_old_branch_words,
    the_front_end_result_view_preserves_arbitrary_old_branch_words] at actual
  exact actual

theorem dirty_D00_frontend_actual_local_run (value : R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller dirty_D00.frontEndTicks (dirty_D00.toClosedFixture.start value ctx)
      (cfg (some (phaseLabel dispatchPhase))
        (FrontEndMachine.afterInputDecoder (dirty_D00.fields.withUser value)) dirty_D00.frontEndAfter ctx) := by
  convert frontEnd_phase_localRun caller (.inr (.inr (.inr .emit))) dirty_D00.before
    (dirty_D00.fields.withUser value) ctx using 1 <;> rfl

theorem dirty_D01_frontend_actual_local_run (value : R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller dirty_D01.frontEndTicks (dirty_D01.toClosedFixture.start value ctx)
      (cfg (some (phaseLabel dispatchPhase))
        (FrontEndMachine.reset (dirty_D01.fields.withUser value)) dirty_D01.frontEndAfter ctx) := by
  convert actual_front_end_processing_does_not_clean_the_old_branch_words caller
    dirty_D01.before.framedRaw dirty_D01.before.moveReverse dirty_D01.before.path
    (dirty_D01.fields.withUser value) ctx using 1 <;> rfl

theorem dirty_D02_frontend_actual_local_run (value : R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller dirty_D02.frontEndTicks (dirty_D02.toClosedFixture.start value ctx)
      (cfg (some (phaseLabel dispatchPhase))
        (FrontEndMachine.reset (dirty_D02.fields.withUser value)) dirty_D02.frontEndAfter ctx) := by
  convert actual_front_end_processing_does_not_clean_the_old_branch_words caller
    dirty_D02.before.framedRaw dirty_D02.before.moveReverse dirty_D02.before.path
    (dirty_D02.fields.withUser value) ctx using 1 <;> rfl

theorem dirty_D03_frontend_actual_local_run (value : R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller dirty_D03.frontEndTicks (dirty_D03.toClosedFixture.start value ctx)
      (cfg (some (phaseLabel dispatchPhase))
        (FrontEndMachine.reset (dirty_D03.fields.withUser value)) dirty_D03.frontEndAfter ctx) := by
  convert actual_front_end_processing_does_not_clean_the_old_branch_words caller
    dirty_D03.before.framedRaw dirty_D03.before.moveReverse dirty_D03.before.path
    (dirty_D03.fields.withUser value) ctx using 1 <;> rfl

theorem dispatch_stream_and_cleanup_preserve_the_actual_full_endpoint
    (D output : LocalData) (bit : Bool) (ticks : Nat) (regs : Registers R)
    (ctx : ∀ k, List (Γ k))
    (streamed : LocalRun caller ticks
      (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase))) (fullReset regs) D ctx)
      (cfg (some (phaseLabel (resultPhase bit))) (fullReset regs) output ctx)) :
    LocalRun caller (1 + ticks + 1 + cleanupSteps 0 output)
      (cfg (some (phaseLabel dispatchPhase)) regs D ctx)
      (cfg none (fullReset regs) (cleanupData 0 bit output) ctx) := by
  have head := phase_step_localRun caller (dispatch_step caller D regs ctx)
  have before := LocalRun.trans caller head streamed
  have answerJoin := phase_step_localRun caller (result_step caller bit output (fullReset regs) ctx)
  have tail := cleanup_localRun caller 0 output (answerRegisters bit (fullReset regs)) ctx
  have complete := LocalRun.trans caller (LocalRun.trans caller before answerJoin) tail
  simpa only [fullReset_answerRegisters, fullReset_fullReset, answer_answerRegisters] using complete

theorem join_J03_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    join_J03.toClosedFixture.RunExpected (step caller) value ctx := by
  have actual := dispatch_stream_and_cleanup_preserve_the_actual_full_endpoint caller
    join_J03.before join_J03.before true 4 (join_J03.fields.withUser value) ctx
    (join_J03_stream_actual_local_run caller (join_J03.fields.withUser value) ctx)
  exact first_halt_of_actual_local_run caller actual rfl

theorem dirty_D00_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    dirty_D00.toClosedFixture.RunExpected (step caller) value ctx := by
  have first := dirty_D00_frontend_actual_local_run caller value ctx
  have tail := dispatch_stream_and_cleanup_preserve_the_actual_full_endpoint caller
    dirty_D00.stream.before dirty_D00.stream.after dirty_D00.stream.result dirty_D00.stream.ticks
    (FrontEndMachine.afterInputDecoder (dirty_D00.fields.withUser value)) ctx
    (dirty_D00_stream_actual_local_run caller (dirty_D00.fields.withUser value) ctx)
  exact first_halt_of_actual_local_run caller (LocalRun.trans caller first tail) rfl

theorem dirty_D01_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    dirty_D01.toClosedFixture.RunExpected (step caller) value ctx := by
  have first := dirty_D01_frontend_actual_local_run caller value ctx
  have tail := dispatch_stream_and_cleanup_preserve_the_actual_full_endpoint caller
    dirty_D01.stream.before dirty_D01.stream.after dirty_D01.stream.result dirty_D01.stream.ticks
    (FrontEndMachine.reset (dirty_D01.fields.withUser value)) ctx
    (dirty_D01_stream_actual_local_run caller (dirty_D01.fields.withUser value) ctx)
  exact first_halt_of_actual_local_run caller (LocalRun.trans caller first tail) rfl

theorem dirty_D02_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    dirty_D02.toClosedFixture.RunExpected (step caller) value ctx := by
  have first := dirty_D02_frontend_actual_local_run caller value ctx
  have tail := dispatch_stream_and_cleanup_preserve_the_actual_full_endpoint caller
    dirty_D02.stream.before dirty_D02.stream.after dirty_D02.stream.result dirty_D02.stream.ticks
    (FrontEndMachine.reset (dirty_D02.fields.withUser value)) ctx
    (dirty_D02_stream_actual_local_run caller (dirty_D02.fields.withUser value) ctx)
  exact first_halt_of_actual_local_run caller (LocalRun.trans caller first tail) rfl

theorem dirty_D03_actual_first_halt (value : R) (ctx : ∀ k, List (Γ k)) :
    dirty_D03.toClosedFixture.RunExpected (step caller) value ctx := by
  have first := dirty_D03_frontend_actual_local_run caller value ctx
  have tail := dispatch_stream_and_cleanup_preserve_the_actual_full_endpoint caller
    dirty_D03.stream.before dirty_D03.stream.after dirty_D03.stream.result dirty_D03.stream.ticks
    (FrontEndMachine.reset (dirty_D03.fields.withUser value)) ctx
    (dirty_D03_stream_actual_local_run caller (dirty_D03.fields.withUser value) ctx)
  exact first_halt_of_actual_local_run caller (LocalRun.trans caller first tail) rfl

end DirtyFrontEndConnections

section DirtyFrontEndPhysicalPeaks

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : Λ → Statement Γ Λ R)

theorem front_end_with_old_branch_words_has_its_attained_initial_mass_as_peak
    (raw : Bits) (reverse path : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller)
      (cfg (some (phaseLabel rawEntryPhase)) regs (branchRawData raw reverse path) ctx)
      (FrontEndMachine.runSteps raw)
      (raw.length + reverse.length + path.length + externalCells ctx) := by
  let localCaller : FrontEndMachine.External (FrontEndCallerLabel Λ) → FrontEndStatement Γ Λ R := fun _ => .halt
  let localContext := frontEndContext (branchRawData raw reverse path) ctx
  let start := FrontEndMachine.entry (Λ := FrontEndCallerLabel Λ) regs raw localContext
  have trace := FrontEndMachine.run_source_trace localCaller regs raw localContext
  constructor
  · intro n bound reached executed
    obtain ⟨middle, run, _⟩ := FrontEndMachine.run_prefix localCaller regs raw localContext n bound
    have mapped := frontEnd_prefix_transport caller localCaller n start
      (fun j smaller => trace.owned_prefix j (Nat.lt_of_lt_of_le smaller bound))
    rw [run, the_front_end_entry_view_preserves_arbitrary_old_branch_words] at mapped
    have same : reached = frontEndCfg middle := Option.some.inj (executed.symm.trans mapped)
    subst reached
    change stackCells (frontEndCfg middle) ≤ _
    rw [stackCells_frontEndCfg]
    have bounded := FrontEndMachine.prefix_stackCells_le localCaller regs raw localContext n bound middle run
    rw [frontEndContext_cells] at bounded
    change FrontEndMachine.stackCells middle ≤ raw.length + (reverse.length + path.length + externalCells ctx) at bounded
    omega
  · refine ⟨0, cfg (some (phaseLabel rawEntryPhase)) regs (branchRawData raw reverse path) ctx,
      Nat.zero_le _, rfl, ?_⟩
    rw [actual_physical_cells_of_cfg]
    simp only [branchRawData, localCells, List.length_nil, Nat.add_zero]

theorem dirty_D00_frontend_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (dirty_D00.toClosedFixture.start value ctx)
      dirty_D00.frontEndTicks (22 + externalCells ctx) := by
  constructor
  · intro n bound reached executed
    have bounded := frontEnd_component_prefix_cells caller (.inr (.inr (.inr .emit)))
      dirty_D00.before (dirty_D00.fields.withUser value) ctx n bound reached executed
    exact bounded
  · refine ⟨0, dirty_D00.toClosedFixture.start value ctx, by decide, rfl, ?_⟩
    rw [ClosedFixture.start, actual_physical_cells_of_cfg]
    rfl

theorem dispatch_with_an_actual_stream_peak_has_the_composed_exact_peak
    (D output : LocalData) (bit : Bool) (ticks peak : Nat) (regs : Registers R)
    (ctx : ∀ k, List (Γ k))
    (streamed : LocalRun caller ticks
      (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase))) (fullReset regs) D ctx)
      (cfg (some (phaseLabel (resultPhase bit))) (fullReset regs) output ctx))
    (streamPeak : ExactPeak (step caller)
      (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase))) (fullReset regs) D ctx)
      ticks (peak + externalCells ctx)) :
    ExactPeak (step caller) (cfg (some (phaseLabel dispatchPhase)) regs D ctx)
      (1 + (ticks + (1 + cleanupSteps 0 output)))
      (max (localCells D + externalCells ctx)
        (max (peak + externalCells ctx) (max (localCells output) 1 + externalCells ctx))) := by
  have first := one_step_with_unchanged_words_has_its_initial_mass_as_peak caller
    (dispatch_step caller D regs ctx) (by rw [actual_physical_cells_of_cfg, actual_physical_cells_of_cfg])
  have last := boolean_join_has_the_exact_cleanup_peak caller bit output (fullReset regs) ctx
  have suffix := exact_peaks_compose caller (streamed.iterate caller) streamPeak last
  have dispatchRun : Runs (step caller)
      (cfg (some (phaseLabel dispatchPhase)) regs D ctx) 1
      (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase))) (fullReset regs) D ctx) := by
    simpa only [Runs, Function.iterate_one, Option.bind_some] using dispatch_step caller D regs ctx
  have whole := exact_peaks_compose caller dispatchRun first suffix
  rw [actual_physical_cells_of_cfg] at whole
  exact whole

theorem join_J03_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (join_J03.toClosedFixture.start value ctx) join_J03.ticks
      (join_J03.peak + externalCells ctx) := by
  have whole := dispatch_with_an_actual_stream_peak_has_the_composed_exact_peak caller
    join_J03.before join_J03.before true 4 15 (join_J03.fields.withUser value) ctx
    (join_J03_stream_actual_local_run caller (join_J03.fields.withUser value) ctx)
    (join_J03_stream_actual_exact_peak caller (join_J03.fields.withUser value) ctx)
  change ExactPeak (step caller)
    (cfg (some (phaseLabel dispatchPhase)) (join_J03.fields.withUser value) join_J03.before ctx)
    38 (15 + externalCells ctx)
  simpa only [cleanupSteps_zero, show localCells join_J03.before = 15 from rfl, Nat.max_self,
    show max 15 1 = 15 from rfl] using whole

theorem join_J03_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    join_J03.toClosedFixture.Expected (step caller) value ctx :=
  ⟨join_J03_actual_first_halt caller value ctx, join_J03_actual_exact_peak caller value ctx⟩

end DirtyFrontEndPhysicalPeaks

/-! The dirty literal peaks use their actual component bounds and attained witnesses. -/

section LiteralDirtyPeaks
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : Λ → Statement Γ Λ R)

theorem dirty_D00_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (dirty_D00.toClosedFixture.start value ctx) dirty_D00.ticks
      (dirty_D00.peak + externalCells ctx) := by
  have first := dirty_D00_frontend_actual_local_run caller value ctx
  have firstPeak := dirty_D00_frontend_actual_exact_peak caller value ctx
  have tail := dispatch_with_an_actual_stream_peak_has_the_composed_exact_peak caller
    dirty_D00.stream.before dirty_D00.stream.after dirty_D00.stream.result dirty_D00.stream.ticks 22
    (FrontEndMachine.afterInputDecoder (dirty_D00.fields.withUser value)) ctx
    (dirty_D00_stream_actual_local_run caller (dirty_D00.fields.withUser value) ctx)
    (dirty_D00_stream_actual_exact_peak caller (dirty_D00.fields.withUser value) ctx)
  have whole := exact_peaks_compose caller (first.iterate caller) firstPeak tail
  have peakEquation : max (22 + externalCells ctx)
      (max (localCells dirty_D00.stream.before + externalCells ctx)
        (max (22 + externalCells ctx) (max (localCells dirty_D00.stream.after) 1 + externalCells ctx))) =
      dirty_D00.peak + externalCells ctx := by
    change max (22 + externalCells ctx)
      (max (22 + externalCells ctx) (max (22 + externalCells ctx) (max 8 1 + externalCells ctx))) =
      22 + externalCells ctx
    omega
  rw [peakEquation] at whole
  exact whole

theorem dirty_D00_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    dirty_D00.toClosedFixture.Expected (step caller) value ctx :=
  ⟨dirty_D00_actual_first_halt caller value ctx, dirty_D00_actual_exact_peak caller value ctx⟩

theorem dirty_D01_frontend_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (dirty_D01.toClosedFixture.start value ctx)
      dirty_D01.frontEndTicks (123 + externalCells ctx) :=
  front_end_with_old_branch_words_has_its_attained_initial_mass_as_peak caller
    dirty_D01.before.framedRaw dirty_D01.before.moveReverse dirty_D01.before.path
    (dirty_D01.fields.withUser value) ctx

theorem dirty_D01_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (dirty_D01.toClosedFixture.start value ctx) dirty_D01.ticks
      (dirty_D01.peak + externalCells ctx) := by
  have first := dirty_D01_frontend_actual_local_run caller value ctx
  have firstPeak := dirty_D01_frontend_actual_exact_peak caller value ctx
  have tail := dispatch_with_an_actual_stream_peak_has_the_composed_exact_peak caller
    dirty_D01.stream.before dirty_D01.stream.after dirty_D01.stream.result dirty_D01.stream.ticks 15
    (FrontEndMachine.reset (dirty_D01.fields.withUser value)) ctx
    (dirty_D01_stream_actual_local_run caller (dirty_D01.fields.withUser value) ctx)
    (dirty_D01_stream_actual_exact_peak caller (dirty_D01.fields.withUser value) ctx)
  have whole := exact_peaks_compose caller (first.iterate caller) firstPeak tail
  have peakEquation : max (123 + externalCells ctx)
      (max (localCells dirty_D01.stream.before + externalCells ctx)
        (max (15 + externalCells ctx) (max (localCells dirty_D01.stream.after) 1 + externalCells ctx))) =
      dirty_D01.peak + externalCells ctx := by
    change max (123 + externalCells ctx)
      (max (15 + externalCells ctx) (max (15 + externalCells ctx) (max 11 1 + externalCells ctx))) =
      123 + externalCells ctx
    omega
  rw [peakEquation] at whole
  exact whole

theorem dirty_D01_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    dirty_D01.toClosedFixture.Expected (step caller) value ctx :=
  ⟨dirty_D01_actual_first_halt caller value ctx, dirty_D01_actual_exact_peak caller value ctx⟩

theorem dirty_D02_frontend_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (dirty_D02.toClosedFixture.start value ctx)
      dirty_D02.frontEndTicks (161 + externalCells ctx) := by
  have peak := front_end_with_old_branch_words_has_its_attained_initial_mass_as_peak caller
    dirty_D02.before.framedRaw dirty_D02.before.moveReverse dirty_D02.before.path
    (dirty_D02.fields.withUser value) ctx
  have rawLength : dirty_D02.before.framedRaw.length = 157 := by
    change raw_V13.raw.length = 157
    norm_num [raw_V13]
  have reverseLength : dirty_D02.before.moveReverse.length = 2 := rfl
  have pathLength : dirty_D02.before.path.length = 2 := rfl
  have mass : dirty_D02.before.framedRaw.length + dirty_D02.before.moveReverse.length +
      dirty_D02.before.path.length = 161 := by
    rw [rawLength, reverseLength, pathLength]
  rw [mass] at peak
  exact peak

theorem dirty_D02_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (dirty_D02.toClosedFixture.start value ctx) dirty_D02.ticks
      (dirty_D02.peak + externalCells ctx) := by
  have first := dirty_D02_frontend_actual_local_run caller value ctx
  have firstPeak := dirty_D02_frontend_actual_exact_peak caller value ctx
  have tail := dispatch_with_an_actual_stream_peak_has_the_composed_exact_peak caller
    dirty_D02.stream.before dirty_D02.stream.after dirty_D02.stream.result dirty_D02.stream.ticks 22
    (FrontEndMachine.reset (dirty_D02.fields.withUser value)) ctx
    (dirty_D02_stream_actual_local_run caller (dirty_D02.fields.withUser value) ctx)
    (dirty_D02_stream_actual_exact_peak caller (dirty_D02.fields.withUser value) ctx)
  have whole := exact_peaks_compose caller (first.iterate caller) firstPeak tail
  have peakEquation : max (161 + externalCells ctx)
      (max (localCells dirty_D02.stream.before + externalCells ctx)
        (max (22 + externalCells ctx) (max (localCells dirty_D02.stream.after) 1 + externalCells ctx))) =
      dirty_D02.peak + externalCells ctx := by
    change max (161 + externalCells ctx)
      (max (22 + externalCells ctx) (max (22 + externalCells ctx) (max 18 1 + externalCells ctx))) =
      161 + externalCells ctx
    omega
  rw [peakEquation] at whole
  exact whole

theorem dirty_D02_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    dirty_D02.toClosedFixture.Expected (step caller) value ctx :=
  ⟨dirty_D02_actual_first_halt caller value ctx, dirty_D02_actual_exact_peak caller value ctx⟩

theorem dirty_D03_frontend_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (dirty_D03.toClosedFixture.start value ctx)
      dirty_D03.frontEndTicks (121 + externalCells ctx) :=
  front_end_with_old_branch_words_has_its_attained_initial_mass_as_peak caller
    dirty_D03.before.framedRaw dirty_D03.before.moveReverse dirty_D03.before.path
    (dirty_D03.fields.withUser value) ctx

theorem dirty_D03_actual_exact_peak (value : R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak (step caller) (dirty_D03.toClosedFixture.start value ctx) dirty_D03.ticks
      (dirty_D03.peak + externalCells ctx) := by
  have first := dirty_D03_frontend_actual_local_run caller value ctx
  have firstPeak := dirty_D03_frontend_actual_exact_peak caller value ctx
  have tail := dispatch_with_an_actual_stream_peak_has_the_composed_exact_peak caller
    dirty_D03.stream.before dirty_D03.stream.after dirty_D03.stream.result dirty_D03.stream.ticks 13
    (FrontEndMachine.reset (dirty_D03.fields.withUser value)) ctx
    (dirty_D03_stream_actual_local_run caller (dirty_D03.fields.withUser value) ctx)
    (dirty_D03_stream_actual_exact_peak caller (dirty_D03.fields.withUser value) ctx)
  have whole := exact_peaks_compose caller (first.iterate caller) firstPeak tail
  have peakEquation : max (121 + externalCells ctx)
      (max (localCells dirty_D03.stream.before + externalCells ctx)
        (max (13 + externalCells ctx) (max (localCells dirty_D03.stream.after) 1 + externalCells ctx))) =
      dirty_D03.peak + externalCells ctx := by
    change max (121 + externalCells ctx)
      (max (13 + externalCells ctx) (max (13 + externalCells ctx) (max 1 1 + externalCells ctx))) =
      121 + externalCells ctx
    omega
  rw [peakEquation] at whole
  exact whole

theorem dirty_D03_expected (value : R) (ctx : ∀ k, List (Γ k)) :
    dirty_D03.toClosedFixture.Expected (step caller) value ctx :=
  ⟨dirty_D03_actual_first_halt caller value ctx, dirty_D03_actual_exact_peak caller value ctx⟩

end LiteralDirtyPeaks

section LiteralDirtyIntermediateStates
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : Λ → Statement Γ Λ R)

theorem dirty_D00_actual_intermediate_states (value : R) (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (dirty_D00.toClosedFixture.start value ctx) dirty_D00.frontEndTicks
      (cfg (some (phaseLabel dispatchPhase)) (FrontEndMachine.afterInputDecoder (dirty_D00.fields.withUser value))
        dirty_D00.frontEndAfter ctx) ∧
    Runs (step caller) (dirty_D00.toClosedFixture.start value ctx) (dirty_D00.frontEndTicks + 1)
      (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase)))
        (clean value) dirty_D00.stream.before ctx) ∧
    Runs (step caller) (dirty_D00.toClosedFixture.start value ctx)
      (dirty_D00.frontEndTicks + 1 + dirty_D00.stream.ticks)
      (cfg (some (phaseLabel (resultPhase dirty_D00.stream.result)))
        (clean value) dirty_D00.stream.after ctx) ∧
    Runs (step caller) (dirty_D00.toClosedFixture.start value ctx)
      (dirty_D00.frontEndTicks + 1 + dirty_D00.stream.ticks + 1)
      (cfg (some (clearLabel 0)) (answerRegisters dirty_D00.stream.result (clean value))
        dirty_D00.stream.after ctx) := by
  have first := dirty_D00_frontend_actual_local_run caller value ctx
  have join := phase_step_localRun caller (dispatch_step caller dirty_D00.frontEndAfter
    (FrontEndMachine.afterInputDecoder (dirty_D00.fields.withUser value)) ctx)
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before
    (dirty_D00_stream_actual_local_run caller (dirty_D00.fields.withUser value) ctx)
  have tail := LocalRun.trans caller streamed (phase_step_localRun caller
    (result_step caller dirty_D00.stream.result dirty_D00.stream.after (clean value) ctx))
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, tail.iterate caller⟩

theorem dirty_D01_actual_intermediate_states (value : R) (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (dirty_D01.toClosedFixture.start value ctx) dirty_D01.frontEndTicks
      (cfg (some (phaseLabel dispatchPhase)) (FrontEndMachine.reset (dirty_D01.fields.withUser value))
        dirty_D01.frontEndAfter ctx) ∧
    Runs (step caller) (dirty_D01.toClosedFixture.start value ctx) (dirty_D01.frontEndTicks + 1)
      (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase)))
        (clean value) dirty_D01.stream.before ctx) ∧
    Runs (step caller) (dirty_D01.toClosedFixture.start value ctx)
      (dirty_D01.frontEndTicks + 1 + dirty_D01.stream.ticks)
      (cfg (some (phaseLabel (resultPhase dirty_D01.stream.result)))
        (clean value) dirty_D01.stream.after ctx) ∧
    Runs (step caller) (dirty_D01.toClosedFixture.start value ctx)
      (dirty_D01.frontEndTicks + 1 + dirty_D01.stream.ticks + 1)
      (cfg (some (clearLabel 0)) (answerRegisters dirty_D01.stream.result (clean value))
        dirty_D01.stream.after ctx) := by
  have first := dirty_D01_frontend_actual_local_run caller value ctx
  have join := phase_step_localRun caller (dispatch_step caller dirty_D01.frontEndAfter
    (FrontEndMachine.reset (dirty_D01.fields.withUser value)) ctx)
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before
    (dirty_D01_stream_actual_local_run caller (dirty_D01.fields.withUser value) ctx)
  have tail := LocalRun.trans caller streamed (phase_step_localRun caller
    (result_step caller dirty_D01.stream.result dirty_D01.stream.after (clean value) ctx))
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, tail.iterate caller⟩

theorem dirty_D02_actual_intermediate_states (value : R) (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (dirty_D02.toClosedFixture.start value ctx) dirty_D02.frontEndTicks
      (cfg (some (phaseLabel dispatchPhase)) (FrontEndMachine.reset (dirty_D02.fields.withUser value))
        dirty_D02.frontEndAfter ctx) ∧
    Runs (step caller) (dirty_D02.toClosedFixture.start value ctx) (dirty_D02.frontEndTicks + 1)
      (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase)))
        (clean value) dirty_D02.stream.before ctx) ∧
    Runs (step caller) (dirty_D02.toClosedFixture.start value ctx)
      (dirty_D02.frontEndTicks + 1 + dirty_D02.stream.ticks)
      (cfg (some (phaseLabel (resultPhase dirty_D02.stream.result)))
        (clean value) dirty_D02.stream.after ctx) ∧
    Runs (step caller) (dirty_D02.toClosedFixture.start value ctx)
      (dirty_D02.frontEndTicks + 1 + dirty_D02.stream.ticks + 1)
      (cfg (some (clearLabel 0)) (answerRegisters dirty_D02.stream.result (clean value))
        dirty_D02.stream.after ctx) := by
  have first := dirty_D02_frontend_actual_local_run caller value ctx
  have join := phase_step_localRun caller (dispatch_step caller dirty_D02.frontEndAfter
    (FrontEndMachine.reset (dirty_D02.fields.withUser value)) ctx)
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before
    (dirty_D02_stream_actual_local_run caller (dirty_D02.fields.withUser value) ctx)
  have tail := LocalRun.trans caller streamed (phase_step_localRun caller
    (result_step caller dirty_D02.stream.result dirty_D02.stream.after (clean value) ctx))
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, tail.iterate caller⟩

theorem dirty_D03_actual_intermediate_states (value : R) (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (dirty_D03.toClosedFixture.start value ctx) dirty_D03.frontEndTicks
      (cfg (some (phaseLabel dispatchPhase)) (FrontEndMachine.reset (dirty_D03.fields.withUser value))
        dirty_D03.frontEndAfter ctx) ∧
    Runs (step caller) (dirty_D03.toClosedFixture.start value ctx) (dirty_D03.frontEndTicks + 1)
      (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase)))
        (clean value) dirty_D03.stream.before ctx) ∧
    Runs (step caller) (dirty_D03.toClosedFixture.start value ctx)
      (dirty_D03.frontEndTicks + 1 + dirty_D03.stream.ticks)
      (cfg (some (phaseLabel (resultPhase dirty_D03.stream.result)))
        (clean value) dirty_D03.stream.after ctx) ∧
    Runs (step caller) (dirty_D03.toClosedFixture.start value ctx)
      (dirty_D03.frontEndTicks + 1 + dirty_D03.stream.ticks + 1)
      (cfg (some (clearLabel 0)) (answerRegisters dirty_D03.stream.result (clean value))
        dirty_D03.stream.after ctx) := by
  have first := dirty_D03_frontend_actual_local_run caller value ctx
  have join := phase_step_localRun caller (dispatch_step caller dirty_D03.frontEndAfter
    (FrontEndMachine.reset (dirty_D03.fields.withUser value)) ctx)
  have before := LocalRun.trans caller first join
  have streamed := LocalRun.trans caller before
    (dirty_D03_stream_actual_local_run caller (dirty_D03.fields.withUser value) ctx)
  have tail := LocalRun.trans caller streamed (phase_step_localRun caller
    (result_step caller dirty_D03.stream.result dirty_D03.stream.after (clean value) ctx))
  exact ⟨first.iterate caller, before.iterate caller, streamed.iterate caller, tail.iterate caller⟩

end LiteralDirtyIntermediateStates

/-! ## Live halt, outer none, and an actually allocating external caller -/

def allocatingExternal : Nat → Statement IndependentAlphabet Nat Bool :=
  fun _ => .push (.inr (.inr (0 : Fin 2))) (fun _ => true) .halt

def haltingExternal : Nat → Statement IndependentAlphabet Nat Bool := fun _ => .halt

def reenteringExternal : Nat → Statement IndependentAlphabet Nat Bool :=
  fun _ => .goto (fun _ => clearLabel 0)

def allocationStart (value : Bool) : InfiniteLabelCfg :=
  cfg (some (callerLabel 42)) (stale value) clear_C00.before ordinaryContext

def allocationFinish (value : Bool) : InfiniteLabelCfg :=
  cfg none (stale value) clear_C00.before
    (independentWords [true, true, false, true] [11, 15])

theorem the_literal_live_halt_preserves_every_dirty_field_at_zero
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : Λ → Statement Γ Λ R) (value : R) (ctx : ∀ k, List (Γ k)) :
    FirstHalt (step caller) (cfg none (staleFields.withUser value) clear_C00.before ctx) 0
      (cfg none (staleFields.withUser value) clear_C00.before ctx) ∧
    ExactPeak (step caller) (cfg none (staleFields.withUser value) clear_C00.before ctx) 0
      (32 + externalCells ctx) ∧
    next caller (some (cfg none (staleFields.withUser value) clear_C00.before ctx)) = none := by
  have first := live_halt_has_zero_first_halt_and_keeps_all_dirty_fields caller
    clear_C00.before (staleFields.withUser value) ctx
  have cells : physicalCells (cfg (Λ := Λ) none (staleFields.withUser value) clear_C00.before ctx) =
      32 + externalCells ctx := by rw [actual_physical_cells_of_cfg]; rfl
  refine ⟨first.1, ⟨?_, ?_⟩, first.2⟩
  · intro n bound reached executed
    have zero : n = 0 := by omega
    subst n
    have same := Option.some.inj executed
    subst reached
    exact Nat.le_of_eq cells
  · exact ⟨0, cfg none (staleFields.withUser value) clear_C00.before ctx, by omega, rfl, cells⟩

theorem the_literal_outer_none_has_zero_optional_rank_and_stays_none
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : Λ → Statement Γ Λ R) (n : Nat) :
    stateRemainingSteps (Γ := Γ) (Λ := Λ) (R := R) none = 0 ∧
    (next caller)^[n] none = none := ⟨rfl, outer_none_stays_none caller n⟩

theorem the_literal_external_allocator_executes_its_real_push_without_resetting_the_registers
    (value : Bool) : step allocatingExternal (allocationStart value) = some (allocationFinish value) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl k => cases k <;> rfl
      | inr k => fin_cases k <;> rfl

theorem the_external_first_boundary_is_zero_even_though_the_caller_later_allocates
    (value : Bool) :
    FirstBoundary (step allocatingExternal) (allocationStart value) 0 (allocationStart value) ∧
    remainingSteps (allocationStart value) = 0 ∧ finalCfg (allocationStart value) = allocationStart value ∧
    Runs (step allocatingExternal) (allocationStart value) 1 (allocationFinish value) ∧
    physicalCells (allocationStart value) = 37 ∧ physicalCells (allocationFinish value) = 38 ∧
    ¬ physicalCells (allocationFinish value) ≤ physicalCells (allocationStart value) ∧
    next allocatingExternal (some (allocationFinish value)) = none := by
  have before : physicalCells (allocationStart value) = 37 := by
    rw [allocationStart, actual_physical_cells_of_cfg]
    rfl
  have after : physicalCells (allocationFinish value) = 38 := by
    rw [allocationFinish, actual_physical_cells_of_cfg]
    rfl
  refine ⟨external_first_boundary_is_zero_identity allocatingExternal 42 clear_C00.before
    (stale value) ordinaryContext, rfl, rfl,
    the_literal_external_allocator_executes_its_real_push_without_resetting_the_registers value,
    before, after, ?_, rfl⟩
  rw [before, after]
  omega

theorem a_later_external_halt_does_not_satisfy_owned_first_halt
    (value : Bool) : ¬ FirstHalt (step allocatingExternal)
      (allocationStart value) 1 (allocationFinish value) := by
  intro alleged
  obtain ⟨reached, executed, owned⟩ := alleged.2.2 0 (by decide)
  have same := Option.some.inj executed
  subst reached
  exact not_owned_caller 42 owned

theorem the_three_concrete_external_bodies_are_irrelevant_from_every_owned_start
    (start : InfiniteLabelCfg) (owned : Owned start.l) (n : Nat) :
    (next allocatingExternal)^[n] (some start) = (next haltingExternal)^[n] (some start) ∧
    (next reenteringExternal)^[n] (some start) = (next haltingExternal)^[n] (some start) :=
  ⟨owned_iterate_caller_independent allocatingExternal haltingExternal start owned n,
    owned_iterate_caller_independent reenteringExternal haltingExternal start owned n⟩

/-! ## Actual physical paths after dirty FrontEnd handoff -/

section LiteralDirtyPhysicalPaths

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : Λ → Statement Γ Λ R)

omit caller [DecidableEq K] in
theorem a_stream_phase_view_reinserts_all_the_front_end_complement_words
    (q : StreamMachine.Phase) (D : LocalData) (E : StreamMachine.LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    streamCfg (Λ := Λ) (StreamMachine.cfg (some (StreamMachine.phaseLabel q))
      (StreamMachine.frontEndRegisterEquiv regs) E (streamContext D ctx)) =
    cfg (some (phaseLabel (streamPhase q))) regs (withStream D E) ctx := by
  simpa only [streamView, streamData_withStream, streamContext_withStream,
    Option.map_some, streamLabelEquiv_phase] using
      streamCfg_view (Λ := Λ) (some (StreamMachine.phaseLabel q)) regs (withStream D E) ctx

theorem a_literal_stream_prefix_is_an_actual_common_carrier_prefix
    (points : Nat → Examples.RotationCertificateStreamMachine.TracePoint)
    (ticks n : Nat) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (localCaller : StreamMachine.External (StreamCallerLabel Λ) → StreamStatement Γ Λ R)
    (initial : (points 0).reached (Λ := StreamCallerLabel Λ)
        (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx) =
      StreamMachine.cfg (some (StreamMachine.phaseLabel StreamMachine.inspectPhase))
        (StreamMachine.frontEndRegisterEquiv regs) (streamData D) (streamContext D ctx))
    (adjacent : ∀ j, j < ticks →
      StreamMachine.step localCaller ((points j).reached
        (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx)) =
      some ((points (j + 1)).reached
        (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx)))
    (owned : ∀ j, j < ticks → (points j).control.isLeft = true) (bound : n ≤ ticks) :
    LocalRun caller n
      (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase))) regs D ctx)
      (streamCfg ((points n).reached
        (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx))) := by
  have executed := Examples.RotationCertificateStreamMachine.finite_trace_actual_prefix
    localCaller (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx)
    points ticks adjacent n bound
  have earlier : ∀ j, j < n → ∃ reached,
      (StreamMachine.next localCaller)^[j]
        (some ((points 0).reached (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx))) =
      some reached ∧ StreamMachine.Owned reached.l := by
    intro j strict
    refine ⟨(points j).reached (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx),
      Examples.RotationCertificateStreamMachine.finite_trace_actual_prefix localCaller
        (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx)
        points ticks adjacent j (by omega), ?_⟩
    exact Examples.RotationCertificateStreamMachine.trace_point_with_phase_control_is_owned
      (points j) (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx) (owned j (by omega))
  have actual := stream_localRun caller localCaller
    (StreamMachine.LocalRun.of_iterate localCaller executed earlier)
  rw [initial, common_stream_start_is_the_complete_view] at actual
  exact actual

def dirty_D01_physical_path_data : LocalData :=
  withStream dirty_D01.stream.before (Examples.RotationCertificateStreamMachine.trace_r10 9).stores

def dirty_D02_physical_path_data : LocalData :=
  withStream dirty_D02.stream.before (StreamCertificates.trace_segment_d02 12).stores

def dirty_D02_consumed_failing_head_data : LocalData :=
  withStream dirty_D02.stream.before (StreamCertificates.trace_segment_d02 14).stores

theorem dirty_D01_actual_physical_path_is_reverse_old_reverse_followed_by_old_path
    (value : R) (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (dirty_D01.toClosedFixture.start value ctx) 209
      (cfg (some (phaseLabel (streamPhase (StreamMachine.applyPhase
        (MoveApplyMachine.positionPhase (.seek .left)))))) (clean value) dirty_D01_physical_path_data ctx) ∧
    dirty_D01_physical_path_data.path = [.right, .left] ∧
    dirty_D01_physical_path_data.moveReverse = [] ∧
    dirty_D01_physical_path_data.sourceTree = [1, 0, 1, 0, 0] := by
  let localCaller : StreamMachine.External (StreamCallerLabel Λ) → StreamStatement Γ Λ R := fun _ => .halt
  have source := a_literal_stream_prefix_is_an_actual_common_carrier_prefix caller
    Examples.RotationCertificateStreamMachine.trace_r10 20 9 dirty_D01.stream.before
    (clean value) ctx localCaller rfl
    (Examples.RotationCertificateStreamMachine.trace_r10_steps localCaller
      (StreamMachine.frontEndRegisterEquiv (clean value)) (streamContext dirty_D01.stream.before ctx))
    Examples.RotationCertificateStreamMachine.trace_r10_owned (by decide)
  have endpoint : streamCfg (Λ := Λ) ((Examples.RotationCertificateStreamMachine.trace_r10 9).reached
      (StreamMachine.frontEndRegisterEquiv (clean value)) (streamContext dirty_D01.stream.before ctx)) =
    cfg (some (phaseLabel (streamPhase (StreamMachine.applyPhase
      (MoveApplyMachine.positionPhase (.seek .left)))))) (clean value) dirty_D01_physical_path_data ctx :=
    a_stream_phase_view_reinserts_all_the_front_end_complement_words (Λ := Λ)
      (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.seek .left)))
      dirty_D01.stream.before (Examples.RotationCertificateStreamMachine.trace_r10 9).stores
      (clean value) ctx
  rw [endpoint] at source
  have first := dirty_D01_frontend_actual_local_run caller value ctx
  have joined := phase_step_localRun caller (dispatch_step caller dirty_D01.frontEndAfter
    (FrontEndMachine.reset (dirty_D01.fields.withUser value)) ctx)
  exact ⟨(LocalRun.trans caller (LocalRun.trans caller first joined) source).iterate caller, rfl, rfl, rfl⟩

theorem dirty_D02_actual_physical_path_keeps_both_old_branch_words_in_order
    (value : R) (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (dirty_D02.toClosedFixture.start value ctx) 270
      (cfg (some (phaseLabel (streamPhase (StreamMachine.applyPhase
        (MoveApplyMachine.positionPhase (.seek .left)))))) (clean value) dirty_D02_physical_path_data ctx) ∧
    dirty_D02_physical_path_data.path = [.left, .right, .right, .left, .right] ∧
    dirty_D02_physical_path_data.moveReverse = [] ∧
    dirty_D02_physical_path_data.sourceTree = [1, 0, 1, 0, 1, 0, 0] := by
  let localCaller : StreamMachine.External (StreamCallerLabel Λ) → StreamStatement Γ Λ R := fun _ => .halt
  have source := a_literal_stream_prefix_is_an_actual_common_carrier_prefix caller
    StreamCertificates.trace_segment_d02 18 12 dirty_D02.stream.before (clean value) ctx localCaller rfl
    (StreamCertificates.trace_segment_d02_steps localCaller
      (StreamMachine.frontEndRegisterEquiv (clean value)) (streamContext dirty_D02.stream.before ctx))
    StreamCertificates.trace_segment_d02_owned (by decide)
  have endpoint : streamCfg (Λ := Λ) ((StreamCertificates.trace_segment_d02 12).reached
      (StreamMachine.frontEndRegisterEquiv (clean value)) (streamContext dirty_D02.stream.before ctx)) =
    cfg (some (phaseLabel (streamPhase (StreamMachine.applyPhase
      (MoveApplyMachine.positionPhase (.seek .left)))))) (clean value) dirty_D02_physical_path_data ctx :=
    a_stream_phase_view_reinserts_all_the_front_end_complement_words (Λ := Λ)
      (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.seek .left)))
      dirty_D02.stream.before (StreamCertificates.trace_segment_d02 12).stores (clean value) ctx
  rw [endpoint] at source
  have first := dirty_D02_frontend_actual_local_run caller value ctx
  have joined := phase_step_localRun caller (dispatch_step caller dirty_D02.frontEndAfter
    (FrontEndMachine.reset (dirty_D02.fields.withUser value)) ctx)
  exact ⟨(LocalRun.trans caller (LocalRun.trans caller first joined) source).iterate caller, rfl, rfl, rfl⟩

theorem dirty_D02_actual_failure_has_already_consumed_the_failing_path_head
    (value : R) (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (dirty_D02.toClosedFixture.start value ctx) 272
      (cfg (some (phaseLabel (streamPhase (StreamMachine.applyPhase
        (MoveApplyMachine.positionPhase .dropPending))))) (clean value) dirty_D02_consumed_failing_head_data ctx) ∧
    dirty_D02_consumed_failing_head_data.path = [.right, .left, .right] ∧
    dirty_D02_consumed_failing_head_data.sourceTree = [0, 1, 0, 1, 0, 0] ∧
    dirty_D02_consumed_failing_head_data.treeReverse = [1] := by
  let localCaller : StreamMachine.External (StreamCallerLabel Λ) → StreamStatement Γ Λ R := fun _ => .halt
  have source := a_literal_stream_prefix_is_an_actual_common_carrier_prefix caller
    StreamCertificates.trace_segment_d02 18 14 dirty_D02.stream.before (clean value) ctx localCaller rfl
    (StreamCertificates.trace_segment_d02_steps localCaller
      (StreamMachine.frontEndRegisterEquiv (clean value)) (streamContext dirty_D02.stream.before ctx))
    StreamCertificates.trace_segment_d02_owned (by decide)
  have endpoint : streamCfg (Λ := Λ) ((StreamCertificates.trace_segment_d02 14).reached
      (StreamMachine.frontEndRegisterEquiv (clean value)) (streamContext dirty_D02.stream.before ctx)) =
    cfg (some (phaseLabel (streamPhase (StreamMachine.applyPhase
      (MoveApplyMachine.positionPhase .dropPending))))) (clean value) dirty_D02_consumed_failing_head_data ctx :=
    a_stream_phase_view_reinserts_all_the_front_end_complement_words (Λ := Λ)
      (StreamMachine.applyPhase (MoveApplyMachine.positionPhase .dropPending))
      dirty_D02.stream.before (StreamCertificates.trace_segment_d02 14).stores (clean value) ctx
  rw [endpoint] at source
  have first := dirty_D02_frontend_actual_local_run caller value ctx
  have joined := phase_step_localRun caller (dispatch_step caller dirty_D02.frontEndAfter
    (FrontEndMachine.reset (dirty_D02.fields.withUser value)) ctx)
  exact ⟨(LocalRun.trans caller (LocalRun.trans caller first joined) source).iterate caller, rfl, rfl, rfl⟩

end LiteralDirtyPhysicalPaths

/-! ## Every positive closed fixture has its fixed complete endpoint and attained peak -/

theorem all_81_positive_closed_cases_have_their_actual_first_halt_and_exact_peak
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
    (caller : Λ → Statement Γ Λ R) (value : R) (ctx : ∀ k, List (Γ k)) :
    ∀ fixture ∈ allClosedCases, fixture.Expected (step caller) value ctx := by
  intro fixture member
  simp only [allClosedCases, rawCases, partialClearCases, emitCases, joinCases, dirtyFrontEndCases,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have checked := raw_F01_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_F02_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_F03_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_F04_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_F05_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_F06_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_F07_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_F08_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_I01_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_I02_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_I03_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_I04_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_I05_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_I06_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_I07_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_C01_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_C02_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_C03_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_V01_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_V02_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_V03_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_V04_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_V05_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_V06_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_V07_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_V08_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_V09_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_V10_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_V11_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_V12_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_V13_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_V14_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_V15_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_V16_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_V17_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · have checked := raw_V18_expected caller (staleFields.withUser value) ctx
    exact ⟨checked.1, checked.2.2.2⟩
  · exact clear_C00_expected caller value ctx
  · exact clear_C00E_expected caller value ctx
  · exact clear_C01_expected caller value ctx
  · exact clear_C01E_expected caller value ctx
  · exact clear_C02_expected caller value ctx
  · exact clear_C02E_expected caller value ctx
  · exact clear_C03_expected caller value ctx
  · exact clear_C03E_expected caller value ctx
  · exact clear_C04_expected caller value ctx
  · exact clear_C04E_expected caller value ctx
  · exact clear_C05_expected caller value ctx
  · exact clear_C05E_expected caller value ctx
  · exact clear_C06_expected caller value ctx
  · exact clear_C06E_expected caller value ctx
  · exact clear_C07_expected caller value ctx
  · exact clear_C07E_expected caller value ctx
  · exact clear_C08_expected caller value ctx
  · exact clear_C08E_expected caller value ctx
  · exact clear_C09_expected caller value ctx
  · exact clear_C09E_expected caller value ctx
  · exact clear_C10_expected caller value ctx
  · exact clear_C10E_expected caller value ctx
  · exact clear_C11_expected caller value ctx
  · exact clear_C11E_expected caller value ctx
  · exact clear_C12_expected caller value ctx
  · exact clear_C12E_expected caller value ctx
  · exact clear_C13_expected caller value ctx
  · exact clear_C13E_expected caller value ctx
  · exact clear_C14_expected caller value ctx
  · exact clear_C14E_expected caller value ctx
  · exact clear_C15_expected caller value ctx
  · exact clear_C15E_expected caller value ctx
  · exact emit_E00_expected caller value ctx
  · exact emit_E01_expected caller value ctx
  · exact emit_E02_expected caller value ctx
  · exact emit_E03_expected caller value ctx
  · exact join_J00_expected caller value ctx
  · exact join_J01_expected caller value ctx
  · exact join_J02_expected caller value ctx
  · exact join_J03_expected caller value ctx
  · exact dirty_D00_expected caller value ctx
  · exact dirty_D01_expected caller value ctx
  · exact dirty_D02_expected caller value ctx
  · exact dirty_D03_expected caller value ctx
  · exact clear_CZERO_expected caller value ctx

theorem the_fixed_84_records_keep_81_positive_runs_separate_from_the_three_liveness_domains :
    allClosedCases.length = 81 ∧ livenessCases.length = 3 ∧
    allClosedCases.length + livenessCases.length = 84 := ⟨rfl, rfl, rfl⟩

/-! ## Dirty component contracts retain every old reverse, output, pending and fuel word -/

namespace DirtyComponentConnections

open Resources.RotationCertificate.FrontEndStreamMachine.DirtyFrontEnd

theorem every_one_of_the_five_tree_phases_has_its_actual_complete_dirty_endpoint
    {D K Λ R : Type} {Γ : K → Type} [DecidableEq D] [DecidableEq K]
    (caller : TreeParserMachine.External D Λ → TreeParserMachine.Statement D Γ Λ R)
    (destination : D) (phase : TreeParserMachine.Phase) (data : TreeState D)
    (regs : TreeParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    (TreeParserMachine.next caller)^[(treePhaseFinish destination phase data).steps]
      (some (treeCfg (some (TreeParserMachine.phaseLabel destination phase)) regs data ctx)) =
      some (treeCfg (some (TreeParserMachine.resultLabel destination
        (treePhaseFinish destination phase data).result)) (TreeParserMachine.reset regs)
        (treePhaseFinish destination phase data).data ctx) ∧
    0 < (treePhaseFinish destination phase data).steps ∧
    ∀ n, n < (treePhaseFinish destination phase data).steps → ∃ reached,
      (TreeParserMachine.next caller)^[n]
        (some (treeCfg (some (TreeParserMachine.phaseLabel destination phase)) regs data ctx)) =
      some reached ∧ TreeParserMachine.Owned reached.l :=
  ⟨treePhaseFinish_iterate caller destination phase data regs ctx,
    treePhaseFinish_steps_pos destination phase data,
    treePhaseFinish_owned_prefix caller destination phase data regs ctx⟩

theorem all_25_input_domains_have_the_actual_dirty_endpoint_and_strict_ownership
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : InputParserMachine.External Λ → InputParserMachine.Statement Γ Λ R)
    (phase : InputParserMachine.OwnedLabels) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    (InputParserMachine.next caller)^[(inputPhaseFinish phase data).steps]
      (some (inputCfg (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx)) =
      some (inputCfg (some (InputParserMachine.resultLabel (inputPhaseFinish phase data).result))
        (InputParserMachine.reset regs) (inputPhaseFinish phase data).data ctx) ∧
    ∀ n, n < (inputPhaseFinish phase data).steps → ∃ reached,
      (InputParserMachine.next caller)^[n]
        (some (inputCfg (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx)) =
      some reached ∧ InputParserMachine.FullOwned reached.l :=
  ⟨inputPhaseFinish_iterate caller phase data regs ctx,
    inputPhaseFinish_owned_prefix caller phase data regs ctx⟩

theorem an_actual_dirty_input_first_boundary_fixes_its_count_and_entire_configuration
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : InputParserMachine.External Λ → InputParserMachine.Statement Γ Λ R)
    (phase : InputParserMachine.OwnedLabels) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (reached : InputParserMachine.Cfg Γ Λ R)
    (executed : (InputParserMachine.next caller)^[n]
      (some (inputCfg (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx)) = some reached)
    (outside : ¬ InputParserMachine.FullOwned reached.l)
    (earlier : ∀ j, j < n → ∃ actual,
      (InputParserMachine.next caller)^[j]
        (some (inputCfg (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx)) = some actual ∧
      InputParserMachine.FullOwned actual.l) :
    n = (inputPhaseFinish phase data).steps ∧
      reached = inputCfg (some (InputParserMachine.resultLabel (inputPhaseFinish phase data).result))
        (InputParserMachine.reset regs) (inputPhaseFinish phase data).data ctx :=
  inputPhaseFinish_first_return_unique caller phase data regs ctx n reached executed outside earlier

section CompleteFrontEnd

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : FrontEndMachine.External Λ → FrontEndMachine.Statement Γ Λ R)

theorem all_36_front_end_domains_have_the_actual_complete_dirty_first_boundary
    (phase : FrontEndMachine.OwnedLabels) (data : FrontEndMachine.LocalData)
    (regs : FrontEndMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    (FrontEndMachine.next caller)^[frontEndPhaseSteps phase data]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)) =
      some (frontEndPhaseResult phase regs data ctx) ∧
    ¬ FrontEndMachine.Owned (frontEndPhaseResult (Λ := Λ) phase regs data ctx).l ∧
    0 < frontEndPhaseSteps phase data ∧
    ∀ n, n < frontEndPhaseSteps phase data → ∃ reached,
      (FrontEndMachine.next caller)^[n]
        (some (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)) =
      some reached ∧ FrontEndMachine.Owned reached.l :=
  ⟨frontEnd_phase_iterate caller phase data regs ctx,
    frontEndFinishCfg_not_owned (frontEndPhaseFinish phase data) regs ctx,
    frontEndPhaseSteps_pos phase data,
    frontEnd_phase_owned_prefix caller phase data regs ctx⟩

theorem the_front_end_canonical_boundary_is_exact_for_every_initial_configuration
    (start : FrontEndMachine.Cfg Γ Λ R) :
    (FrontEndMachine.next caller)^[frontEndRemainingSteps start] (some start) =
      some (frontEndFinalCfg start) ∧
    ¬ FrontEndMachine.Owned (frontEndFinalCfg start).l ∧
    ∀ n, n < frontEndRemainingSteps start → ∃ reached,
      (FrontEndMachine.next caller)^[n] (some start) = some reached ∧ FrontEndMachine.Owned reached.l :=
  ⟨frontEnd_cfg_iterate caller start, frontEndFinalCfg_not_owned start,
    (frontEnd_cfg_trace caller start).owned_prefix⟩

theorem the_front_end_first_boundary_converse_requires_actual_earlier_ownership
    (start reached : FrontEndMachine.Cfg Γ Λ R) (n : Nat)
    (executed : (FrontEndMachine.next caller)^[n] (some start) = some reached)
    (outside : ¬ FrontEndMachine.Owned reached.l)
    (earlier : ∀ j, j < n → ∃ actual,
      (FrontEndMachine.next caller)^[j] (some start) = some actual ∧ FrontEndMachine.Owned actual.l) :
    n = frontEndRemainingSteps start ∧ reached = frontEndFinalCfg start :=
  frontEnd_first_return_unique caller start reached n executed outside earlier

theorem an_actual_front_end_step_decreases_rank_and_preserves_the_entire_canonical_endpoint
    (before after : FrontEndMachine.Cfg Γ Λ R) (owned : FrontEndMachine.Owned before.l)
    (executed : FrontEndMachine.step caller before = some after) :
    frontEndRemainingSteps before = frontEndRemainingSteps after + 1 ∧
      frontEndFinalCfg before = frontEndFinalCfg after :=
  frontEnd_local_step_remaining caller owned executed

omit caller [DecidableEq K] in
theorem an_external_front_end_label_has_zero_rank_and_identity_boundary
    (start : FrontEndMachine.Cfg Γ Λ R) (outside : ¬ FrontEndMachine.Owned start.l) :
    frontEndRemainingSteps start = 0 ∧ frontEndFinalCfg start = start :=
  frontEnd_nonowned_identity start outside

theorem clean_front_end_entry_agrees_with_the_existing_public_runtime_and_endpoint
    (regs : FrontEndMachine.Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    frontEndRemainingSteps (FrontEndMachine.entry (Λ := Λ) regs raw ctx) = FrontEndMachine.runSteps raw ∧
    frontEndFinalCfg (FrontEndMachine.entry (Λ := Λ) regs raw ctx) =
      FrontEndMachine.resultCfg regs ctx (FrontEndMachine.sourceOutcome raw) :=
  frontEnd_clean_alignment (Λ := Λ) (fun _ => .halt) regs raw ctx

def frontEndPhaseExactTime (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (FrontEndMachine.step caller)
      (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)
      (some (frontEndPhaseResult phase regs data ctx)) (frontEndPhaseSteps phase data) :=
  frontEndPhaseInTime caller phase data regs ctx

def frontEndConfigurationExactTime (start : FrontEndMachine.Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (FrontEndMachine.step caller) start
      (some (frontEndFinalCfg start)) (frontEndRemainingSteps start) :=
  frontEndCfgInTime caller start

theorem front_end_type_valued_records_store_the_actual_exact_counts
    (phase : FrontEndMachine.OwnedLabels) (data : FrontEndMachine.LocalData)
    (regs : FrontEndMachine.Registers R) (ctx : ∀ k, List (Γ k))
    (start : FrontEndMachine.Cfg Γ Λ R) :
    (frontEndPhaseExactTime caller phase data regs ctx).steps = frontEndPhaseSteps phase data ∧
    (frontEndConfigurationExactTime caller start).steps = frontEndRemainingSteps start := ⟨rfl, rfl⟩

variable [Fintype K]

theorem an_actual_dirty_front_end_step_does_not_increase_its_full_physical_potential
    (before after : FrontEndMachine.Cfg Γ Λ R) (owned : FrontEndMachine.Owned before.l)
    (executed : FrontEndMachine.step caller before = some after) :
    frontEndPotential after ≤ frontEndPotential before :=
  frontEnd_local_step_potential caller owned executed

theorem one_front_end_prefix_witness_carries_rank_masks_frame_credit_and_the_final_endpoint
    (start : FrontEndMachine.Cfg Γ Λ R) (n : Nat) (bound : n ≤ frontEndRemainingSteps start) :
    ∃ reached, (FrontEndMachine.next caller)^[n] (some start) = some reached ∧
      frontEndRemainingSteps reached = frontEndRemainingSteps start - n ∧
      Relation.ReflTransGen (FrontEndLocalStep caller) start reached ∧
      (n < frontEndRemainingSteps start ↔ FrontEndMachine.Owned reached.l) ∧
      (n = 0 → reached = start) ∧
      reached.var = frontEndRegistersAt start n ∧
      reached.var.2.2 = start.var.2.2 ∧
      (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧
      frontEndPotential reached ≤ frontEndPotential start ∧
      FrontEndMachine.stackCells reached ≤ frontEndPotential start ∧
      frontEndFinalCfg reached = frontEndFinalCfg start ∧
      (n = frontEndRemainingSteps start → reached = frontEndFinalCfg start) :=
  frontEnd_owned_prefix caller start n bound

theorem a_dirty_front_end_phase_has_one_witness_for_its_literal_mask_schedule_and_space
    (phase : FrontEndMachine.OwnedLabels) (data : FrontEndMachine.LocalData)
    (regs : FrontEndMachine.Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ frontEndPhaseSteps phase data) :
    ∃ reached : FrontEndMachine.Cfg Γ Λ R,
      (FrontEndMachine.next caller)^[n]
        (some (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)) =
      some reached ∧ reached.var = frontEndPhaseRegisters phase data regs n ∧
      reached.var.2.2 = regs.2.2 ∧ (∀ k, reached.stk (.inr k) = ctx k) ∧
      FrontEndMachine.stackCells reached ≤ FrontEndMachine.localCells data +
        frontEndPhaseCredit phase data + FrontEndMachine.contextCells ctx ∧
      (n < frontEndPhaseSteps phase data ↔ FrontEndMachine.Owned reached.l) ∧
      (n = 0 → reached = FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx) ∧
      (n = frontEndPhaseSteps phase data → reached = frontEndPhaseResult phase regs data ctx) :=
  frontEnd_phase_shared_prefix caller phase data regs ctx n bound

end CompleteFrontEnd
end DirtyComponentConnections

/-! ## Actual finite-package outputs, exact stored counts and one prefix witness -/

section ActualPackageTiming

variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : Λ → Statement Γ Λ R) (initial : R)

def packageExactOutput (raw : Bits) :
    Turing.TM2OutputsInTime (machine caller initial) raw
      (some [BitPairFraming.verifyFramed raw]) (runSteps raw) :=
  initOutputsInTimeExact caller initial raw

def packagePolynomialOutput (raw : Bits) :
    Turing.TM2OutputsInTime (machine caller initial) raw
      (some [BitPairFraming.verifyFramed raw]) (raw.length * raw.length + 10 * raw.length + 36) :=
  initOutputsInTimePolynomial caller initial raw

def packageActualOutput (raw : Bits) :
    Turing.TM2Outputs (machine caller initial) raw (some [BitPairFraming.verifyFramed raw]) :=
  initOutputs caller initial raw

def packageOuterNoneTime (raw : Bits) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (Turing.initList (machine caller initial) raw) none (runSteps raw + 1) :=
  initNoneInTime caller initial raw

theorem package_output_records_keep_the_executed_count_separate_from_the_polynomial_bound
    (raw : Bits) :
    (packageExactOutput caller initial raw).steps = runSteps raw ∧
    (packagePolynomialOutput caller initial raw).steps = runSteps raw ∧
    (packageOuterNoneTime caller initial raw).steps = runSteps raw + 1 := ⟨rfl, rfl, rfl⟩

theorem a_genuine_package_first_halt_converse_fixes_both_time_and_literal_haltList
    (raw : Bits) (n : Nat) (finish : Cfg Γ Λ R) :
    FirstHalt (machine caller initial).step (Turing.initList (machine caller initial) raw) n finish ↔
      n = runSteps raw ∧
      finish = Turing.haltList (machine caller initial) [BitPairFraming.verifyFramed raw] :=
  init_first_halt_iff caller initial raw n finish

theorem the_genuine_package_has_a_live_output_at_its_exact_clock_and_outer_none_afterward
    (raw : Bits) :
    (fun state : Option (Cfg Γ Λ R) => state.bind (machine caller initial).step)^[runSteps raw]
      (some (Turing.initList (machine caller initial) raw)) =
      some (Turing.haltList (machine caller initial) [BitPairFraming.verifyFramed raw]) ∧
    ∀ n, runSteps raw < n →
      (fun state : Option (Cfg Γ Λ R) => state.bind (machine caller initial).step)^[n]
        (some (Turing.initList (machine caller initial) raw)) = none :=
  ⟨init_iterate caller initial raw, init_after_halt caller initial raw⟩

theorem one_genuine_package_prefix_witness_has_rank_reset_empty_context_halt_target_and_space
    (raw : Bits) (n : Nat) (bound : n ≤ runSteps raw) :
    ∃ reached,
      (fun state : Option (Cfg Γ Λ R) => state.bind (machine caller initial).step)^[n]
        (some (Turing.initList (machine caller initial) raw)) = some reached ∧
      remainingSteps reached = runSteps raw - n ∧
      Relation.ReflTransGen (LocalStep caller) (Turing.initList (machine caller initial) raw) reached ∧
      (n < runSteps raw ↔ Owned reached.l) ∧
      (n = 0 → reached = Turing.initList (machine caller initial) raw) ∧
      reached.var = registersAt (Turing.initList (machine caller initial) raw) n ∧
      user reached.var = initial ∧
      (∀ k, reached.stk (.inr (.inr k)) = []) ∧
      finalCfg reached = Turing.haltList (machine caller initial) [BitPairFraming.verifyFramed raw] ∧
      physicalCells reached ≤ max raw.length 1 ∧
      runSteps raw ≤ raw.length * raw.length + 10 * raw.length + 36 :=
  init_prefix caller initial raw n bound

theorem the_genuine_package_peak_is_both_an_upper_bound_and_attained
    (raw : Bits) :
    ExactPeak (machine caller initial).step (Turing.initList (machine caller initial) raw)
      (runSteps raw) (max raw.length 1) :=
  exact_peak_from_the_actual_public_prefix_contract caller (init_peak caller initial raw)

def arbitraryPackageConfigurationTime (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (machine caller initial).step start
      (some (finalCfg start)) (remainingSteps start) := machine_cfgInTime caller initial start

def arbitraryPackagePhaseTime (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (cfg (some (phaseLabel q)) regs D ctx) (some (phaseResult q regs D ctx)) (phaseSteps q D) :=
  machine_phaseInTime caller initial q D regs ctx

theorem arbitrary_package_time_records_do_not_assume_actual_initialization
    (start : Cfg Γ Λ R) (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (arbitraryPackageConfigurationTime caller initial start).steps = remainingSteps start ∧
    (arbitraryPackagePhaseTime caller initial q D regs ctx).steps = phaseSteps q D := ⟨rfl, rfl⟩

end ActualPackageTiming

/-! ## Owned-only installations retain the canonical shared witness and closed halt tail -/

section InstalledCanonicalTiming

variable {K Λ R K' Λ' R' : Type} {Γ : K → Type} {Γ' : K' → Type}
variable [DecidableEq K] [DecidableEq K']
variable (names : StackId K ≃ K') (symbols : ∀ k, alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')
variable (caller : Λ → Statement Γ Λ R) (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
variable (installed : ∀ label, Owned (some label) →
  ambient (labels label) =
    FrontEndMachine.Transport.statement names symbols registers labels (program caller label))

include installed in
theorem the_actual_installed_first_halt_iff_needs_only_owned_body_agreement
    (start : Cfg Γ Λ R) (owned : Owned start.l) (n : Nat) (finish : Turing.TM2.Cfg Γ' Λ' R') :
    ((FrontEndMachine.Transport.next ambient)^[n]
        (some (installedCfg names symbols registers labels start)) = some finish ∧
      finish.l = none ∧
      ∀ j, j < n → ∃ reached,
        (FrontEndMachine.Transport.next ambient)^[j]
          (some (installedCfg names symbols registers labels start)) = some reached ∧
        installedOwned labels reached.l) ↔
      n = remainingSteps start ∧ finish = installedCfg names symbols registers labels (finalCfg start) :=
  installed_first_halt_iff names symbols registers labels caller ambient installed start owned n finish

include installed in
theorem all_installed_owned_start_iterates_include_the_real_halt_tail
    (start : Cfg Γ Λ R) (owned : Owned start.l) (n : Nat) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) =
      ((next caller)^[n] (some start)).map (installedCfg names symbols registers labels) :=
  installed_iterate_owned_start names symbols registers labels caller ambient installed start owned n

include installed in
theorem one_installed_prefix_witness_has_source_and_ambient_execution_and_the_complete_frame
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, Runs (step caller) start n reached ∧
      (FrontEndMachine.Transport.next ambient)^[n]
        (some (installedCfg names symbols registers labels start)) =
        some (installedCfg names symbols registers labels reached) ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ installedOwned labels (installedCfg names symbols registers labels reached).l) ∧
      (n = 0 → reached = start) ∧
      (installedCfg names symbols registers labels reached).var = registers (registersAt start n) ∧
      user reached.var = user start.var ∧
      (∀ k, (installedCfg names symbols registers labels reached).stk (names (.inr (.inr k))) =
        (start.stk (.inr (.inr k))).map (symbols (.inr (.inr k)))) ∧
      finalCfg reached = finalCfg start :=
  installed_owned_prefix_frame names symbols registers labels caller ambient installed start n bound

include installed in
def installedConfigurationExactTime (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels start)
      (some (installedCfg names symbols registers labels (finalCfg start))) (remainingSteps start) :=
  installed_ownedInTime names symbols registers labels caller ambient installed start

include installed in
def installedPhaseExactTime (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels (cfg (some (phaseLabel q)) regs D ctx))
      (some (installedCfg names symbols registers labels (phaseResult q regs D ctx))) (phaseSteps q D) :=
  installed_phaseInTime names symbols registers labels caller ambient installed q D regs ctx

include installed in
def installedOuterNoneExactTime (start : Cfg Γ Λ R) (halted : (finalCfg start).l = none) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels start) none (remainingSteps start + 1) :=
  installed_haltNoneInTime names symbols registers labels caller ambient installed start halted

theorem installed_type_valued_records_retain_the_exact_source_counts
    (start : Cfg Γ Λ R) (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (halted : (finalCfg start).l = none) :
    (installedConfigurationExactTime names symbols registers labels caller ambient installed start).steps =
      remainingSteps start ∧
    (installedPhaseExactTime names symbols registers labels caller ambient installed q D regs ctx).steps =
      phaseSteps q D ∧
    (installedOuterNoneExactTime names symbols registers labels caller ambient installed start halted).steps =
      remainingSteps start + 1 := ⟨rfl, rfl, rfl⟩

variable [Fintype K] [Fintype K']

include installed in
theorem the_same_installed_prefix_witness_carries_the_actual_full_physical_bound
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, Runs (step caller) start n reached ∧
      (FrontEndMachine.Transport.next ambient)^[n]
        (some (installedCfg names symbols registers labels start)) =
        some (installedCfg names symbols registers labels reached) ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ installedOwned labels (installedCfg names symbols registers labels reached).l) ∧
      (n = 0 → reached = start) ∧
      (installedCfg names symbols registers labels reached).var = registers (registersAt start n) ∧
      user reached.var = user start.var ∧
      (∀ k, (installedCfg names symbols registers labels reached).stk (names (.inr (.inr k))) =
        (start.stk (.inr (.inr k))).map (symbols (.inr (.inr k)))) ∧
      finalCfg reached = finalCfg start ∧
      (∑ k, ((installedCfg names symbols registers labels reached).stk k).length) ≤ allowance start :=
  installed_owned_prefix_space names symbols registers labels caller ambient installed start n bound

end InstalledCanonicalTiming

/-! ## Exact class clocks, endpoints, staged registers and structural allowances -/

theorem all_seven_owned_class_clock_formulas_use_the_actual_component_endpoint
    (f : FrontEndMachine.OwnedLabels) (s : StreamMachine.Phase) (i : Fin 16)
    (bit : Bool) (D : LocalData) :
    phaseSteps (frontEndPhase f) D =
      (DirtyFrontEnd.frontEndPhaseFinish f (frontEndData D)).steps +
      (match (DirtyFrontEnd.frontEndPhaseFinish f (frontEndData D)).result with
        | .success => (dispatchEvaluation (frontEndFinishData f D)).steps
        | .failure => (answerEvaluation false (frontEndFinishData f D)).steps) ∧
    phaseSteps rejectPhase D = localCells D + 18 ∧
    phaseSteps dispatchPhase D =
      StreamMachine.phaseSteps StreamMachine.inspectPhase (streamData D) +
      localCells (withStream D (StreamMachine.evaluate StreamMachine.inspectPhase (streamData D)).data) + 19 ∧
    phaseSteps (streamPhase s) D = StreamMachine.phaseSteps s (streamData D) +
      localCells (withStream D (StreamMachine.evaluate s (streamData D)).data) + 18 ∧
    phaseSteps (resultPhase bit) D = localCells D + 18 ∧
    phaseSteps (clearPhase i) D = suffixCells i D + (16 - i.val) + 1 ∧
    phaseSteps emitPhase D = 1 :=
  ⟨phaseSteps_frontEnd f D, phaseSteps_reject D, phaseSteps_dispatch D,
    phaseSteps_stream s D, phaseSteps_result bit D, phaseSteps_clear i D, phaseSteps_emit D⟩

theorem all_seven_owned_class_endpoints_keep_the_direct_cleaner_answer_and_dirty_emit_fuel
    {K Λ R : Type} {Γ : K → Type}
    (f : FrontEndMachine.OwnedLabels) (s : StreamMachine.Phase) (i : Fin 16)
    (bit : Bool) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    phaseResult (Λ := Λ) (frontEndPhase f) regs D ctx =
      cfg none (fullReset regs) (frontEndEvaluation f D).data ctx ∧
    phaseResult (Λ := Λ) rejectPhase regs D ctx = cfg none (fullReset regs) { fuel := [false] } ctx ∧
    phaseResult (Λ := Λ) dispatchPhase regs D ctx = cfg none (fullReset regs)
      { fuel := [(StreamMachine.evaluate StreamMachine.inspectPhase (streamData D)).result] } ctx ∧
    phaseResult (Λ := Λ) (streamPhase s) regs D ctx = cfg none (fullReset regs)
      { fuel := [(StreamMachine.evaluate s (streamData D)).result] } ctx ∧
    phaseResult (Λ := Λ) (resultPhase bit) regs D ctx = cfg none (fullReset regs) { fuel := [bit] } ctx ∧
    phaseResult (Λ := Λ) (clearPhase i) regs D ctx =
      cfg none (fullReset regs) (cleanupData i (answer regs) D) ctx ∧
    phaseResult (Λ := Λ) emitPhase regs D ctx =
      cfg none (fullReset regs) { D with fuel := answer regs :: D.fuel } ctx :=
  ⟨phaseResult_frontEnd f regs D ctx, phaseResult_reject regs D ctx,
    phaseResult_dispatch regs D ctx, phaseResult_stream s regs D ctx,
    phaseResult_result bit regs D ctx, phaseResult_clear i regs D ctx, phaseResult_emit regs D ctx⟩

section ActualStagedFields

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : Λ → Statement Γ Λ R)

theorem an_actual_front_end_prefix_uses_its_component_masks_before_the_paid_join
    (q : FrontEndMachine.OwnedLabels) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ DirtyFrontEnd.frontEndPhaseSteps q (frontEndData D))
    (reached : Cfg Γ Λ R)
    (executed : Runs (step caller) (cfg (some (phaseLabel (frontEndPhase q))) regs D ctx) n reached) :
    reached.var = DirtyFrontEnd.frontEndPhaseRegisters q (frontEndData D) regs n ∧
    user reached.var = user regs ∧ ∀ k, reached.stk (.inr (.inr k)) = ctx k :=
  frontEnd_component_prefix_state caller q D regs ctx n bound reached executed

theorem an_actual_stream_prefix_keeps_the_complete_decoder_complement_and_staged_masks
    (q : StreamMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ StreamMachine.phaseSteps q (streamData D))
    (reached : Cfg Γ Λ R)
    (executed : Runs (step caller) (cfg (some (phaseLabel (streamPhase q))) regs D ctx) n reached) :
    reached.var = StreamMachine.frontEndRegisterEquiv.symm
      (StreamMachine.phaseRegistersAt (Λ := StreamCallerLabel Λ) q
        (StreamMachine.frontEndRegisterEquiv regs) (streamData D) (streamContext D ctx) n) ∧
    user reached.var = user regs ∧ ∀ k, reached.stk (.inr (.inr k)) = ctx k :=
  stream_component_prefix_state caller q D regs ctx n bound reached executed

theorem every_actual_indexed_clear_prefix_has_the_original_zero_fields_and_exact_positive_occupancy
    (i j : Fin 16) (t : Nat) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (ordered : i.val ≤ j.val) (within : t ≤ slotLength j D) :
    Runs (step caller) (cfg (some (clearLabel i)) regs D ctx) (boundarySteps i j D + t)
      (cleanupPrefixCfg i j t regs D ctx) ∧
    (cleanupPrefixCfg (Λ := Λ) i j t regs D ctx).var =
      (if t = 0 then (if i = j then regs else occupancyRegisters false regs)
       else occupancyRegisters true regs) :=
  ⟨cleanup_prefix_iterate caller i j t D regs ctx ordered within,
    cleanupPrefixCfg_registers i j t regs D ctx⟩

theorem every_actual_pre_emit_prefix_has_a_unique_slot_and_consumed_length
    (i : Fin 16) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (beforeEmit : n < cleanupSteps i D - 1) :
    ∃ j : Fin 16, i.val ≤ j.val ∧ ∃ t, t ≤ slotLength j D ∧
      n = boundarySteps i j D + t ∧
      Runs (step caller) (cfg (some (clearLabel i)) regs D ctx) n (cleanupPrefixCfg i j t regs D ctx) ∧
      ∀ k u, i.val ≤ k.val → u ≤ slotLength k D →
        n = boundarySteps i k D + u → k = j ∧ u = t :=
  clear_prefix caller i D regs ctx n beforeEmit

theorem the_last_empty_pop_reaches_emit_before_the_separate_answer_push
    (i : Fin 16) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (cfg (some (clearLabel i)) regs D ctx) (cleanupSteps i D - 1)
      (cfg (some emitLabel) (occupancyRegisters false regs) (clearSuffix i D) ctx) ∧
    Runs (step caller) (cfg (some (clearLabel i)) regs D ctx) (cleanupSteps i D)
      (cfg none (fullReset regs) (cleanupData i (answer regs) D) ctx) :=
  ⟨cleanup_emit_iterate caller i D regs ctx, (cleanup_localRun caller i D regs ctx).iterate caller⟩

def expectedCleanerFields (i : Fin 16) (regs : Registers R) (D : LocalData) (n : Nat) : Registers R :=
  if n = 0 then regs else
  if n = cleanupSteps i D - 1 then (regs.1, { regs.2.1 with b1 := some false }, regs.2.2) else
  if cleanupSteps i D ≤ n then fullReset regs else
  if ∃ j : Fin 16, i.val ≤ j.val ∧ n = boundarySteps i j D
  then (regs.1, { regs.2.1 with b1 := some false }, regs.2.2)
  else (regs.1, { regs.2.1 with b1 := some true }, regs.2.2)

theorem every_actual_clear_prefix_preserves_all_fields_except_the_recorded_occupancy_until_emit
    (i : Fin 16) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ cleanupSteps i D) (reached : Cfg Γ Λ R)
    (executed : Runs (step caller) (cfg (some (clearLabel i)) regs D ctx) n reached) :
    reached.var = expectedCleanerFields i regs D n ∧ user reached.var = user regs ∧
    ∀ k, reached.stk (.inr (.inr k)) = ctx k :=
  cleanup_prefix_registers caller i D regs ctx n bound reached executed

def frontEndSegmentTime (q : FrontEndMachine.OwnedLabels) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (frontEndPhase q))) regs D ctx)
      (some (frontEndComponentCfg q D regs ctx)) (DirtyFrontEnd.frontEndPhaseSteps q (frontEndData D)) :=
  frontEndInTime caller q D regs ctx

def streamSegmentTime (q : StreamMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (streamPhase q))) regs D ctx)
      (some (cfg (some (phaseLabel (resultPhase (StreamMachine.evaluate q (streamData D)).result)))
        (streamReset regs) (withStream D (StreamMachine.evaluate q (streamData D)).data) ctx))
      (StreamMachine.phaseSteps q (streamData D)) := streamInTime caller q D regs ctx

theorem component_time_records_stop_at_the_owned_join_before_the_whole_phase_halt
    (f : FrontEndMachine.OwnedLabels) (s : StreamMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (frontEndSegmentTime caller f D regs ctx).steps = DirtyFrontEnd.frontEndPhaseSteps f (frontEndData D) ∧
    (streamSegmentTime caller s D regs ctx).steps = StreamMachine.phaseSteps s (streamData D) ∧
    (phaseExactTime caller (frontEndPhase f) D regs ctx).steps = phaseSteps (frontEndPhase f) D ∧
    (phaseExactTime caller (streamPhase s) D regs ctx).steps = phaseSteps (streamPhase s) D :=
  ⟨rfl, rfl, rfl, rfl⟩

end ActualStagedFields

section StructuralAllowanceEquations

variable {K : Type} {Γ : K → Type} [Fintype K]

def expectedFrontEndAllowance (q : FrontEndMachine.OwnedLabels) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : Nat :=
  let finish := DirtyFrontEnd.frontEndPhaseFinish q (frontEndData D)
  let out := withFrontEnd D finish.data
  max (localCells D + DirtyFrontEnd.frontEndPhaseCredit q (frontEndData D) + externalCells ctx)
    (match finish.result with
      | .success => max (StreamMachine.inspectAllowance (streamData out) (streamContext out ctx))
          (1 + externalCells ctx)
      | .failure => max (localCells out) 1 + externalCells ctx)

theorem the_front_end_allowance_uses_the_actual_dirty_endpoint_and_counts_its_protected_words_once
    (q : FrontEndMachine.OwnedLabels) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    phaseAllowance (frontEndPhase q) D ctx = expectedFrontEndAllowance q D ctx := by
  change (match frontEndClass (frontEndControl (.inl q)) with
    | .inl q => frontEndAllowance q D ctx
    | .inr false => max (localCells D) 1 + contextCells ctx
    | .inr true => max (StreamMachine.inspectAllowance (streamData D) (streamContext D ctx))
        (1 + contextCells ctx)) = _
  rw [frontEndClass_control]
  rfl

theorem all_other_owned_allowances_retain_the_emit_push_and_exact_cleaner_prefix_mass
    (q : StreamMachine.Phase) (i : Fin 16) (bit : Bool) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    phaseAllowance rejectPhase D ctx = max (localCells D) 1 + externalCells ctx ∧
    phaseAllowance dispatchPhase D ctx =
      max (StreamMachine.inspectAllowance (streamData D) (streamContext D ctx)) (1 + externalCells ctx) ∧
    phaseAllowance (streamPhase q) D ctx =
      max (StreamMachine.phaseAllowance q (streamData D) (streamContext D ctx)) (1 + externalCells ctx) ∧
    phaseAllowance (resultPhase bit) D ctx = max (localCells D) 1 + externalCells ctx ∧
    phaseAllowance (clearPhase i) D ctx = max (localCells D) (prefixCells i D + 1) + externalCells ctx ∧
    phaseAllowance emitPhase D ctx = localCells D + 1 + externalCells ctx := by
  refine ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩
  · change (match streamClass (streamControl (.inl q)) with
      | .inl q => max (StreamMachine.phaseAllowance q (streamData D) (streamContext D ctx))
          (1 + contextCells ctx)
      | .inr _ => max (localCells D) 1 + contextCells ctx) = _
    rw [streamClass_control]
    rfl
  · cases bit <;> rfl

end StructuralAllowanceEquations

/-! ## Full component configuration inverses and the external reentry boundary -/

section CompleteComponentViews

variable {K Λ R : Type} {Γ : K → Type}

def frontEndReadback (c : Cfg Γ Λ R) : FrontEndCfg Γ Λ R :=
  frontEndView (c.l.map frontEndLabelEquiv.symm) c.var (dataOfCfg c) (contextOfCfg c)

def streamReadback (c : Cfg Γ Λ R) : StreamCfg Γ Λ R :=
  streamView (c.l.map streamLabelEquiv.symm) c.var (dataOfCfg c) (contextOfCfg c)

theorem front_end_readback_restores_every_arbitrary_common_configuration
    (c : Cfg Γ Λ R) : frontEndCfg (frontEndReadback c) = c := by
  rw [frontEndReadback, frontEndCfg_view]
  have labels : (c.l.map frontEndLabelEquiv.symm).map frontEndLabelEquiv = c.l := by
    cases c.l <;> simp
  rw [labels, cfg_eta]

theorem stream_readback_restores_every_arbitrary_common_configuration
    (c : Cfg Γ Λ R) : streamCfg (streamReadback c) = c := by
  rw [streamReadback, streamCfg_view]
  have labels : (c.l.map streamLabelEquiv.symm).map streamLabelEquiv = c.l := by
    cases c.l <;> simp
  rw [labels, cfg_eta]

theorem both_complete_component_views_have_actual_two_sided_configuration_inverses
    (f : FrontEndCfg Γ Λ R) (s : StreamCfg Γ Λ R) (c : Cfg Γ Λ R) :
    frontEndCfg (frontEndReadback c) = c ∧ frontEndReadback (frontEndCfg f) = f ∧
    streamCfg (streamReadback c) = c ∧ streamReadback (streamCfg s) = s := by
  refine ⟨front_end_readback_restores_every_arbitrary_common_configuration c, ?_,
    stream_readback_restores_every_arbitrary_common_configuration c, ?_⟩
  · apply FrontEndMachine.Transport.cfg_injective (Equiv.refl _) (fun _ => Equiv.refl _)
      (Equiv.refl _) frontEndLabelEquiv frontEndLabelEquiv.injective
    exact front_end_readback_restores_every_arbitrary_common_configuration (frontEndCfg f)
  · apply FrontEndMachine.Transport.cfg_injective streamStackEquiv streamSymbolEquiv
      streamRegisterEquiv streamLabelEquiv streamLabelEquiv.injective
    exact stream_readback_restores_every_arbitrary_common_configuration (streamCfg s)

theorem sixteen_local_slots_and_original_external_stores_exhaust_the_physical_carrier
    (k : StackId K) : (∃ i : Fin 16, slot i = k) ∨ ∃ external, k = .inr (.inr external) :=
  slot_complete k

theorem each_literal_local_slot_has_its_unique_physical_index
    (i j : Fin 16) : slot (K := K) i = slot j ↔ i = j :=
  ⟨fun same => slot_injective (K := K) same,
    fun same => congrArg (slot (K := K)) same⟩

theorem every_symbol_equivalence_has_a_complete_inverse
    (k : StreamMachine.StackId (StreamMachine.FrontEndProtected ⊕ K))
    (symbol : StreamMachine.alphabet (StreamMachine.frontEndProtectedAlphabet Γ) k) :
    (streamSymbolEquiv k).symm (streamSymbolEquiv k symbol) = symbol :=
  (streamSymbolEquiv k).symm_apply_apply symbol

theorem both_component_maps_preserve_the_complete_physical_sum
    [Fintype K] (f : FrontEndCfg Γ Λ R) (s : StreamCfg Γ Λ R) :
    physicalCells (frontEndCfg f) = FrontEndMachine.stackCells f ∧
    physicalCells (streamCfg s) = StreamMachine.stackCells s :=
  ⟨stackCells_frontEndCfg f, stackCells_streamCfg s⟩

theorem the_component_label_complements_count_every_other_owned_domain
    [Fintype Λ] :
    Fintype.card (FrontEndCallerLabel Λ) = 58 + Fintype.card Λ ∧
    Fintype.card (StreamCallerLabel Λ) = 55 + Fintype.card Λ := by
  have f : Fintype.card (FrontEndMachine.Label Empty) = 38 := by
    simpa only [Fintype.card_empty, Nat.add_zero] using FrontEndMachine.label_card (Λ := Empty)
  have s : Fintype.card (StreamMachine.Label Empty) = 41 := by
    simpa only [Fintype.card_empty, Nat.add_zero] using StreamMachine.card_label (Λ := Empty)
  constructor
  · simp only [FrontEndCallerLabel, Fintype.card_sum, s, card_cleanupPhase]
    omega
  · simp only [StreamCallerLabel, Fintype.card_sum, f, card_cleanupPhase]
    omega

end CompleteComponentViews

section ExternalReentryScope

variable {K R : Type} {Γ : K → Type} [DecidableEq K]

def genericReenteringCaller : Nat → Statement Γ Nat R := fun _ => .goto (fun _ => clearLabel 0)

theorem an_external_reentry_executes_the_caller_before_any_owned_cleanup_step
    (label : Nat) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step genericReenteringCaller (cfg (some (callerLabel label)) regs D ctx) =
      some (cfg (some (clearLabel 0)) regs D ctx) := rfl

theorem an_external_reentry_can_later_halt_but_is_not_an_owned_first_halt
    (label : Nat) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstBoundary (step genericReenteringCaller)
      (cfg (some (callerLabel label)) regs D ctx) 0
      (cfg (some (callerLabel label)) regs D ctx) ∧
    Runs (step genericReenteringCaller) (cfg (some (callerLabel label)) regs D ctx)
      (1 + cleanupSteps 0 D) (cfg none (fullReset regs) (cleanupData 0 (answer regs) D) ctx) ∧
    ¬ FirstHalt (step genericReenteringCaller) (cfg (some (callerLabel label)) regs D ctx)
      (1 + cleanupSteps 0 D) (cfg none (fullReset regs) (cleanupData 0 (answer regs) D) ctx) := by
  refine ⟨external_first_boundary_is_zero_identity genericReenteringCaller label D regs ctx, ?_, ?_⟩
  · change (next genericReenteringCaller)^[1 + cleanupSteps 0 D]
      (some (cfg (some (callerLabel label)) regs D ctx)) = _
    rw [Nat.add_comm 1 _, Function.iterate_succ_apply, next_some,
      an_external_reentry_executes_the_caller_before_any_owned_cleanup_step]
    exact (cleanup_localRun genericReenteringCaller 0 D regs ctx).iterate genericReenteringCaller
  · intro alleged
    obtain ⟨reached, executed, owned⟩ := alleged.2.2 0 (by omega)
    have same := Option.some.inj executed
    subst reached
    exact not_owned_caller label owned

end ExternalReentryScope

/-! ## Component boundaries stay owned until their paid controller joins -/

section ComponentBoundaryDomains

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : Λ → Statement Γ Λ R)

theorem all_36_front_end_domains_reach_their_complete_owned_join_before_the_global_halt
    (q : FrontEndMachine.OwnedLabels) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (cfg (some (phaseLabel (frontEndPhase q))) regs D ctx)
      (DirtyFrontEnd.frontEndPhaseSteps q (frontEndData D)) (frontEndComponentCfg q D regs ctx) ∧
    Owned (frontEndComponentCfg (Λ := Λ) q D regs ctx).l ∧
    (∀ n, n < DirtyFrontEnd.frontEndPhaseSteps q (frontEndData D) →
      ∃ reached, Runs (step caller) (cfg (some (phaseLabel (frontEndPhase q))) regs D ctx)
        n reached ∧ Owned reached.l) ∧
    FirstHalt (step caller) (cfg (some (phaseLabel (frontEndPhase q))) regs D ctx)
      (phaseSteps (frontEndPhase q) D) (phaseResult (frontEndPhase q) regs D ctx) := by
  have component := frontEnd_phase_localRun caller q D regs ctx
  refine ⟨component.iterate caller, ?_, component.owned_prefix caller,
    phase_first_halt caller (frontEndPhase q) D regs ctx⟩
  exact owned_phase _

theorem all_39_stream_domains_reach_their_complete_owned_boolean_join_before_the_global_halt
    (q : StreamMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    Runs (step caller) (cfg (some (phaseLabel (streamPhase q))) regs D ctx)
      (StreamMachine.phaseSteps q (streamData D))
      (cfg (some (phaseLabel (resultPhase (StreamMachine.evaluate q (streamData D)).result)))
        (streamReset regs) (withStream D (StreamMachine.evaluate q (streamData D)).data) ctx) ∧
    Owned (some (phaseLabel (Λ := Λ) (resultPhase (StreamMachine.evaluate q (streamData D)).result))) ∧
    (∀ n, n < StreamMachine.phaseSteps q (streamData D) →
      ∃ reached, Runs (step caller) (cfg (some (phaseLabel (streamPhase q))) regs D ctx)
        n reached ∧ Owned reached.l) ∧
    FirstHalt (step caller) (cfg (some (phaseLabel (streamPhase q))) regs D ctx)
      (phaseSteps (streamPhase q) D) (phaseResult (streamPhase q) regs D ctx) := by
  have component := stream_phase_localRun caller q D regs ctx
  exact ⟨component.iterate caller, owned_phase _, component.owned_prefix caller,
    phase_first_halt caller (streamPhase q) D regs ctx⟩

theorem neither_component_result_is_already_a_global_first_boundary
    (f : FrontEndMachine.OwnedLabels) (s : StreamMachine.Phase)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ¬ FirstBoundary (step caller) (cfg (some (phaseLabel (frontEndPhase f))) regs D ctx)
        (DirtyFrontEnd.frontEndPhaseSteps f (frontEndData D)) (frontEndComponentCfg f D regs ctx) ∧
    ¬ FirstBoundary (step caller) (cfg (some (phaseLabel (streamPhase s))) regs D ctx)
        (StreamMachine.phaseSteps s (streamData D))
        (cfg (some (phaseLabel (resultPhase (StreamMachine.evaluate s (streamData D)).result)))
          (streamReset regs) (withStream D (StreamMachine.evaluate s (streamData D)).data) ctx) := by
  constructor
  · intro alleged
    exact alleged.2.1 (owned_phase _)
  · intro alleged
    exact alleged.2.1 (owned_phase _)

end ComponentBoundaryDomains

theorem the_81_fixed_closed_runs_retain_the_five_cell_context_and_stale_fields
    (caller : ExampleCaller) (value : Bool) :
    ∀ fixture ∈ allClosedCases,
      FirstHalt (step caller) (fixture.start value ordinaryContext) fixture.ticks
        (fixture.finish value ordinaryContext) ∧
      ExactPeak (step caller) (fixture.start value ordinaryContext) fixture.ticks (fixture.peak + 5) := by
  intro fixture member
  have connected := all_81_positive_closed_cases_have_their_actual_first_halt_and_exact_peak
    caller value ordinaryContext fixture member
  simpa only [ClosedFixture.Expected, ClosedFixture.RunExpected, ordinary_context_has_five_cells] using connected

end Examples.RotationCertificateFrontEndStreamMachine
