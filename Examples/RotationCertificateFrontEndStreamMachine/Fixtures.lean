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
def emptyRawFixture : RawFixture where
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

def truncatedPrefixFixture : RawFixture where
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
  [emptyRawFixture, truncatedPrefixFixture, raw_F03, raw_F04, raw_F05, raw_F06, raw_F07, raw_F08, raw_I01, raw_I02, raw_I03, raw_I04, raw_I05, raw_I06, raw_I07, raw_C01, raw_C02, raw_C03, raw_V01, raw_V02, raw_V03, raw_V04, raw_V05, raw_V06, raw_V07, raw_V08, raw_V09, raw_V10, raw_V11, raw_V12, raw_V13, raw_V14, raw_V15, raw_V16, raw_V17, raw_V18]

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


end Examples.RotationCertificateFrontEndStreamMachine
