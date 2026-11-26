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

def rawF03 : RawFixture where
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

def rawF04 : RawFixture where
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

def rawF05 : RawFixture where
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

def rawF06 : RawFixture where
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

def rawF07 : RawFixture where
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

def rawF08 : RawFixture where
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

def rawI01 : RawFixture where
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

def rawI02 : RawFixture where
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

def rawI03 : RawFixture where
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

def rawI04 : RawFixture where
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

def rawI05 : RawFixture where
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

def rawI06 : RawFixture where
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

def rawI07 : RawFixture where
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

def rawC01 : RawFixture where
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

def rawC02 : RawFixture where
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

def rawC03 : RawFixture where
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

def rawV01 : RawFixture where
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

def rawV02 : RawFixture where
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

def rawV03 : RawFixture where
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

def rawV04 : RawFixture where
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

def rawV05 : RawFixture where
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

def rawV06 : RawFixture where
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

def rawV07 : RawFixture where
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

def rawV08 : RawFixture where
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

def rawV09 : RawFixture where
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

def rawV10 : RawFixture where
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

def rawV11 : RawFixture where
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

def rawV12 : RawFixture where
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

def rawV13 : RawFixture where
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

def rawV14 : RawFixture where
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

def rawV15 : RawFixture where
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

def rawV16 : RawFixture where
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

def rawV17 : RawFixture where
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

def rawV18 : RawFixture where
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
  [emptyRawFixture, truncatedPrefixFixture, rawF03, rawF04, rawF05, rawF06, rawF07, rawF08, rawI01, rawI02, rawI03, rawI04, rawI05, rawI06, rawI07, rawC01, rawC02, rawC03, rawV01, rawV02, rawV03, rawV04, rawV05, rawV06, rawV07, rawV08, rawV09, rawV10, rawV11, rawV12, rawV13, rawV14, rawV15, rawV16, rawV17, rawV18]

theorem raw_cases_count : rawCases.length = 36 := rfl

/-! ## Literal partial cleaners, emitters, joins and dirty FrontEnd starts -/

def dirtyData : LocalData :=
  localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]

def cleanupC00 : CleanupFixture where
  name := "additional/C00"
  phase := clearPhase 0
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 49
  peak := 32
  index := 0

def cleanupC00Boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 0), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 2, phase := some (clearPhase 0), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 3, phase := some (clearPhase 1), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 48, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [], cells := 0 },
   { ticks := 49, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [true], cells := 1 }]

def cleanupC00E : CleanupFixture where
  name := "additional/C00E"
  phase := clearPhase 0
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 47
  peak := 30
  index := 0

def cleanupC00EBoundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 0), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 1, phase := some (clearPhase 1), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 46, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [], cells := 0 },
   { ticks := 47, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false], cells := 1 }]

def cleanupC01 : CleanupFixture where
  name := "additional/C01"
  phase := clearPhase 1
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 46
  peak := 32
  index := 1

def cleanupC01Boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 1), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 1, phase := some (clearPhase 1), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 2, phase := some (clearPhase 2), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 45, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [], cells := 2 },
   { ticks := 46, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [true], cells := 3 }]

def cleanupC01E : CleanupFixture where
  name := "additional/C01E"
  phase := clearPhase 1
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 45
  peak := 31
  index := 1

def cleanupC01EBoundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 1), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 1, phase := some (clearPhase 2), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 44, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [], cells := 2 },
   { ticks := 45, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false], cells := 3 }]

def cleanupC02 : CleanupFixture where
  name := "additional/C02"
  phase := clearPhase 2
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [] [] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 44
  peak := 32
  index := 2

def cleanupC02Boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 2), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 2, phase := some (clearPhase 2), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 3, phase := some (clearPhase 3), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 43, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [] [] [] [] [] [] [] [] [] [] [] [] [] [], cells := 3 },
   { ticks := 44, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [] [] [] [] [] [] [] [] [] [] [] [] [] [true], cells := 4 }]

def cleanupC02E : CleanupFixture where
  name := "additional/C02E"
  phase := clearPhase 2
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 42
  peak := 30
  index := 2

def cleanupC02EBoundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 2), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 1, phase := some (clearPhase 3), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 41, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [] [] [] [] [] [] [] [] [] [] [] [] [] [], cells := 3 },
   { ticks := 42, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [] [] [] [] [] [] [] [] [] [] [] [] [] [false], cells := 4 }]

def cleanupC03 : CleanupFixture where
  name := "additional/C03"
  phase := clearPhase 3
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 41
  peak := 32
  index := 3

def cleanupC03Boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 3), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 1, phase := some (clearPhase 3), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 2, phase := some (clearPhase 4), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 40, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [] [] [] [] [] [] [] [] [] [] [] [] [], cells := 5 },
   { ticks := 41, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [] [] [] [] [] [] [] [] [] [] [] [] [true], cells := 6 }]

def cleanupC03E : CleanupFixture where
  name := "additional/C03E"
  phase := clearPhase 3
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 40
  peak := 31
  index := 3

def cleanupC03EBoundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 3), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 1, phase := some (clearPhase 4), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 39, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [] [] [] [] [] [] [] [] [] [] [] [] [], cells := 5 },
   { ticks := 40, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [] [] [] [] [] [] [] [] [] [] [] [] [false], cells := 6 }]

def cleanupC04 : CleanupFixture where
  name := "additional/C04"
  phase := clearPhase 4
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 39
  peak := 32
  index := 4

def cleanupC04Boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 4), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 3, phase := some (clearPhase 4), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 4, phase := some (clearPhase 5), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 38, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [] [] [] [] [] [] [] [] [] [] [] [], cells := 6 },
   { ticks := 39, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [] [] [] [] [] [] [] [] [] [] [] [true], cells := 7 }]

def cleanupC04E : CleanupFixture where
  name := "additional/C04E"
  phase := clearPhase 4
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 36
  peak := 29
  index := 4

def cleanupC04EBoundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 4), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 1, phase := some (clearPhase 5), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 35, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [] [] [] [] [] [] [] [] [] [] [] [], cells := 6 },
   { ticks := 36, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [] [] [] [] [] [] [] [] [] [] [] [false], cells := 7 }]

def cleanupC05 : CleanupFixture where
  name := "additional/C05"
  phase := clearPhase 5
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 35
  peak := 32
  index := 5

def cleanupC05Boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 5), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 2, phase := some (clearPhase 5), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 3, phase := some (clearPhase 6), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 34, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [] [] [] [] [] [] [] [] [] [] [], cells := 9 },
   { ticks := 35, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [] [] [] [] [] [] [] [] [] [] [true], cells := 10 }]

def cleanupC05E : CleanupFixture where
  name := "additional/C05E"
  phase := clearPhase 5
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 33
  peak := 30
  index := 5

def cleanupC05EBoundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 5), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 1, phase := some (clearPhase 6), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 32, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [] [] [] [] [] [] [] [] [] [] [], cells := 9 },
   { ticks := 33, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [] [] [] [] [] [] [] [] [] [] [false], cells := 10 }]

def cleanupC06 : CleanupFixture where
  name := "additional/C06"
  phase := clearPhase 6
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [] [] [] [] [] [] [] [] [] [true]
  ticks := 32
  peak := 32
  index := 6

def cleanupC06Boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 6), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 1, phase := some (clearPhase 6), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 2, phase := some (clearPhase 7), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 31, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [] [] [] [] [] [] [] [] [] [], cells := 11 },
   { ticks := 32, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [] [] [] [] [] [] [] [] [] [true], cells := 12 }]

def cleanupC06E : CleanupFixture where
  name := "additional/C06E"
  phase := clearPhase 6
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [] [] [] [] [] [] [] [] [] [false]
  ticks := 31
  peak := 31
  index := 6

def cleanupC06EBoundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 6), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 1, phase := some (clearPhase 7), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 30, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [] [] [] [] [] [] [] [] [] [], cells := 11 },
   { ticks := 31, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [] [] [] [] [] [] [] [] [] [false], cells := 12 }]

def cleanupC07 : CleanupFixture where
  name := "additional/C07"
  phase := clearPhase 7
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [] [] [] [] [] [] [] [] [true]
  ticks := 30
  peak := 32
  index := 7

def cleanupC07Boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 7), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 2, phase := some (clearPhase 7), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 3, phase := some (clearPhase 8), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 29, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [] [] [] [] [] [] [] [] [], cells := 12 },
   { ticks := 30, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [] [] [] [] [] [] [] [] [true], cells := 13 }]

def cleanupC07E : CleanupFixture where
  name := "additional/C07E"
  phase := clearPhase 7
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [] [] [] [] [] [] [] [] [false]
  ticks := 28
  peak := 30
  index := 7

def cleanupC07EBoundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 7), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 1, phase := some (clearPhase 8), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 27, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [] [] [] [] [] [] [] [] [], cells := 12 },
   { ticks := 28, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [] [] [] [] [] [] [] [] [false], cells := 13 }]

def cleanupC08 : CleanupFixture where
  name := "additional/C08"
  phase := clearPhase 8
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [] [] [] [] [] [] [] [true]
  ticks := 27
  peak := 32
  index := 8

def cleanupC08Boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 8), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 3, phase := some (clearPhase 8), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 4, phase := some (clearPhase 9), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 26, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [] [] [] [] [] [] [] [], cells := 14 },
   { ticks := 27, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [] [] [] [] [] [] [] [true], cells := 15 }]

def cleanupC08E : CleanupFixture where
  name := "additional/C08E"
  phase := clearPhase 8
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [] [] [] [] [] [] [] [false]
  ticks := 24
  peak := 29
  index := 8

def cleanupC08EBoundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 8), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 1, phase := some (clearPhase 9), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 23, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [] [] [] [] [] [] [] [], cells := 14 },
   { ticks := 24, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [] [] [] [] [] [] [] [false], cells := 15 }]

def cleanupC09 : CleanupFixture where
  name := "additional/C09"
  phase := clearPhase 9
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [] [] [] [] [] [] [true]
  ticks := 23
  peak := 32
  index := 9

def cleanupC09Boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 9), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 1, phase := some (clearPhase 9), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 2, phase := some (clearPhase 10), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 22, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [] [] [] [] [] [] [], cells := 17 },
   { ticks := 23, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [] [] [] [] [] [] [true], cells := 18 }]

def cleanupC09E : CleanupFixture where
  name := "additional/C09E"
  phase := clearPhase 9
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [] [] [] [] [] [] [false]
  ticks := 22
  peak := 31
  index := 9

def cleanupC09EBoundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 9), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 1, phase := some (clearPhase 10), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 31 },
   { ticks := 21, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [] [] [] [] [] [] [], cells := 17 },
   { ticks := 22, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [] [] [] [] [] [] [false], cells := 18 }]

def cleanupC10 : CleanupFixture where
  name := "additional/C10"
  phase := clearPhase 10
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [] [] [] [] [] [true]
  ticks := 21
  peak := 32
  index := 10

def cleanupC10Boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 10), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 2, phase := some (clearPhase 10), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 3, phase := some (clearPhase 11), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 20, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [] [] [] [] [] [], cells := 18 },
   { ticks := 21, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [] [] [] [] [] [true], cells := 19 }]

def cleanupC10E : CleanupFixture where
  name := "additional/C10E"
  phase := clearPhase 10
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [] [] [] [] [] [false]
  ticks := 19
  peak := 30
  index := 10

def cleanupC10EBoundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 10), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 1, phase := some (clearPhase 11), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 18, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [] [] [] [] [] [], cells := 18 },
   { ticks := 19, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [] [] [] [] [] [false], cells := 19 }]

def cleanupC11 : CleanupFixture where
  name := "additional/C11"
  phase := clearPhase 11
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [] [] [] [] [true]
  ticks := 18
  peak := 32
  index := 11

def cleanupC11Boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 11), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 2, phase := some (clearPhase 11), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 3, phase := some (clearPhase 12), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 17, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [] [] [] [] [], cells := 20 },
   { ticks := 18, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [] [] [] [] [true], cells := 21 }]

def cleanupC11E : CleanupFixture where
  name := "additional/C11E"
  phase := clearPhase 11
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [] [] [] [] [false]
  ticks := 16
  peak := 30
  index := 11

def cleanupC11EBoundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 11), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 1, phase := some (clearPhase 12), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 15, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [] [] [] [] [], cells := 20 },
   { ticks := 16, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [] [] [] [] [false], cells := 21 }]

def cleanupC12 : CleanupFixture where
  name := "additional/C12"
  phase := clearPhase 12
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [] [] [] [true]
  ticks := 15
  peak := 32
  index := 12

def cleanupC12Boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 12), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 3, phase := some (clearPhase 12), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 4, phase := some (clearPhase 13), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 14, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [] [] [] [], cells := 22 },
   { ticks := 15, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [] [] [] [true], cells := 23 }]

def cleanupC12E : CleanupFixture where
  name := "additional/C12E"
  phase := clearPhase 12
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [] [] [] [false]
  ticks := 12
  peak := 29
  index := 12

def cleanupC12EBoundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 12), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 1, phase := some (clearPhase 13), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [] [.right, .left] [.left, .right, .left] [false, true], cells := 29 },
   { ticks := 11, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [] [] [] [], cells := 22 },
   { ticks := 12, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [] [] [] [false], cells := 23 }]

def cleanupC13 : CleanupFixture where
  name := "additional/C13"
  phase := clearPhase 13
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [] [] [true]
  ticks := 11
  peak := 32
  index := 13

def cleanupC13Boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 13), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 2, phase := some (clearPhase 13), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 3, phase := some (clearPhase 14), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 10, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [] [] [], cells := 25 },
   { ticks := 11, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [] [] [true], cells := 26 }]

def cleanupC13E : CleanupFixture where
  name := "additional/C13E"
  phase := clearPhase 13
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [] [] [false]
  ticks := 9
  peak := 30
  index := 13

def cleanupC13EBoundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 13), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 1, phase := some (clearPhase 14), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [] [.left, .right, .left] [false, true], cells := 30 },
   { ticks := 8, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [] [] [], cells := 25 },
   { ticks := 9, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [] [] [false], cells := 26 }]

def cleanupC14 : CleanupFixture where
  name := "additional/C14"
  phase := clearPhase 14
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [] [true]
  ticks := 8
  peak := 32
  index := 14

def cleanupC14Boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 14), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 3, phase := some (clearPhase 14), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [] [false, true], cells := 29 },
   { ticks := 4, phase := some (clearPhase 15), fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [] [false, true], cells := 29 },
   { ticks := 7, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [] [], cells := 27 },
   { ticks := 8, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [] [true], cells := 28 }]

def cleanupC14E : CleanupFixture where
  name := "additional/C14E"
  phase := clearPhase 14
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [] [false]
  ticks := 5
  peak := 29
  index := 14

def cleanupC14EBoundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 14), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [] [false, true], cells := 29 },
   { ticks := 1, phase := some (clearPhase 15), fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [] [false, true], cells := 29 },
   { ticks := 4, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [] [], cells := 27 },
   { ticks := 5, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [] [false], cells := 28 }]

def cleanupC15 : CleanupFixture where
  name := "additional/C15"
  phase := clearPhase 15
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [true]
  ticks := 4
  peak := 32
  index := 15

def cleanupC15Boundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 15), fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true], cells := 32 },
   { ticks := 2, phase := some (clearPhase 15), fields := ⟨some 15, some (), some true, some true, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [], cells := 30 },
   { ticks := 3, phase := some emitPhase, fields := ⟨some 15, some (), some true, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [], cells := 30 },
   { ticks := 4, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [true], cells := 31 }]

def cleanupC15E : CleanupFixture where
  name := "additional/C15E"
  phase := clearPhase 15
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] []
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false]
  ticks := 2
  peak := 31
  index := 15

def cleanupC15EBoundaries : List Boundary :=
  [{ ticks := 0, phase := some (clearPhase 15), fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [], cells := 30 },
   { ticks := 1, phase := some emitPhase, fields := ⟨some 15, some (), none, some false, some false, some true, some 11, some .right⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [], cells := 30 },
   { ticks := 2, phase := none, fields := ⟨none, none, none, none, none, none, none, none⟩, words := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false], cells := 31 }]

def emitE00 : EmitFixture where
  name := "additional/E00"
  phase := emitPhase
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, false, true]
  ticks := 1
  peak := 33

def emitE01 : EmitFixture where
  name := "additional/E01"
  phase := emitPhase
  fields := ⟨some 15, some (), some false, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, false, true]
  ticks := 1
  peak := 33

def emitE02 : EmitFixture where
  name := "additional/E02"
  phase := emitPhase
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]
  after := localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [true, false, true]
  ticks := 1
  peak := 33

def emitE03 : EmitFixture where
  name := "additional/E03"
  phase := emitPhase
  fields := ⟨some 15, some (), none, none, some false, some true, some 11, some .right⟩
  before := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [false]
  ticks := 1
  peak := 1

def joinJ00 : JoinFixture where
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

def joinJ01 : JoinFixture where
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

def joinJ02 : JoinFixture where
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

def joinJ03 : JoinFixture where
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

def dirtyD00 : DirtyFrontEndFixture where
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

def dirtyD01 : DirtyFrontEndFixture where
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

def dirtyD02 : DirtyFrontEndFixture where
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

def dirtyD03 : DirtyFrontEndFixture where
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

def emptyCleanupFixture : CleanupFixture where
  name := "additional/CZERO"
  phase := clearPhase 0
  fields := ⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩
  before := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []
  after := localData [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [true]
  ticks := 17
  peak := 1
  index := 0

def partialClearCases : List CleanupFixture :=
  [cleanupC00, cleanupC00E, cleanupC01, cleanupC01E, cleanupC02, cleanupC02E, cleanupC03, cleanupC03E, cleanupC04, cleanupC04E, cleanupC05, cleanupC05E, cleanupC06, cleanupC06E, cleanupC07, cleanupC07E, cleanupC08, cleanupC08E, cleanupC09, cleanupC09E, cleanupC10, cleanupC10E, cleanupC11, cleanupC11E, cleanupC12, cleanupC12E, cleanupC13, cleanupC13E, cleanupC14, cleanupC14E, cleanupC15, cleanupC15E]

theorem partialClearCases_count : partialClearCases.length = 32 := rfl

def emitCases : List EmitFixture :=
  [emitE00, emitE01, emitE02, emitE03]

theorem emitCases_count : emitCases.length = 4 := rfl

def joinCases : List JoinFixture :=
  [joinJ00, joinJ01, joinJ02, joinJ03]

theorem joinCases_count : joinCases.length = 4 := rfl

def dirtyFrontEndCases : List DirtyFrontEndFixture :=
  [dirtyD00, dirtyD01, dirtyD02, dirtyD03]

theorem dirtyFrontEndCases_count : dirtyFrontEndCases.length = 4 := rfl

def partialClearBoundaries : List (CleanupFixture × List Boundary) :=
  [(cleanupC00, cleanupC00Boundaries),
   (cleanupC00E, cleanupC00EBoundaries),
   (cleanupC01, cleanupC01Boundaries),
   (cleanupC01E, cleanupC01EBoundaries),
   (cleanupC02, cleanupC02Boundaries),
   (cleanupC02E, cleanupC02EBoundaries),
   (cleanupC03, cleanupC03Boundaries),
   (cleanupC03E, cleanupC03EBoundaries),
   (cleanupC04, cleanupC04Boundaries),
   (cleanupC04E, cleanupC04EBoundaries),
   (cleanupC05, cleanupC05Boundaries),
   (cleanupC05E, cleanupC05EBoundaries),
   (cleanupC06, cleanupC06Boundaries),
   (cleanupC06E, cleanupC06EBoundaries),
   (cleanupC07, cleanupC07Boundaries),
   (cleanupC07E, cleanupC07EBoundaries),
   (cleanupC08, cleanupC08Boundaries),
   (cleanupC08E, cleanupC08EBoundaries),
   (cleanupC09, cleanupC09Boundaries),
   (cleanupC09E, cleanupC09EBoundaries),
   (cleanupC10, cleanupC10Boundaries),
   (cleanupC10E, cleanupC10EBoundaries),
   (cleanupC11, cleanupC11Boundaries),
   (cleanupC11E, cleanupC11EBoundaries),
   (cleanupC12, cleanupC12Boundaries),
   (cleanupC12E, cleanupC12EBoundaries),
   (cleanupC13, cleanupC13Boundaries),
   (cleanupC13E, cleanupC13EBoundaries),
   (cleanupC14, cleanupC14Boundaries),
   (cleanupC14E, cleanupC14EBoundaries),
   (cleanupC15, cleanupC15Boundaries),
   (cleanupC15E, cleanupC15EBoundaries)]

theorem partial_clear_boundary_count : (partialClearBoundaries.map (fun p => p.2.length)).sum = 142 := rfl

/-! ## Three distinct liveness records -/

def livenessL00 : LivenessFixture :=
  .liveHalt "liveness/L00" (⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩) (localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]) 32

def livenessL01 : LivenessFixture :=
  .outerNone "liveness/L01"

def livenessL02 : LivenessFixture :=
  .externalAllocator "liveness/L02" 42 (⟨some 15, some (), some true, none, some false, some true, some 11, some .right⟩) (localData [true, false] [false] [false, true] [true] [true, false, true] [11, 15] [3] [6, 10] [1, 0, 0] [0] [12, 2] [(), ()] [false, false, true] [.right, .left] [.left, .right, .left] [false, true]) [true, true, false, true] [11, 15] 38

def livenessCases : List LivenessFixture := [livenessL00, livenessL01, livenessL02]

theorem liveness_cases_count : livenessCases.length = 3 := rfl

def allClosedCases : List ClosedFixture :=
  rawCases.map RawFixture.toClosed ++ partialClearCases.map CleanupFixture.toClosedFixture ++
    emitCases.map EmitFixture.toClosedFixture ++ joinCases.map JoinFixture.toClosedFixture ++
    dirtyFrontEndCases.map DirtyFrontEndFixture.toClosedFixture ++ [emptyCleanupFixture.toClosedFixture]

theorem all_positive_closed_cases_count : allClosedCases.length = 81 := rfl

theorem all_frozen_case_records_count : allClosedCases.length + livenessCases.length = 84 := rfl

/-! ## All 96 owned control domains, independently listed -/

def frontEndFramerScanPrefixPhase : Phase := .inl (FrontEndMachine.framerLabel .scanPrefix)
def frontEndFramerCopyCertPhase : Phase := .inl (FrontEndMachine.framerLabel .copyCert)
def frontEndFramerEmitCertPhase : Phase := .inl (FrontEndMachine.framerLabel .emitCert)
def frontEndFramerEmitFirstPhase : Phase := .inl (FrontEndMachine.framerLabel .emitFirst)
def frontEndFramerClearFirstPhase : Phase := .inl (FrontEndMachine.framerLabel .clearFirst)
def frontEndInputDecoderScanPhase : Phase := .inl (FrontEndMachine.inputDecoderLabel .scan)
def frontEndInputDecoderEmitPhase : Phase := .inl (FrontEndMachine.inputDecoderLabel .emit)
def frontEndInputDecoderClearPhase : Phase := .inl (FrontEndMachine.inputDecoderLabel .clear)
def frontEndSourceTreeInitPhase : Phase := .inl (InputParserMachine.treeLabel .source .init)
def frontEndSourceTreeScanPhase : Phase := .inl (InputParserMachine.treeLabel .source .scan)
def frontEndSourceTreeEmitPhase : Phase := .inl (InputParserMachine.treeLabel .source .emit)
def frontEndSourceTreeUndoPhase : Phase := .inl (InputParserMachine.treeLabel .source .undo)
def frontEndSourceTreeDropPendingPhase : Phase := .inl (InputParserMachine.treeLabel .source .dropPending)
def frontEndTargetTreeInitPhase : Phase := .inl (InputParserMachine.treeLabel .target .init)
def frontEndTargetTreeScanPhase : Phase := .inl (InputParserMachine.treeLabel .target .scan)
def frontEndTargetTreeEmitPhase : Phase := .inl (InputParserMachine.treeLabel .target .emit)
def frontEndTargetTreeUndoPhase : Phase := .inl (InputParserMachine.treeLabel .target .undo)
def frontEndTargetTreeDropPendingPhase : Phase := .inl (InputParserMachine.treeLabel .target .dropPending)
def frontEndInputBitsScanPhase : Phase := .inl (InputParserMachine.phaseLabel .bitsScan)
def frontEndInputBitsEmitPhase : Phase := .inl (InputParserMachine.phaseLabel .bitsEmit)
def frontEndInputEOFPhase : Phase := .inl (InputParserMachine.phaseLabel .eof)
def frontEndInputRestoreEndPhase : Phase := .inl (InputParserMachine.phaseLabel .restoreEnd)
def frontEndInputFuelUndoPhase : Phase := .inl (InputParserMachine.phaseLabel .fuelUndo)
def frontEndInputBitsUndoPhase : Phase := .inl (InputParserMachine.phaseLabel .bitsUndo)
def frontEndInputRestoreSep2Phase : Phase := .inl (InputParserMachine.phaseLabel .restoreSep2)
def frontEndInputTargetToReversePhase : Phase := .inl (InputParserMachine.phaseLabel .targetToReverse)
def frontEndInputTargetToRawPhase : Phase := .inl (InputParserMachine.phaseLabel .targetToRaw)
def frontEndInputRestoreSep1Phase : Phase := .inl (InputParserMachine.phaseLabel .restoreSep1)
def frontEndInputSourceToReversePhase : Phase := .inl (InputParserMachine.phaseLabel .sourceToReverse)
def frontEndInputSourceToRawPhase : Phase := .inl (InputParserMachine.phaseLabel .sourceToRaw)
def frontEndSourceSuccessPhase : Phase := .inl (InputParserMachine.treeResultLabel .source .success)
def frontEndTargetSuccessPhase : Phase := .inl (InputParserMachine.treeResultLabel .target .success)
def frontEndTargetFailurePhase : Phase := .inl (InputParserMachine.treeResultLabel .target .failure)
def frontEndCertificateDecoderScanPhase : Phase := .inl (FrontEndMachine.certificateDecoderLabel .scan)
def frontEndCertificateDecoderEmitPhase : Phase := .inl (FrontEndMachine.certificateDecoderLabel .emit)
def frontEndCertificateDecoderClearPhase : Phase := .inl (FrontEndMachine.certificateDecoderLabel .clear)
def frontEndDispatchPhase : Phase := .inl (FrontEndMachine.dispatchLabel)
def frontEndRejectPhase : Phase := .inl (FrontEndMachine.rejectLabel)
def streamInspectPhase : Phase := streamPhase (StreamMachine.inspectPhase)
def streamCounterBorrowPhase : Phase := streamPhase (StreamMachine.counterPhase .borrow)
def streamCounterRestoreTruePhase : Phase := streamPhase (StreamMachine.counterPhase .restoreTrue)
def streamCounterRestoreFalsePhase : Phase := streamPhase (StreamMachine.counterPhase .restoreFalse)
def streamFuelJoinAtEndPhase : Phase := streamPhase (StreamMachine.fuelJoinPhase .atEnd)
def streamFuelJoinPositivePhase : Phase := streamPhase (StreamMachine.fuelJoinPhase .positive)
def streamFuelJoinZeroPhase : Phase := streamPhase (StreamMachine.fuelJoinPhase .zero)
def streamMoveStartPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.movePhase (.start)))
def streamMoveScanLeftPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.movePhase (.scan .left)))
def streamMoveScanRightPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.movePhase (.scan .right)))
def streamMoveEmitLeftPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.movePhase (.emit .left)))
def streamMoveEmitRightPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.movePhase (.emit .right)))
def streamMoveUndoLeftPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.movePhase (.undo .left)))
def streamMoveUndoRightPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.movePhase (.undo .right)))
def streamMoveDispatchSuccessLeftPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.dispatchPhase (.success .left)))
def streamMoveDispatchSuccessRightPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.dispatchPhase (.success .right)))
def streamMoveDispatchFailurePhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.dispatchPhase (.failure)))
def streamPositionSeekLeftPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.seek .left)))
def streamPositionSeekRightPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.seek .right)))
def streamPositionScanPrefixLeftPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.scanPrefix .left)))
def streamPositionScanPrefixRightPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.scanPrefix .right)))
def streamPositionStartLeftPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.start .left)))
def streamPositionStartRightPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.start .right)))
def streamPositionScanScratchLeftPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.scanScratch .left)))
def streamPositionScanScratchRightPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.scanScratch .right)))
def streamPositionCheckRightPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.checkRight)))
def streamPositionRestoreScratchSuccessLeftPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successLeft)))
def streamPositionRestoreScratchSuccessRightPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .successRight)))
def streamPositionRestoreScratchFailureLeftPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .failureLeft)))
def streamPositionRestoreScratchFailureRightPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.restoreScratch .failureRight)))
def streamPositionDropPendingPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.dropPending)))
def streamPositionRestorePrefixSuccessPhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .success)))
def streamPositionRestorePrefixFailurePhase : Phase := streamPhase (StreamMachine.applyPhase (MoveApplyMachine.positionPhase (.restorePrefix .failure)))
def streamApplyJoinParseFailurePhase : Phase := streamPhase (StreamMachine.applyJoinPhase MoveApplyMachine.parseFailure)
def streamApplyJoinRotationFailurePhase : Phase := streamPhase (StreamMachine.applyJoinPhase MoveApplyMachine.rotationFailure)
def streamApplyJoinSuccessPhase : Phase := streamPhase (StreamMachine.applyJoinPhase MoveApplyMachine.success)
def streamComparePhase : Phase := streamPhase (StreamMachine.comparePhase)
def streamEqualityJoinEqualPhase : Phase := streamPhase (StreamMachine.equalityJoinPhase .equal)
def streamEqualityJoinDifferentPhase : Phase := streamPhase (StreamMachine.equalityJoinPhase .different)
def streamResultFalsePhase : Phase := resultPhase false
def streamResultTruePhase : Phase := resultPhase true
def clearPhase00 : Phase := clearPhase 0
def clearPhase01 : Phase := clearPhase 1
def clearPhase02 : Phase := clearPhase 2
def clearPhase03 : Phase := clearPhase 3
def clearPhase04 : Phase := clearPhase 4
def clearPhase05 : Phase := clearPhase 5
def clearPhase06 : Phase := clearPhase 6
def clearPhase07 : Phase := clearPhase 7
def clearPhase08 : Phase := clearPhase 8
def clearPhase09 : Phase := clearPhase 9
def clearPhase10 : Phase := clearPhase 10
def clearPhase11 : Phase := clearPhase 11
def clearPhase12 : Phase := clearPhase 12
def clearPhase13 : Phase := clearPhase 13
def clearPhase14 : Phase := clearPhase 14
def clearPhase15 : Phase := clearPhase 15
def emit : Phase := emitPhase

def phaseDomains : List Phase :=
  [frontEndFramerScanPrefixPhase,
   frontEndFramerCopyCertPhase,
   frontEndFramerEmitCertPhase,
   frontEndFramerEmitFirstPhase,
   frontEndFramerClearFirstPhase,
   frontEndInputDecoderScanPhase,
   frontEndInputDecoderEmitPhase,
   frontEndInputDecoderClearPhase,
   frontEndSourceTreeInitPhase,
   frontEndSourceTreeScanPhase,
   frontEndSourceTreeEmitPhase,
   frontEndSourceTreeUndoPhase,
   frontEndSourceTreeDropPendingPhase,
   frontEndTargetTreeInitPhase,
   frontEndTargetTreeScanPhase,
   frontEndTargetTreeEmitPhase,
   frontEndTargetTreeUndoPhase,
   frontEndTargetTreeDropPendingPhase,
   frontEndInputBitsScanPhase,
   frontEndInputBitsEmitPhase,
   frontEndInputEOFPhase,
   frontEndInputRestoreEndPhase,
   frontEndInputFuelUndoPhase,
   frontEndInputBitsUndoPhase,
   frontEndInputRestoreSep2Phase,
   frontEndInputTargetToReversePhase,
   frontEndInputTargetToRawPhase,
   frontEndInputRestoreSep1Phase,
   frontEndInputSourceToReversePhase,
   frontEndInputSourceToRawPhase,
   frontEndSourceSuccessPhase,
   frontEndTargetSuccessPhase,
   frontEndTargetFailurePhase,
   frontEndCertificateDecoderScanPhase,
   frontEndCertificateDecoderEmitPhase,
   frontEndCertificateDecoderClearPhase,
   frontEndDispatchPhase,
   frontEndRejectPhase,
   streamInspectPhase,
   streamCounterBorrowPhase,
   streamCounterRestoreTruePhase,
   streamCounterRestoreFalsePhase,
   streamFuelJoinAtEndPhase,
   streamFuelJoinPositivePhase,
   streamFuelJoinZeroPhase,
   streamMoveStartPhase,
   streamMoveScanLeftPhase,
   streamMoveScanRightPhase,
   streamMoveEmitLeftPhase,
   streamMoveEmitRightPhase,
   streamMoveUndoLeftPhase,
   streamMoveUndoRightPhase,
   streamMoveDispatchSuccessLeftPhase,
   streamMoveDispatchSuccessRightPhase,
   streamMoveDispatchFailurePhase,
   streamPositionSeekLeftPhase,
   streamPositionSeekRightPhase,
   streamPositionScanPrefixLeftPhase,
   streamPositionScanPrefixRightPhase,
   streamPositionStartLeftPhase,
   streamPositionStartRightPhase,
   streamPositionScanScratchLeftPhase,
   streamPositionScanScratchRightPhase,
   streamPositionCheckRightPhase,
   streamPositionRestoreScratchSuccessLeftPhase,
   streamPositionRestoreScratchSuccessRightPhase,
   streamPositionRestoreScratchFailureLeftPhase,
   streamPositionRestoreScratchFailureRightPhase,
   streamPositionDropPendingPhase,
   streamPositionRestorePrefixSuccessPhase,
   streamPositionRestorePrefixFailurePhase,
   streamApplyJoinParseFailurePhase,
   streamApplyJoinRotationFailurePhase,
   streamApplyJoinSuccessPhase,
   streamComparePhase,
   streamEqualityJoinEqualPhase,
   streamEqualityJoinDifferentPhase,
   streamResultFalsePhase,
   streamResultTruePhase,
   clearPhase00,
   clearPhase01,
   clearPhase02,
   clearPhase03,
   clearPhase04,
   clearPhase05,
   clearPhase06,
   clearPhase07,
   clearPhase08,
   clearPhase09,
   clearPhase10,
   clearPhase11,
   clearPhase12,
   clearPhase13,
   clearPhase14,
   clearPhase15,
   emit]

theorem phase_domains_count : phaseDomains.length = 96 := rfl


end Examples.RotationCertificateFrontEndStreamMachine
