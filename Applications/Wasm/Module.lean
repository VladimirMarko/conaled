import Applications.Wasm.Rules

/-! Closed generated modules and their standard administrative invocation path.
The body-execution lemma is compositional; compiler correctness must discharge
its body premise rather than expose that premise to source clients. -/
namespace Applications.Wasm

variable {I : Type}

/-- The inspectable single-function module. Omitted sections are empty by
construction; its only export is the function at module index zero, named run. -/
structure Module where
  type : FuncType
  locals : List ValueType
  body : List Instr
  deriving DecidableEq, Repr

def Module.instance (m : Module) (address : Nat) : ModuleInstance :=
  ⟨[m.type], [address], [], [], [], [], [], [("run", .func address)]⟩

def Module.function (m : Module) (address : Nat) : Function :=
  ⟨m.type, m.instance address, m.locals, m.body⟩

def Module.Valid (m : Module) : Prop :=
  CodeTyped (m.type.params ++ m.locals) m.body [] m.type.results

def Module.instantiate (m : Module) (s : Store F O) : ExtendedStore F O × ModuleInstance :=
  (s.extend (m.function s.funcs.length), m.instance s.funcs.length)

def ModuleInstance.export (m : ModuleInstance) (name : String) : Option Extern :=
  (m.exports.find? (fun x => x.1 == name)).map Prod.snd

@[simp] theorem Module.export_run (m : Module) (address : Nat) :
    (m.instance address).export "run" = some (.func address) := by
  simp [Module.instance, ModuleInstance.export]

@[simp] theorem Module.instantiate_lookup (m : Module) (s : Store F O) :
    (m.instantiate s).1.funcs[s.funcs.length]? =
      some (.inr (m.function s.funcs.length)) := by
  exact Store.extend_fresh _ _

/-- The external invocation's dummy frame has no locals and no module entries. -/
def dummyFrame : Frame := ⟨[], ⟨[], [], [], [], [], [], [], []⟩⟩

/-- External invocation checks the signature before creating its initial
configuration. Canonical Boolean admission is a separate, stronger condition. -/
def externalInvoke (s : ExtendedStore F O) (address : Nat) (args : List Value) :
    Option (Frame × List (Admin I)) := do
  let .inr f ← s.funcs[address]? | none
  if args.map Value.type = f.type.params then
    some (dummyFrame, values args ++ [.invoke address])
  else none

theorem externalInvoke_generated (s : ExtendedStore F O) (address : Nat)
    (f : Function) (args : List Value)
    (lookup : s.funcs[address]? = some (.inr f))
    (types : args.map Value.type = f.type.params) :
    externalInvoke (I := I) s address args = some (dummyFrame, values args ++ [.invoke address]) := by
  simp [externalInvoke, lookup, types]

/-- Complete administrative path, including invocation, its label, and return.
The premise describes only the body segment and is discharged by lowering. -/
theorem invoke_of_body (s : ExtendedStore F O) (address : Nat) (f : Function)
    (args result : List Value) (after : Frame)
    (lookup : s.funcs[address]? = some (.inr f))
    (inputs : args.length = f.type.params.length)
    (outputs : result.length = f.type.results.length)
    (body : Steps (I := I) s ⟨args ++ f.locals.map Value.default, f.module⟩
      (expression f.body) after (values result)) :
    Steps (I := I) s dummyFrame (values args ++ [.invoke address]) dummyFrame (values result) := by
  apply Steps.cons (.invoke _ _ _ _ lookup inputs)
  have inLabel := body.context (.label f.type.results.length [] .hole)
  have inFrame := inLabel.inFrame dummyFrame f.type.results.length
  apply inFrame.trans
  apply Steps.cons (.inFrame _ _ _ _ _ _ (.label _ _ _ _))
  exact Steps.single (.frame _ _ _ _ outputs)

/-- Stack-height validation for the uniform i32 signature used by generated
modules. All arithmetic stays in Nat until the separate u32 admission test. -/
def Instr.checkHeight (count : Nat) (i : Instr) (height : Nat) : Option Nat :=
  match i with
  | .const _ => some (height + 1)
  | .get n => if n < count then some (height + 1) else none
  | .set n => if n < count ∧ 0 < height then some (height - 1) else none
  | .eqz => if 0 < height then some height else none
  | .binary _ => if 2 ≤ height then some (height - 1) else none

def checkHeights (count : Nat) : List Instr → Nat → Option Nat
  | [], height => some height
  | i :: rest, height => do
      let next ← i.checkHeight count height
      checkHeights count rest next

theorem InstrTyped.checkHeight (h : InstrTyped (List.replicate count .i32) i before after) :
    i.checkHeight count before.length = some after.length := by
  cases h with
  | const => simp [Instr.checkHeight]
  | get ts i t hi =>
    have bound : i < count := by
      by_contra hn
      simp [hn] at hi
    simp [Instr.checkHeight, bound]
  | set ts i t hi =>
    have bound : i < count := by
      by_contra hn
      simp [hn] at hi
    simp [Instr.checkHeight, bound]
  | eqz => simp [Instr.checkHeight]
  | binary => simp [Instr.checkHeight]

theorem CodeTyped.checkHeights (h : CodeTyped (List.replicate count .i32) code before after) :
    checkHeights count code before.length = some after.length := by
  induction h with
  | nil => rfl
  | cons head tail ih =>
    simp only [Wasm.checkHeights, head.checkHeight, bind, Option.bind_some]
    exact ih

theorem Instr.checkHeight_sound (i : Instr) (h : i.checkHeight count before = some after) :
    InstrTyped (List.replicate count .i32) i
      (List.replicate before .i32) (List.replicate after .i32) := by
  cases i with
  | const v =>
    cases h
    simpa [List.replicate_succ'] using InstrTyped.const (List.replicate before .i32) v
  | get n =>
    simp only [checkHeight] at h
    split at h
    · rename_i bound
      cases h
      simpa [List.replicate_succ'] using
        InstrTyped.get (locals := List.replicate count .i32) (List.replicate before .i32) n .i32 (by simp [bound])
    · contradiction
  | set n =>
    simp only [checkHeight] at h
    split at h
    · rename_i bound
      cases h
      have size : before = (before - 1) + 1 := by omega
      conv_lhs => rw [size]
      simpa [List.replicate_succ'] using
        InstrTyped.set (locals := List.replicate count .i32) (List.replicate (before - 1) .i32) n .i32 (by simp [bound.1])
    · contradiction
  | eqz =>
    simp only [checkHeight] at h
    split at h
    · rename_i bound
      cases h
      have size : before = (before - 1) + 1 := by omega
      simpa only [← List.replicate_succ', ← size] using
        InstrTyped.eqz (locals := List.replicate count .i32) (List.replicate (before - 1) .i32)
    · contradiction
  | binary op =>
    simp only [checkHeight] at h
    split at h
    · rename_i bound
      cases h
      have size : before = (before - 2) + 2 := by omega
      have result : before - 1 = (before - 2) + 1 := by omega
      have hin : List.replicate before ValueType.i32 = List.replicate (before - 2) .i32 ++ [.i32, .i32] := by
        calc
          _ = List.replicate ((before - 2) + 2) .i32 := congrArg (fun n => List.replicate n ValueType.i32) size
          _ = _ := by rw [List.replicate_add]; rfl
      have hout : List.replicate (before - 1) ValueType.i32 = List.replicate (before - 2) .i32 ++ [.i32] := by
        calc
          _ = List.replicate ((before - 2) + 1) .i32 := congrArg (fun n => List.replicate n ValueType.i32) result
          _ = _ := by rw [List.replicate_add]; rfl
      rw [hin, hout]
      exact InstrTyped.binary _ op
    · contradiction

theorem checkHeights_sound (code : List Instr) (h : checkHeights count code before = some after) :
    CodeTyped (List.replicate count .i32) code
      (List.replicate before .i32) (List.replicate after .i32) := by
  induction code generalizing before with
  | nil => cases h; exact .nil _
  | cons i rest ih =>
    simp only [checkHeights, bind, Option.bind_eq_some_iff] at h
    obtain ⟨next, head, tail⟩ := h
    exact .cons (i.checkHeight_sound head) (ih tail)

/-- Validation of the selected uniform-i32 module class. Other standard types
remain available in ambient stores and preserved operand-stack prefixes. -/
def Module.validate (m : Module) : Bool :=
  decide (m.type.params = List.replicate m.type.params.length .i32 ∧
    m.type.results = List.replicate m.type.results.length .i32 ∧
    m.locals = List.replicate m.locals.length .i32 ∧
    checkHeights (m.type.params.length + m.locals.length) m.body 0 = some m.type.results.length)

theorem Module.validate_sound (m : Module) (h : m.validate = true) : m.Valid := by
  simp only [validate, decide_eq_true_eq] at h
  obtain ⟨params, results, locals, checked⟩ := h
  have typed := checkHeights_sound m.body checked
  have localtypes : m.type.params ++ m.locals =
      List.replicate (m.type.params.length + m.locals.length) ValueType.i32 := by
    calc
      _ = List.replicate m.type.params.length .i32 ++ List.replicate m.locals.length .i32 := congrArg₂ List.append params locals
      _ = _ := (List.replicate_add _ _ _).symm
  change CodeTyped (m.type.params ++ m.locals) m.body [] m.type.results
  rw [localtypes, results]
  exact typed

/-- Resource admission concerns syntax counts, not engine memory or speed. -/
structure Limits where
  parameters : Nat
  results : Nat
  locals : Nat
  instructions : Nat
  deriving DecidableEq, Repr

/-- A concrete conservative profile; binary byte lengths remain a later encoder
obligation. The width-32 selector fits these limits. -/
def Limits.default : Limits := ⟨1024, 1024, 65536, 1048576⟩

def Module.admit (m : Module) (limits : Limits := .default) : Bool :=
  m.validate && decide (m.type.params.length ≤ limits.parameters ∧
    m.type.results.length ≤ limits.results ∧
    m.type.params.length + m.locals.length ≤ limits.locals ∧
    m.body.length ≤ limits.instructions ∧
    m.type.params.length < 2^32 ∧ m.type.results.length < 2^32 ∧
    m.type.params.length + m.locals.length < 2^32 ∧ m.body.length < 2^32)

theorem Module.admit_valid (m : Module) (limits : Limits) (h : m.admit limits = true) : m.Valid := by
  simp only [admit, Bool.and_eq_true] at h
  exact m.validate_sound h.1

end Applications.Wasm
