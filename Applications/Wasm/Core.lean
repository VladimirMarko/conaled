import Mathlib.Data.List.Basic
import Mathlib.Data.BitVec

/-! The memory-free generated fragment of WebAssembly Core 2.0. Administrative
syntax is separate from emitted instructions. Untouched store components remain
parameters; their contents, including embedded addresses, are never rewritten. -/
namespace Applications.Wasm

variable {I : Type}

inductive ValueType where
  | i32 | i64 | f32 | f64 | v128 | funcref | externref
  deriving DecidableEq, Repr

inductive Value where
  | i32 (bits : BitVec 32)
  | i64 (bits : BitVec 64)
  | f32 (bits : BitVec 32)
  | f64 (bits : BitVec 64)
  | v128 (bits : BitVec 128)
  | funcref (address : Option Nat)
  | externref (address : Option Nat)
  deriving DecidableEq, Repr

def Value.type : Value → ValueType
  | .i32 _ => .i32 | .i64 _ => .i64 | .f32 _ => .f32 | .f64 _ => .f64
  | .v128 _ => .v128 | .funcref _ => .funcref | .externref _ => .externref

def Value.default : ValueType → Value
  | .i32 => .i32 0 | .i64 => .i64 0 | .f32 => .f32 0 | .f64 => .f64 0
  | .v128 => .v128 0 | .funcref => .funcref none | .externref => .externref none

@[simp] theorem Value.default_type (t : ValueType) : (Value.default t).type = t := by
  cases t <;> rfl

inductive BinOp where
  | and | or | xor
  deriving DecidableEq, Repr

def BinOp.eval : BinOp → BitVec 32 → BitVec 32 → BitVec 32
  | .and => (· &&& ·)
  | .or => (· ||| ·)
  | .xor => (· ^^^ ·)

inductive Instr where
  | const (bits : BitVec 32)
  | get (index : Nat)
  | set (index : Nat)
  | eqz
  | binary (op : BinOp)
  deriving DecidableEq, Repr

structure FuncType where
  params : List ValueType
  results : List ValueType
  deriving DecidableEq, Repr

/-- All module address vectors, including empty vectors in the generated module.
Exports retain their external kind, so function address zero is not confused with
an export's position or a memory address. -/
inductive Extern where
  | func (address : Nat) | table (address : Nat)
  | memory (address : Nat) | global (address : Nat)
  deriving DecidableEq, Repr

structure ModuleInstance where
  types : List FuncType
  funcs : List Nat
  tables : List Nat
  memories : List Nat
  globals : List Nat
  elems : List Nat
  datas : List Nat
  exports : List (String × Extern)
  deriving DecidableEq, Repr

structure Function where
  type : FuncType
  module : ModuleInstance
  locals : List ValueType
  body : List Instr
  deriving DecidableEq, Repr

/-- `AmbientFunction` ranges over whole standard function instances, including
host instances. `Other` ranges over the tuple of every other standard store
field. Neither parameter restricts its inhabitants to the generated fragment. -/
structure Store (AmbientFunction Other : Type) where
  funcs : List AmbientFunction
  other : Other

/-- Tagged functions distinguish untouched ambient instances from the generated
instance. Numeric addresses retain their ordinary list positions. -/
abbrev ExtendedStore (AmbientFunction Other : Type) :=
  Store (Sum AmbientFunction Function) Other

def Store.embed (s : Store F O) : ExtendedStore F O :=
  ⟨s.funcs.map Sum.inl, s.other⟩

def Store.extend (s : Store F O) (f : Function) : ExtendedStore F O :=
  ⟨s.funcs.map Sum.inl ++ [Sum.inr f], s.other⟩

/-- Rebuild a standard store using the concrete syntax embedding of the generated
function. This is a data map, with no premise about execution equivalence. -/
def Store.reconstruct (encode : Function → F) (s : ExtendedStore F O) : Store F O :=
  ⟨s.funcs.map (Sum.elim id encode), s.other⟩

@[simp] theorem Store.reconstruct_embed (encode : Function → F) (s : Store F O) :
    reconstruct encode s.embed = s := by
  cases s
  simp [reconstruct, embed, List.map_map, Function.comp_def]

@[simp] theorem Store.reconstruct_extend (encode : Function → F)
    (s : Store F O) (f : Function) :
    reconstruct encode (s.extend f) = ⟨s.funcs ++ [encode f], s.other⟩ := by
  simp [reconstruct, extend, List.map_map, Function.comp_def]

@[simp] theorem Store.extend_other (s : Store F O) (f : Function) :
    (s.extend f).other = s.other := rfl

@[simp] theorem Store.extend_fresh (s : Store F O) (f : Function) :
    (s.extend f).funcs[s.funcs.length]? = some (.inr f) := by
  simp [extend]

theorem Store.extend_old (s : Store F O) (f : Function) (i : Nat)
    (h : i < s.funcs.length) :
    (s.extend f).funcs[i]? = (s.funcs[i]?).map Sum.inl := by
  simp [extend, List.getElem?_append, h]

structure Frame where
  locals : List Value
  module : ModuleInstance
  deriving DecidableEq, Repr

/-- Constants are values in the standard reduction grammar, not redexes. -/
inductive Admin (I : Type) where
  | foreign (instruction : I)
  | value (v : Value)
  | instr (i : Instr)
  | invoke (address : Nat)
  | label (arity : Nat) (continuation : List (Admin I)) (body : List (Admin I))
  | frame (arity : Nat) (frame : Frame) (body : List (Admin I))
  | trap
  deriving Repr

def Instr.admin : Instr → Admin I
  | .const n => .value (.i32 n)
  | i => .instr i

def values (vs : List Value) : List (Admin I) := vs.map Admin.value

def expression (code : List Instr) : List (Admin I) := code.map Instr.admin

/-- Evaluation contexts inside a frame. A frame has a separate contextual rule. -/
inductive Context (I : Type) where
  | hole
  | seq (before : List Value) (inner : Context I) (suffix : List (Admin I))
  | label (arity : Nat) (continuation : List (Admin I)) (inner : Context I)

def Context.fill : Context I → List (Admin I) → List (Admin I)
  | .hole, code => code
  | .seq vs inner suffix, code => values vs ++ inner.fill code ++ suffix
  | .label n cont inner, code => [.label n cont (inner.fill code)]

/-- Constructors supplied by the full administrative syntax. Foreign syntax is
already in that syntax and is returned unchanged. This interface specifies data
reconstruction only; it carries no operational or equivalence assumptions. -/
structure Reconstruction (I : Type) where
  value : Value → I
  instr : Instr → I
  invoke : Nat → I
  label : Nat → List I → List I → I
  frame : Nat → Frame → List I → I
  trap : I

def Admin.reconstruct (r : Reconstruction I) : Admin I → I
  | .foreign i => i
  | .value v => r.value v
  | .instr i => r.instr i
  | .invoke address => r.invoke address
  | .label n cont body => r.label n (cont.map (Admin.reconstruct r)) (body.map (Admin.reconstruct r))
  | .frame n fr body => r.frame n fr (body.map (Admin.reconstruct r))
  | .trap => r.trap

@[simp] theorem Admin.reconstruct_foreign (r : Reconstruction I) (i : I) :
    (Admin.foreign i).reconstruct r = i := by simp [Admin.reconstruct]

/-- A suffix containing any full-standard syntax has an exact projection. -/
theorem reconstruct_foreign_suffix (r : Reconstruction I) (code : List (Admin I)) (suffix : List I) :
    ((code ++ suffix.map Admin.foreign).map (Admin.reconstruct r)) =
      code.map (Admin.reconstruct r) ++ suffix := by
  simp [List.map_map, Function.comp_def]

end Applications.Wasm
