import Applications.Wasm.Binary
import Applications.Wasm.Correctness

/-! Native serialization with erased grammar witnesses. Lengths are measured
on encoded payloads and checked before conversion to u32. -/
namespace Applications.Wasm.Binary

abbrev Encoded (R : α → Bytes → Prop) (a : α) := { b : Bytes // R a b }

/-- Fuel limits physical LEB128 length; the grammar checks the remaining width. -/
def unsigned : (fuel width n : Nat) → Option (Encoded (Unsigned width) n)
  | 0, _, _ => none
  | fuel+1, w, n =>
    if hd : n < 128 then
      if hb : n < 2^w then some ⟨[UInt8.ofNat n], .last w n hd hb⟩ else none
    else if hw : 7 < w then do
      let tail ← unsigned fuel (w-7) (n/128)
      have heq : 128*(n/128)+n%128 = n := by omega
      return ⟨UInt8.ofNat (128+n%128)::tail.val,
        by simpa only [heq] using Unsigned.more w (n%128) (n/128) hw (Nat.mod_lt _ (by decide)) tail.property⟩
    else none

def u32 (n : Nat) : Option (Encoded (Unsigned 32) n) := unsigned 5 32 n

/-- Signed division uses floor quotient and a nonnegative base-128 remainder. -/
def signed : (fuel width : Nat) → (n : Int) → Option (Encoded (Signed width) n)
  | 0, _, _ => none
  | fuel+1, w, n =>
    if hp : 0 ≤ n ∧ n < 64 then
      if hb : n.toNat < 2^(w-1) then
        have hn : (n.toNat : Int) = n := Int.toNat_of_nonneg hp.1
        some ⟨[UInt8.ofNat n.toNat], hn ▸ Signed.positive w n.toNat (by omega) hb⟩
      else none
    else if hn : -64 ≤ n ∧ n < 0 then
      if hb : (128 : Int)-2^(w-1) ≤ (n+128).toNat then
        have heq : ((n+128).toNat : Int)-128 = n := by omega
        some ⟨[UInt8.ofNat (n+128).toNat], by simpa only [heq] using Signed.negative w (n+128).toNat (by omega) (by omega) hb⟩
      else none
    else if hw : 7 < w then do
      let tail ← signed fuel (w-7) (n/128)
      have hd : (n%128).toNat < 128 := by omega
      have heq : 128*(n/128)+((n%128).toNat : Int) = n := by omega
      return ⟨UInt8.ofNat (128+(n%128).toNat)::tail.val,
        by simpa only [heq] using Signed.more w (n%128).toNat (n/128) hw hd tail.property⟩
    else none

def s32 (n : Int) : Option (Encoded (Signed 32) n) := signed 5 32 n

def sequence (encode : (a : α) → Option (Encoded R a)) :
    (as : List α) → Option (Encoded (Sequence R) as)
  | [] => some ⟨[], .nil⟩
  | a::as => do
    let head ← encode a
    let tail ← sequence encode as
    some ⟨head.val++tail.val, .cons head.property tail.property⟩

def vector (encode : (a : α) → Option (Encoded R a)) (as : List α) :
    Option (Encoded (Vector R) as) := do
  let count ← u32 as.length
  let items ← sequence encode as
  some ⟨count.val++items.val, .intro count.property items.property⟩

def valType : (t : ValueType) → Encoded ValType t
  | .i32 => ⟨[0x7f], .i32⟩
  | .i64 => ⟨[0x7e], .i64⟩
  | .f32 => ⟨[0x7d], .f32⟩
  | .f64 => ⟨[0x7c], .f64⟩
  | .v128 => ⟨[0x7b], .v128⟩
  | .funcref => ⟨[0x70], .funcref⟩
  | .externref => ⟨[0x6f], .externref⟩

def functionType (t : FuncType) : Option (Encoded FunctionType t) := do
  let ps ← vector (fun t => some (valType t)) t.params
  let rs ← vector (fun t => some (valType t)) t.results
  some ⟨0x60::(ps.val++rs.val), .intro ps.property rs.property⟩

def instruction : (i : Instr) → Option (Encoded Instruction i)
  | .const v => do
    let n ← s32 v.toInt
    some ⟨0x41::n.val, by simpa using Instruction.const n.property⟩
  | .get index => do
    let n ← u32 index
    some ⟨0x20::n.val, .get n.property⟩
  | .set index => do
    let n ← u32 index
    some ⟨0x21::n.val, .set n.property⟩
  | .eqz => some ⟨[0x45], .eqz⟩
  | .binary .and => some ⟨[0x71], .and⟩
  | .binary .or => some ⟨[0x72], .or⟩
  | .binary .xor => some ⟨[0x73], .xor⟩
  | .binary .add => some ⟨[0x6a], .add⟩
  | .select => some ⟨[0x1b], .select⟩

def expression (is : List Instr) : Option (Encoded Expression is) := do
  let code ← sequence instruction is
  some ⟨code.val++[0x0b], .intro code.property⟩

def localGroup (g : Nat × ValueType) : Option (Encoded LocalGroup g) := do
  let n ← u32 g.1
  let t := valType g.2
  some ⟨n.val++t.val, .intro n.property t.property⟩

theorem singleton_flatten (ls : List ValueType) :
    ((ls.map fun t => (1,t)).flatMap fun g => List.replicate g.1 g.2) = ls := by
  induction ls with
  | nil => rfl
  | cons t ts ih => simpa using congrArg (List.cons t) ih

/-- Singleton groups preserve arbitrary local-type order without a compression pass. -/
def locals (ls : List ValueType) : Option (Encoded Locals ls) := do
  if hb : ls.length < 2^32 then
    let groups ← vector localGroup (ls.map fun t => (1,t))
    have flatten := singleton_flatten ls
    some ⟨groups.val, by
      have h := Locals.intro groups.property (by simpa only [flatten] using hb)
      simpa only [flatten] using h⟩
  else none

def sized (encode : (a : α) → Option (Encoded R a)) (a : α) :
    Option (Encoded (Sized R) a) := do
  let payload ← encode a
  let size ← u32 payload.val.length
  some ⟨size.val++payload.val, .intro size.property payload.property⟩

def functionBody (body : List ValueType × List Instr) :
    Option (Encoded FunctionBody body) := do
  let ls ← locals body.1
  let is ← expression body.2
  some ⟨ls.val++is.val, .intro ls.property is.property⟩

def runName : Encoded Name "run" := ⟨[3,0x72,0x75,0x6e], .run (.last 32 3 (by decide) (by decide))⟩

def runExport : Encoded Export ("run",0) :=
  ⟨[3,0x72,0x75,0x6e,0,0], .func runName.property (.last 32 0 (by decide) (by decide))⟩

def exportEntry (e : String × Nat) : Option (Encoded Export e) :=
  if h : e = ("run",0) then
    some ⟨runExport.val, by simpa only [h] using runExport.property⟩
  else none

def encodeSection (id : UInt8) (encode : (a : α) → Option (Encoded R a)) (a : α) :
    Option (Encoded (Section id R) a) := do
  let payload ← sized encode a
  some ⟨id::payload.val, .intro payload.property⟩

def module (m : Module) : Option (Encoded ModuleBytes m) := do
  let types ← encodeSection 1 (vector functionType) [m.type]
  let functions ← encodeSection 3 (vector u32) [0]
  let exports ← encodeSection 7 (vector exportEntry) [("run",0)]
  let code ← encodeSection 10 (vector (sized functionBody)) [(m.locals,m.body)]
  some ⟨[0,0x61,0x73,0x6d,1,0,0,0]++types.val++functions.val++exports.val++code.val,
    .intro types.property functions.property exports.property code.property⟩

end Applications.Wasm.Binary

namespace Applications.Wasm

def Module.serialize (m : Module) : Option Binary.Bytes := (Binary.module m).map Subtype.val

theorem Module.serialize_correct (m : Module) (h : m.serialize = some bytes) :
    Binary.ModuleBytes m bytes := by
  obtain ⟨result, _, same⟩ := Option.map_eq_some_iff.mp h
  exact same ▸ result.property

/-- Native storage adapter. The list theorem names the exact bytes before IO. -/
def Module.serializeArray (m : Module) : Option ByteArray :=
  m.serialize.map fun bytes => ⟨bytes.toArray⟩

theorem Module.serializeArray_correct (m : Module) (h : m.serializeArray = some bytes) :
    Binary.ModuleBytes m bytes.data.toList := by
  obtain ⟨raw, encoded, same⟩ := Option.map_eq_some_iff.mp h
  subst bytes
  simpa using m.serialize_correct encoded

end Applications.Wasm

namespace Applications.Wasm.Lowering
open Applications.Circuits FirstOrderCompiler

/-- Source-to-bytes execution: serialization supplies exact decoding, while
`invoke_correct` supplies every reachable state's complete source result. -/
theorem serialize_invoke_correct (s : Store F O) (c : Circuit a b) (x : Val Bool a)
    (serialized : (assemble c).serialize = some bytes)
    (path : Steps (I := I) ((assemble c).instantiate s).1 dummyFrame
      (values (ABI.encode x) ++ [.invoke s.funcs.length]) fr code) :
    Binary.ModuleBytes (assemble c) bytes ∧
    ((assemble c).instantiate s).2.export "run" = some (.func s.funcs.length) ∧
    outside ((assemble c).instantiate s).1 code = 0 ∧ code ≠ [.trap] ∧
    Steps ((assemble c).instantiate s).1 fr code dummyFrame
      (values (ABI.encode (c.execute x))) :=
  ⟨Module.serialize_correct _ serialized, Module.export_run _ _, invoke_correct s c x path⟩

end Applications.Wasm.Lowering
