import Applications.Wasm.Serialize
import Examples.WasmCircuit

set_option maxRecDepth 10000

namespace Examples.WasmBinary
open Applications.Wasm Applications.Wasm.Binary Applications.Wasm.Lowering
open Applications.Circuits FirstOrderCompiler

/-- Independently calculated Core header and four sections for an empty function. -/
def unitBytes : Bytes :=
  [0,97,115,109,1,0,0,0, 1,4,1,96,0,0, 3,2,1,0,
   7,7,1,3,114,117,110,0,0, 10,4,1,2,0,11]

def unitModule : Module := assemble (Circuit.identity (a := .unit))

theorem unit_serialized : unitModule.serialize = some unitBytes := by decide

theorem unit_decodes : ModuleBytes unitModule unitBytes :=
  Module.serialize_correct _ unit_serialized

example (s : Store F O) : ModuleBytes unitModule unitBytes ∧
    (unitModule.instantiate s).2.export "run" = some (.func s.funcs.length) ∧
    outside (unitModule.instantiate s).1 ([.invoke s.funcs.length] : List (Admin String)) = 0 ∧
    ([.invoke s.funcs.length] : List (Admin String)) ≠ [.trap] ∧
    Steps (I := String) (unitModule.instantiate s).1 dummyFrame [.invoke s.funcs.length] dummyFrame [] :=
  serialize_invoke_correct s (Circuit.identity (a := .unit)) () unit_serialized (.refl _ _)

example : (u32 127).map Subtype.val = some [127] := by decide
example : (u32 128).map Subtype.val = some [128,1] := by decide
example : (u32 16384).map Subtype.val = some [128,128,1] := by decide
example : (u32 (2^32-1)).map Subtype.val = some [255,255,255,255,15] := by decide
example : (u32 (2^32)).map Subtype.val = none := by decide
example : (s32 (-1)).map Subtype.val = some [127] := by decide
example : (s32 (-64)).map Subtype.val = some [64] := by decide
example : (s32 (-65)).map Subtype.val = some [191,127] := by decide
example : (s32 64).map Subtype.val = some [192,0] := by decide
example : (s32 (-2147483648)).map Subtype.val = some [128,128,128,128,120] := by decide
example : (s32 2147483647).map Subtype.val = some [255,255,255,255,7] := by decide
example : (s32 2147483648).map Subtype.val = none := by decide
example : (s32 (-2147483649)).map Subtype.val = none := by decide
example : (instruction (.get 128)).map Subtype.val = some [32,128,1] := by decide
example : (instruction (.const (0x80000000#32))).map Subtype.val =
    some [65,128,128,128,128,120] := by decide
example : (instruction (.const (0xffffffff#32))).map Subtype.val = some [65,127] := by decide

/-- A length of 128 is measured in encoded bytes, requiring a two-byte size. -/
example : ((sized (fun b : Bytes => some ⟨b, rfl⟩) (List.replicate 128 0)) :
    Option (Encoded (Sized (fun a b => a = b)) (List.replicate 128 0))).map Subtype.val =
    some ([128,1]++List.replicate 128 0) := by decide

example : (locals [.i64,.i32,.externref]).map Subtype.val = some [3,1,126,1,127,1,111] := by decide

def selectorModule : Module := assemble (Words.selector 32)
def nestedModule : Module := assemble (FRPSpec.FiniteSum.lower Examples.WasmCircuit.NestedCase.source)
def delayProgram : FRPSpec.Indefinite.Program .base .base (.prod .base .base) :=
  (FRPSpec.Indefinite.Program.delay false).seq (FRPSpec.Indefinite.Program.delay false)
def delayModule : Module := assemble delayProgram.body

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem selector_serializable : selectorModule.serialize.isSome = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem nested_serializable : nestedModule.serialize.isSome = true := by decide +kernel

theorem delay_serializable : delayModule.serialize.isSome = true := by decide

/-- Existence supplies actual bytes and their independently specified decoding. -/
theorem serialized_exists (m : Module) (h : m.serialize.isSome = true) :
    ∃ bytes, m.serialize = some bytes ∧ ModuleBytes m bytes := by
  cases he : m.serialize with
  | none => simp [he] at h
  | some bytes => exact ⟨bytes, rfl, m.serialize_correct he⟩

example : ∃ bytes, selectorModule.serialize = some bytes ∧ ModuleBytes selectorModule bytes :=
  serialized_exists _ selector_serializable
example : ∃ bytes, nestedModule.serialize = some bytes ∧ ModuleBytes nestedModule bytes :=
  serialized_exists _ nested_serializable
example : ∃ bytes, delayModule.serialize = some bytes ∧ ModuleBytes delayModule bytes :=
  serialized_exists _ delay_serializable

end Examples.WasmBinary
