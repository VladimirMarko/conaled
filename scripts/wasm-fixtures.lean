import Examples.WasmBinary
import Applications.Wasm.WordContinuation

open Applications.Wasm Applications.Wasm.Lowering Applications.Circuits
open FirstOrderCompiler

private def twoDelay : FRPSpec.Indefinite.Program .base .base (.prod .base .base) :=
  (FRPSpec.Indefinite.Program.delay false).seq (FRPSpec.Indefinite.Program.delay false)

def main : IO Unit := do
  let fixtures : List (String × Module) :=
    [("unit", Examples.WasmBinary.unitModule),
     ("negative", ⟨⟨[],[.i32]⟩,[],[.const (0xffffffff#32)]⟩),
     ("highbit", ⟨⟨[],[.i32]⟩,[],[.const (0x80000000#32)]⟩),
     ("selector32", assemble (Words.selector 32)),
     ("selector32-packed", PackedWords.selectorModule),
     ("word-delay-boolean", WordContinuation.booleanModule),
     ("word-delay-packed", WordContinuation.packedModule),
     ("nested", assemble (FRPSpec.FiniteSum.lower Examples.WasmCircuit.NestedCase.source)),
     ("two-delay", assemble twoDelay.body),
     ("index128", ⟨⟨List.replicate 129 .i32,[.i32]⟩,[],[.get 128]⟩)]
  for (name, m) in fixtures do
    let some bytes := m.serialize | throw (IO.userError s!"serialization failed: {name}")
    IO.println (Lean.Json.mkObj [("name", Lean.toJson name), ("bytes", Lean.toJson (bytes.map UInt8.toNat))]).compress
