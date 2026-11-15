import Applications.Wasm.Serialize
import Examples.WasmCircuit

open Applications.Wasm Applications.Wasm.Lowering Applications.Circuits

private def twoDelay : FRPSpec.Indefinite.Program .base .base (.prod .base .base) :=
  (FRPSpec.Indefinite.Program.delay false).seq (FRPSpec.Indefinite.Program.delay false)

/-- Deterministic production artifacts use the proved native encoder directly. -/
def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: WasmEmit.lean OUTPUT_DIRECTORY")
  IO.FS.createDirAll directory
  let modules : List (String × Applications.Wasm.Module) := [
    ("selector32", assemble (Words.selector 32)),
    ("nested", assemble (FRPSpec.FiniteSum.lower Examples.WasmCircuit.NestedCase.source)),
    ("two-delay", assemble twoDelay.body),
    ("unit", assemble (Circuit.identity (a := .unit))),
    ("not", assemble (.gate (.not 0)))]
  for (name, m) in modules do
    let some bytes := m.serializeArray | throw (IO.userError s!"serialization refused: {name}")
    IO.FS.writeBinFile (System.FilePath.mk directory / s!"{name}.wasm") bytes
    IO.println s!"{name}: {bytes.size} bytes"
