import Applications.Wasm.Artifacts

/-! Checked clients of the source/serializer/runtime composition. -/
namespace Examples.WasmArtifacts
open Applications.Wasm Applications.Wasm.Lowering Applications.Wasm.Artifacts
open Applications.Circuits FirstOrderCompiler

/-- Width 32 retains the selected word and both inputs, hence all 96 bits. -/
theorem selector32_result (engine : ByteArray → List Value → List Value → Prop)
    (conforms : RuntimeConforms engine) (tag : Bool) (x y : BitVec 32)
    (serialized : (assemble (Words.selector 32)).serializeArray = some emitted)
    (fidelity : loaded = emitted)
    (marshal : engine loaded
      (ABI.encode (a := .prod .base (.prod (Words.shape 32) (Words.shape 32)))
        (tag,(Words.encode x,Words.encode y))) observed) :
    observed = ABI.encode (a := .prod (Words.shape 32) (.prod (Words.shape 32) (Words.shape 32)))
      (Words.encode (if tag then x+y else x ^^^ y),(Words.encode x,Words.encode y)) := by
  have result := host_result engine conforms (Words.selector 32)
    (tag,(Words.encode x,Words.encode y)) serialized fidelity marshal
  rw [word_result] at result
  exact result

private def twoDelay : FRPSpec.Indefinite.Program .base .base (.prod .base .base) :=
  (FRPSpec.Indefinite.Program.delay false).seq (FRPSpec.Indefinite.Program.delay false)

/-- Every successful admitted step shifts both retained bits. Initialization
and commit-after-success are obligations of the tested host adapter. -/
example (engine : ByteArray → List Value → List Value → Prop)
    (conforms : RuntimeConforms engine) (x old recent : Bool)
    (serialized : (assemble twoDelay.body).serializeArray = some emitted)
    (fidelity : loaded = emitted)
    (marshal : engine loaded (ABI.encode (a := .prod .base (.prod .base .base))
      (x,(old,recent))) observed) :
    observed = ABI.encode (a := .prod .base (.prod .base .base)) (recent,(x,old)) :=
  stateful_result engine conforms twoDelay x (old,recent) serialized fidelity marshal

end Examples.WasmArtifacts
