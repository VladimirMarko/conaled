import Applications.Wasm.Serialize

/-! Composition across the external runtime boundary. These hypotheses describe
completed invocations; they do not promise availability or resource admission. -/
namespace Applications.Wasm.Artifacts
open FirstOrderCompiler Applications.Circuits Lowering

/-- Execution of the closed module in an empty ambient store. -/
def StandardRun (m : Module) (input output : List Value) : Prop :=
  Steps (I := Empty) (m.instantiate (⟨[], ()⟩ : Store Empty Unit)).1 dummyFrame
    (values input ++ [.invoke 0]) dummyFrame (values output)

/-- External engine conformance, independent of file IO and host marshalling.
Only successful engine observations are constrained. Refusal is permitted. -/
def RuntimeConforms (engine : ByteArray → List Value → List Value → Prop) : Prop :=
  ∀ m bytes input expected actual,
    Binary.ModuleBytes m bytes.data.toList → StandardRun m input expected →
    engine bytes input actual → actual = expected

/-- Serialization and source execution meet at the same module and exact bytes. -/
theorem serialized_source (c : Circuit a b) (x : Val Bool a)
    (serialized : (assemble c).serializeArray = some bytes) :
    Binary.ModuleBytes (assemble c) bytes.data.toList ∧
    StandardRun (assemble c) (ABI.encode x) (ABI.encode (c.execute x)) :=
  ⟨Module.serializeArray_correct _ serialized, invoke_compiled (⟨[], ()⟩ : Store Empty Unit) c x⟩

/-- File fidelity and faithful host marshalling remain separate from runtime
conformance. The engine relation witnesses a completed invocation; exceptions,
refusals and interruptions do not supply that premise. -/
theorem host_result (engine : ByteArray → List Value → List Value → Prop)
    (conforms : RuntimeConforms engine) (c : Circuit a b) (x : Val Bool a)
    (serialized : (assemble c).serializeArray = some emitted)
    (file_fidelity : loaded = emitted)
    (faithful_marshalling : engine loaded (ABI.encode x) observed) :
    observed = ABI.encode (c.execute x) := by
  obtain ⟨binary, run⟩ := serialized_source c x serialized
  subst loaded
  exact conforms _ _ _ _ _ binary run faithful_marshalling

/-- The same boundary preserves both the returned value and continuation state. -/
theorem stateful_result (engine : ByteArray → List Value → List Value → Prop)
    (conforms : RuntimeConforms engine) (p : FRPSpec.Indefinite.Program a b state)
    (input : Val Bool a) (current : Val Bool state)
    (serialized : (assemble p.body).serializeArray = some emitted)
    (file_fidelity : loaded = emitted)
    (faithful_marshalling : engine loaded (ABI.encode (a := .prod a state) (input,current)) observed) :
    observed = ABI.encode (a := .prod b state) (p.meaning.step (input,current)) := by
  have result := host_result engine conforms p.body (input,current) serialized file_fidelity faithful_marshalling
  rw [Circuit.execute_correct] at result
  exact result

end Applications.Wasm.Artifacts
