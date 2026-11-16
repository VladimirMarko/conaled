import Applications.Wasm.Artifacts

/-! A concrete packed word client of the selected standard Wasm subset.
The source meaning and Boolean codecs remain those of `Circuits.Words`.
No mixed-sort circuit language or automatic representation optimizer is added. -/
namespace Applications.Wasm.PackedWords
open Applications.Circuits Words FirstOrderCompiler

abbrev Word := BitVec 32
abbrev Input := Bool × (Word × Word)
abbrev Output := Word × (Word × Word)

def input (tag : Bool) (x y : Word) : List Value :=
  [.i32 (NativeI32.encodeTag tag), .i32 x, .i32 y]

def output (r : Output) : List Value := [.i32 r.1, .i32 r.2.1, .i32 r.2.2]

def decodeInput : List Value → Option Input
  | [.i32 tag, .i32 x, .i32 y] => (NativeI32.decodeTag tag).map (fun b => (b,(x,y)))
  | _ => none

def decodeOutput : List Value → Option Output
  | [.i32 z, .i32 x, .i32 y] => some (z,(x,y))
  | _ => none

@[simp] theorem decode_input (tag : Bool) (x y : Word) :
    decodeInput (input tag x y) = some (tag,(x,y)) := by
  simp [decodeInput, input, NativeI32.decodeTag_iff]

@[simp] theorem decode_output (r : Output) : decodeOutput (output r) = some r := by
  rcases r with ⟨z,x,y⟩; rfl

/-- Admission is exact, including arity, i32 types and canonical tag. -/
theorem decodeInput_iff (raw : List Value) (tag : Bool) (x y : Word) :
    decodeInput raw = some (tag,(x,y)) ↔ raw = input tag x y := by
  rcases raw with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
  all_goals try simp [decodeInput, input]
  cases a <;> cases b <;> cases c <;>
    simp [Option.map_eq_some_iff, NativeI32.decodeTag_iff]
  cases tag <;> simp

/-- Every admitted output is precisely the complete ordered three-word encoding. -/
theorem decodeOutput_iff (raw : List Value) (r : Output) :
    decodeOutput raw = some r ↔ raw = output r := by
  rcases r with ⟨z,x,y⟩
  rcases raw with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
  all_goals try simp [decodeOutput, output]
  cases a <;> cases b <;> cases c <;> simp

/-- Native numerical laws connect the new opcode to the prior packed comparison. -/
theorem add_native (x y : Word) : BinOp.eval .add x y = NativeI32.add x y :=
  (NativeI32.add_correct x y).symm

/-- Actual instructions, including ordered result loads and all scratch writes. -/
def body : List Instr :=
  [.get 1,.get 2,.binary .add,.set 3, .get 1,.get 2,.binary .xor,.set 4,
   .get 3,.get 4,.get 0,.select,.set 5, .get 5,.get 1,.get 2]

def selectorModule : Module :=
  ⟨⟨List.replicate 3 .i32,List.replicate 3 .i32⟩,List.replicate 3 .i32,body⟩

def rawResult (tag x y : Word) : Word := Wasm.select (x+y) (x ^^^ y) tag

theorem rawResult_correct (tag : Bool) (x y : Word) :
    rawResult (NativeI32.encodeTag tag) x y = (meaning tag x y).1 := by
  change NativeI32.select (x+y) (x ^^^ y) (NativeI32.encodeTag tag) = _
  rw [NativeI32.select_correct]
  rfl

/-- The top-first evaluator returns the reverse of the standard result order. -/
theorem body_eval (mi : ModuleInstance) (tag x y : Word) :
    evalCode body ⟨[.i32 tag,.i32 x,.i32 y,.i32 0,.i32 0,.i32 0],mi⟩ [] =
      some (⟨[.i32 tag,.i32 x,.i32 y,.i32 (x+y),.i32 (x ^^^ y),
        .i32 (rawResult tag x y)],mi⟩,
        [.i32 y,.i32 x,.i32 (rawResult tag x y)]) := by rfl

theorem validates : selectorModule.validate = true := by decide

theorem valid : selectorModule.Valid := selectorModule.validate_sound validates

/-- Complete invocation, for arbitrary ambient store and every canonical input. -/
theorem invoke (s : Store F O) (tag : Bool) (x y : Word) :
    Steps (I := I) (selectorModule.instantiate s).1 dummyFrame
      (values (input tag x y) ++ [.invoke s.funcs.length]) dummyFrame
      (values (output (meaning tag x y))) := by
  have bodyRun := evalCode_steps (I := I) (selectorModule.instantiate s).1 body
    _ _ [] _ (body_eval (selectorModule.instance s.funcs.length) (NativeI32.encodeTag tag) x y)
  simp only [List.reverse_nil, values, List.map_nil, List.nil_append] at bodyRun
  rw [rawResult_correct] at bodyRun
  apply invoke_of_body _ _ (selectorModule.function s.funcs.length) _ _ _
    (Module.instantiate_lookup _ _) (by rfl) (by rfl)
  exact bodyRun

theorem entry (s : Store F O) (tag : Bool) (x y : Word) :
    (selectorModule.instantiate s).2.export "run" = some (.func s.funcs.length) ∧
    externalInvoke (I := I) (selectorModule.instantiate s).1 s.funcs.length (input tag x y) =
      some (dummyFrame, values (input tag x y) ++ [.invoke s.funcs.length]) := by
  refine ⟨Module.export_run _ _, ?_⟩
  exact externalInvoke_generated _ _ _ _ (Module.instantiate_lookup _ _) rfl

/-- Every alternative finite path stays in the selected rule domain, cannot trap,
and can finish with all three words. General `Step.no_infinite` also applies. -/
theorem invocation_safe (s : Store F O) (tag : Bool) (x y : Word)
    (path : Steps (I := I) (selectorModule.instantiate s).1 dummyFrame
      (values (input tag x y) ++ [.invoke s.funcs.length]) fr code) :
    outside (selectorModule.instantiate s).1 code = 0 ∧ code ≠ [.trap] ∧
    Steps (selectorModule.instantiate s).1 fr code dummyFrame (values (output (meaning tag x y))) := by
  have clean : traps (values (I := I) (input tag x y) ++ [.invoke s.funcs.length]) = 0 := by
    rw [traps_append, traps_values]
    simp [traps, Admin.traps]
  have domain : outside (selectorModule.instantiate s).1
      (values (I := I) (input tag x y) ++ [.invoke s.funcs.length]) = 0 := by
    rw [outside_append, outside_values]
    simp [outside, Admin.outside, Module.instantiate_lookup]
  exact ⟨Nat.eq_zero_of_le_zero (domain ▸ path.outside_le),path.no_trap clean,
    (invoke s tag x y).remaining clean path⟩

/-- Source-level adapters preserve all three output words. -/
def unpackOutput (r : Output) : Bits 32 × (Bits 32 × Bits 32) :=
  (NativeI32.unpack r.1,(NativeI32.unpack r.2.1,NativeI32.unpack r.2.2))
def packOutput (r : Bits 32 × (Bits 32 × Bits 32)) : Output :=
  (NativeI32.pack r.1,(NativeI32.pack r.2.1,NativeI32.pack r.2.2))

@[simp] theorem pack_unpack_output (r : Output) : packOutput (unpackOutput r) = r := by
  simp [packOutput, unpackOutput]
@[simp] theorem unpack_pack_output (r : Bits 32 × (Bits 32 × Bits 32)) :
    unpackOutput (packOutput r) = r := by simp [packOutput, unpackOutput]

theorem routes_agree (tag : Bool) (x y : Word) :
    (Words.selector 32).execute (tag,(Words.encode x,Words.encode y)) =
      unpackOutput (meaning tag x y) := by
  exact Lowering.word_result tag x y

/-- Both actual modules execute the same full source result, at their own ABIs. -/
theorem both_routes (tag : Bool) (x y : Word) :
    Artifacts.StandardRun selectorModule (input tag x y) (output (meaning tag x y)) ∧
    Artifacts.StandardRun (Lowering.assemble (Words.selector 32))
      (ABI.encode (a := .prod .base (.prod (shape 32) (shape 32))) (tag,(Words.encode x,Words.encode y)))
      (ABI.encode (a := .prod (shape 32) (.prod (shape 32) (shape 32))) (unpackOutput (meaning tag x y))) :=
  ⟨invoke (⟨[],()⟩ : Store Empty Unit) tag x y,
    Lowering.word_source (⟨[],()⟩ : Store Empty Unit) tag x y⟩

/-- Native bytes and standard invocation meet at the same complete observation. -/
theorem serialized (tag : Bool) (x y : Word)
    (h : selectorModule.serializeArray = some bytes) :
    Binary.ModuleBytes selectorModule bytes.data.toList ∧
    Artifacts.StandardRun selectorModule (input tag x y) (output (meaning tag x y)) :=
  ⟨selectorModule.serializeArray_correct h,invoke (⟨[],()⟩ : Store Empty Unit) tag x y⟩

theorem host_result (engine : ByteArray → List Value → List Value → Prop)
    (conforms : Artifacts.RuntimeConforms engine) (tag : Bool) (x y : Word)
    (h : selectorModule.serializeArray = some emitted) (fidelity : loaded = emitted)
    (marshal : engine loaded (input tag x y) observed) :
    observed = output (meaning tag x y) := by
  obtain ⟨binary,run⟩ := serialized tag x y h
  subst loaded
  exact conforms _ _ _ _ _ binary run marshal

/-- Syntax counts cover the emitted body, not adapters or engine memory. -/
theorem profile : selectorModule.body.length = 16 ∧
    selectorModule.type.params.length = 3 ∧ selectorModule.locals.length = 3 ∧
    selectorModule.type.results.length = 3 ∧ Lowering.scanStack selectorModule.body 0 = (3,3) := by decide

/-- Every successfully executed prefix respects the three-value operand bound. -/
theorem prefix_stack_bound (first rest : List Instr) (split : first ++ rest = body)
    (h : evalCode first fr [] = some (after,stack)) : stack.length ≤ 3 := by
  have bound := Lowering.eval_prefix_bound first rest h
  rw [split] at bound
  exact bound


/-- Counted codecs execute the same recursive conversions, charging one bit
visit per recursive step. These are logical work units, not host CPU cycles. -/
def packCounted : {n : Nat} → Bits n → BitVec n × Nat
  | 0, _ => (0,0)
  | _+1, (b,bs) => let r := packCounted bs; (r.1.concat b,r.2+1)

def unpackCounted : {n : Nat} → BitVec n → Bits n × Nat
  | 0, _ => ((),0)
  | n+1, x => let r := unpackCounted (x.extractLsb' 1 n); ((x.getLsbD 0,r.1),r.2+1)

theorem packCounted_correct (bs : Bits n) : packCounted bs = (Words.decode bs,n) := by
  induction n with
  | zero => cases bs; rfl
  | succ n ih => cases bs; simp [packCounted, Words.decode, ih]

theorem unpackCounted_correct (x : BitVec n) : unpackCounted x = (Words.encode x,n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [unpackCounted, Words.encode, ih]

/-- Boolean input conversion visits both operands; the canonical tag is retained. -/
def packInputs (tag : Bool) (x y : Bits 32) : Input × Nat :=
  let px := packCounted x
  let py := packCounted y
  ((tag,(px.1,py.1)),px.2+py.2)

/-- Return conversion visits every bit of all three result words. -/
def unpackOutputs (r : Output) : (Bits 32 × (Bits 32 × Bits 32)) × Nat :=
  let pz := unpackCounted r.1
  let px := unpackCounted r.2.1
  let py := unpackCounted r.2.2
  ((pz.1,(px.1,py.1)),pz.2+px.2+py.2)

theorem packInputs_correct (tag : Bool) (x y : Bits 32) :
    packInputs tag x y = ((tag,(Words.decode x,Words.decode y)),64) := by
  simp [packInputs, packCounted_correct]

theorem unpackOutputs_correct (r : Output) :
    unpackOutputs r = (unpackOutput r,96) := by
  simp [unpackOutputs, unpackCounted_correct, unpackOutput, NativeI32.unpack]

/-- Independent byte layout: 10-byte type payload, one function and export,
then a 37-byte body with three singleton local groups and 29 instruction bytes. -/
def selectorBytes : Binary.Bytes :=
  [0,97,115,109,1,0,0,0,
   1,10,1,96,3,127,127,127,3,127,127,127,
   3,2,1,0, 7,7,1,3,114,117,110,0,0,
   10,39,1,37,3,1,127,1,127,1,127,
   32,1,32,2,106,33,3,32,1,32,2,115,33,4,
   32,3,32,4,32,0,27,33,5,32,5,32,1,32,2,11]

theorem selector_serialized : selectorModule.serialize = some selectorBytes := by decide

theorem serialized_length : selectorBytes.length = 74 := by decide

/-- Sizes come from the same encoder used for production artifacts. -/
theorem encoded_sizes :
    (Binary.sequence Binary.instruction body).map (fun b => b.val.length) = some 29 ∧
    (Binary.functionBody (selectorModule.locals,body)).map (fun b => b.val.length) = some 37 := by decide

/-- The largest referenced local plus one accounts for all six live local slots. -/
theorem local_bound :
    (body.map (fun i => match i with | .get n | .set n => n+1 | _ => 0)).foldl max 0 = 6 := by decide

/-- Caller-requested alternatives for this one source client. -/
inductive Representation where | boolean | packed deriving DecidableEq, Repr

def Representation.module : Representation → Module
  | .boolean => Lowering.assemble (Words.selector 32)
  | .packed => selectorModule

/-- Limits and serialization refusal remain explicit; no automatic winner. -/
def admitWithinLimits (r : Representation) (limits : Limits) : Option ByteArray :=
  if r.module.withinLimits limits then r.module.serializeArray else none

theorem admitWithinLimits_sound (r : Representation) (limits : Limits) (h : admitWithinLimits r limits = some bytes) :
    r.module.Valid ∧ Binary.ModuleBytes r.module bytes.data.toList := by
  unfold admitWithinLimits at h
  split at h
  next within => exact ⟨r.module.withinLimits_valid limits within,r.module.serializeArray_correct h⟩
  next => contradiction

end Applications.Wasm.PackedWords
