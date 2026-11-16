import Applications.Wasm.PackedWords

/-! Two delayed words with exact continuation transfer between two Wasm ABIs.
Migration happens only between completed ticks; pending publication is separate. -/
namespace Applications.Wasm.WordContinuation
open Applications.Circuits Words FirstOrderCompiler Progress Progress.Feedback

abbrev Word := BitVec 32
abbrev State := Word × Word
abbrev BooleanState := Bits 32 × Bits 32
abbrev Representation := PackedWords.Representation

/-- Independent source: add the current input to its twice-delayed value. -/
def source : Initialized Word Word State :=
  ⟨fun (x,recent,older) => (x+older,(x,recent)),(0x12345678,0xffffffff)⟩

def packState (s : BooleanState) : State := (NativeI32.pack s.1,NativeI32.pack s.2)
def unpackState (s : State) : BooleanState := (NativeI32.unpack s.1,NativeI32.unpack s.2)
@[simp] theorem pack_unpack (s : State) : packState (unpackState s) = s := by simp [packState,unpackState]
@[simp] theorem unpack_pack (s : BooleanState) : unpackState (packState s) = s := by simp [packState,unpackState]

/-- Reuse the existing initialized reactive composition, retaining exactly two words. -/
def delays := (FRPSpec.Indefinite.Program.delay (Words.encode source.initial.1)).seq
  (FRPSpec.Indefinite.Program.delay (Words.encode source.initial.2))

def booleanProgram : FRPSpec.Indefinite.Program (shape 32) (shape 32) (.prod (shape 32) (shape 32)) where
  initial := delays.initial
  body := .compose
    (.pair (.compose (Words.add 32) (.pair .first (.compose .first .second)))
      (.compose .second .second))
    (.pair .first delays.body)

theorem delay_step (x : Bits 32) (s : BooleanState) :
    delays.machine.step (x,s) = (s.2,(x,s.1)) := by rfl

/-- This body equation uses the public word-addition theorem and both codecs. -/
theorem boolean_step (x : Bits 32) (s : BooleanState) :
    booleanProgram.machine.step (x,s) =
      (Words.encode (Words.decode x + Words.decode s.2),(x,s.1)) := by
  change ((Words.add 32).execute (x,s.2),(x,s.1)) = _
  congr 1
  apply Words.decode_injective
  simp

def booleanMachine : Initialized Word Word BooleanState where
  initial := booleanProgram.initial
  step p := let r := booleanProgram.machine.step (Words.encode p.1,p.2); (Words.decode r.1,r.2)

theorem boolean_simulation (x : Word) (s : BooleanState) :
    (booleanMachine.step (x,s)).1 = (source.step (x,packState s)).1 ∧
    packState (booleanMachine.step (x,s)).2 = (source.step (x,packState s)).2 := by
  dsimp only [booleanMachine]
  rw [boolean_step]
  simp [source,packState,NativeI32.pack]

theorem initial_recovers : packState booleanMachine.initial = source.initial := by
  simp [booleanMachine,booleanProgram,delays,FRPSpec.Indefinite.Program.seq,
    FRPSpec.Indefinite.Program.delay,packState,NativeI32.pack]

/-- All finite suffixes, including empty, preserve outputs and the live continuation. -/
theorem finite_suffix (s : BooleanState) (xs : List Word) :
    (run booleanMachine.mealy s xs).1 = (run source.mealy (packState s) xs).1 ∧
    packState (run booleanMachine.mealy s xs).2 = (run source.mealy (packState s) xs).2 := by
  have h := run_related booleanMachine.mealy source.mealy Eq
    (fun b w => packState b = w) Eq
    (by intro x y b w hi hs; subst y; subst w; exact boolean_simulation x b)
    (List.forall₂_same.mpr (fun _ _ => rfl) : List.Forall₂ Eq xs xs) (s := s) rfl
  exact ⟨by simpa only [List.forall₂_eq_eq_eq] using h.1,h.2⟩

/-- Reverse transfer starts from the supplied live state, not the original seed. -/
theorem reverse_suffix (s : State) (xs : List Word) :
    (run booleanMachine.mealy (unpackState s) xs).1 = (run source.mealy s xs).1 ∧
    packState (run booleanMachine.mealy (unpackState s) xs).2 = (run source.mealy s xs).2 := by
  simpa using finite_suffix (unpackState s) xs

theorem prefix_migration (s : BooleanState) (pre suffix : List Word) :
    (run booleanMachine.mealy s (pre ++ suffix)).1 =
      (run booleanMachine.mealy s pre).1 ++
      (run source.mealy (packState (run booleanMachine.mealy s pre).2) suffix).1 ∧
    packState (run booleanMachine.mealy s (pre ++ suffix)).2 =
      (run source.mealy (packState (run booleanMachine.mealy s pre).2) suffix).2 := by
  rw [run_append]
  have h := finite_suffix (run booleanMachine.mealy s pre).2 suffix
  exact ⟨congrArg ((run booleanMachine.mealy s pre).1 ++ ·) h.1,h.2⟩

/-- A round trip can happen after any live prefix and preserves every future suffix. -/
theorem round_trip (s : BooleanState) (pre suffix : List Word) :
    run booleanMachine.mealy (unpackState (packState (run booleanMachine.mealy s pre).2)) suffix =
      run booleanMachine.mealy (run booleanMachine.mealy s pre).2 suffix := by simp

theorem reverse_round_trip (s : State) (pre suffix : List Word) :
    run source.mealy (packState (unpackState (run source.mealy s pre).2)) suffix =
      run source.mealy (run source.mealy s pre).2 suffix := by simp

def encodeState : Representation → State → List Value
  | .boolean,s => ABI.encode (a := .prod (shape 32) (shape 32)) (unpackState s)
  | .packed,s => [.i32 s.1,.i32 s.2]

def decodeState : Representation → List Value → Option State
  | .boolean,raw => (ABI.decode (.prod (shape 32) (shape 32)) raw).map packState
  | .packed,[.i32 recent,.i32 older] => some (recent,older)
  | .packed,_ => none

theorem decodeState_iff (r : Representation) (raw : List Value) (s : State) :
    decodeState r raw = some s ↔ raw = encodeState r s := by
  cases r with
  | boolean =>
    simp only [decodeState,Option.map_eq_some_iff,encodeState]
    constructor
    · rintro ⟨b,hb,rfl⟩
      rw [unpack_pack]
      exact (ABI.decode_iff (a := .prod (shape 32) (shape 32)) raw b).1 hb
    · intro h
      exact ⟨unpackState s,(ABI.decode_iff (a := .prod (shape 32) (shape 32)) raw _).2 h,pack_unpack s⟩
  | packed =>
    rcases s with ⟨recent,older⟩
    rcases raw with _ | ⟨a,_ | ⟨b,_ | ⟨c,rest⟩⟩⟩
    all_goals try simp [decodeState,encodeState]
    cases a <;> cases b <;> simp

@[simp] theorem decode_encode (r : Representation) (s : State) :
    decodeState r (encodeState r s) = some s := (decodeState_iff r _ s).2 rfl

/-- Checked conversion is executable and refuses malformed source state. -/
def convertState (origin target : Representation) (raw : List Value) : Option (List Value) :=
  (decodeState origin raw).map (encodeState target)

@[simp] theorem convert_encoded (origin target : Representation) (s : State) :
    convertState origin target (encodeState origin s) = some (encodeState target s) := by
  simp [convertState]

theorem conversion_recovers (origin target : Representation) (raw next : List Value)
    (h : convertState origin target raw = some next) :
    convertState target origin next = some raw := by
  simp only [convertState,Option.map_eq_some_iff] at h
  obtain ⟨s,hs,rfl⟩ := h
  rw [convert_encoded,(decodeState_iff origin raw s).1 hs]

/-- A concrete owner stores its representation and executable encoded continuation. -/
structure Owner where
  representation : Representation
  raw : List Value

def Owner.logical (o : Owner) : Option State := decodeState o.representation o.raw

def prepare (o : Owner) (target : Representation) : Option Owner :=
  (convertState o.representation target o.raw).map (fun raw => ⟨target,raw⟩)

theorem prepare_preserves (o candidate : Owner) (target : Representation)
    (h : prepare o target = some candidate) : candidate.logical = o.logical := by
  simp only [prepare,convertState,Option.map_eq_some_iff] at h
  obtain ⟨raw,⟨s,hs,rfl⟩,rfl⟩ := h
  simp [Owner.logical,decode_encode,hs]

/-- Installation is gated by preparation and the final cancellation observation.
Loader/resource refusal is represented by a false ready flag, never by a new owner. -/
def transfer (o : Owner) (target : Representation) (ready publish : Bool) : Owner :=
  if ready && publish then (prepare o target).getD o else o

theorem transfer_preserves (o : Owner) (target : Representation) (ready publish : Bool) :
    (transfer o target ready publish).logical = o.logical := by
  unfold transfer
  split
  · cases h : prepare o target with
    | none => rfl
    | some candidate => exact prepare_preserves o candidate target h
  · rfl

theorem transfer_refused (o : Owner) (target : Representation) :
    transfer o target false publish = o ∧ transfer o target ready false = o := by
  simp [transfer]

/-- Counts scalar slots owned by this adapter, excluding host/engine allocations. -/
def stateSlots : Representation → Nat | .boolean => 64 | .packed => 2

def ownedStatePeak (origin target : Representation) : Nat :=
  3 * stateSlots origin + 3 * stateSlots target

/-- Named operations for valid owned state; host preparation remains an external operation. -/
inductive MigrationEvent where
  | snapshot (slots : Nat)
  | validateSource (slots : Nat)
  | convert (bits slots : Nat)
  | cloneInitial (slots : Nat)
  | hostPrepare (artifactBytes stateSlots : Nat)
  | copyActive (slots : Nat)
  | install
  | discardCandidate
  deriving DecidableEq, Repr

/-- An explicit schedule, not a measurement of engine execution or physical heap use.
`admitted` includes the pre-allocation budget/cancellation checks. `loaded` and
`publish` are observations at the two subsequent host boundaries. -/
def migrationTrace (origin target : Representation) (artifactBytes : Nat)
    (admitted loaded publish : Bool) : List MigrationEvent :=
  if admitted then
    [.snapshot (stateSlots origin), .validateSource (stateSlots origin),
     .convert (if origin = target then 0 else 64) (stateSlots target),
     .cloneInitial (stateSlots target), .hostPrepare artifactBytes (stateSlots target)] ++
    if loaded then [.copyActive (stateSlots target),
      if publish then .install else .discardCandidate] else [.discardCandidate]
  else []

/-- Sum a named operation's units without conflating validation, copies, and bit visits. -/
def eventTotal (weight : MigrationEvent → Nat) (events : List MigrationEvent) : Nat :=
  (events.map weight).sum

def copyWeight : MigrationEvent → Nat
  | .snapshot n | .cloneInitial n | .copyActive n => n
  | _ => 0

def validationWeight : MigrationEvent → Nat | .validateSource n => n | _ => 0
def conversionWeight : MigrationEvent → Nat | .convert bits _ => bits | _ => 0
def writeWeight : MigrationEvent → Nat | .convert _ slots => slots | _ => 0
def installationWeight : MigrationEvent → Nat | .install => 1 | _ => 0

theorem migration_accounting (origin target : Representation) (bytes : Nat)
    (admitted loaded publish : Bool) :
    let events := migrationTrace origin target bytes admitted loaded publish
    eventTotal copyWeight events = (if admitted then stateSlots origin + stateSlots target +
      (if loaded then stateSlots target else 0) else 0) ∧
    eventTotal validationWeight events = (if admitted then stateSlots origin else 0) ∧
    eventTotal conversionWeight events = (if admitted then (if origin = target then 0 else 64) else 0) ∧
    eventTotal writeWeight events = (if admitted then stateSlots target else 0) ∧
    eventTotal installationWeight events = (if admitted && loaded && publish then 1 else 0) := by
  cases origin <;> cases target <;> cases admitted <;> cases loaded <;> cases publish <;>
    simp [migrationTrace,eventTotal,copyWeight,validationWeight,conversionWeight,writeWeight,
      installationWeight,stateSlots]

/-- Decoration preserves the existing executable ownership transition. The schedule
assumes valid source ownership; malformed raw inputs are rejected by `prepare`. -/
def costedTransfer (o : Owner) (target : Representation) (bytes : Nat)
    (admitted loaded publish : Bool) : Owner × List MigrationEvent :=
  (transfer o target (admitted && loaded) publish,
   migrationTrace o.representation target bytes admitted loaded publish)

theorem costedTransfer_erases (o : Owner) (target : Representation) (bytes : Nat)
    (admitted loaded publish : Bool) :
    (costedTransfer o target bytes admitted loaded publish).1 =
      transfer o target (admitted && loaded) publish := rfl

theorem costedTransfer_preserves (o : Owner) (target : Representation) (bytes : Nat)
    (admitted loaded publish : Bool) :
    (costedTransfer o target bytes admitted loaded publish).1.logical = o.logical :=
  transfer_preserves o target _ _

theorem valid_preparation (origin target : Representation) (s : State) :
    prepare ⟨origin,encodeState origin s⟩ target = some ⟨target,encodeState target s⟩ := by
  simp [prepare,convert_encoded]

theorem transfer_encoded (origin target : Representation) (s : State) :
    transfer ⟨origin,encodeState origin s⟩ target true true =
      ⟨target,encodeState target s⟩ := by
  simp [transfer,valid_preparation]


/-- Admission counts the old retained artifact and two target adapter copies.
Worker/engine copies are outside this adapter byte bound. -/
def adapterByteBudget (oldBytes targetBytes : Nat) : Nat := oldBytes + 2 * targetBytes

theorem overlap_bound (origin target : Representation) : ownedStatePeak origin target ≤ 384 := by
  cases origin <;> cases target <;> decide

theorem cross_representation_overlap : ownedStatePeak .boolean .packed = 198 ∧
    ownedStatePeak .packed .boolean = 198 := by decide


def packedBody : List Instr := [.get 0,.get 2,.binary .add,.get 0,.get 1]
def packedModule : Module := ⟨⟨List.replicate 3 .i32,List.replicate 3 .i32⟩,[],packedBody⟩
def booleanModule : Module := Lowering.assemble booleanProgram.body

def packedInput (x : Word) (s : State) : List Value := [.i32 x,.i32 s.1,.i32 s.2]
def packedOutput (x : Word) (s : State) : List Value := [.i32 (x+s.2),.i32 x,.i32 s.1]

theorem packed_valid : packedModule.Valid := packedModule.validate_sound (by decide)
theorem boolean_valid : booleanModule.Valid := Lowering.assemble_valid _

theorem packed_invoke (store : Store F O) (x : Word) (s : State) :
    Steps (I := I) (packedModule.instantiate store).1 dummyFrame
      (values (packedInput x s) ++ [.invoke store.funcs.length]) dummyFrame (values (packedOutput x s)) := by
  apply invoke_of_body _ _ (packedModule.function store.funcs.length) _ _ _
    (Module.instantiate_lookup _ _) (by rfl) (by rfl)
  exact evalCode_steps _ packedBody
    ⟨packedInput x s,packedModule.instance store.funcs.length⟩
    ⟨packedInput x s,packedModule.instance store.funcs.length⟩ []
    [.i32 s.1,.i32 x,.i32 (x+s.2)] (by rfl)

theorem boolean_invoke (store : Store F O) (x : Word) (s : State) :
    Steps (I := I) (booleanModule.instantiate store).1 dummyFrame
      (values (ABI.encode (a := .prod (shape 32) (.prod (shape 32) (shape 32)))
        (Words.encode x,unpackState s)) ++ [.invoke store.funcs.length]) dummyFrame
      (values (ABI.encode (a := .prod (shape 32) (.prod (shape 32) (shape 32)))
        (Words.encode (source.step (x,s)).1,unpackState (source.step (x,s)).2))) := by
  have h := Lowering.invoke_compiled (I := I) store booleanProgram.body (Words.encode x,unpackState s)
  have eq := boolean_step (Words.encode x) (unpackState s)
  change booleanProgram.body.execute _ = _ at eq
  rw [eq] at h
  simpa [booleanModule,unpackState,NativeI32.unpack,source] using h

theorem packed_host_result (engine : ByteArray → List Value → List Value → Prop)
    (conforms : Artifacts.RuntimeConforms engine) (x : Word) (s : State)
    (serialized : packedModule.serializeArray = some emitted) (fidelity : loaded = emitted)
    (marshal : engine loaded (packedInput x s) observed) : observed = packedOutput x s := by
  subst loaded
  exact conforms _ _ _ _ _ (packedModule.serializeArray_correct serialized)
    (packed_invoke (⟨[],()⟩ : Store Empty Unit) x s) marshal

def module : Representation → Module
  | .boolean => booleanModule
  | .packed => packedModule

def encodeTick : Representation → Word → State → List Value
  | .boolean,x,s => ABI.encode (a := .prod (shape 32) (.prod (shape 32) (shape 32)))
      (Words.encode x,unpackState s)
  | .packed,x,s => packedInput x s

theorem invoke_complete (r : Representation) (store : Store F O) (x : Word) (s : State) :
    Steps (I := I) ((module r).instantiate store).1 dummyFrame
      (values (encodeTick r x s) ++ [.invoke store.funcs.length]) dummyFrame
      (values (encodeTick r (source.step (x,s)).1 (source.step (x,s)).2)) := by
  cases r with
  | boolean => exact boolean_invoke store x s
  | packed => exact packed_invoke store x s

/-- The generic safety laws apply to every reached state of either module. -/
theorem invocation_safe (r : Representation) (store : Store F O) (x : Word) (s : State)
    (path : Steps (I := I) ((module r).instantiate store).1 dummyFrame
      (values (encodeTick r x s) ++ [.invoke store.funcs.length]) fr code) :
    outside ((module r).instantiate store).1 code = 0 ∧ code ≠ [.trap] ∧
    Steps ((module r).instantiate store).1 fr code dummyFrame
      (values (encodeTick r (source.step (x,s)).1 (source.step (x,s)).2)) := by
  have clean : traps (values (I := I) (encodeTick r x s) ++ [.invoke store.funcs.length]) = 0 := by
    rw [traps_append,traps_values]
    simp [traps,Admin.traps]
  have domain : outside ((module r).instantiate store).1
      (values (I := I) (encodeTick r x s) ++ [.invoke store.funcs.length]) = 0 := by
    rw [outside_append,outside_values]
    simp [outside,Admin.outside,Module.instantiate_lookup]
  exact ⟨Nat.eq_zero_of_le_zero (domain ▸ path.outside_le),path.no_trap clean,
    (invoke_complete r store x s).remaining clean path⟩

theorem host_result (engine : ByteArray → List Value → List Value → Prop)
    (conforms : Artifacts.RuntimeConforms engine) (r : Representation) (x : Word) (s : State)
    (serialized : (module r).serializeArray = some emitted) (fidelity : loaded = emitted)
    (marshal : engine loaded (encodeTick r x s) observed) :
    observed = encodeTick r (source.step (x,s)).1 (source.step (x,s)).2 := by
  subst loaded
  exact conforms _ _ _ _ _ ((module r).serializeArray_correct serialized)
    (invoke_complete r (⟨[],()⟩ : Store Empty Unit) x s) marshal

/-- Exact instruction, scratch-local and stack profile of the packed module. -/
theorem packed_profile : packedModule.body.length = 5 ∧ packedModule.locals.length = 0 ∧
    Lowering.scanStack packedModule.body 0 = (3,3) := by decide

/-- Exact packed bytes, independently laid out from the standard sections. -/
def packedBytes : Binary.Bytes :=
  [0,97,115,109,1,0,0,0,1,10,1,96,3,127,127,127,3,127,127,127,
   3,2,1,0,7,7,1,3,114,117,110,0,0,10,13,1,11,0,32,0,32,2,106,32,0,32,1,11]

theorem packed_serialized : packedModule.serialize = some packedBytes := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem boolean_profile : booleanModule.type.params.length = 96 ∧
    booleanModule.type.results.length = 96 ∧ booleanModule.locals.length = 545 ∧
    booleanModule.body.length = 2274 ∧ Lowering.scanStack booleanModule.body 0 = (96,96) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem boolean_serialized_length : booleanModule.serialize.map List.length = some 6216 := by decide +kernel

end Applications.Wasm.WordContinuation
