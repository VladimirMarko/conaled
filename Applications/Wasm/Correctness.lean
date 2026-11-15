import Applications.Wasm.Circuits
import Applications.FRP.Indefinite

/-! Operational correctness under local layouts. -/
namespace Applications.Wasm.Lowering
open FirstOrderCompiler Applications.Circuits

def Bounded : {a : Ty} → Layout a → Nat → Prop
  | .base, ref, n => ref < n
  | .unit, _, _ => True
  | .prod _ _, (x, y), n => Bounded x n ∧ Bounded y n

def Represents : {a : Ty} → Layout a → Val Bool a → List Value → Prop
  | .base, ref, x, locals => locals[ref]? = some (ABI.bit x)
  | .unit, _, _, _ => True
  | .prod _ _, (xr, yr), (x, y), locals => Represents xr x locals ∧ Represents yr y locals

/-- Every local outside the generated allocation interval retains its value,
including indices above the interval, not just the parameters below it. -/
def Preserves (lo hi : Nat) (before after : List Value) : Prop :=
  before.length = after.length ∧
    ∀ i, i < lo ∨ hi ≤ i → after[i]? = before[i]?

theorem Bounded.mono {a : Ty} (layout : Layout a) (h : Bounded layout n) (hn : n ≤ m) :
    Bounded layout m := by
  induction a with
  | base => exact Nat.lt_of_lt_of_le h hn
  | unit => trivial
  | prod a b ia ib => exact ⟨ia layout.1 h.1, ib layout.2 h.2⟩

theorem Represents.congr {a : Ty} (layout : Layout a) (x : Val Bool a)
    (bound : Bounded layout n) (h : Represents layout x before)
    (same : ∀ i, i < n → after[i]? = before[i]?) : Represents layout x after := by
  induction a with
  | base => exact (same layout bound).trans h
  | unit => trivial
  | prod a b ia ib => exact ⟨ia layout.1 x.1 bound.1 h.1, ib layout.2 x.2 bound.2 h.2⟩

theorem Preserves.refl (lo hi : Nat) (locals : List Value) : Preserves lo hi locals locals :=
  ⟨rfl, fun _ _ => rfl⟩

theorem Preserves.trans (h : Preserves lo mid a b) (k : Preserves mid hi b c)
    (hlo : lo ≤ mid) (hhi : mid ≤ hi) : Preserves lo hi a c := by
  refine ⟨h.1.trans k.1, ?_⟩
  intro i outside
  rcases outside with low | high
  · exact (k.2 i (.inl (Nat.lt_of_lt_of_le low hlo))).trans (h.2 i (.inl low))
  · exact (k.2 i (.inr high)).trans (h.2 i (.inr (hhi.trans high)))

theorem Preserves.set (locals : List Value) (n : Nat) (v : Value) :
    Preserves n (n + 1) locals (locals.set n v) := by
  constructor
  · simp
  · intro i h
    have ne : n ≠ i := by omega
    simp [ne]

theorem gate_eval (p : Gate a b) (next : Nat) (input : Layout a) (x : Val Bool a)
    (fr : Frame) (stack : List Value) (represented : Represents input x fr.locals)
    (space : next < fr.locals.length) :
    evalCode (gate p next input).code fr stack =
      some ({ fr with locals := fr.locals.set next ((ABI.encode (p.meaning x)).headD (.i32 0)) }, stack) := by
  cases p with
  | constant v => cases v <;> simp [gate, evalCode, evalInstr, ABI.encode, ABI.bit, Gate.meaning, space]
  | not delay =>
    change fr.locals[input]? = some (ABI.bit x) at represented
    cases x <;> simp [gate, evalCode, evalInstr, represented, ABI.encode, ABI.bit, Gate.meaning, space, eqz]
  | nand dl dr =>
    rcases x with ⟨x, y⟩
    rcases represented with ⟨hx, hy⟩
    change fr.locals[input.1]? = some (ABI.bit x) at hx
    change fr.locals[input.2]? = some (ABI.bit y) at hy
    cases x <;> cases y <;>
      simp [gate, evalCode, evalInstr, hx, hy, ABI.encode, ABI.bit, Gate.meaning, space, eqz, BinOp.eval]
  | nor dl dr =>
    rcases x with ⟨x, y⟩
    rcases represented with ⟨hx, hy⟩
    change fr.locals[input.1]? = some (ABI.bit x) at hx
    change fr.locals[input.2]? = some (ABI.bit y) at hy
    cases x <;> cases y <;>
      simp [gate, evalCode, evalInstr, hx, hy, ABI.encode, ABI.bit, Gate.meaning, space, eqz, BinOp.eval]
  | xor dl dr =>
    rcases x with ⟨x, y⟩
    rcases represented with ⟨hx, hy⟩
    change fr.locals[input.1]? = some (ABI.bit x) at hx
    change fr.locals[input.2]? = some (ABI.bit y) at hy
    cases x <;> cases y <;>
      simp [gate, evalCode, evalInstr, hx, hy, ABI.encode, ABI.bit, Gate.meaning, space, BinOp.eval]

theorem evalCode_append (first second : List Instr) (fr : Frame) (stack : List Value) :
    evalCode (first ++ second) fr stack = (do
      let (mid, st) ← evalCode first fr stack
      evalCode second mid st) := by
  induction first generalizing fr stack with
  | nil => rfl
  | cons i code ih =>
    simp only [List.cons_append, evalCode]
    cases h : evalInstr i fr stack with
    | none => simp
    | some p => simp [ih]

theorem lower_next_le (c : Circuit a b) (next : Nat) (input : Layout a) :
    next ≤ (lower c next input).next := by
  rw [(lower_profile c next input).2]
  exact Nat.le_add_right _ _

theorem gate_result (p : Gate a b) (next : Nat) (input : Layout a) (x : Val Bool a)
    (locals : List Value) (space : next < locals.length) :
    Represents (gate p next input).output (p.meaning x)
      (locals.set next ((ABI.encode (p.meaning x)).headD (.i32 0))) := by
  cases p <;> simp [gate, Represents, ABI.encode, space]

theorem gate_bound (p : Gate a b) (next : Nat) (input : Layout a) :
    Bounded (gate p next input).output (gate p next input).next := by
  cases p <;> simp [gate, Bounded]

/-- Every circuit executes with an arbitrary preserved operand stack and a
preallocated local array. Input references may alias. The result includes the
complete outside-interval local preservation law. -/
theorem lower_eval (c : Circuit a b) (next : Nat) (input : Layout a) (x : Val Bool a)
    (fr : Frame) (stack : List Value) (bound : Bounded input next)
    (represented : Represents input x fr.locals)
    (space : (lower c next input).next ≤ fr.locals.length) :
    ∃ after : Frame,
      evalCode (lower c next input).code fr stack = some (after, stack) ∧
      Bounded (lower c next input).output (lower c next input).next ∧
      Represents (lower c next input).output (c.execute x) after.locals ∧
      Preserves next (lower c next input).next fr.locals after.locals ∧
      after.module = fr.module := by
  induction c generalizing next fr with
  | identity => exact ⟨fr, rfl, bound, represented, Preserves.refl _ _ _, rfl⟩
  | terminate => exact ⟨fr, rfl, trivial, trivial, Preserves.refl _ _ _, rfl⟩
  | first => exact ⟨fr, rfl, bound.1, represented.1, Preserves.refl _ _ _, rfl⟩
  | second => exact ⟨fr, rfl, bound.2, represented.2, Preserves.refl _ _ _, rfl⟩
  | gate p =>
    have room : next < fr.locals.length := by
      have hp := (lower_profile (.gate p) next input).2
      have one : (Words.plan (.gate p)).locals = 1 := by cases p <;> rfl
      rw [one] at hp
      omega
    refine ⟨{ fr with locals := fr.locals.set next ((ABI.encode (p.meaning x)).headD (.i32 0)) },
      gate_eval p next input x fr stack represented room, gate_bound p next input,
      gate_result p next input x fr.locals room, ?_, rfl⟩
    convert Preserves.set fr.locals next ((ABI.encode (p.meaning x)).headD (.i32 0)) using 1
    cases p <;> rfl
  | compose g f ig iff =>
    have mn := lower_next_le g (lower f next input).next (lower f next input).output
    have firstSpace : (lower f next input).next ≤ fr.locals.length := mn.trans space
    obtain ⟨middle, ef, bf, rf, pf, mf⟩ := iff next input x fr bound represented firstSpace
    have secondSpace : (lower g (lower f next input).next (lower f next input).output).next ≤
        middle.locals.length := by rw [← pf.1]; exact space
    obtain ⟨after, eg, bg, rg, pg, mg⟩ :=
      ig (lower f next input).next (lower f next input).output (f.execute x) middle bf rf secondSpace
    refine ⟨after, ?_, bg, rg, ?_, mg.trans mf⟩
    · change evalCode ((lower f next input).code ++
        (lower g (lower f next input).next (lower f next input).output).code) fr stack = _
      simp [evalCode_append, ef, eg]
    · exact pf.trans pg (lower_next_le f next input) mn
  | pair f g iff ig =>
    have mn := lower_next_le g (lower f next input).next input
    have firstSpace : (lower f next input).next ≤ fr.locals.length := mn.trans space
    obtain ⟨middle, ef, bf, rf, pf, mf⟩ := iff next input x fr bound represented firstSpace
    have inputBound := bound.mono input (lower_next_le f next input)
    have inputRep := represented.congr input x bound (fun i hi => pf.2 i (.inl hi))
    have secondSpace : (lower g (lower f next input).next input).next ≤ middle.locals.length := by
      rw [← pf.1]; exact space
    obtain ⟨after, eg, bg, rg, pg, mg⟩ :=
      ig (lower f next input).next input x middle inputBound inputRep secondSpace
    refine ⟨after, ?_, ⟨bf.mono _ mn, bg⟩,
      ⟨rf.congr _ _ bf (fun i hi => pg.2 i (.inl hi)), rg⟩,
      pf.trans pg (lower_next_le f next input) mn, mg.trans mf⟩
    change evalCode ((lower f next input).code ++ (lower g (lower f next input).next input).code)
      fr stack = _
    simp [evalCode_append, ef, eg]

theorem parameters_bound (a : Ty) (start : Nat) :
    Bounded (parameters a start) (start + ABI.slots a) := by
  induction a generalizing start with
  | base => simp [parameters, ABI.slots, Bounded]
  | unit => trivial
  | prod a b ia ib =>
    constructor
    · exact (ia start).mono _ (by simp [ABI.slots])
    · simpa [parameters, ABI.slots, Nat.add_assoc] using ib (start + ABI.slots a)

theorem parameters_represent {a : Ty} (x : Val Bool a) (before after : List Value) :
    Represents (parameters a before.length) x (before ++ ABI.encode x ++ after) := by
  induction a generalizing before after with
  | base => simp [parameters, Represents, ABI.encode]
  | unit => trivial
  | prod a b ia ib =>
    constructor
    · simpa [parameters, ABI.encode, List.append_assoc] using ia x.1 before (ABI.encode x.2 ++ after)
    · simpa [parameters, ABI.encode, List.append_assoc] using ib x.2 (before ++ ABI.encode x.1) after

theorem load_refs {a : Ty} (layout : Layout a) (x : Val Bool a) (fr : Frame)
    (stack : List Value) (represented : Represents layout x fr.locals) :
    evalCode ((refs layout).map Instr.get) fr stack =
      some (fr, (ABI.encode x).reverse ++ stack) := by
  induction a generalizing stack with
  | base =>
    change fr.locals[layout]? = some (ABI.bit x) at represented
    simp [refs, evalCode, evalInstr, represented, ABI.encode]
  | unit => rfl
  | prod a b ia ib =>
    simp only [refs, List.map_append, evalCode_append]
    rw [ia layout.1 x.1 stack represented.1]
    simpa [ABI.encode, List.reverse_append, List.append_assoc] using
      ib layout.2 x.2 ((ABI.encode x.1).reverse ++ stack) represented.2

def initialFrame (c : Circuit a b) (address : Nat) (x : Val Bool a) : Frame :=
  ⟨ABI.encode x ++ (assemble c).locals.map Value.default, (assemble c).instance address⟩

theorem assemble_eval (c : Circuit a b) (address : Nat) (x : Val Bool a) :
    ∃ after : Frame,
      evalCode (assemble c).body (initialFrame c address x) [] =
        some (after, (ABI.encode (c.execute x)).reverse) ∧
      after.module = (assemble c).instance address := by
  have bounded : Bounded (parameters a 0) (ABI.slots a) := by
    simpa using parameters_bound a 0
  have represented : Represents (parameters a 0) x (initialFrame c address x).locals := by
    simpa [initialFrame] using parameters_represent x [] ((assemble c).locals.map Value.default)
  have room : (lower c (ABI.slots a) (parameters a 0)).next ≤
      (initialFrame c address x).locals.length := by
    rw [(lower_profile c _ _).2]
    simp [initialFrame, assemble]
  obtain ⟨after, run, _, result, _, sameModule⟩ :=
    lower_eval c (ABI.slots a) (parameters a 0) x (initialFrame c address x) [] bounded represented room
  refine ⟨after, ?_, sameModule⟩
  change evalCode ((lower c (ABI.slots a) (parameters a 0)).code ++
    (refs (lower c (ABI.slots a) (parameters a 0)).output).map Instr.get) _ [] = _
  rw [evalCode_append, run]
  simpa using load_refs _ (c.execute x) after [] result

/-- The complete successful invocation trace. Uniqueness, exclusion of stuck
states, and absence of divergent alternatives are separate reachable-domain
obligations, not consequences of this existential trace alone. -/
theorem invoke_compiled {I : Type} (s : Store F O) (c : Circuit a b) (x : Val Bool a) :
    Steps (I := I) ((assemble c).instantiate s).1 dummyFrame
      (values (ABI.encode x) ++ [.invoke s.funcs.length]) dummyFrame
      (values (ABI.encode (c.execute x))) := by
  obtain ⟨after, run, _⟩ := assemble_eval c s.funcs.length x
  apply invoke_of_body _ _ ((assemble c).function s.funcs.length) _ _ after
  · exact Module.instantiate_lookup _ _
  · simp [Module.function, assemble]
  · simp [Module.function, assemble]
  · have steps := evalCode_steps (I := I) ((assemble c).instantiate s).1
      (assemble c).body (initialFrame c s.funcs.length x) after []
      (ABI.encode (c.execute x)).reverse run
    simpa [initialFrame, Module.function, values] using steps

theorem gate_typed (p : Gate a b) (next count : Nat) (input : Layout a)
    (bound : Bounded input next) (space : next < count) :
    CodeTyped (List.replicate count .i32) (gate p next input).code [] [] := by
  have output : (List.replicate count ValueType.i32)[next]? = some .i32 := by simp [space]
  cases p with
  | constant v => exact .cons (.const [] _) (.cons (.set [] next .i32 output) (.nil []))
  | not delay =>
    have hi : (List.replicate count ValueType.i32)[input]? = some .i32 := by
      simp [Nat.lt_trans bound space]
    exact .cons (.get [] input .i32 hi)
      (.cons (.eqz []) (.cons (.set [] next .i32 output) (.nil [])))
  | nand dl dr =>
    have hl : (List.replicate count ValueType.i32)[input.1]? = some .i32 := by
      simp [Nat.lt_trans bound.1 space]
    have hr : (List.replicate count ValueType.i32)[input.2]? = some .i32 := by
      simp [Nat.lt_trans bound.2 space]
    exact .cons (.get [] input.1 .i32 hl) (.cons (.get [.i32] input.2 .i32 hr)
      (.cons (.binary [] .and) (.cons (.eqz []) (.cons (.set [] next .i32 output) (.nil [])))))
  | nor dl dr =>
    have hl : (List.replicate count ValueType.i32)[input.1]? = some .i32 := by
      simp [Nat.lt_trans bound.1 space]
    have hr : (List.replicate count ValueType.i32)[input.2]? = some .i32 := by
      simp [Nat.lt_trans bound.2 space]
    exact .cons (.get [] input.1 .i32 hl) (.cons (.get [.i32] input.2 .i32 hr)
      (.cons (.binary [] .or) (.cons (.eqz []) (.cons (.set [] next .i32 output) (.nil [])))))
  | xor dl dr =>
    have hl : (List.replicate count ValueType.i32)[input.1]? = some .i32 := by
      simp [Nat.lt_trans bound.1 space]
    have hr : (List.replicate count ValueType.i32)[input.2]? = some .i32 := by
      simp [Nat.lt_trans bound.2 space]
    exact .cons (.get [] input.1 .i32 hl) (.cons (.get [.i32] input.2 .i32 hr)
      (.cons (.binary [] .xor) (.cons (.set [] next .i32 output) (.nil []))))

theorem lower_static (c : Circuit a b) (next count : Nat) (input : Layout a)
    (bound : Bounded input next) (space : (lower c next input).next ≤ count) :
    Bounded (lower c next input).output (lower c next input).next ∧
    CodeTyped (List.replicate count .i32) (lower c next input).code [] [] := by
  induction c generalizing next with
  | identity => exact ⟨bound, .nil []⟩
  | terminate => exact ⟨trivial, .nil []⟩
  | first => exact ⟨bound.1, .nil []⟩
  | second => exact ⟨bound.2, .nil []⟩
  | gate p =>
    have room : next < count := by
      have hp := (lower_profile (.gate p) next input).2
      have one : (Words.plan (.gate p)).locals = 1 := by cases p <;> rfl
      rw [one] at hp
      omega
    exact ⟨gate_bound p next input, gate_typed p next count input bound room⟩
  | compose g f ig iff =>
    have mn := lower_next_le g (lower f next input).next (lower f next input).output
    have hf := iff next input bound (mn.trans space)
    have hg := ig (lower f next input).next (lower f next input).output hf.1 space
    exact ⟨hg.1, hf.2.append hg.2⟩
  | pair f g iff ig =>
    have mn := lower_next_le g (lower f next input).next input
    have hf := iff next input bound (mn.trans space)
    have hg := ig (lower f next input).next input (bound.mono input (lower_next_le f next input)) space
    exact ⟨⟨hf.1.mono _ mn, hg.1⟩, hf.2.append hg.2⟩

theorem refs_bound {a : Ty} (layout : Layout a) (h : Bounded layout n) :
    ∀ i ∈ refs layout, i < n := by
  induction a with
  | base => simpa [refs, Bounded] using h
  | unit => simp [refs]
  | prod a b ia ib =>
    intro i hi
    rcases List.mem_append.mp hi with hl | hr
    · exact ia layout.1 h.1 i hl
    · exact ib layout.2 h.2 i hr

theorem loads_typed (rs : List Nat) (count : Nat) (before : List ValueType)
    (bound : ∀ i ∈ rs, i < count) :
    CodeTyped (List.replicate count .i32) (rs.map Instr.get) before
      (before ++ List.replicate rs.length .i32) := by
  induction rs generalizing before with
  | nil => simpa using CodeTyped.nil (locals := List.replicate count .i32) before
  | cons i rs ih =>
    have hi : (List.replicate count ValueType.i32)[i]? = some .i32 := by simp [bound i (by simp)]
    have tail := ih (before ++ [.i32]) (fun j hj => bound j (by simp [hj]))
    have whole := CodeTyped.cons (InstrTyped.get before i .i32 hi) tail
    simpa [List.replicate_succ, List.append_assoc] using whole

theorem assemble_valid (c : Circuit a b) : (assemble c).Valid := by
  let count := ABI.slots a + (Words.plan c).locals
  have room : (lower c (ABI.slots a) (parameters a 0)).next ≤ count := by
    rw [(lower_profile c _ _).2]
  have bound : Bounded (parameters a 0) (ABI.slots a) := by simpa using parameters_bound a 0
  have h := lower_static c (ABI.slots a) count (parameters a 0) bound room
  have loads := loads_typed (refs (lower c (ABI.slots a) (parameters a 0)).output) count []
    (refs_bound _ (h.1.mono _ room))
  have whole := h.2.append loads
  simpa [Module.Valid, assemble, count, ← List.replicate_add] using whole

@[simp] theorem encode_types {a : Ty} (x : Val Bool a) :
    (ABI.encode x).map Value.type = List.replicate (ABI.slots a) .i32 := by
  induction a with
  | base => simp [ABI.encode, ABI.bit, Value.type, ABI.slots]
  | unit => rfl
  | prod a b ia ib => simp only [ABI.encode, List.map_append, ABI.slots, ia, ib, List.replicate_add]

theorem assemble_validate (c : Circuit a b) : (assemble c).validate = true := by
  have typed : CodeTyped (List.replicate (ABI.slots a + (Words.plan c).locals) .i32)
      (assemble c).body [] (List.replicate (ABI.slots b) .i32) := by
    simpa only [Module.Valid, assemble, ← List.replicate_add] using assemble_valid c
  have checked := typed.checkHeights
  simp only [List.length_nil, List.length_replicate, assemble] at checked
  simp [Module.validate, assemble, checked]

/-- Signature checks, export resolution and selected static validity are
established for every source input, without a body-evaluation premise. -/
theorem invoke_entry (s : Store F O) (c : Circuit a b) (x : Val Bool a) :
    (assemble c).validate = true ∧
    ((assemble c).instantiate s).2.export "run" = some (.func s.funcs.length) ∧
    externalInvoke (I := I) ((assemble c).instantiate s).1 s.funcs.length (ABI.encode x) =
      some (dummyFrame, values (ABI.encode x) ++ [.invoke s.funcs.length]) := by
  refine ⟨assemble_validate c, Module.export_run _ _, ?_⟩
  apply externalInvoke_generated _ _ ((assemble c).function s.funcs.length) _
  · exact Module.instantiate_lookup _ _
  · simp [Module.function, assemble]

/-- Every reachable state remains inside the selected standard-rule domain,
is not a trap, and retains a finite path to the independently computed result.
Together with `Step.no_infinite` and `Steps.progress`, this excludes divergent
and stuck alternatives. The store is the fixed post-instantiation store. -/
theorem invoke_correct (s : Store F O) (c : Circuit a b) (x : Val Bool a)
    (path : Steps (I := I) ((assemble c).instantiate s).1 dummyFrame
      (values (ABI.encode x) ++ [.invoke s.funcs.length]) fr code) :
    outside ((assemble c).instantiate s).1 code = 0 ∧ code ≠ [.trap] ∧
    Steps ((assemble c).instantiate s).1 fr code dummyFrame
      (values (ABI.encode (c.execute x))) := by
  have clean : traps (values (I := I) (ABI.encode x) ++ [.invoke s.funcs.length]) = 0 := by
    rw [traps_append, traps_values]
    simp [traps, Admin.traps]
  have domain : outside ((assemble c).instantiate s).1
      (values (I := I) (ABI.encode x) ++ [.invoke s.funcs.length]) = 0 := by
    rw [outside_append, outside_values]
    simp [outside, Admin.outside, Module.instantiate_lookup]
  refine ⟨Nat.eq_zero_of_le_zero (domain ▸ path.outside_le), path.no_trap clean, ?_⟩
  exact (invoke_compiled s c x).remaining clean path

/-- The original frontend theorem supplies the source meaning; target reduction
never calls this evaluator. Context products retain their existing order. -/
theorem compile_source (s : Store F O) (t : Term Gate Γ a) (ρ : Val Bool (context Γ)) :
    Steps (I := I) ((assemble (compile Circuit.target t)).instantiate s).1 dummyFrame
      (values (ABI.encode ρ) ++ [.invoke s.funcs.length]) dummyFrame
      (values (ABI.encode (eval Gate.meaning t ρ))) := by
  have run := invoke_compiled (I := I) s (compile Circuit.target t) ρ
  rw [Circuit.execute_correct (compile Circuit.target t) ρ, Circuit.compile_value] at run
  exact run

theorem finite_sum_source (s : Store F O) (t : FRPSpec.FiniteSum.Term Γ a)
    (ρ : FRPSpec.FiniteSum.Env Γ) :
    Steps (I := I) ((assemble (FRPSpec.FiniteSum.lower t)).instantiate s).1 dummyFrame
      (values (ABI.encode (FRPSpec.FiniteSum.encodeEnv ρ)) ++ [.invoke s.funcs.length]) dummyFrame
      (values (ABI.encodeSum (FRPSpec.FiniteSum.eval t ρ))) := by
  have run := invoke_compiled (I := I) s (FRPSpec.FiniteSum.lower t) (FRPSpec.FiniteSum.encodeEnv ρ)
  rw [FRPSpec.FiniteSum.lower_correct] at run
  exact run

theorem state_step (store : Store F O) (p : FRPSpec.Indefinite.Program a b state)
    (input : Val Bool a) (current : Val Bool state) :
    Steps (I := I) ((assemble p.body).instantiate store).1 dummyFrame
      (values (ABI.encode (a := .prod a state) (input, current)) ++ [.invoke store.funcs.length]) dummyFrame
      (values (ABI.encode (a := .prod b state) (p.meaning.step (input, current)))) := by
  have run := invoke_compiled (I := I) store p.body (input, current)
  rw [Circuit.execute_correct] at run
  exact run

/-- Full word observations are recovered using #509's inverse codec. -/
theorem word_result (tag : Bool) (x y : BitVec n) :
    (Words.selector n).execute (tag, (Words.encode x, Words.encode y)) =
      (Words.encode (if tag then x+y else x ^^^ y), (Words.encode x, Words.encode y)) := by
  have h := Words.selector_correct tag (Words.encode x) (Words.encode y)
  simp only [Words.decode_encode, Words.meaning] at h
  have encoded := congrArg (fun p : BitVec n × (BitVec n × BitVec n) =>
    (Words.encode p.1, (Words.encode p.2.1, Words.encode p.2.2))) h
  simpa only [Words.encode_decode] using encoded

theorem word_source (s : Store F O) (tag : Bool) (x y : BitVec n) :
    Steps (I := I) ((assemble (Words.selector n)).instantiate s).1 dummyFrame
      (values (ABI.encode (a := .prod .base (.prod (Words.shape n) (Words.shape n))) (tag, (Words.encode x, Words.encode y))) ++ [.invoke s.funcs.length]) dummyFrame
      (values (ABI.encode (a := .prod (Words.shape n) (.prod (Words.shape n) (Words.shape n))) (Words.encode (if tag then x+y else x ^^^ y), (Words.encode x, Words.encode y)))) := by
  have run := invoke_compiled (I := I) s (Words.selector n) (tag, (Words.encode x, Words.encode y))
  rw [word_result (n := n) tag x y] at run
  exact run

/-- Weighted body size bounds standard reductions separately from instruction
entries: constants are values and invocation/label/frame completion has a cost. -/
theorem body_weight_bound (body : List Instr) : (body.map Instr.weight).sum ≤ 2 * body.length := by
  induction body with
  | nil => rfl
  | cons i rest ih => cases i <;> simp only [List.map_cons, List.sum_cons, List.length_cons, Instr.weight] <;> omega

theorem invocation_reduction_bound (s : Store F O) (c : Circuit a b) (x : Val Bool a)
    (states : Nat → Frame × List (Admin I)) (n : Nat)
    (start : states 0 = (dummyFrame, values (ABI.encode x) ++ [.invoke s.funcs.length]))
    (chain : ∀ i, i < n → Step ((assemble c).instantiate s).1
      (states i).1 (states i).2 (states (i+1)).1 (states (i+1)).2) :
    n ≤ ABI.slots a + 2 * (assemble c).body.length + 3 := by
  have bound := Step.chain_bound ((assemble c).instantiate s).1 states n chain
  rw [start, weight_append, weight_values] at bound
  have body := body_weight_bound (assemble c).body
  simp only [weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, Admin.weight, invocationCost, Module.instantiate_lookup] at bound
  simp only [Module.function, ABI.encode_length] at bound
  omega

end Applications.Wasm.Lowering
