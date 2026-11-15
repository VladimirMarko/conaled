import Applications.Wasm.Core

/-! Transcription of the reachable numeric, variable, administrative and context
rules from Core 2.0. Rule anchors and the reachable-domain boundary are recorded
in `docs/research/wasm-standard-subset.md`. -/
namespace Applications.Wasm

variable {I : Type}

/-- Core 2 `ieqz`: zero maps to one and every nonzero word maps to zero. -/
def eqz (x : BitVec 32) : BitVec 32 := if x = 0 then 1 else 0

/-- The selected standard reduction rules. The store is an index because these
rules leave it unchanged; allocation is handled separately. Arbitrary ambient
functions are retained but this relation does not execute their bodies. -/
inductive Step {I : Type} (s : ExtendedStore F O) : Frame → List (Admin I) → Frame → List (Admin I) → Prop
  | get (fr : Frame) (i : Nat) (v : Value) (h : fr.locals[i]? = some v) :
      Step (I := I) s fr [.instr (.get i)] fr [.value v]
  | set (fr : Frame) (i : Nat) (v : Value) (h : i < fr.locals.length) :
      Step (I := I) s fr [.value v, .instr (.set i)]
        { fr with locals := fr.locals.set i v } []
  | eqz (fr : Frame) (x : BitVec 32) :
      Step (I := I) s fr [.value (.i32 x), .instr .eqz] fr [.value (.i32 (eqz x))]
  | binary (fr : Frame) (op : BinOp) (x y : BitVec 32) :
      Step (I := I) s fr [.value (.i32 x), .value (.i32 y), .instr (.binary op)]
        fr [.value (.i32 (op.eval x y))]
  | invoke (fr : Frame) (address : Nat) (f : Function) (args : List Value)
      (lookup : s.funcs[address]? = some (.inr f))
      (arity : args.length = f.type.params.length) :
      Step (I := I) s fr (values args ++ [.invoke address]) fr
        [.frame f.type.results.length
          ⟨args ++ f.locals.map Value.default, f.module⟩
          [.label f.type.results.length [] (expression f.body)]]
  | label (fr : Frame) (n : Nat) (cont : List (Admin I)) (vs : List Value) :
      Step (I := I) s fr [.label n cont (values vs)] fr (values vs)
  | frame (outer inner : Frame) (n : Nat) (vs : List Value)
      (arity : vs.length = n) :
      Step (I := I) s outer [.frame n inner (values vs)] outer (values vs)
  | context (c : Context I) {fr fr' : Frame} {code code' : List (Admin I)}
      (step : Step (I := I) s fr code fr' code') :
      Step (I := I) s fr (c.fill code) fr' (c.fill code')
  | inFrame (outer inner inner' : Frame) (n : Nat) (code code' : List (Admin I))
      (step : Step (I := I) s inner code inner' code') :
      Step (I := I) s outer [.frame n inner code] outer [.frame n inner' code']
  | trap (fr : Frame) (c : Context I) (nonempty : c.fill [.trap] ≠ [.trap]) :
      Step (I := I) s fr (c.fill [.trap]) fr [.trap]
  | trapFrame (outer inner : Frame) (n : Nat) :
      Step (I := I) s outer [.frame n inner [.trap]] outer [.trap]

/-- Finite standard reduction, with the store fixed throughout. -/
inductive Steps {I : Type} (s : ExtendedStore F O) : Frame → List (Admin I) → Frame → List (Admin I) → Prop
  | refl (fr : Frame) (code : List (Admin I)) : Steps (I := I) s fr code fr code
  | cons {fr fr' fr'' : Frame} {code code' code'' : List (Admin I)}
      (head : Step (I := I) s fr code fr' code') (tail : Steps (I := I) s fr' code' fr'' code'') :
      Steps (I := I) s fr code fr'' code''

theorem Steps.single (h : Step (I := I) s fr code fr' code') : Steps (I := I) s fr code fr' code' :=
  .cons h (.refl _ _)

theorem Steps.trans (h : Steps (I := I) s fr code fr' code')
    (k : Steps (I := I) s fr' code' fr'' code'') : Steps (I := I) s fr code fr'' code'' := by
  induction h with
  | refl => exact k
  | cons head _ ih => exact .cons head (ih k)

theorem Steps.context (h : Steps (I := I) s fr code fr' code') (c : Context I) :
    Steps (I := I) s fr (c.fill code) fr' (c.fill code') := by
  induction h with
  | refl => exact .refl _ _
  | cons head _ ih => exact .cons (.context c head) ih

theorem Steps.inFrame (h : Steps (I := I) s fr code fr' code') (outer : Frame) (n : Nat) :
    Steps (I := I) s outer [.frame n fr code] outer [.frame n fr' code'] := by
  induction h with
  | refl => exact .refl _ _
  | cons head _ ih => exact .cons (.inFrame _ _ _ _ _ _ head) ih

/-- Straight-line instruction typing on ordinary, reachable stacks. These rules
use an arbitrary typed prefix; no unreachable-polymorphic code is emitted. -/
inductive InstrTyped (locals : List ValueType) : Instr → List ValueType → List ValueType → Prop
  | const (ts : List ValueType) (n : BitVec 32) : InstrTyped locals (.const n) ts (ts ++ [.i32])
  | get (ts : List ValueType) (i : Nat) (t : ValueType) (h : locals[i]? = some t) :
      InstrTyped locals (.get i) ts (ts ++ [t])
  | set (ts : List ValueType) (i : Nat) (t : ValueType) (h : locals[i]? = some t) :
      InstrTyped locals (.set i) (ts ++ [t]) ts
  | eqz (ts : List ValueType) : InstrTyped locals .eqz (ts ++ [.i32]) (ts ++ [.i32])
  | binary (ts : List ValueType) (op : BinOp) :
      InstrTyped locals (.binary op) (ts ++ [.i32, .i32]) (ts ++ [.i32])

inductive CodeTyped (locals : List ValueType) : List Instr → List ValueType → List ValueType → Prop
  | nil (ts : List ValueType) : CodeTyped locals [] ts ts
  | cons {i : Instr} {code : List Instr} {a b c : List ValueType}
      (head : InstrTyped locals i a b) (tail : CodeTyped locals code b c) :
      CodeTyped locals (i :: code) a c

/-- A practical straight-line evaluator uses a stack with its top first. The
standard syntax has the top last; `evalInstr_steps` relates the conventions. -/
def evalInstr (i : Instr) (fr : Frame) (stack : List Value) : Option (Frame × List Value) :=
  match i with
  | .const n => some (fr, .i32 n :: stack)
  | .get n => do
    let v ← fr.locals[n]?
    some (fr, v :: stack)
  | .set n => match stack with
    | v :: st =>
      if n < fr.locals.length then some ({ fr with locals := fr.locals.set n v }, st)
      else none
    | _ => none
  | .eqz => match stack with
    | .i32 x :: st => some (fr, .i32 (eqz x) :: st)
    | _ => none
  | .binary op => match stack with
    | .i32 y :: .i32 x :: st => some (fr, .i32 (op.eval x y) :: st)
    | _ => none

def evalCode : List Instr → Frame → List Value → Option (Frame × List Value)
  | [], fr, stack => some (fr, stack)
  | i :: code, fr, stack => do
    let (fr', stack') ← evalInstr i fr stack
    evalCode code fr' stack'

theorem evalInstr_steps (s : ExtendedStore F O) (i : Instr) (fr fr' : Frame)
    (stack out : List Value) (h : evalInstr i fr stack = some (fr', out)) :
    Steps (I := I) s fr (values stack.reverse ++ [i.admin]) fr' (values out.reverse) := by
  cases i with
  | const n =>
    simp only [evalInstr, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simpa [values, Instr.admin] using Steps.refl (I := I) (s := s) fr (values stack.reverse ++ [.value (.i32 n)])
  | get n =>
    simp only [evalInstr, bind, Option.bind_eq_some_iff] at h
    rcases h with ⟨v, hv, he⟩
    cases he
    simpa [Context.fill, values, Instr.admin] using
      (Steps.single (Step.get (I := I) (s := s) fr n v hv)).context (.seq stack.reverse .hole [])
  | set n =>
    cases stack with
    | nil => simp [evalInstr] at h
    | cons v st =>
      simp only [evalInstr] at h
      split at h
      · rename_i hn
        have he := Option.some.inj h
        have hfr := congrArg Prod.fst he
        have hout := congrArg Prod.snd he
        dsimp only at hfr hout
        subst fr'
        subst out
        simpa [Context.fill, values, Instr.admin, List.append_assoc] using
          (Steps.single (Step.set (I := I) (s := s) fr n v hn)).context (.seq st.reverse .hole [])
      · contradiction
  | eqz =>
    cases stack with
    | nil => simp [evalInstr] at h
    | cons v st =>
      cases v with
      | i32 x =>
        simp only [evalInstr, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨hfr, hout⟩
        subst fr'
        subst out
        simpa [Context.fill, values, Instr.admin, List.append_assoc] using
          (Steps.single (Step.eqz (I := I) (s := s) fr x)).context (.seq st.reverse .hole [])
      | _ => simp [evalInstr] at h
  | binary op =>
    cases stack with
    | nil => simp [evalInstr] at h
    | cons v st =>
      cases v with
      | i32 y =>
        cases st with
        | nil => simp [evalInstr] at h
        | cons w tail =>
          cases w with
          | i32 x =>
            simp only [evalInstr, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨hfr, hout⟩
            subst fr'
            subst out
            simpa [Context.fill, values, Instr.admin, List.append_assoc] using
              (Steps.single (Step.binary (I := I) (s := s) fr op x y)).context (.seq tail.reverse .hole [])
          | _ => simp [evalInstr] at h
      | _ => simp [evalInstr] at h

theorem evalCode_steps (s : ExtendedStore F O) (code : List Instr)
    (fr fr' : Frame) (stack out : List Value)
    (h : evalCode code fr stack = some (fr', out)) :
    Steps (I := I) s fr (values stack.reverse ++ expression code) fr' (values out.reverse) := by
  induction code generalizing fr stack with
  | nil =>
    simp only [evalCode, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simpa [expression] using Steps.refl (I := I) (s := s) fr (values stack.reverse)
  | cons i code ih =>
    simp only [evalCode, bind, Option.bind_eq_some_iff] at h
    rcases h with ⟨⟨mid, midStack⟩, head, tail⟩
    have first := (evalInstr_steps (I := I) s i fr mid stack midStack head).context
      (.seq [] .hole (expression code))
    have second := ih mid midStack tail
    apply Steps.trans _ second
    simpa [Context.fill, expression, values, List.append_assoc] using first

def Instr.weight : Instr → Nat
  | .const _ => 1
  | _ => 2

def Admin.weight (cost : Nat → Nat) : Admin I → Nat
  | .foreign _ | .value _ | .trap => 1
  | .instr _ => 2
  | .invoke address => cost address + 3
  | .label _ _ body => 1 + (body.map (Admin.weight cost)).sum
  | .frame _ _ body => 1 + (body.map (Admin.weight cost)).sum

def weight (cost : Nat → Nat) (code : List (Admin I)) : Nat :=
  (code.map (Admin.weight cost)).sum

theorem Admin.weight_pos (cost : Nat → Nat) (a : Admin I) : 0 < a.weight cost := by
  cases a <;> simp [Admin.weight] <;> omega

theorem length_le_weight (cost : Nat → Nat) (code : List (Admin I)) : code.length ≤ weight cost code := by
  induction code with
  | nil => simp [weight]
  | cons a rest ih =>
    have positive := a.weight_pos cost
    simp only [List.length_cons, weight, List.map_cons, List.sum_cons] at *
    omega

@[simp] theorem weight_append (cost : Nat → Nat) (a b : List (Admin I)) :
    weight cost (a ++ b) = weight cost a + weight cost b := by simp [weight]

@[simp] theorem weight_values (cost : Nat → Nat) (vs : List Value) :
    weight cost (values (I := I) vs) = vs.length := by
  induction vs with
  | nil => rfl
  | cons v rest ih => simp [values, weight, Admin.weight] at *; omega

@[simp] theorem weight_expression (cost : Nat → Nat) (code : List Instr) :
    weight cost (expression (I := I) code) = (code.map Instr.weight).sum := by
  induction code with
  | nil => rfl
  | cons i rest ih => cases i <;> simp [expression, weight, Instr.admin, Admin.weight, Instr.weight] at * <;> omega

def Context.weight (cost : Nat → Nat) : Context I → Nat
  | .hole => 0
  | .seq before inner suffix => before.length + inner.weight cost + Wasm.weight cost suffix
  | .label _ _ inner => 1 + inner.weight cost

theorem Context.weight_fill (cost : Nat → Nat) (c : Context I) (code : List (Admin I)) :
    Wasm.weight cost (c.fill code) = Wasm.weight cost code + c.weight cost := by
  induction c with
  | hole => simp [Context.fill, Context.weight]
  | seq before inner suffix ih => simp [Context.fill, Context.weight, ih, Nat.add_comm, Nat.add_left_comm]
  | label n cont inner ih =>
    simp only [Context.fill, Context.weight, Wasm.weight, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero, Admin.weight]
    change 1 + Wasm.weight cost (inner.fill code) = _
    rw [ih]
    simp [Wasm.weight, Nat.add_left_comm]

theorem Context.fill_of_weight_zero (cost : Nat → Nat) (c : Context I)
    (zero : c.weight cost = 0) (code : List (Admin I)) : c.fill code = code := by
  induction c with
  | hole => rfl
  | seq before inner suffix ih =>
    have bounded := length_le_weight cost suffix
    simp only [Context.weight] at zero
    have hb : before.length = 0 := by omega
    have hs : suffix.length = 0 := by omega
    have hi : inner.weight cost = 0 := by omega
    have eb := List.length_eq_zero_iff.mp hb
    have es := List.length_eq_zero_iff.mp hs
    simp [Context.fill, values, eb, es, ih hi]
  | label n cont inner ih => simp [Context.weight] at zero

def invocationCost (s : ExtendedStore F O) (address : Nat) : Nat :=
  match s.funcs[address]? with
  | some (.inr f) => (f.body.map Instr.weight).sum
  | _ => 0

/-- Every selected reduction strictly decreases this natural-valued measure.
Applying this to standard execution requires the separate reachable-rule
coverage argument; foreign instructions are not interpreted by this relation. -/
theorem Step.decreases {s : ExtendedStore F O} {fr fr' : Frame}
    {code code' : List (Admin I)} (h : Step s fr code fr' code') :
    weight (invocationCost s) code' < weight (invocationCost s) code := by
  induction h with
  | get => simp [weight, Admin.weight]
  | set => simp [weight, Admin.weight]
  | eqz => simp [weight, Admin.weight]
  | binary => simp [weight, Admin.weight]
  | invoke fr address f args lookup arity =>
    simp [weight, Admin.weight, invocationCost, lookup,
      ← weight_expression (I := I) (invocationCost s) f.body]
    omega
  | label => simp [weight, Admin.weight]
  | frame => simp [weight, Admin.weight]
  | context c step ih => rw [Context.weight_fill, Context.weight_fill]; omega
  | inFrame outer inner inner' n code code' step ih =>
    simp only [weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, Admin.weight] at *
    omega
  | trap fr c nonempty =>
    rw [Context.weight_fill]
    have pos : c.weight (invocationCost s) ≠ 0 := by
      intro hz
      exact nonempty (c.fill_of_weight_zero _ hz _)
    omega
  | trapFrame => simp [weight, Admin.weight]

theorem Step.chain_bound (s : ExtendedStore F O) (states : Nat → Frame × List (Admin I))
    (n : Nat) (steps : ∀ i, i < n → Step s (states i).1 (states i).2 (states (i+1)).1 (states (i+1)).2) :
    weight (invocationCost s) (states n).2 + n ≤ weight (invocationCost s) (states 0).2 := by
  induction n with
  | zero => omega
  | succ n ih =>
    have prior := ih (fun i hi => steps i (Nat.lt_trans hi (Nat.lt_succ_self n)))
    have last := (steps n (Nat.lt_succ_self n)).decreases
    omega

theorem Step.no_infinite (s : ExtendedStore F O) (states : Nat → Frame × List (Admin I)) :
    ¬ ∀ i, Step s (states i).1 (states i).2 (states (i+1)).1 (states (i+1)).2 := by
  intro h
  have bound := Step.chain_bound s states (weight (invocationCost s) (states 0).2 + 1) (fun i _ => h i)
  omega

/-- Counts active administrative traps. Foreign syntax and label continuations
are untouched here; this count makes no assertion about running either later. -/
def Admin.traps : Admin I → Nat
  | .trap => 1
  | .label _ _ body | .frame _ _ body => (body.map Admin.traps).sum
  | _ => 0

def traps (code : List (Admin I)) : Nat := (code.map Admin.traps).sum

@[simp] theorem traps_append (a b : List (Admin I)) : traps (a ++ b) = traps a + traps b := by
  simp [traps]

@[simp] theorem traps_values (vs : List Value) : traps (values (I := I) vs) = 0 := by
  induction vs with
  | nil => rfl
  | cons v rest ih => simpa [traps, values, Admin.traps] using ih

@[simp] theorem traps_expression (code : List Instr) : traps (expression (I := I) code) = 0 := by
  induction code with
  | nil => rfl
  | cons i rest ih => cases i <;> simpa [traps, expression, Instr.admin, Admin.traps] using ih

def Context.traps : Context I → Nat
  | .hole => 0
  | .seq _ inner suffix => inner.traps + Wasm.traps suffix
  | .label _ _ inner => inner.traps

theorem Context.traps_fill (c : Context I) (code : List (Admin I)) :
    Wasm.traps (c.fill code) = Wasm.traps code + c.traps := by
  induction c with
  | hole => simp [Context.fill, Context.traps]
  | seq before inner suffix ih => simp [Context.fill, Context.traps, ih, Nat.add_assoc]
  | label n cont inner ih =>
    simpa [Context.fill, Context.traps, Wasm.traps, Admin.traps] using ih

theorem Step.traps_le {s : ExtendedStore F O} {fr fr' : Frame}
    {code code' : List (Admin I)} (h : Step s fr code fr' code') : traps code' ≤ traps code := by
  induction h with
  | get => simp [traps, Admin.traps]
  | set => simp [traps, Admin.traps]
  | eqz => simp [traps, Admin.traps]
  | binary => simp [traps, Admin.traps]
  | invoke fr address f args lookup arity =>
    rw [traps_append, traps_values]
    simp only [traps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, Admin.traps]
    change traps (expression (I := I) f.body) ≤ 0
    rw [traps_expression]
  | label => simp [traps, Admin.traps]
  | frame => simp [traps, Admin.traps]
  | context c step ih => rw [Context.traps_fill, Context.traps_fill]; omega
  | inFrame outer inner inner' n code code' step ih =>
    simpa [traps, Admin.traps] using ih
  | trap => rw [Context.traps_fill]; omega
  | trapFrame => simp [traps, Admin.traps]

theorem Steps.traps_le {s : ExtendedStore F O} {fr fr' : Frame}
    {code code' : List (Admin I)} (h : Steps s fr code fr' code') : traps code' ≤ traps code := by
  induction h with
  | refl => rfl
  | cons step tail ih => exact ih.trans step.traps_le

theorem Steps.no_trap {s : ExtendedStore F O} {fr fr' : Frame}
    {code code' : List (Admin I)} (h : Steps s fr code fr' code') (clean : traps code = 0) :
    code' ≠ [.trap] := by
  intro eq
  have bound := h.traps_le
  rw [eq, clean] at bound
  simp [traps, Admin.traps] at bound

theorem CodeTyped.append (h : CodeTyped locals first a b) (k : CodeTyped locals second b c) :
    CodeTyped locals (first ++ second) a c := by
  induction h with
  | nil => exact k
  | cons head _ ih => exact .cons head (ih k)

def asValues : List (Admin I) → Option (List Value)
  | [] => some []
  | .value v :: rest => (asValues rest).map (v :: ·)
  | _ => none

@[simp] theorem asValues_values (vs : List Value) : asValues (values (I := I) vs) = some vs := by
  induction vs with
  | nil => rfl
  | cons v rest ih => simp [values, asValues] at *; exact ih

/-- A deterministic focus operation for the selected trap-free rules. This is
used to prove uniqueness of the transcribed relation, not to define that relation.
It does not execute a foreign instruction or an ambient function. -/
def focus (s : ExtendedStore F O) (fr : Frame) (stack : List Value)
    (code : List (Admin I)) : Option (Frame × List (Admin I)) :=
  match code with
  | [] => none
  | .value v :: rest => focus s fr (v :: stack) rest
  | .instr i :: rest => do
      let (after, st) ← evalInstr i fr stack
      some (after, values st.reverse ++ rest)
  | .invoke address :: rest => do
      let .inr f ← s.funcs[address]? | none
      if f.type.params.length ≤ stack.length then
        let args := (stack.take f.type.params.length).reverse
        let kept := (stack.drop f.type.params.length).reverse
        some (fr, values kept ++ [.frame f.type.results.length
          ⟨args ++ f.locals.map Value.default, f.module⟩
          [.label f.type.results.length [] (expression f.body)]] ++ rest)
      else none
  | .label n cont body :: rest =>
      match focus s fr [] body with
      | some (after, body') => some (after, values stack.reverse ++ [.label n cont body'] ++ rest)
      | none => do
        let vs ← asValues body
        some (fr, values stack.reverse ++ values vs ++ rest)
  | .frame n inner body :: rest =>
      match focus s inner [] body with
      | some (after, body') => some (fr, values stack.reverse ++ [.frame n after body'] ++ rest)
      | none => do
        let vs ← asValues body
        if vs.length = n then some (fr, values stack.reverse ++ values vs ++ rest) else none
  | _ => none
termination_by sizeOf code

@[simp] theorem focus_nil (s : ExtendedStore F O) (fr : Frame) (stack : List Value) :
    focus (I := I) s fr stack [] = none := by simp [focus]

theorem focus_values (s : ExtendedStore F O) (fr : Frame) (stack vs : List Value)
    (code : List (Admin I)) :
    focus s fr stack (values vs ++ code) = focus s fr (vs.reverse ++ stack) code := by
  induction vs generalizing stack with
  | nil => simp [values]
  | cons v rest ih =>
    simpa [values, focus, List.reverse_cons, List.append_assoc] using ih (v :: stack)

theorem focus_all_values (s : ExtendedStore F O) (fr : Frame) (stack vs : List Value) :
    focus (I := I) s fr stack (values vs) = none := by
  simpa using focus_values s fr stack vs ([] : List (Admin I))

theorem evalInstr_append (i : Instr) (fr fr' : Frame) (stack out extra : List Value)
    (h : evalInstr i fr stack = some (fr', out)) :
    evalInstr i fr (stack ++ extra) = some (fr', out ++ extra) := by
  cases i with
  | const n => cases h; rfl
  | get n =>
    simp only [evalInstr, bind, Option.bind_eq_some_iff] at h
    rcases h with ⟨v, hv, he⟩
    cases he
    simp [evalInstr, hv]
  | set n =>
    cases stack with
    | nil => simp [evalInstr] at h
    | cons v st =>
      simp only [evalInstr] at h
      split at h
      · rename_i hn
        cases h
        simp [evalInstr, hn]
      · contradiction
  | eqz =>
    cases stack with
    | nil => simp [evalInstr] at h
    | cons v st =>
      cases v with
      | i32 x => cases h; rfl
      | _ => simp [evalInstr] at h
  | binary op =>
    cases stack with
    | nil => simp [evalInstr] at h
    | cons v st =>
      cases v with
      | i32 y =>
        cases st with
        | nil => simp [evalInstr] at h
        | cons w tail =>
          cases w with
          | i32 x => cases h; rfl
          | _ => simp [evalInstr] at h
      | _ => simp [evalInstr] at h

/-- Adding values below a reducible segment and retaining an arbitrary suffix
cannot change which selected redex executes. -/
theorem focus_extend (s : ExtendedStore F O) (fr fr' : Frame) (stack : List Value)
    (code out : List (Admin I)) (extra : List Value) (suffix : List (Admin I))
    (h : focus s fr stack code = some (fr', out)) :
    focus s fr (stack ++ extra) (code ++ suffix) =
      some (fr', values extra.reverse ++ out ++ suffix) := by
  induction code generalizing stack out with
  | nil => simp at h
  | cons head rest ih =>
    cases head with
    | foreign i => simp [focus] at h
    | trap => simp [focus] at h
    | value v =>
      simp only [focus] at h
      simpa only [List.cons_append, focus] using ih (v :: stack) out h
    | instr i =>
      simp only [focus, bind, Option.bind_eq_some_iff] at h
      rcases h with ⟨⟨after, st⟩, hi, he⟩
      cases he
      simp [focus, evalInstr_append i fr after stack st extra hi,
        List.reverse_append, values, List.append_assoc]
    | invoke address =>
      cases lookup : s.funcs[address]? with
      | none => simp [focus, lookup] at h
      | some f =>
        cases f with
        | inl ambient => simp [focus, lookup] at h
        | inr f =>
          simp only [focus, lookup, bind, Option.bind_some] at h
          split at h
          · rename_i enough
            have more : f.type.params.length ≤ (stack ++ extra).length := by
              simp only [List.length_append]
              omega
            cases h
            simp only [List.cons_append, focus, lookup, bind, Option.bind_some, ite_eq_left more]
            rw [List.take_append_of_le_length enough, List.drop_append_of_le_length enough,
              List.reverse_append]
            simp [values, List.append_assoc]
          · contradiction
    | label n cont body =>
      cases inner : focus s fr [] body with
      | some p =>
        rcases p with ⟨after, body'⟩
        simp only [focus, inner] at h
        cases h
        simp [focus, inner, List.reverse_append, values, List.append_assoc]
      | none =>
        cases done : asValues body with
        | none => simp [focus, inner, done] at h
        | some vs =>
          simp only [focus, inner, done, bind, Option.bind_some] at h
          cases h
          simp [focus, inner, done, List.reverse_append, values, List.append_assoc]
    | frame n frame body =>
      cases inner : focus s frame [] body with
      | some p =>
        rcases p with ⟨after, body'⟩
        simp only [focus, inner] at h
        cases h
        simp [focus, inner, List.reverse_append, values, List.append_assoc]
      | none =>
        cases done : asValues body with
        | none => simp [focus, inner, done] at h
        | some vs =>
          simp only [focus, inner, done, bind, Option.bind_some] at h
          split at h
          · rename_i arity
            cases h
            simp [focus, inner, done, arity, List.reverse_append, values, List.append_assoc]
          · contradiction

theorem focus_context (s : ExtendedStore F O) (fr fr' : Frame)
    (code out : List (Admin I)) (h : focus s fr [] code = some (fr', out)) (c : Context I) :
    focus s fr [] (c.fill code) = some (fr', c.fill out) := by
  induction c with
  | hole => exact h
  | seq before inner suffix ih =>
    have extended := focus_extend s fr fr' [] (inner.fill code) (inner.fill out) before.reverse suffix ih
    change focus s fr [] (values before ++ inner.fill code ++ suffix) =
      some (fr', values before ++ inner.fill out ++ suffix)
    rw [List.append_assoc, focus_values]
    simpa only [List.nil_append, List.append_nil, List.reverse_reverse] using extended
  | label n cont inner ih => simp [Context.fill, focus, ih, values]

/-- A redex that prevents evaluation from reaching a later suffix. Both clauses
are needed: labels and frames may exit only when their whole body is values. -/
def Blocked (s : ExtendedStore F O) (code : List (Admin I)) : Prop :=
  ∀ fr stack suffix, focus s fr stack (code ++ suffix) = none ∧
    asValues (code ++ suffix) = none

theorem asValues_prefix_none (vs : List Value) (code : List (Admin I))
    (h : asValues code = none) : asValues (values vs ++ code) = none := by
  induction vs with
  | nil => simpa [values] using h
  | cons v vs ih =>
    change Option.map (v :: ·) (asValues (values vs ++ code)) = none
    rw [ih]; rfl

theorem Blocked.context (h : Blocked s code) (c : Context I) : Blocked s (c.fill code) := by
  induction c with
  | hole => exact h
  | seq before inner suffix ih =>
    intro fr stack tail
    have hb := ih fr (before.reverse ++ stack) (suffix ++ tail)
    constructor
    · simpa only [Context.fill, List.append_assoc, focus_values] using hb.1
    · simpa only [Context.fill, List.append_assoc] using asValues_prefix_none before _ hb.2
  | label n cont inner ih =>
    intro fr stack tail
    have hb := ih fr [] []
    simp only [List.append_nil] at hb
    simp [Context.fill, focus, hb.1, hb.2, asValues]

theorem Blocked.frame (h : Blocked s code) (n : Nat) (inner : Frame) :
    Blocked s [.frame n inner code] := by
  intro fr stack suffix
  have hb := h inner [] []
  simp only [List.append_nil] at hb
  simp [focus, hb.1, hb.2, asValues]

/-- Standard evaluation contexts place this trap before any retained suffix. -/
inductive TrapActive {I : Type} : List (Admin I) → Prop
  | root : TrapActive [.trap]
  | context (c : Context I) (h : TrapActive code) : TrapActive (c.fill code)
  | frame (n : Nat) (fr : Frame) (h : TrapActive code) : TrapActive [.frame n fr code]

theorem TrapActive.blocked (s : ExtendedStore F O) (h : TrapActive code) : Blocked s code := by
  induction h with
  | root => intro fr stack suffix; simp [focus, asValues]
  | context c _ ih => exact ih.context c
  | frame n fr _ ih => exact ih.frame n fr

theorem TrapActive.positive (h : TrapActive code) : 0 < traps code := by
  induction h with
  | root => simp [traps, Admin.traps]
  | context c _ ih => rw [Context.traps_fill]; omega
  | frame n fr _ ih => simpa [traps, Admin.traps] using ih

/-- A foreign redex, including an arbitrary ambient function invocation, cannot
be selected while an earlier generated segment has a successful focus. -/
theorem foreign_blocked (s : ExtendedStore F O) (i : I) : Blocked s [.foreign i] := by
  intro fr stack suffix
  simp [focus, asValues]

theorem ambient_invoke_blocked (s : ExtendedStore F O) (address : Nat) (f : F)
    (lookup : s.funcs[address]? = some (.inl f)) : Blocked (I := I) s [.invoke address] := by
  intro fr stack suffix
  simp [focus, lookup, asValues]

theorem Blocked.not_focus (h : Blocked s code)
    (run : focus s fr [] code = some (fr', out)) : False := by
  have hb := (h fr [] []).1
  simp only [List.append_nil] at hb
  rw [run] at hb
  contradiction

/-- Every selected step is the focused step, unless an active trap is being
propagated. The latter exception allows arbitrary trap-bearing continuations. -/
theorem Step.focus_or_trap (h : Step (I := I) s fr code fr' out) :
    focus s fr [] code = some (fr', out) ∨ TrapActive code := by
  induction h with
  | get fr i v h => exact .inl (by simp [focus, evalInstr, h, values])
  | set fr i v h => exact .inl (by simp [focus, evalInstr, h, values])
  | eqz fr x => exact .inl (by simp [focus, evalInstr, values])
  | binary fr op x y => exact .inl (by simp [focus, evalInstr, values])
  | invoke fr address f args lookup arity =>
    left
    rw [focus_values]
    have take : args.reverse.take args.length = args.reverse := by
      simpa only [List.length_reverse] using (show args.reverse.take args.reverse.length = args.reverse by simp)
    have drop : args.reverse.drop args.length = [] := by
      simpa only [List.length_reverse] using (show args.reverse.drop args.reverse.length = [] by simp)
    simp only [focus, lookup, bind, Option.bind_some, List.append_nil, List.length_reverse]
    simp [← arity, take, drop]
    rfl
  | label fr n cont vs => exact .inl (by simp only [focus, focus_all_values, asValues_values]; simp [values])
  | frame outer inner n vs arity =>
    exact .inl (by simp only [focus, focus_all_values, asValues_values]; simp [arity, values])
  | context c step ih =>
    rcases ih with ih | ih
    · exact .inl (focus_context _ _ _ _ _ ih c)
    · exact .inr (.context c ih)
  | inFrame outer inner inner' n code code' step ih =>
    rcases ih with ih | ih
    · exact .inl (by simp [focus, ih, values])
    · exact .inr (.frame n inner ih)
  | trap fr c nonempty => exact .inr (.context c .root)
  | trapFrame outer inner n => exact .inr (.frame n inner .root)

theorem Step.focus_eq (h : Step (I := I) s fr code fr' out)
    (run : focus s fr [] code = some (other, result)) : fr' = other ∧ out = result := by
  rcases h.focus_or_trap with hs | ht
  · rw [run] at hs
    exact Prod.mk.inj (Option.some.inj hs).symm
  · exact False.elim ((ht.blocked s).not_focus run)

theorem Step.focus_of_clean (h : Step (I := I) s fr code fr' out)
    (clean : traps code = 0) : focus s fr [] code = some (fr', out) := by
  rcases h.focus_or_trap with hs | ht
  · exact hs
  · have := ht.positive
    omega

theorem Step.deterministic (h : Step (I := I) s fr code fr' out)
    (k : Step (I := I) s fr code other result) (clean : traps code = 0) :
    fr' = other ∧ out = result := h.focus_eq (k.focus_of_clean clean)

theorem Step.not_values (h : Step (I := I) s fr (values vs) fr' out) : False := by
  have run := h.focus_of_clean (traps_values vs)
  rw [focus_all_values] at run
  contradiction

/-- Any alternative finite path from a clean state is a prefix of a successful
path to values. This rules out stuck alternatives and characterizes every final
result, rather than merely exhibiting one successful run. -/
theorem Steps.remaining (success : Steps (I := I) s fr code final (values vs))
    (clean : traps code = 0) (path : Steps (I := I) s fr code reached rest) :
    Steps (I := I) s reached rest final (values vs) := by
  induction path with
  | refl => exact success
  | cons head tail ih =>
    cases success with
    | refl => exact False.elim head.not_values
    | cons first later =>
      obtain ⟨rfl, rfl⟩ := head.deterministic first clean
      have hc : traps _ = 0 := Nat.eq_zero_of_le_zero (clean ▸ head.traps_le)
      exact ih later hc

/-- Counts active syntax outside the transcribed rule domain. Label continuation
code is dormant: generated bodies contain no branch instruction that could enter
it. Traps are inside the domain and handled by the propagation rules. -/
def Admin.outside (s : ExtendedStore F O) : Admin I → Nat
  | .foreign _ => 1
  | .instr (.const _) => 1
  | .invoke address => match s.funcs[address]? with | some (.inr _) => 0 | _ => 1
  | .label _ _ body | .frame _ _ body => (body.map (Admin.outside s)).sum
  | _ => 0

def outside (s : ExtendedStore F O) (code : List (Admin I)) : Nat :=
  (code.map (Admin.outside s)).sum

@[simp] theorem outside_append (s : ExtendedStore F O) (a b : List (Admin I)) :
    outside s (a ++ b) = outside s a + outside s b := by simp [outside]

@[simp] theorem outside_values (s : ExtendedStore F O) (vs : List Value) :
    outside s (values (I := I) vs) = 0 := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simpa [outside, values, Admin.outside] using ih

@[simp] theorem outside_expression (s : ExtendedStore F O) (code : List Instr) :
    outside s (expression (I := I) code) = 0 := by
  induction code with
  | nil => rfl
  | cons i rest ih => cases i <;> simpa [outside, expression, Instr.admin, Admin.outside] using ih

def Context.outside (s : ExtendedStore F O) : Context I → Nat
  | .hole => 0
  | .seq _ inner suffix => inner.outside s + Wasm.outside s suffix
  | .label _ _ inner => inner.outside s

theorem Context.outside_fill (s : ExtendedStore F O) (c : Context I) (code : List (Admin I)) :
    Wasm.outside s (c.fill code) = Wasm.outside s code + c.outside s := by
  induction c with
  | hole => simp [Context.fill, Context.outside]
  | seq before inner suffix ih => simp [Context.fill, Context.outside, ih, Nat.add_assoc]
  | label n cont inner ih => simpa [Context.fill, Context.outside, Wasm.outside, Admin.outside] using ih

theorem Step.outside_le (h : Step (I := I) s fr code fr' out) : outside s out ≤ outside s code := by
  induction h with
  | get => simp [outside, Admin.outside]
  | set => simp [outside, Admin.outside]
  | eqz => simp [outside, Admin.outside]
  | binary => simp [outside, Admin.outside]
  | invoke fr address f args lookup arity =>
    rw [outside_append, outside_values]
    simp only [outside, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, Admin.outside, lookup]
    change outside s (expression (I := I) f.body) ≤ 0
    rw [outside_expression]
  | label => simp [outside, Admin.outside]
  | frame => simp [outside, Admin.outside]
  | context c step ih => rw [Context.outside_fill, Context.outside_fill]; omega
  | inFrame outer inner inner' n code code' step ih => simpa [outside, Admin.outside] using ih
  | trap => simp [outside, Admin.outside]
  | trapFrame => simp [outside, Admin.outside]

theorem Steps.outside_le (h : Steps (I := I) s fr code fr' out) : outside s out ≤ outside s code := by
  induction h with
  | refl => rfl
  | cons step tail ih => exact ih.trans step.outside_le

/-- Every reachable normal form is precisely the successful result. -/
theorem Steps.normal_result (success : Steps (I := I) s fr code final (values vs))
    (clean : traps code = 0) (path : Steps (I := I) s fr code reached rest)
    (normal : ∀ f c, ¬ Step s reached rest f c) : reached = final ∧ rest = values vs := by
  have remaining := success.remaining clean path
  cases remaining with
  | refl => exact ⟨rfl, rfl⟩
  | cons head tail => exact False.elim (normal _ _ head)

/-- A reachable state either is the result or admits another standard step. -/
theorem Steps.progress (success : Steps (I := I) s fr code final (values vs))
    (clean : traps code = 0) (path : Steps (I := I) s fr code reached rest) :
    (reached = final ∧ rest = values vs) ∨ ∃ f c, Step s reached rest f c := by
  have remaining := success.remaining clean path
  cases remaining with
  | refl => exact .inl ⟨rfl, rfl⟩
  | cons head tail => exact .inr ⟨_, _, head⟩

end Applications.Wasm
