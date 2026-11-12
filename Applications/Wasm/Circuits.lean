import Applications.Wasm.ABI
import Applications.Wasm.Module
import Applications.Circuits.Words

/-! Fresh-local compilation of circuits. Structural wiring aliases read-only
references; each gate writes one fresh local. -/
namespace Applications.Wasm.Lowering
open FirstOrderCompiler Applications.Circuits

abbrev Layout (a : Ty) := Val Nat a

structure Chunk (a : Ty) where
  code : List Instr
  output : Layout a
  next : Nat

abbrev Hom (a b : Ty) := Nat → Layout a → Chunk b

def ident : Hom a a := fun next input => ⟨[], input, next⟩
def terminate : Hom a .unit := fun next _ => ⟨[], (), next⟩
def first : Hom (.prod a b) a := fun next input => ⟨[], input.1, next⟩
def second : Hom (.prod a b) b := fun next input => ⟨[], input.2, next⟩
def comp (g : Hom b c) (f : Hom a b) : Hom a c := fun next input =>
  let cf := f next input
  let cg := g cf.next cf.output
  ⟨cf.code ++ cg.code, cg.output, cg.next⟩
def pair (f : Hom a b) (g : Hom a c) : Hom a (.prod b c) := fun next input =>
  let cf := f next input
  let cg := g cf.next input
  ⟨cf.code ++ cg.code, (cf.output, cg.output), cg.next⟩

def gate : Gate a b → Hom a b
  | .constant v => fun next _ =>
      ⟨[.const (if v then 1 else 0), .set next], next, next + 1⟩
  | .not _ => fun next input => ⟨[.get input, .eqz, .set next], next, next + 1⟩
  | .nand _ _ => fun next input =>
      ⟨[.get input.1, .get input.2, .binary .and, .eqz, .set next], next, next + 1⟩
  | .nor _ _ => fun next input =>
      ⟨[.get input.1, .get input.2, .binary .or, .eqz, .set next], next, next + 1⟩
  | .xor _ _ => fun next input =>
      ⟨[.get input.1, .get input.2, .binary .xor, .set next], next, next + 1⟩

def target : Target Gate where
  Hom := Hom
  ident := ident
  comp := comp
  terminal := terminate
  fst := first
  snd := second
  pair := pair
  primitive := gate

def lower (c : Circuit a b) : Hom a b := c.interpret target

def refs : {a : Ty} → Layout a → List Nat
  | .base, n => [n]
  | .unit, _ => []
  | .prod _ _, (x, y) => refs x ++ refs y

def parameters : (a : Ty) → Nat → Layout a
  | .base, start => start
  | .unit, _ => ()
  | .prod a b, start => (parameters a start, parameters b (start + ABI.slots a))

@[simp] theorem refs_length {a : Ty} (layout : Layout a) :
    (refs layout).length = ABI.slots a := by
  induction a with
  | base => rfl
  | unit => rfl
  | prod a b ia ib => simp [refs, ABI.slots, ia, ib]

/-- The generated instruction entries realize #509's proposed counts. This does
not count standard reductions, binary bytes, codec work, or physical resources. -/
theorem lower_profile (c : Circuit a b) (next : Nat) (input : Layout a) :
    (lower c next input).code.length = (Words.plan c).instructions ∧
    (lower c next input).next = next + (Words.plan c).locals := by
  induction c generalizing next with
  | identity => simp [lower, Circuit.interpret, target, ident, Words.plan]
  | terminate => simp [lower, Circuit.interpret, target, terminate, Words.plan]
  | first => simp [lower, Circuit.interpret, target, first, Words.plan]
  | second => simp [lower, Circuit.interpret, target, second, Words.plan]
  | gate p => cases p <;> simp [lower, Circuit.interpret, target, gate, Words.plan, Words.gatePlan]
  | compose g f ig iff =>
    have hf := iff next input
    have hg := ig (lower f next input).next (lower f next input).output
    change ((lower f next input).code ++
      (lower g (lower f next input).next (lower f next input).output).code).length = _ ∧ _
    simp only [List.length_append, Words.plan, Words.Plan.then]
    constructor
    · exact congrArg₂ (· + ·) hf.1 hg.1
    · change (lower g (lower f next input).next (lower f next input).output).next = _
      rw [hg.2, hf.2, Nat.add_assoc]
  | pair f g iff ig =>
    have hf := iff next input
    have hg := ig (lower f next input).next input
    change ((lower f next input).code ++ (lower g (lower f next input).next input).code).length = _ ∧ _
    simp only [List.length_append, Words.plan, Words.Plan.then]
    constructor
    · exact congrArg₂ (· + ·) hf.1 hg.1
    · change (lower g (lower f next input).next input).next = _
      rw [hg.2, hf.2, Nat.add_assoc]

def assemble (c : Circuit a b) : Module :=
  let chunk := lower c (ABI.slots a) (parameters a 0)
  ⟨⟨List.replicate (ABI.slots a) .i32, List.replicate (ABI.slots b) .i32⟩,
    List.replicate (Words.plan c).locals .i32,
    chunk.code ++ (refs chunk.output).map Instr.get⟩

/-- Operand height after one instruction. Underflow is excluded by validation;
this scan counts the actual ordered instruction list, not circuit nodes. -/
def stackAfter (i : Instr) (height : Nat) : Nat :=
  match i with
  | .const _ | .get _ => height + 1
  | .set _ | .binary _ => height - 1
  | .eqz => height

/-- Final and maximum operand heights, including the initial height. This is a
body operand-stack model, not a count of activation frames or engine bytes. -/
def scanStack : List Instr → Nat → Nat × Nat
  | [], height => (height, height)
  | i :: rest, height =>
      let tail := scanStack rest (stackAfter i height)
      (tail.1, max height tail.2)

theorem scanStack_ge (code : List Instr) (height : Nat) : height ≤ (scanStack code height).2 := by
  cases code with
  | nil => exact Nat.le_refl _
  | cons => exact Nat.le_max_left _ _

theorem scanStack_append (first second : List Instr) (height : Nat) :
    scanStack (first ++ second) height =
      let f := scanStack first height
      let g := scanStack second f.1
      (g.1, max f.2 g.2) := by
  induction first generalizing height with
  | nil => simp [scanStack, Nat.max_eq_right (scanStack_ge second height)]
  | cons i rest ih => simp [scanStack, ih, Nat.max_assoc]

theorem gate_stack (p : Gate a b) (next : Nat) (input : Layout a) (height : Nat) :
    scanStack (gate p next input).code height = (height, height + (Words.gatePlan p).stack) := by
  cases p <;> simp [gate, scanStack, stackAfter, Words.gatePlan] <;> omega

theorem lower_stack (c : Circuit a b) (next : Nat) (input : Layout a) (height : Nat) :
    scanStack (lower c next input).code height = (height, height + (Words.plan c).stack) := by
  induction c generalizing next with
  | identity => simp [lower, Circuit.interpret, target, ident, scanStack, Words.plan]
  | terminate => simp [lower, Circuit.interpret, target, terminate, scanStack, Words.plan]
  | first => simp [lower, Circuit.interpret, target, first, scanStack, Words.plan]
  | second => simp [lower, Circuit.interpret, target, second, scanStack, Words.plan]
  | gate p => exact gate_stack p next input height
  | compose g f ig iff =>
    change scanStack ((lower f next input).code ++
      (lower g (lower f next input).next (lower f next input).output).code) height = _
    simp only [scanStack_append, iff, ig]
    simp [Words.plan, Words.Plan.then, Nat.add_max_add_left]
  | pair f g iff ig =>
    change scanStack ((lower f next input).code ++
      (lower g (lower f next input).next input).code) height = _
    simp only [scanStack_append, iff, ig]
    simp [Words.plan, Words.Plan.then, Nat.add_max_add_left]

theorem loads_stack (rs : List Nat) (height : Nat) :
    scanStack (rs.map Instr.get) height = (height + rs.length, height + rs.length) := by
  induction rs generalizing height with
  | nil => simp [scanStack]
  | cons i rs ih => simp [scanStack, stackAfter, ih, Nat.add_assoc]; omega

theorem assemble_profile (c : Circuit a b) :
    (assemble c).body.length = (Words.plan c).instructions + ABI.slots b ∧
    (assemble c).type.params.length + (assemble c).locals.length = ABI.slots a + (Words.plan c).locals ∧
    scanStack (assemble c).body 0 = (ABI.slots b, max (Words.plan c).stack (ABI.slots b)) := by
  have lengths := (lower_profile c (ABI.slots a) (parameters a 0)).1
  simp only [assemble, List.length_append, List.length_map, refs_length,
    List.length_replicate, lengths, scanStack_append, lower_stack, loads_stack, Nat.zero_add]
  exact ⟨trivial, trivial, trivial⟩

/-- Every successful concrete instruction evaluation has the scanned height.
This connects the syntax profile to operand-stack lengths in execution. -/
theorem evalInstr_stack (i : Instr) (h : evalInstr i fr stack = some (after, out)) :
    out.length = stackAfter i stack.length := by
  cases i with
  | const => cases h; rfl
  | get n =>
    simp only [evalInstr, bind, Option.bind_eq_some_iff] at h
    obtain ⟨v, _, e⟩ := h
    cases e
    rfl
  | set n =>
    cases stack with
    | nil => simp [evalInstr] at h
    | cons v rest =>
      simp only [evalInstr] at h
      split at h
      · cases h; simp [stackAfter]
      · contradiction
  | eqz =>
    cases stack with
    | nil => simp [evalInstr] at h
    | cons v rest =>
      cases v <;> simp only [evalInstr] at h
      all_goals try contradiction
      cases h
      rfl
  | binary op =>
    cases stack with
    | nil => simp [evalInstr] at h
    | cons v rest =>
      cases v with
      | i32 y =>
        cases rest with
        | nil => simp [evalInstr] at h
        | cons w tail =>
          cases w <;> simp only [evalInstr] at h
          all_goals try contradiction
          cases h
          simp [stackAfter]
      | _ => simp [evalInstr] at h

theorem scanStack_final_le (code : List Instr) (height : Nat) :
    (scanStack code height).1 ≤ (scanStack code height).2 := by
  induction code generalizing height with
  | nil => exact Nat.le_refl _
  | cons i rest ih => exact (ih (stackAfter i height)).trans (Nat.le_max_right _ _)

theorem evalCode_stack (code : List Instr) (h : evalCode code fr stack = some (after, out)) :
    out.length = (scanStack code stack.length).1 := by
  induction code generalizing fr stack with
  | nil => cases h; rfl
  | cons i rest ih =>
    simp only [evalCode, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨middle, midStack⟩, first, tail⟩ := h
    have lengths := evalInstr_stack i first
    simpa only [scanStack, ← lengths] using ih tail

/-- Every executed prefix lies below the computed peak, including prefixes
ending between the loads and the numeric operation of a gate. -/
theorem eval_prefix_bound (first rest : List Instr)
    (h : evalCode first fr stack = some (after, out)) :
    out.length ≤ (scanStack (first ++ rest) stack.length).2 := by
  rw [evalCode_stack first h, scanStack_append]
  exact (scanStack_final_le first stack.length).trans (Nat.le_max_left _ _)

theorem slots_cells (a : Ty) : ABI.slots a = cells a := by
  induction a with
  | base => rfl
  | unit => rfl
  | prod a b ia ib => simp [ABI.slots, cells, ia, ib]

/-- Actual generated syntax and operand-height counts. This supplies the
implementation connection that the unchanged #509 plan intentionally lacked. -/
def actualPlan (c : Circuit a b) : Words.Plan :=
  ⟨(assemble c).body.length, (assemble c).type.params.length + (assemble c).locals.length,
    (scanStack (assemble c).body 0).2⟩

theorem actualPlan_eq (c : Circuit a b) : actualPlan c = Words.invocationPlan c := by
  obtain ⟨instructions, locals, stack⟩ := assemble_profile c
  simp only [actualPlan, instructions, locals, stack, Words.invocationPlan, slots_cells]


end Applications.Wasm.Lowering
