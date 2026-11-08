import SquareKit.OwnedHandle

namespace SquareKit.OwnedHandle
open AdjointModes
set_option backward.isDefEq.respectTransparency false

def weight : Option Cell → Nat | none => 0 | some _ => 1
def degree (s : State) : Nat := weight (s.slots false) + weight (s.slots true)

/-- Failure retains the ledger and makes the failure observable. -/
def execute (c : Command) (s : State) : State :=
  (step c s).getD {s with failed := true}

theorem acts_weight {c : Command} {s t : State} (h : Acts c s t) (k : Bool) :
    weight (t.slots k) = weight (s.slots k) := by
  cases h with
  | transfer s h a b cell hp hl ho hf =>
    by_cases hk : k = h
    · subst k; simp [replace, hp, weight]
    · simp [replace, hk]
  | consume s h a cell hp hl ho hf =>
    by_cases hk : k = h
    · subst k; simp [replace, hp, weight]
    · simp [replace, hk]

theorem execute_degree (c : Command) (s : State) : degree (execute c s) = degree s := by
  cases hs : step c s with
  | none => simp [execute, hs, degree]
  | some t =>
    simp only [execute, hs, Option.getD_some]
    exact congrArg₂ (· + ·) (acts_weight ((step_acts c s t).mp hs) false)
      (acts_weight ((step_acts c s t).mp hs) true)

def ledger : Resource := ⟨State, degree⟩
def atoms : Atoms := ⟨Command, ledger⟩

/-- The command is unrestricted data; the ledger is linear. -/
inductive Prim : Signature where
  | execute : Prim (.times (.atom .linear) (.down (.atom .unrestricted))) (.atom .linear)
  | literal (c : Command) : Prim (.one .unrestricted) (.atom .unrestricted)

def meanings : PrimitiveMeaning atoms Prim
  | _, _, _, .execute => ⟨fun x => execute x.2 x.1, fun x => by
      simpa [Ty.meaning, atoms, ledger, tensor, down] using execute_degree x.2 x.1⟩
  | _, _, _, .literal c => ⟨fun _ => c, fun _ => rfl⟩

def payload : PayloadMeaning atoms Prim
  | _, _, _, .execute => fun x => execute x.2 x.1
  | _, _, _, .literal c => fun _ => c

theorem primitive_payload {m} {A B : Ty m} (p : Prim A B)
    (x : (A.meaning atoms).Carrier) :
    B.forget atoms ((meanings p).run x) = payload p (A.forget atoms x) := by
  cases p <;> rfl

/-- Source code actually crosses the downshift to import a command literal. -/
def instruction (c : Command) : Term Prim (.atom .linear) (.atom .linear) :=
  .comp (.prim .execute)
    (.comp .swap (.comp (.times (.downMap (.prim (.literal c))) .id)
      (.comp (.times .oneDown .id) .ununitor)))

def program : List Command → Term Prim (.atom .linear) (.atom .linear)
  | [] => .id
  | c :: cs => .comp (program cs) (instruction c)

def totalRun : List Command → State → State
  | [], s => s
  | c :: cs, s => totalRun cs (execute c s)

theorem program_denote (cs : List Command) (s : State) :
    (program cs).denote atoms payload s = totalRun cs s := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih => exact ih _

/-- Generic mode compilation supplies the whole-program payload square. -/
theorem program_compile (cs : List Command) (s : State) :
    ((program cs).compile atoms meanings).run s = totalRun cs s :=
  (Term.compile_preserves atoms meanings payload primitive_payload (program cs) s).trans
    (program_denote cs s)

theorem successful_total {cs : List Command} {s t : State} (h : Runs cs s t) :
    totalRun cs s = t := by
  induction h with
  | nil => rfl
  | cons ha hr ih =>
    simp only [totalRun, execute, (step_acts _ _ _).mpr ha, Option.getD_some]
    exact ih

theorem compiled_protocol {cs : List Command} {s t : State} (h : Runs cs s t) :
    ((program cs).compile atoms meanings).run s = t :=
  (program_compile cs s).trans (successful_total h)

/-- The actual source transpose is interpreted by the existing hom adjunction. -/
def commandShift (c : Command) : Term Prim (.down (.one .unrestricted))
    (.down (.atom .unrestricted)) := .downMap (.prim (.literal c))

theorem commandShift_adjunction (c : Command) :
    ((commandShift c).transpose.compile atoms meanings).run =
      shiftAdjunction ((Ty.one .unrestricted).meaning atoms).Carrier
        ((Ty.down (.atom .unrestricted)).meaning atoms)
        ((commandShift c).compile atoms meanings) :=
  Term.transpose_compiles atoms meanings (commandShift c)

theorem commandShift_roundtrip (c : Command) :
    ((commandShift c).transpose.untranspose).compile atoms meanings =
      (commandShift c).compile atoms meanings :=
  Term.transpose_roundtrip atoms meanings (commandShift c)

end SquareKit.OwnedHandle
