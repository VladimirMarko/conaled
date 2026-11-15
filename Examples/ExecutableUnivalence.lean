import Applications.Representations.ExecutableTransport
import Examples.CubicalNativeUnivalenceTransport
import Examples.CompositionalUnivalence
import Examples.CubicalFiniteStateIdentity
import Examples.FiniteUniverseLoops
import Examples.ParserWorkload

/-! Executable finite transports refine actual native ua observations. The
machine runner records each observation and charges all declared source events. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.ExecutableUnivalence
open Resources Representations.ExecutableTransport
open CubicalUnivalenceTransport CubicalFiniteStateIdentity

/-- A supplied executable map agrees with the observation of actual decoded ua. -/
theorem forward_native {S T : Type} {e : S ≃ T} (a : Adapter e) (s : S) :
    constantSection (a.forward s).1 = CubicalNativeUnivalenceTransport.observedNative e s := by
  rw [a.forward_value, CubicalNativeUnivalenceTransport.observedNative_eq]

/-- The target is the selected reverse of the original native path. -/
theorem backward_native {S T : Type} {e : S ≃ T} (a : Adapter e) (t : T) :
    constantSection (a.backward t).1 = CompositionalUnivalence.observedInverse e t := by
  rw [a.backward_value, CompositionalUnivalence.observedInverse_eq]

theorem composition_native {S T V : Type} {e : S ≃ T} {d : T ≃ V}
    (a : Adapter e) (b : Adapter d) (s : S) :
    constantSection ((a.trans b).forward s).1 = CompositionalUnivalence.observedConcat e d s := by
  rw [(a.trans b).forward_value, CompositionalUnivalence.observedConcat_eq]
  rfl

def boolAdapter := primitive CubicalGlue.booleanTransposition

def cycle : Fin 3 ≃ Fin 3 := FiniteUniverseLoops.swap01.trans FiniteUniverseLoops.swap12

def cycleAdapter := primitive cycle

def cycleRecipe : Recipe (Fin 3) (Fin 3) := .atom cycle

def cancellation : Recipe (Fin 3) (Fin 3) := .sequence cycleRecipe (.reverse cycleRecipe)

theorem cycle_directions : (cycleAdapter.forward 0).1 = 2 ∧
    (cycleAdapter.backward 0).1 = 1 := by decide

theorem syntax_forward_native (p : Recipe (Fin 3) (Fin 3)) (s : Fin 3) :
    constantSection (p.execute.forward s).1 =
      CubicalNativeUnivalenceTransport.observedNative p.denote s := forward_native p.execute s

theorem syntax_reverse_native (p : Recipe (Fin 3) (Fin 3)) (s : Fin 3) :
    constantSection (p.execute.backward s).1 =
      CompositionalUnivalence.observedInverse p.denote s := backward_native p.execute s

theorem cancellation_value (s : Fin 3) : (cancellation.execute.forward s).1 = s := by
  rw [cancellation.execute.forward_value]
  exact cycle.symm_apply_apply s

theorem cancellation_positive_cost (s : Fin 3) : (cancellation.execute.forward s).2 = 6 :=
  cancellation.execute_cost.1 s

/-- Three direct calls implement the conjugated step; observation and list
construction each add one declared event. -/
abbrev MachineState := Phase × List Nat

def advance (a : Adapter presentation) (_ : Unit) (z : MachineState) : Measured MachineState Nat :=
  Resources.bind (a.backward z.1) fun s =>
  Resources.bind (machine.step s, 1) fun s' =>
  Resources.bind (a.forward s') fun p =>
  Resources.bind (observer p, 1) fun o => ((p, o :: z.2), 1)

def directPresentation : Adapter presentation := primitive presentation

def syntaxPresentation : Adapter presentation := (Recipe.atom presentation).execute

def specAdvance (_ : Unit) (z : MachineState) : MachineState :=
  let p := presentedMachine.step z.1
  (p, observer p :: z.2)

noncomputable def nativeAdvance (_ : Unit) (z : MachineState) : MachineState :=
  let p := machineTransported.step z.1
  (p, observer p :: z.2)

theorem advance_value (a : Adapter presentation) (i : Unit) (z : MachineState) :
    (advance a i z).1 = specAdvance i z := by
  simp only [advance, Resources.bind, a.backward_value, a.forward_value]
  rfl

theorem nativeAdvance_eq : nativeAdvance = specAdvance := by
  funext i z
  simp only [nativeAdvance, machineTransported_eq, specAdvance]

theorem run_native (a : Adapter presentation) (is : List Unit) (z : MachineState) :
    (Resources.run (advance a) is z).1 = is.foldl (fun s i => nativeAdvance i s) z := by
  rw [nativeAdvance_eq]
  exact Resources.run_value_fusion (advance a) specAdvance id (fun _ => True)
    (fun _ _ _ => trivial) (fun i s _ => advance_value a i s) is z trivial

theorem run_invariant (a : Adapter presentation) (is : List Unit) (z : MachineState)
    (hz : machineTransported.invariant z.1) :
    machineTransported.invariant (Resources.run (advance a) is z).1.1 := by
  rw [machineTransported_eq] at hz ⊢
  apply Resources.run_invariant (advance a) (fun s => presentedMachine.invariant s.1) _ is z hz
  intro i s hs
  rw [advance_value]
  exact presentedMachine.preserves s.1 hs

/-- Input conversion and setup are eager even for an empty command list.
Export reverses the collected observations and charges one event per list cell. -/
def executeMachine (setup : Nat) (a : Adapter presentation) (is : List Unit) (s : Fin 3) :
    Measured MachineState Nat :=
  Resources.bind ((), setup) fun _ =>
  Resources.bind (a.forward s) fun p =>
  Resources.bind (Resources.run (advance a) is (p, [])) fun z =>
    ((z.1, z.2.reverse), z.2.length + 1)

noncomputable def nativeMachine (is : List Unit) (s : Fin 3) : MachineState :=
  let z := is.foldl (fun z i => nativeAdvance i z) (presentation s, [])
  (z.1, z.2.reverse)

theorem executeMachine_native (setup : Nat) (a : Adapter presentation) (is : List Unit) (s : Fin 3) :
    (executeMachine setup a is s).1 = nativeMachine is s := by
  simp only [executeMachine, Resources.bind, a.forward_value, run_native, nativeMachine]

/-- Complete native package equality supplies the operation and invariant used
above; execution does not replace its proof-bearing fields with a new package. -/
theorem full_package_recovery : machineTransported = machine.conjugate presentation :=
  machineTransported_eq

theorem history_length (a : Adapter presentation) (is : List Unit) (z : MachineState) :
    (Resources.run (advance a) is z).1.2.length = is.length + z.2.length := by
  induction is generalizing z with
  | nil => simp
  | cons i is ih =>
      rw [Resources.run_cons, ih, advance_value]
      simp only [specAdvance, List.length_cons]
      omega

theorem advance_cost (a : Adapter presentation) (c : Nat)
    (hf : ∀ s, (a.forward s).2 = c) (hb : ∀ p, (a.backward p).2 = c)
    (i : Unit) (z : MachineState) : (advance a i z).2 = 2 * c + 3 := by
  simp only [advance, Resources.bind, hf, hb]
  omega

theorem run_cost (a : Adapter presentation) (c : Nat)
    (hf : ∀ s, (a.forward s).2 = c) (hb : ∀ p, (a.backward p).2 = c)
    (is : List Unit) (z : MachineState) :
    (Resources.run (advance a) is z).2 = is.length * (2 * c + 3) := by
  induction is generalizing z with
  | nil => simp
  | cons i is ih =>
      rw [Resources.run_cons, advance_cost a c hf hb, ih]
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem executeMachine_cost (setup : Nat) (a : Adapter presentation) (c : Nat)
    (hf : ∀ s, (a.forward s).2 = c) (hb : ∀ p, (a.backward p).2 = c)
    (is : List Unit) (s : Fin 3) :
    (executeMachine setup a is s).2 = setup + c + is.length * (2 * c + 4) + 1 := by
  simp only [executeMachine, Resources.bind, hf, run_cost a c hf hb, history_length, List.length_nil, Nat.add_zero]
  simp only [Nat.mul_succ]
  omega

def directMachine := executeMachine 1 directPresentation

def syntaxMachine := executeMachine 1 syntaxPresentation

theorem directMachine_cost (is : List Unit) (s : Fin 3) :
    (directMachine is s).2 = 3 + 6 * is.length := by
  have h := executeMachine_cost 1 directPresentation 1 (fun _ => rfl) (fun _ => rfl) is s
  change (executeMachine 1 directPresentation is s).2 = _
  omega

theorem syntaxMachine_cost (is : List Unit) (s : Fin 3) :
    (syntaxMachine is s).2 = 4 + 8 * is.length := by
  have h := executeMachine_cost 1 syntaxPresentation 2 (fun _ => rfl) (fun _ => rfl) is s
  change (executeMachine 1 syntaxPresentation is s).2 = _
  omega

theorem matched_observations (is : List Unit) (s : Fin 3) :
    (directMachine is s).1 = (syntaxMachine is s).1 :=
  (executeMachine_native 1 directPresentation is s).trans
    (executeMachine_native 1 syntaxPresentation is s).symm

theorem syntax_extra_work (is : List Unit) (s : Fin 3) :
    (syntaxMachine is s).2 = (directMachine is s).2 + 1 + 2 * is.length := by
  rw [directMachine_cost, syntaxMachine_cost]
  omega

/-- The known wrong presentation preserves the start but fails the first step. -/
theorem wrong_adapter_rejected : ¬ CubicalStructuredState.Preserves wrongPresentation machine presentedMachine :=
  wrong_rejected

/-- Executed checks include every finite input, both directions, and all
machine states, including the state excluded by the reachable invariant. -/
def runtimeTests : IO Unit := do
  for b in [false, true] do
    unless (boolAdapter.forward b).1 == !b do
      throw (IO.userError "Boolean forward mismatch")
    unless (boolAdapter.backward b).1 == !b do
      throw (IO.userError "Boolean inverse mismatch")
  for s in ([0, 1, 2] : List (Fin 3)) do
    unless (cycleRecipe.execute.forward s).1 == cycle s do
      throw (IO.userError "Cycle forward mismatch")
    unless (cycleRecipe.execute.backward s).1 == cycle.symm s do
      throw (IO.userError "Cycle inverse mismatch")
    unless (cancellation.execute.forward s) == (s, 6) do
      throw (IO.userError "Cancellation lost value or cost")
    for n in [0, 1, 8] do
      let commands := List.replicate n ()
      let direct := directMachine commands s
      let interpreted :=  syntaxMachine commands s
      unless direct.1 == interpreted.1 do
        throw (IO.userError "Machine observation mismatch")
      unless direct.2 == 3 + 6 * n && interpreted.2 == 4 + 8 * n do
        throw (IO.userError "Machine cost mismatch")
      let expected := if n == 0 then presentation s else if s == 2 then Phase.failed else Phase.ready
      unless direct.1.1 == expected do
        throw (IO.userError "Machine final state mismatch")
      unless direct.1.2 == List.replicate n (if s == 2 then 2 else 1) do
        throw (IO.userError "Machine intermediate observations mismatch")
  unless (cycleAdapter.forward 0).1 != (cycleAdapter.backward 0).1 do
    throw (IO.userError "Direction control failed")
  unless FiniteUniverseLoops.swap12 (FiniteUniverseLoops.swap01 0) !=
      FiniteUniverseLoops.swap01 (FiniteUniverseLoops.swap12 0) do
    throw (IO.userError "Composition order control failed")
  IO.println "Executable ua tests passed: Boolean, cycle/reversal, positive-cost cancellation, and all machine states at 0/1/8 steps."

#eval runtimeTests

end Examples.ExecutableUnivalence
