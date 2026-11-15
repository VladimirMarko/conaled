import Applications.Resources.Workload

/-! Supplied executable bijections, and an optional finite recipe interpreter.
The bills count declared source events; they are not machine instruction costs. -/
set_option autoImplicit false
set_option warningAsError true
namespace Representations.ExecutableTransport
open Resources
universe u v

/-- Executable maps are supplied independently of their semantic specification. -/
structure Adapter {S : Type u} {T : Type v} (e : S ≃ T) where
  forward : S → Measured T Nat
  backward : T → Measured S Nat
  forward_value : ∀ s, (forward s).1 = e s
  backward_value : ∀ t, (backward t).1 = e.symm t

def Adapter.trans {S T V : Type u} {e : S ≃ T} {d : T ≃ V}
    (a : Adapter e) (b : Adapter d) : Adapter (e.trans d) where
  forward s := bind (a.forward s) b.forward
  backward v := bind (b.backward v) a.backward
  forward_value s := by simp [a.forward_value, b.forward_value]
  backward_value v := by simp [a.backward_value, b.backward_value]

def Adapter.symm {S : Type u} {T : Type v} {e : S ≃ T} (a : Adapter e) : Adapter e.symm where
  forward := a.backward
  backward := a.forward
  forward_value := a.backward_value
  backward_value := a.forward_value

/-- A single named primitive call. Its unit tariff is an explicit model choice. -/
def primitive {S : Type u} {T : Type v} (e : S ≃ T) : Adapter e where
  forward s := (e s, 1)
  backward t := (e.symm t, 1)
  forward_value _ := rfl
  backward_value _ := rfl

/-- The finite recipe retains its typed source and target. Primitives are
supplied executable equivalences, not extracted from native semantic paths. -/
inductive Recipe : Type u → Type u → Type (u + 1) where
  | identity (S : Type u) : Recipe S S
  | atom {S T : Type u} (e : S ≃ T) : Recipe S T
  | sequence {S T V : Type u} (first : Recipe S T) (second : Recipe T V) : Recipe S V
  | reverse {S T : Type u} (body : Recipe S T) : Recipe T S

namespace Recipe
variable {S T : Type u}

def nodes : {S T : Type u} → Recipe S T → Nat
  | _, _, .identity _ => 1
  | _, _, .atom _ => 1
  | _, _, .sequence p q => 1 + p.nodes + q.nodes
  | _, _, .reverse p => 1 + p.nodes

def atoms : {S T : Type u} → Recipe S T → Nat
  | _, _, .identity _ => 0
  | _, _, .atom _ => 1
  | _, _, .sequence p q => p.atoms + q.atoms
  | _, _, .reverse p => p.atoms

def denote : {S T : Type u} → Recipe S T → S ≃ T
  | _, _, .identity S => Equiv.refl S
  | _, _, .atom e => e
  | _, _, .sequence p q => p.denote.trans q.denote
  | _, _, .reverse p => p.denote.symm

private def dispatch {S T : Type u} {e : S ≃ T} (a : Adapter e) : Adapter e where
  forward s := Resources.bind ((), 1) (fun _ => a.forward s)
  backward t := Resources.bind ((), 1) (fun _ => a.backward t)
  forward_value s := a.forward_value s
  backward_value t := a.backward_value t

/-- Each recursive visit charges dispatch, including identity and reversal. -/
def execute : {S T : Type u} → (p : Recipe S T) → Adapter p.denote
  | _, _, .identity S => {
      forward := fun s => (s, 1)
      backward := fun s => (s, 1)
      forward_value := fun _ => rfl
      backward_value := fun _ => rfl }
  | _, _, .atom e => dispatch (primitive e)
  | _, _, .sequence p q => dispatch (p.execute.trans q.execute)
  | _, _, .reverse p => dispatch p.execute.symm

/-- The recursive executor charges every visited node and primitive call in
both directions; reversal changes order without deleting calls. -/
theorem execute_cost (p : Recipe S T) :
    (∀ s, (p.execute.forward s).2 = p.nodes + p.atoms) ∧
    (∀ t, (p.execute.backward t).2 = p.nodes + p.atoms) := by
  induction p with
  | identity S => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | atom e => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | sequence p q hp hq =>
      constructor <;> intro x <;>
        simp only [execute, dispatch, Adapter.trans, Resources.bind, nodes, atoms, hp.1, hp.2, hq.1, hq.2] <;> omega
  | reverse p hp =>
      constructor <;> intro x <;>
        simp only [execute, dispatch, Adapter.symm, Resources.bind, nodes, atoms, hp.1, hp.2, Nat.add_assoc]

/-- Setup scans the immutable recipe afresh. There is no retained cache. -/
def prepared (p : Recipe S T) (s : S) : Measured T Nat :=
  Resources.bind ((), p.nodes) (fun _ => p.execute.forward s)

theorem prepared_cost (p : Recipe S T) (s : S) :
    (p.prepared s).2 = p.nodes + (p.nodes + p.atoms) := by
  exact congrArg (p.nodes + ·) (p.execute_cost.1 s)
end Recipe
end Representations.ExecutableTransport
