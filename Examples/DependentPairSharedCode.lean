import Examples.DependentPairSharedModel

/-! Independent executable code for arithmetic, dependent pair construction,
and observation. Code contains no typing derivations or semantic certificates. -/
namespace SquareKit.DependentPairSharedFragment
open DependentTheoryMaps DependentPairTheoryTransport DependentBranchTheoryMaps
set_option backward.isDefEq.respectTransparency false

inductive Code : Phase → Tag → Type
  | load {p} (v : SingleV) : Code p .index
  | successor {p} : Code p .index → Code p .index
  | double {p} : Code p .index → Code p .index
  | pair : Code .source .index → Code .source .packet
  | etaPair : Code .extended .index → Code .extended .packet
  | pack : Code .target .index → Code .target .packet
  | project : Code .source .packet → Code .source .second
  | etaProject : Code .extended .packet → Code .extended .second
  | split : Code .target .packet → Code .target .second

/-- Runtime construction calculates the bound and selected component. -/
def makePacket (n : Nat) : Packet :=
  let first := n+1
  let second : Fin (first+2) := ⟨n+1, by omega⟩
  ⟨first,second⟩

def Code.run (ρ : SingleV → Nat) : {p : Phase} → {t : Tag} → Code p t → t.Value
  | _, _, .load v => ρ v
  | _, _, .successor c => Nat.add (c.run ρ) 1
  | _, _, .double c => Nat.mul 2 (c.run ρ)
  | _, _, .pair c => makePacket (c.run ρ)
  | _, _, .etaPair c => makePacket (c.run ρ)
  | _, _, .pack c => makePacket (c.run ρ)
  | _, _, .project c => DependentPairSharedFragment.project (c.run ρ)
  | _, _, .etaProject c => DependentPairSharedFragment.project (c.run ρ)
  | _, _, .split c => DependentPairSharedFragment.split (c.run ρ)

def packetCode (p : Phase) : Code p .index → Code p .packet :=
  match p with
  | .source => Code.pair
  | .extended => Code.etaPair
  | .target => Code.pack

def secondCode (p : Phase) : Code p .packet → Code p .second :=
  match p with
  | .source => Code.project
  | .extended => Code.etaProject
  | .target => Code.split

def Code.pass (q : Phase) : {p : Phase} → {t : Tag} → Code p t → Code q t
  | _, _, .load v => .load v
  | _, _, .successor c => .successor (c.pass q)
  | _, _, .double c => .double (c.pass q)
  | _, _, .pair c => packetCode q (c.pass q)
  | _, _, .etaPair c => packetCode q (c.pass q)
  | _, _, .pack c => packetCode q (c.pass q)
  | _, _, .project c => secondCode q (c.pass q)
  | _, _, .etaProject c => secondCode q (c.pass q)
  | _, _, .split c => secondCode q (c.pass q)

@[simp] theorem packetCode_run (p) (ρ) (c : Code p .index) :
    (packetCode p c).run ρ = selected (c.run ρ) := by cases p <;> rfl

@[simp] theorem secondCode_run (p) (ρ) (c : Code p .packet) :
    (secondCode p c).run ρ = observe p (c.run ρ) := by cases p <;> rfl

theorem Code.pass_run {p t} (c : Code p t) (q) (ρ) :
    (c.pass q).run ρ = c.run ρ := by
  induction c with
  | load v => rfl
  | successor c ih => exact congrArg (fun n : Nat => n + 1) ih
  | double c ih => exact congrArg (fun n : Nat => 2 * n) ih
  | pair c ih | etaPair c ih | pack c ih =>
    simp only [Code.pass, packetCode_run, Code.run, ih]
    rfl
  | project c ih =>
    simp only [Code.pass, secondCode_run, Code.run, ih]
    exact observe_eq q .source _
  | etaProject c ih =>
    simp only [Code.pass, secondCode_run, Code.run, ih]
    exact observe_eq q .extended _
  | split c ih =>
    simp only [Code.pass, secondCode_run, Code.run, ih]
    exact observe_eq q .target _

@[simp] theorem Code.pass_packet (p q) (c : Code p .index) :
    (packetCode p c).pass q = packetCode q (c.pass q) := by cases p <;> rfl
@[simp] theorem Code.pass_second (p q) (c : Code p .packet) :
    (secondCode p c).pass q = secondCode q (c.pass q) := by cases p <;> rfl

theorem Code.pass_identity {p t} (c : Code p t) : c.pass p = c := by
  induction c <;> simp_all [Code.pass, packetCode, secondCode]

theorem Code.pass_comp {p t} (c : Code p t) (q r) :
    (c.pass q).pass r = c.pass r := by
  induction c <;> simp_all [Code.pass]

def codeModel (p : Phase) : Model (rules p) (fun j => Code p j.shape.tag) where
  rule
    | .variable v, _ => .load v
    | .successor _, cs => .successor (cs ())
    | .double _, cs => .double (cs ())
    | .pair _, cs => packetCode p (cs ())
    | .second _, cs => secondCode p (cs ())

def compileCode {p s} (d : Proof p s) : Code p s.tag :=
  d.interpret (codeModel p) (fun _ e => e.elim)

/-- A code compiler's local operations realize the independent model rules. -/
theorem code_rule_sound (p) (ρ) (r : Step) (cs : (i : r.Arity) → Code p (r.premise i).tag) :
    ((codeModel p).rule r cs).run ρ = (model p ρ).rule r (fun i => (cs i).run ρ) := by
  cases r with
  | «variable» v => rfl
  | successor e => rfl
  | double e => rfl
  | pair e => exact packetCode_run p ρ (cs ())
  | second e => exact secondCode_run p ρ (cs ())

theorem interpret_code_sound {p} (ρ) {j : Sentence p}
    (d : Derivation (rules p) (fun _ => Empty) j) :
    (d.interpret (codeModel p) (fun _ e => e.elim)).run ρ =
      d.interpret (model p ρ) (fun _ e => e.elim) := by
  induction d with
  | hyp e => exact e.elim
  | rule r ds ih =>
    simp only [Derivation.interpret]
    rw [code_rule_sound]
    congr 1
    funext i
    exact ih i

theorem compileCode_sound {p s} (ρ) (d : Proof p s) :
    (compileCode d).run ρ = meaning ρ d := interpret_code_sound ρ d

theorem code_pass_local (p q : Phase) :
    (pass p q).LocalMeaning (codeModel p) (codeModel q) (fun _ c => c.pass q) := by
  intro r cs
  cases r with
  | «variable» v => rfl
  | successor e => rfl
  | double e => rfl
  | pair e => exact (Code.pass_packet p q (cs ())).symm
  | second e => exact (Code.pass_second p q (cs ())).symm

/-- Proof compilation and executable pass compilation derive the same code. -/
theorem compileCode_translate {p q s} (d : Proof p s) :
    compileCode (translate (q := q) d) = (compileCode d).pass q :=
  (pass p q).interpret_transport (codeModel p) (codeModel q) (fun _ c => c.pass q)
    (code_pass_local p q) (H' := fun _ => Empty) (fun _ (e : Empty) => e.elim)
    (fun _ (e : Empty) => e.elim) (fun _ (e : Empty) => e.elim) (fun _ (e : Empty) => e.elim) d

end SquareKit.DependentPairSharedFragment
