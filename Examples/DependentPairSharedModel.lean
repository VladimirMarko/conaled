import Examples.DependentPairSharedFragment

/-! Independent selected meanings for the bounded computed-pair fragment. -/
namespace SquareKit.DependentPairSharedFragment
open DependentTheoryMaps DependentPairTheoryTransport DependentBranchTheoryMaps
set_option backward.isDefEq.respectTransparency false

abbrev Packet := (n : Nat) × Fin (n + 2)

def selected (n : Nat) : Packet := ⟨n+1, ⟨n+1, by omega⟩⟩

inductive Tag where | index | packet | second
  deriving DecidableEq

def Shape.tag : Shape → Tag
  | .index _ => .index
  | .packet _ => .packet
  | .second _ => .second

def Tag.Value : Tag → Type
  | .index => Nat
  | .packet | .second => Packet

abbrev Value (s : Shape) := s.tag.Value

/-- Projection keeps its dependency index alongside the selected component. -/
def project (x : Packet) : Packet := ⟨x.1,x.2⟩

/-- Target elimination destructs the pair and returns the selected branch data. -/
def split (x : Packet) : Packet := Sigma.casesOn x (fun n y => ⟨n,y⟩)

theorem split_project (x : Packet) : split x = project x := by cases x; rfl

def observe (p : Phase) : Packet → Packet :=
  match p with
  | .source | .extended => project
  | .target => split

theorem observe_eq (p q : Phase) (x : Packet) : observe p x = observe q x := by
  cases p <;> cases q <;> cases x <;> rfl

def model (p : Phase) (ρ : SingleV → Nat) : Model (rules p) (fun j => Value j.shape) where
  rule
    | .variable v, _ => ρ v
    | .successor _, xs => Nat.add (xs ()) 1
    | .double _, xs => Nat.mul 2 (xs ())
    | .pair _, xs => selected (xs ())
    | .second _, xs => observe p (xs ())

/-- Local certificate semantics concerns independently supplied premise values. -/
theorem pass_local (p q : Phase) (ρ : SingleV → Nat) :
    (pass p q).LocalMeaning (model p ρ) (model q ρ) (fun _ x => x) := by
  intro r xs
  cases r with
  | «variable» v => rfl
  | successor e => rfl
  | double e => rfl
  | pair e => rfl
  | second e => exact observe_eq q p (xs ())

def meaning {p s} (ρ : SingleV → Nat) (d : Proof p s) : Value s :=
  d.interpret (model p ρ) (fun _ e => e.elim)

theorem translate_meaning {p q s} (ρ : SingleV → Nat) (d : Proof p s) :
    meaning ρ (translate (q := q) d) = meaning ρ d :=
  (pass p q).interpret_transport (model p ρ) (model q ρ) (fun _ x => x)
    (pass_local p q ρ) (H' := fun _ => Empty) (fun _ (e : Empty) => e.elim)
    (fun _ (e : Empty) => e.elim) (fun _ (e : Empty) => e.elim) (fun _ (e : Empty) => e.elim) d

/-- Independent mathematical specification, not the definition of model interpretation. -/
def expected (ρ : SingleV → Nat) : (s : Shape) → Value s
  | .index e => e.meaning ρ
  | .packet e | .second e => selected (e.meaning ρ)

theorem model_rule_expected (p : Phase) (ρ : SingleV → Nat) (r : Step) :
    (model p ρ).rule r (fun i => expected ρ (r.premise i)) = expected ρ r.conclusion := by
  cases r with
  | «variable» v => rfl
  | successor e => rfl
  | double e => rfl
  | pair e => rfl
  | second e => cases p <;> rfl

/-- Every closed fragment derivation has its independently specified selected
meaning. The statement does not assert soundness of arbitrary raw theory trees. -/
theorem interpret_expected {p} (ρ : SingleV → Nat) {j : Sentence p}
    (d : Derivation (rules p) (fun _ => Empty) j) :
    d.interpret (model p ρ) (fun _ e => e.elim) = expected ρ j.shape := by
  induction d with
  | hyp e => exact e.elim
  | rule r ds ih =>
    change (model p ρ).rule r (fun i => (ds i).interpret (model p ρ) (fun _ e => e.elim)) = _
    rw [show (fun i => (ds i).interpret (model p ρ) (fun _ e => e.elim)) =
      (fun i => expected ρ (r.premise i)) from funext ih]
    exact model_rule_expected p ρ r

theorem meaning_expected {p s} (ρ : SingleV → Nat) (d : Proof p s) :
    meaning ρ d = expected ρ s := interpret_expected ρ d

end SquareKit.DependentPairSharedFragment
