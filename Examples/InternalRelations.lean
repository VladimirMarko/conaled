import SquareKit.RelationComposition
import Examples.InternalGraphs

/-! Many-valued clients, explicit witnesses, and binder checks for issue #45. -/
namespace Examples.InternalRelations
open Relational SquareKit.Internal

/-- One input relates to both outputs; neither output is selected. -/
def Both : Unit → Bool → Prop := fun _ _ => True

theorem both_outputs : Both () false ∧ Both () true := ⟨True.intro, True.intro⟩

theorem no_decoder : ¬ ∃ decode : Unit → Bool, ∀ a b, Both a b ↔ decode a = b := by
  rintro ⟨decode, h⟩
  have hf := (h () false).mp both_outputs.1
  have ht := (h () true).mp both_outputs.2
  exact Bool.noConfusion (hf.symm.trans ht)

def Small : Bool → Nat → Prop := fun _ n => n = 0 ∨ n = 1
def Shifted : Bool → Nat → Prop := fun _ n => n = 1 ∨ n = 2
def Integer : Nat → Int → Prop := fun n z => z = Int.ofNat n

def flip : RelSquare ⟨Unit, Bool, Both⟩ ⟨Unit, Bool, Both⟩ where
  impl := id
  spec := Bool.not
  preserves _ := True.intro

def raise : RelSquare ⟨Bool, Nat, Small⟩ ⟨Bool, Nat, Shifted⟩ where
  impl b := Bool.xor b true
  spec n := n + 1
  preserves := by
    rintro b n (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

def raiseInt : RelSquare ⟨Nat, Int, Integer⟩ ⟨Nat, Int, Integer⟩ where
  impl n := 1 + n
  spec z := z + 1
  preserves := by
    intro n z hz
    change z = Int.ofNat n at hz
    change z + 1 = Int.ofNat (1 + n)
    rw [hz]
    simp [Int.add_comm]

theorem flip_raise (b : Bool) : flip.spec b = raise.impl b := by cases b <;> rfl
theorem raise_integer (n : Nat) : raise.spec n = raiseInt.impl n := Nat.add_comm n 1

-- A concrete composite has two possible outputs and maps 0 to 1.
example : (existential Both Small).Rel () 0 ∧ (existential Both Small).Rel () 1 :=
  ⟨⟨false, True.intro, Or.inl rfl⟩, ⟨true, True.intro, Or.inr rfl⟩⟩

example : (existential Both Shifted).Rel () 1 :=
  (existentialSquare flip raise flip_raise).preserves
    (show (existential Both Small).Rel () 0 from ⟨false, True.intro, Or.inl rfl⟩)

-- Four distinct carriers, nontrivial maps, and pointwise middle agreement.
example :
    transportRelations (existentialSquare (existentialSquare flip raise flip_raise)
        raiseInt raise_integer)
      (CompRel Both (CompRel Small Integer)) (CompRel Both (CompRel Shifted Integer))
      (compRel_assoc Both Small Integer) (compRel_assoc Both Shifted Integer) =
      existentialSquare flip (existentialSquare raise raiseInt raise_integer) flip_raise :=
  existential_reassociate flip raise raiseInt flip_raise raise_integer

example : CompRel Both (CompRel Shifted Integer) () 2 := by
  have initial : CompRel (CompRel Both Small) Integer () 1 :=
    ⟨1, ⟨false, True.intro, Or.inr rfl⟩, rfl⟩
  exact (compRel_assoc Both Shifted Integer () 2).mp
    ((existentialSquare (existentialSquare flip raise flip_raise) raiseInt raise_integer).preserves initial)

-- Retaining the last two relation hypotheses rejects an unrelated endpoint.
example : ¬ CompRel Both (CompRel Small Integer) () 3 := by
  intro h
  obtain ⟨n, ⟨_, _, hn⟩, hz⟩ := (compRel_assoc Both Small Integer () 3).mpr h
  rcases hn with rfl | rfl <;> simp [Integer] at hz

-- If the middle relation has no witness, reassociation cannot create one.
example : ¬ CompRel Both (CompRel (fun (_ : Bool) (_ : Nat) => False) Integer) () 0 := by
  intro h
  obtain ⟨_, ⟨_, _, impossible⟩, _⟩ :=
    (compRel_assoc Both (fun (_ : Bool) (_ : Nat) => False) Integer () 0).mpr h
  exact impossible

example (R : Unit → Empty → Prop) (S : Empty → Nat → Prop) (z : Int) :
    ¬ CompRel R (CompRel S Integer) () z := by
  intro h
  obtain ⟨_, ⟨b, _, _⟩, _⟩ := (compRel_assoc R S Integer () z).mpr h
  exact nomatch b

/-- Two middle values witness the same pair of endpoints. -/
def viaFalse : Intermediate Both Small := ⟨(), false, 0, True.intro, Or.inl rfl⟩
def viaTrue : Intermediate Both Small := ⟨(), true, 0, True.intro, Or.inl rfl⟩

theorem distinct_middle : viaFalse ≠ viaTrue := by
  intro h
  exact Bool.noConfusion (congrArg Intermediate.middle h)

theorem forgotten_middle : viaFalse.forget = viaTrue.forget := rfl

example :
    Squares.compose (forgetIntermediate Both Shifted) (intermediateSquare flip raise flip_raise) =
      Squares.compose (witnessSquare (existentialSquare flip raise flip_raise))
        (forgetIntermediate Both Small) :=
  forgetIntermediate_natural flip raise flip_raise

example : ((intermediateSquare flip raise flip_raise).impl viaFalse).middle = true := rfl
example : ((intermediateSquare flip raise flip_raise).impl viaFalse).target = 1 := rfl
example : (forgetIntermediate Both Shifted).impl
    ((intermediateSquare flip raise flip_raise).impl viaFalse) =
    (witnessSquare (existentialSquare flip raise flip_raise)).impl viaFalse.forget :=
  congrArg (fun f => f.impl viaFalse) (forgetIntermediate_natural flip raise flip_raise)

-- The same relation theorem is available to ordinary and internal clients.
example : (∃ c, (∃ b, Both () b ∧ Small b c) ∧ Integer c 1) ↔
    (∃ b, Both () b ∧ ∃ c, Small b c ∧ Integer c 1) :=
  Associativity.in_set Both Small Integer () 1

example {S : Type} {F P : S → S → Type} {a b c d : S} {Δ : List S}
    (r : P a b) (s : P b c) (t : P c d) (σ : Sub F [a, d] Δ) :
    Derives ((Associativity.left r s t).subst σ) ((Associativity.right r s t).subst σ) :=
  Rules.substitute σ (Associativity.forward r s t)

example {S : Type} {F P : S → S → Type} {a b c d e : S}
    (r : P a b) (s : P b c) (t : P c d) :
    Derives ((Associativity.right (F := F) r s t).shift (s := e))
      (Associativity.left r s t).shift :=
  Rules.weaken (Associativity.backward r s t)

/-- Substituting a term of the binder's own sort must not capture it in an atom. -/
example {S : Type} {F P : S → S → Type} {s : S} {Δ : List S}
    (M : Interpretation F P) (r : P s s) (ρ : Env M Δ) (t : Term F Δ s) :
    let σ : Sub F [s] Δ := fun {_} i => match i with | .zero => t | .succ i => nomatch i
    ((Formula.ex (.atom r (.var (.succ .zero)) (.var .zero))).subst σ).Eval M ρ ↔
      ∃ x : M.Carrier s, M.Relation r (t.eval M ρ) x := by
  dsimp only
  rw [formula_subst]
  rfl
end Examples.InternalRelations
