import SquareKit.Internal.TwoLoop
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

/-! A finite strict 2-groupoid with observable 2-automorphisms. The identity
levels are explicit data in Mathlib's bicategory, not native Lean equality.
The source fragment is algebraic 2-loops; no dependent identity elimination
or interpretation of unrestricted higher type theory is claimed. -/
namespace Examples.SecondIdentity
open CategoryTheory SquareKit.DoubleDelooping SquareKit.Internal.TwoLoop

abbrev Label := Multiplicative (ZMod 2)
abbrev Bit := Multiplicative Bool
abbrev Two := Space Label
abbrev BitTwo := Space Bit

def zeroCell : Cell Label := (Multiplicative.ofAdd (0 : ZMod 2) : Label)
def oneCell : Cell Label := (Multiplicative.ofAdd (1 : ZMod 2) : Label)

/-- Independent label observation: the integer representative modulo two. -/
def labelObservation (p : Label) : Nat := (Multiplicative.toAdd p).val

/-- Independent Boolean observation of the XOR representation. -/
def bitObservation (p : Bit) : Nat := if Multiplicative.toAdd p then 1 else 0

theorem cell_distinct : zeroCell ≠ oneCell := by
  intro h
  have bad := congrArg labelObservation h
  exact (by decide : (0 : Nat) ≠ 1) bad

/-- Both 2-cell implementations use actual strict bicategories. -/
example : Bicategory.Strict Two := inferInstance
example : Bicategory.Strict BitTwo := inferInstance
example : Groupoid (point Label ⟶ point Label) := inferInstance
local instance : Fintype (Cell Label) := inferInstanceAs (Fintype Label)
local instance : Fintype Two := inferInstanceAs (Fintype Unit)
local instance : Fintype (point Label ⟶ point Label) :=
  inferInstanceAs (Fintype (SingleObj Label))
example : Fintype.card Two = 1 := by decide
example : Fintype.card (point Label ⟶ point Label) = 1 := by decide
example : Fintype.card (Cell Label) = 2 := by decide

/-- Coordinate equivalence, proved from the two finite multiplication tables. -/
def encode : Bit ≃* Label where
  toFun b := Multiplicative.ofAdd (if Multiplicative.toAdd b then 1 else 0)
  invFun n := Multiplicative.ofAdd (Multiplicative.toAdd n == 1)
  left_inv b := by cases b <;> rfl
  right_inv n := by
    have h : ∀ n : ZMod 2, (if n == 1 then (1 : ZMod 2) else 0) = n := by decide
    exact h n
  map_mul' b c := by cases b <;> cases c <;> decide

theorem observation_encode (b : Bit) : labelObservation (encode b) = bitObservation b := by
  cases b <;> rfl

theorem encode_vertical (p q : Cell Bit) :
    encode (vertical Bit p q) = vertical Label (encode p) (encode q) :=
  map_vertical encode.toMonoidHom p q

theorem encode_horizontal (p q : Cell Bit) :
    encode (horizontal Bit p q) = horizontal Label (encode p) (encode q) :=
  map_horizontal encode.toMonoidHom p q

/-- A mixed pasting diagram with odd generator count: h(x, x⁻¹) above h(x, 1). -/
def construction : Expr Unit :=
  .vertical (.horizontal (.var ()) (.inverse (.var ()))) (.horizontal (.var ()) .unit)

/-- Interchange changes the pasting order without changing its boundary. -/
def reordered : Expr Unit :=
  .horizontal (.vertical (.var ()) (.var ())) (.vertical (.inverse (.var ())) .unit)

theorem source_interchange : Derives construction reordered :=
  .interchange _ _ _ _

def bitInput : Unit → Bit := fun _ => Multiplicative.ofAdd true
def labelInput : Unit → Label := fun _ => oneCell

/-- The two interpretations consume exactly the same source expression. -/
theorem routes_agree (e : Expr Unit) :
    encode (e.eval bitInput) = e.eval labelInput :=
  (interpretationSquare encode.toMonoidHom e).commutes bitInput

theorem observations_agree (e : Expr Unit) :
    bitObservation (e.eval bitInput) = labelObservation (e.eval labelInput) := by
  rw [← routes_agree, observation_encode]

theorem bit_interchange : construction.eval bitInput = reordered.eval bitInput :=
  sound source_interchange bitInput

theorem label_interchange : construction.eval labelInput = reordered.eval labelInput :=
  sound source_interchange labelInput

/-- Direct source reduction independently predicts the nonidentity output. -/
theorem bit_construction : construction.eval bitInput = Multiplicative.ofAdd true := rfl

theorem label_construction : construction.eval labelInput = oneCell := by
  rw [← routes_agree, bit_construction]
  rfl

example : bitObservation (construction.eval bitInput) = 1 := rfl
example : labelObservation (construction.eval labelInput) = 1 := by
  rw [label_construction]
  rfl
example : labelObservation ((Expr.unit : Expr Unit).eval labelInput) = 0 := rfl

/-- Replacing the generator by its double changes the mixed diagram to identity. -/
theorem substituted_construction :
    (construction.subst (fun _ => Expr.vertical (.var ()) (.var ()))).eval labelInput =
      zeroCell := by
  rw [Expr.eval_subst]
  rfl

/-- A second pass through the inverse representation recovers the same 2-cell. -/
theorem route_roundtrip (e : Expr Unit) :
    encode.symm (e.eval labelInput) = e.eval bitInput := by
  rw [← routes_agree, encode.symm_apply_apply]

/-- Ordinary clients need no source syntax for interchange or cancellation. -/
example (p q r s : Cell Label) :
    vertical Label (horizontal Label p q) (horizontal Label r s) =
      horizontal Label (vertical Label p r) (vertical Label q s) :=
  interchange Label p q r s
example : vertical Label oneCell oneCell = zeroCell := by
  change (1 + 1 : ZMod 2) = 0
  decide
example : horizontal Label oneCell oneCell = zeroCell := by
  change (1 + 1 : ZMod 2) = 0
  decide
example : arrow Label ≫ arrow Label = 𝟙 (point Label) := arrow_inverse Label

/-- The ordinary groupoid obtained by forgetting all 2-cell labels. -/
abbrev Truncated := LocallyDiscrete (Discrete Unit)
def truncatedPoint : Truncated := ⟨⟨()⟩⟩
def truncatedArrow : truncatedPoint ⟶ truncatedPoint := 𝟙 _
def truncate (_ : Cell Label) : truncatedArrow ⟶ truncatedArrow := 𝟙 _

theorem truncate_vertical (p q : Cell Label) :
    truncate (vertical Label p q) = truncate p ≫ truncate q := by
  apply Subsingleton.elim

theorem truncate_horizontal (p q : Cell Label) :
    truncate (horizontal Label p q) =
      Bicategory.whiskerRight (truncate p) truncatedArrow ≫
        Bicategory.whiskerLeft truncatedArrow (truncate q) := by
  apply Subsingleton.elim

theorem truncation_loses_construction :
    truncate (construction.eval (A := Label) labelInput) = truncate ((Expr.unit : Expr Unit).eval (A := Label) labelInput) :=
  Subsingleton.elim _ _

/-- Loss occurs in any ordinary category viewed as locally discrete, not
only in the terminal example. Boundary-preserving 2-arrows are subsingletons. -/
theorem no_groupoid_observation {C : Type} [Category C]
    (x y : LocallyDiscrete C) (f g : x ⟶ y)
    (forget : Cell Label → (f ⟶ g)) :
    ¬ ∃ observe : (f ⟶ g) → Nat, ∀ c, observe (forget c) = labelObservation c := by
  rintro ⟨observe, h⟩
  have same : forget zeroCell = forget oneCell := Subsingleton.elim _ _
  have bad := (h zeroCell).symm.trans ((congrArg observe same).trans (h oneCell))
  exact (by decide : (0 : Nat) ≠ 1) bad

/-- Even keeping a native equality proof as output cannot encode the two labels. -/
theorem no_native_identity_observation {T : Type} (x : T)
    (forget : Cell Label → (x = x)) :
    ¬ ∃ observe : (x = x) → Nat, ∀ c, observe (forget c) = labelObservation c := by
  rintro ⟨observe, h⟩
  have same : forget zeroCell = forget oneCell := Subsingleton.elim _ _
  have bad := (h zeroCell).symm.trans ((congrArg observe same).trans (h oneCell))
  exact (by decide : (0 : Nat) ≠ 1) bad
end Examples.SecondIdentity
