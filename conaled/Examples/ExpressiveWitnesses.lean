import Applications.Languages.Parser
import Dependent
import Mathlib.Data.List.OfFn

/-! Bounded computational fixtures for #140. Routes are the native split-family
model and certified list representations, and direct parse witnesses and the
witness-preserving derivative rule. No general dependent frontend is claimed. -/
namespace Examples.ExpressiveWitnesses
open DependentSquares LanguageWitnesses

namespace Parse
abbrev Optional : Language Bool := fun w => epsilon w ⊕ atom true w
abbrev Trees := Concat Optional Optional [true]

/-- Independent observation: did the left subtree consume the token? -/
def leftConsumes (t : Trees) : Bool := !t.leftWord.isEmpty

def leftTree : Trees := ⟨[true], [], rfl, .inr ⟨rfl⟩, .inl ⟨rfl⟩⟩
def rightTree : Trees := ⟨[], [true], rfl, .inl ⟨rfl⟩, .inr ⟨rfl⟩⟩

/-- The selected tree is data in a dependent pair; its `joined` field certifies yield. -/
def selected (t : Trees) : ParsedWord (Concat Optional Optional) := ⟨[true], t⟩

def derivativeRoute := derivativeConcatIso Optional Optional true []

def derivativeObservation : (Optional [] × Optional [true]) ⊕
    Concat (derivative Optional true) Optional [] → Bool
  | .inl _ => false
  | .inr _ => true

theorem observation_preserved (t : Trees) :
    derivativeObservation (derivativeRoute.forward t) = leftConsumes t := by
  rcases t with ⟨u, v, h, p, q⟩
  cases u with
  | nil =>
    change v = [true] at h
    subst v
    rfl
  | cons a u =>
    have ha := (List.cons.inj h).1
    subst a
    rfl

theorem selected_roundtrip (t : Trees) :
    selected (derivativeRoute.backward (derivativeRoute.forward t)) = selected t :=
  congrArg selected (derivativeRoute.backward_forward t)

theorem distinct : leftTree ≠ rightTree := by
  intro h
  have := congrArg leftConsumes h
  contradiction

example : derivativeObservation (derivativeRoute.forward leftTree) = true :=
  observation_preserved leftTree
example : derivativeObservation (derivativeRoute.forward rightTree) = false :=
  observation_preserved rightTree
theorem selected_yield (t : Trees) :
    (selected t).2.leftWord ++ (selected t).2.rightWord = (selected t).1 :=
  (selected t).2.joined

/-- Propositional membership deliberately forgets the selected derivation. -/
theorem forget (t : Trees) : Nonempty Trees := ⟨t⟩

theorem observation_does_not_factor :
    ¬ ∃ observe : Nonempty Trees → Bool, ∀ t, observe (forget t) = leftConsumes t := by
  rintro ⟨observe, h⟩
  have same : forget leftTree = forget rightTree := Subsingleton.elim _ _
  have bad := (h leftTree).symm.trans ((congrArg observe same).trans (h rightTree))
  contradiction
end Parse

namespace Vectors
abbrev Vec (n : Nat) := Fin n → Bool
abbrev ListVec (n : Nat) := {xs : List Bool // xs.length = n}

def encode {n} (v : Vec n) : ListVec n := ⟨List.ofFn v, List.length_ofFn⟩
def decode {n} (v : ListVec n) : Vec n := fun i => v.1[i.val]'(by rw [v.2]; exact i.isLt)

theorem decode_encode {n} (v : Vec n) : decode (encode v) = v := by
  funext i
  simp [decode, encode]

/-- The source construction is a section of the genuinely indexed family. -/
def source : Tm Vec := fun _ i => i.val % 2 == 0

abbrev context : CtxRep Nat := ⟨Nat, id⟩
def lists : TyRep context Vec := ⟨ListVec, fun _ => decode⟩
def compileSection (t : Tm Vec) : TermCert context lists t where
  code := fun n => encode (t n)
  commutes := fun n => decode_encode (t n)

abbrev compiled := compileSection source

/-- Lookup is dependent elimination with domain Fin n, including the empty case. -/
def lookup (z : Ext Nat Vec) : Fin z.1 → Bool := z.2

theorem lookup_comparison (n : Nat) (i : Fin n) :
    decode (compiled.code n) i = lookup ⟨n, source n⟩ i :=
  congrFun (compiled.commutes n) i

/-- Duplicate every length: this map is surjective and noninjective. -/
def collapse : Nat → Nat := fun n => n / 2
def shift : Nat → Nat := fun n => n + 2
def collapseCert : SubCert context context collapse := ⟨collapse, fun _ => rfl⟩
def shiftCert : SubCert context context shift := ⟨shift, fun _ => rfl⟩

theorem collapse_noninjective : ¬ Function.Injective collapse := by
  intro h
  have bad := h (show collapse 0 = collapse 1 from rfl)
  contradiction

abbrev once := compiled.reindex collapseCert
abbrev twice := once.reindex shiftCert
abbrev composed := compiled.reindex (collapseCert.compose shiftCert)

theorem substitution_lookup (n : Nat) (i : Fin (collapse n)) :
    decode (once.code n) i = source (collapse n) i :=
  congrFun (once.commutes n) i

theorem composition_code : twice.code = composed.code := rfl

theorem composition_lookup (n : Nat) (i : Fin (collapse (shift n))) :
    decode (twice.code n) i = source (collapse (shift n)) i :=
  congrFun (twice.commutes n) i

/-- Pairing and both projections use the shared certified context extension. -/
abbrev packed := sectionCert compiled

theorem pair_comparison (n : Nat) :
    (extendRep context lists).meaning (packed.code n) = ⟨n, source n⟩ :=
  packed.commutes n

theorem projection_length (n : Nat) : (pCert context lists).code (packed.code n) = n := rfl

theorem projection_value (n : Nat) :
    decode ((qCert context lists).code (packed.code n)) = source n := compiled.commutes n

/-- Substitution of the dependent pair, with a noninjective base substitution. -/
theorem pair_substitution :
    (fun n => (extendRep context lists).meaning (packed.code (collapse n))) =
      extend collapse (tmSub source collapse) := by
  funext n
  exact packed.commutes (collapse n)

/-- The first and dependent second projections commute with substitution. -/
theorem first_substitution :
    compSub p (extend collapse (tmSub source collapse)) = collapse :=
  p_extend collapse (tmSub source collapse)

theorem second_substitution :
    tmSub q (extend collapse (tmSub source collapse)) = tmSub source collapse :=
  q_extend collapse (tmSub source collapse)

/-- The same package as an internal dependent sum over the length term. -/
abbrev lengths : Ty Nat := fun _ => Nat
abbrev entries : Ty (Ext Nat lengths) := fun z => Vec z.2
abbrev lengthTerm : Tm lengths := id
abbrev sumTerm : Tm (sigmaTy lengths entries) := pairTerm lengthTerm source

theorem sum_substitution : tmSub sumTerm collapse =
    pairTerm (B := tySub entries (lift collapse))
      (tmSub lengthTerm collapse) (tmSub source collapse) :=
  pair_subst (B := entries) lengthTerm source collapse

theorem sum_first_substitution : tmSub (fstTerm sumTerm) collapse =
    fstTerm (B := tySub entries (lift collapse)) (tmSub sumTerm collapse) :=
  fst_subst sumTerm collapse

theorem sum_second_substitution : tmSub (sndTerm sumTerm) collapse =
    sndTerm (B := tySub entries (lift collapse)) (tmSub sumTerm collapse) :=
  snd_subst sumTerm collapse

/-- Eliminating the substituted dependent pair commutes with substitution. -/
theorem elimination_substitution (n : Nat) :
    lookup ((extendRep context lists).meaning (packed.code (collapse n))) =
      tmSub source collapse n := by
  exact compiled.commutes (collapse n)

theorem source_two_step : tmSub (tmSub source collapse) shift =
    tmSub source (compSub collapse shift) := tmSub_comp source collapse shift

theorem pair_two_step (n : Nat) :
    (extendRep context lists).meaning (packed.code (collapse (shift n))) =
      extend (compSub collapse shift) (tmSub source (compSub collapse shift)) n :=
  packed.commutes _

example : compiled.code 0 = ⟨[], rfl⟩ := rfl
example : compiled.code 1 = ⟨[true], rfl⟩ := rfl
example : twice.code 0 = ⟨[true], rfl⟩ := rfl
example : decode (twice.code 0) ⟨0, by decide⟩ = true :=
  composition_lookup 0 ⟨0, by decide⟩

/-- The empty fibre has one vector; the length-one fibre has distinguishable values. -/
theorem empty_unique (v w : Vec 0) : v = w := by funext i; exact Fin.elim0 i

theorem one_distinct : (fun _ : Fin 1 => true) ≠ (fun _ : Fin 1 => false) := by
  intro h
  have := congrFun h ⟨0, by decide⟩
  contradiction

theorem fibres_not_equivalent : ¬ Nonempty (Vec 0 ≃ Vec 1) := by
  rintro ⟨e⟩
  apply one_distinct
  exact e.symm.injective (empty_unique _ _)

/-- This particular constant carrier erases entries. Constant encodings with
extra tags can preserve data; no claim against those encodings is made. -/
def erase {n} (_ : Vec n) : Unit := ()

theorem constant_unit_cannot_preserve_lookup :
    ¬ ∃ observe : Unit → Bool, ∀ v : Vec 1, observe (erase v) = v ⟨0, by decide⟩ := by
  rintro ⟨observe, h⟩
  have bad := (h (fun _ => true)).symm.trans (h (fun _ => false))
  contradiction
end Vectors
end Examples.ExpressiveWitnesses
