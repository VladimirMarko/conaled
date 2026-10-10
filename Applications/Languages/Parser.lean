import Applications.Languages.Witnesses

/-!
# A total proof-relevant symbolic parser

This is an indexed, Lean rendition of the essential construction in Conal
Elliott's `Symbolic.lagda`. Parsing returns either an actual parse witness or
a function refuting every purported parse. The `transport` constructor takes
an isomorphism with both inverse proofs. Concatenation and star derivatives
use the proven witness isomorphisms, including nullable factors for star.

This module is independent of Mathlib's Boolean regex recognizer.
-/

namespace LanguageWitnesses

universe u
variable {α : Type u}

inductive Decision (A : Type u) : Type u
  | yes : A → Decision A
  | no : (A → False) → Decision A

def Decision.test {A : Type u} : Decision A → Bool
  | .yes _ => true
  | .no _ => false

theorem Decision.test_correct {A : Type u} (d : Decision A) :
    d.test = true ↔ Nonempty A := by
  cases d with
  | yes a => exact ⟨fun _ => ⟨a⟩, fun _ => rfl⟩
  | no na =>
    constructor
    · intro h; cases h
    · rintro ⟨a⟩; exact False.elim (na a)

def Decision.map {A B : Type u} (e : Iso A B) : Decision A → Decision B
  | .yes a => .yes (e.forward a)
  | .no na => .no (fun b => na (e.backward b))

def Decision.sum {A B : Type u} : Decision A → Decision B → Decision (A ⊕ B)
  | .yes a, _ => .yes (.inl a)
  | .no _, .yes b => .yes (.inr b)
  | .no na, .no nb => .no (fun s => match s with | .inl a => na a | .inr b => nb b)

def Decision.prod {A B : Type u} : Decision A → Decision B → Decision (A × B)
  | .yes a, .yes b => .yes (a, b)
  | .no na, _ => .no (fun ab => na ab.1)
  | _, .no nb => .no (fun ab => nb ab.2)

def Iso.symm {A B : Type u} (e : Iso A B) : Iso B A where
  forward := e.backward
  backward := e.forward
  backward_forward := e.forward_backward
  forward_backward := e.backward_forward

structure Evidence (p : Prop) : Type u where
  proof : p

def epsilon : Language α := fun w => Evidence.{u} (w = [])
def atom (a : α) : Language α := fun w => Evidence.{u} (w = [a])

def nullableEpsilon : Decision (epsilon (α := α) []) := .yes ⟨rfl⟩
def nullableAtom (a : α) : Decision (atom a []) := .no (fun h => List.noConfusion h.proof)

def atomDerivativeIso [DecidableEq α] (a b : α) (w : List α) :
    Iso (atom b (a :: w)) (Evidence.{u} (a = b) × epsilon w) where
  forward := fun p => (⟨(List.cons.inj p.proof).1⟩, ⟨(List.cons.inj p.proof).2⟩)
  backward := fun p => ⟨by rw [p.1.proof, p.2.proof]⟩
  backward_forward := by intro p; cases p; rfl
  forward_backward := by intro p; cases p; rfl

/-- Syntax is indexed by the full type of parse witnesses at every word. -/
inductive Parser : Language α → Type (u + 1)
  | zero : Parser (fun _ => PEmpty)
  | universal : Parser (fun _ => PUnit)
  | epsilon : Parser epsilon
  | atom (a : α) : Parser (atom a)
  | union {P Q} : Parser P → Parser Q → Parser (fun w => P w ⊕ Q w)
  | intersection {P Q} : Parser P → Parser Q → Parser (fun w => P w × Q w)
  | scale {P} {A : Type u} : Decision A → Parser P → Parser (fun w => A × P w)
  | concat {P Q} : Parser P → Parser Q → Parser (Concat P Q)
  | star {P} : Parser P → Parser (Star P)
  | transport {P Q} : (∀ w, Iso (P w) (Q w)) → Parser P → Parser Q

def Parser.nullable {P : Language α} : Parser P → Decision (P [])
  | .zero => .no (fun x => nomatch x)
  | .universal => .yes ⟨⟩
  | .epsilon => nullableEpsilon
  | .atom a => nullableAtom a
  | .union p q => p.nullable.sum q.nullable
  | .intersection p q => p.nullable.prod q.nullable
  | .scale a p => a.prod p.nullable
  | .concat p q => (p.nullable.prod q.nullable).map (nullableConcatIso _ _).symm
  | .star _ => .yes ⟨[], rfl⟩
  | .transport e p => p.nullable.map (e [])

def Parser.derive [DecidableEq α] {P : Language α} : Parser P → (a : α) → Parser (derivative P a)
  | .zero, _ => .zero
  | .universal, _ => .universal
  | .epsilon, a => .transport (fun _ => {
      forward := fun x => nomatch x
      backward := fun x => False.elim (List.noConfusion x.proof)
      backward_forward := fun x => nomatch x
      forward_backward := fun x => False.elim (List.noConfusion x.proof) }) .zero
  | .atom b, a => .transport (fun w => (atomDerivativeIso a b w).symm)
      (.scale (if h : a = b then .yes ⟨h⟩ else .no (fun p => h p.proof)) .epsilon)
  | .union p q, a => .union (p.derive a) (q.derive a)
  | .intersection p q, a => .intersection (p.derive a) (q.derive a)
  | .scale s p, a => .scale s (p.derive a)
  | .concat p q, a => .transport (fun w => (derivativeConcatIso _ _ a w).symm)
      (.union (.scale p.nullable (q.derive a)) (.concat (p.derive a) q))
  | .star p, a => .transport (fun w => (derivativeStarIso _ a w).symm)
      (.scale (.yes []) (.concat (p.derive a) (.star p)))
  | .transport e p, a => .transport (fun w => e (a :: w)) (p.derive a)

/-- The recursion consumes the input word and produces its semantic parse type. -/
def Parser.parse [DecidableEq α] {P : Language α} (p : Parser P) :
    (w : List α) → Decision (P w)
  | [] => p.nullable
  | a :: w => (p.derive a).parse w

theorem Parser.parse_correct [DecidableEq α] {P : Language α}
    (p : Parser P) (w : List α) : (p.parse w).test = true ↔ Nonempty (P w) :=
  Decision.test_correct (p.parse w)

/-- The index carries the semantic language, as in the 2021 Agda development. -/
noncomputable def parserRep (α : Type u) : Squares.Rep.{u + 1} where
  R := (P : Language α) × Parser P
  S := Language α
  decode := Sigma.fst

noncomputable def parseDecisionRep : Squares.Rep.{u + 1} where
  R := (A : Type u) × Decision A
  S := Type u
  decode := Sigma.fst

noncomputable def parserDerivativeSquare [DecidableEq α] (a : α) :
    Squares.Square (parserRep α) (parserRep α) where
  impl := fun p => ⟨derivative p.1 a, p.2.derive a⟩
  spec := fun P => derivative P a
  commutes := fun _ => rfl

noncomputable def parserRecognitionSquare [DecidableEq α] (w : List α) :
    Squares.Square (parserRep α) parseDecisionRep.{u} where
  impl := fun p => ⟨p.1 w, p.2.parse w⟩
  spec := fun P => P w
  commutes := fun _ => rfl

def sampleParser : Parser (α := Char)
    (Concat (Star (fun w => atom 'a' w ⊕ atom 'b' w)) (atom 'a')) :=
  .concat (.star (.union (.atom 'a') (.atom 'b'))) (.atom 'a')

example : (sampleParser.parse "abba".toList).test = true := by decide
example : (sampleParser.parse "abbb".toList).test = false := by decide

end LanguageWitnesses
