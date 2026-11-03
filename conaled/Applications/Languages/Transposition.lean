import SquareKit.EquationTranspose
import Applications.Languages.WitnessTrie

/-! Explicit nullable/derivative equation bodies and their transposed constructor
methods. Recursion inside the existing parser/trie primitives remains external
to the binding-free equation calculus; no infinite codata is asserted. -/
namespace LanguageWitnesses.Transposition
open SquareKit.EquationTranspose
variable {α : Type} [DecidableEq α]

inductive Constructor : Language α → Type 1
  | union (P Q : Language α) : Constructor (fun w => P w ⊕ Q w)
  | concat (P Q : Language α) : Constructor (Concat P Q)
  | star (P : Language α) : Constructor (Star P)

def fields : Constructor (α := α) P → Type 1
  | .union P Q => Parser P × Parser Q
  | .concat P Q => Parser P × Parser Q
  | .star P => Parser P

inductive Observer (P : Language α) : Type 1
  | nullable
  | derive (a : α)
  | snapshot (n : Nat)

def result : Observer (α := α) P → Type 1
  | .nullable => ULift.{1} (Decision (P []))
  | .derive a => Parser (derivative P a)
  | .snapshot n => WitnessTrie P n

abbrev signature (α : Type) : Signature (Language α) where
  Constructor := Constructor
  Observer := Observer
  fields := fields
  arguments := fun _ => PUnit
  result := result

inductive Prim : Type 1 → Type 1 → Type 2
  | nullable {P : Language α} : Prim (Parser P) (ULift.{1} (Decision (P [])))
  | derive {P : Language α} (a : α) : Prim (Parser P) (Parser (derivative P a))
  | union {P Q : Language α} : Prim (Parser P × Parser Q) (Parser (fun w => P w ⊕ Q w))
  | concat {P Q : Language α} : Prim (Parser P × Parser Q) (Parser (Concat P Q))
  | star {P : Language α} : Prim (Parser P) (Parser (Star P))
  | sum {A B : Type} : Prim (ULift.{1} (Decision A) × ULift.{1} (Decision B))
      (ULift.{1} (Decision (A ⊕ B)))
  | concatNull {P Q : Language α} :
      Prim (ULift.{1} (Decision (P [])) × ULift.{1} (Decision (Q [])))
        (ULift.{1} (Decision (Concat P Q [])))
  | starNull {P : Language α} : Prim (Parser P) (ULift.{1} (Decision (Star P [])))
  | scaleNullable {P Q : Language α} : Prim (Parser P × Parser Q) (Parser (fun w => P [] × Q w))
  | scaleEmpty {P Q : Language α} : Prim (Parser Q) (Parser (fun w => List (P []) × Q w))
  | transport {P Q : Language α} (e : ∀ w, Iso (P w) (Q w)) : Prim (Parser P) (Parser Q)
  | unfold {P : Language α} (n : Nat) : Prim (Parser P) (WitnessTrie P n)

def meaning : Prim (α := α) A B → A → B
  | .nullable, p => ⟨p.nullable⟩
  | .derive a, p => p.derive a
  | .union, (p,q) => .union p q
  | .concat, (p,q) => .concat p q
  | .star, p => .star p
  | .sum, (p,q) => ⟨p.down.sum q.down⟩
  | .concatNull, (p,q) => ⟨(p.down.prod q.down).map (nullableConcatIso _ _).symm⟩
  | .starNull, _ => ⟨.yes ⟨[],rfl⟩⟩
  | .scaleNullable, (p,q) => .scale p.nullable q
  | .scaleEmpty, p => .scale (.yes []) p
  | .transport e, p => .transport e p
  | .unfold n, p => WitnessTrie.unfold p n

def symbolic (c : Constructor (α := α) P) : fields c → Parser P :=
  match c with
  | .union _ _ => fun (p,q) => .union p q
  | .concat _ _ => fun (p,q) => .concat p q
  | .star _ => fun p => .star p

def construction (c : Constructor (α := α) P) :
    Expr (Prim (α := α)) (Slot (fields c) PUnit) (Parser P) :=
  match c with
  | .union _ _ => .prim .union (.var .first)
  | .concat _ _ => .prim .concat (.var .first)
  | .star _ => .prim .star (.var .first)

/-- The next/concat cell contains the unchanged right operand explicitly. -/
def equations : DataProgram (signature α) (Prim (α := α)) where
  body P d c := match d, c with
    | .nullable, .union _ _ => .prim .sum
        (.pair (.prim .nullable (.fst (.var .first))) (.prim .nullable (.snd (.var .first))))
    | .nullable, .concat _ _ => .prim .concatNull
        (.pair (.prim .nullable (.fst (.var .first))) (.prim .nullable (.snd (.var .first))))
    | .nullable, .star _ => .prim .starNull (.var .first)
    | .derive a, .union _ _ => .prim .union
        (.pair (.prim (.derive a) (.fst (.var .first))) (.prim (.derive a) (.snd (.var .first))))
    | .derive a, .concat P Q => .prim (.transport (fun w => (derivativeConcatIso P Q a w).symm))
        (.prim .union (.pair
          (.prim .scaleNullable (.pair (.fst (.var .first)) (.prim (.derive a) (.snd (.var .first)))))
          (.prim .concat (.pair (.prim (.derive a) (.fst (.var .first))) (.snd (.var .first))))))
    | .derive a, .star P => .prim (.transport (fun w => (derivativeStarIso P a w).symm))
        (.prim .scaleEmpty (.prim .concat
          (.pair (.prim (.derive a) (.var .first)) (.prim .star (.var .first)))))
    | .snapshot n, c => .prim (.unfold n) (construction c)

def observeParser (d : Observer (α := α) P) (p : Parser P) : result d :=
  match d with
  | .nullable => ⟨p.nullable⟩
  | .derive a => p.derive a
  | .snapshot n => WitnessTrie.unfold p n

theorem equations_correct (c : Constructor (α := α) P) (x : fields c) (d : Observer P) :
    equations.observe meaning d ⟨c,x⟩ PUnit.unit = observeParser d (symbolic c x) := by
  cases d <;> cases c <;> rfl

/-- This is generated syntax, not a second handwritten interpreter. -/
def methods : CodataProgram (signature α) (Prim (α := α)) := transpose equations

theorem methods_correct (c : Constructor (α := α) P) (x : fields c) (d : Observer P) :
    methods.construct meaning c x d PUnit.unit = observeParser d (symbolic c x) :=
  (transpose_preserves equations meaning c x d PUnit.unit).trans (equations_correct c x d)

theorem recovered_nullable (c : Constructor (α := α) P) (x : fields c) :
    (methods.construct meaning c x .nullable PUnit.unit).down = (symbolic c x).nullable :=
  congrArg ULift.down (methods_correct c x .nullable)

theorem recovered_derive (c : Constructor (α := α) P) (x : fields c) (a : α) :
    methods.construct meaning c x (.derive a) PUnit.unit = (symbolic c x).derive a :=
  methods_correct c x (.derive a)

theorem recovered_snapshot (c : Constructor (α := α) P) (x : fields c) (n : Nat)
    (w : List α) (h : w.length ≤ n) :
    (methods.construct meaning c x (.snapshot n) PUnit.unit).lookup w h =
      (symbolic c x).parse w := by
  rw [methods_correct]
  exact WitnessTrie.lookup_unfold _ _ _ _

/-- Direct automatic concatenation from #255 is recovered, at every finite depth. -/
theorem concat_automatic (p : Parser (α := α) P) (q : Parser Q) (n : Nat) :
    methods.construct meaning (.concat P Q) (p,q) (.snapshot n) PUnit.unit =
      WitnessTrie.concat n (WitnessTrie.unfold p n) (WitnessTrie.unfold q n) := by
  exact (methods_correct (.concat P Q) (p,q) (.snapshot n)).trans
    (WitnessTrie.unfold_concat p q n)

theorem star_automatic (p : Parser (α := α) P) (n : Nat) :
    methods.construct meaning (.star P) p (.snapshot n) PUnit.unit =
      WitnessTrie.star n (WitnessTrie.unfold p n) := by
  exact (methods_correct (.star P) p (.snapshot n)).trans
    (WitnessTrie.unfold_star p n)
end LanguageWitnesses.Transposition
