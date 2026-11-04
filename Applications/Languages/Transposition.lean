import SquareKit.EquationTranspose
import Applications.Languages.WitnessTrie

/-! Explicit nullable/derivative equation bodies and their transposed constructor
methods. Recursion inside the existing parser/trie primitives remains external
to the binding-free equation calculus; no infinite codata is asserted. -/
namespace LanguageWitnesses.Transposition
open SquareKit.EquationTranspose
variable {α : Type} [DecidableEq α]

inductive Constructor : Language α → Type 1
  | zero : Constructor (fun _ => PEmpty)
  | universal : Constructor (fun _ => PUnit)
  | epsilon : Constructor epsilon
  | atom (a : α) : Constructor (atom a)
  | intersection (P Q : Language α) : Constructor (fun w => P w × Q w)
  | scale (A : Type) (P : Language α) : Constructor (fun w => A × P w)
  | transport (P Q : Language α) (e : ∀ w, Iso (P w) (Q w)) : Constructor Q
  | union (P Q : Language α) : Constructor (fun w => P w ⊕ Q w)
  | concat (P Q : Language α) : Constructor (Concat P Q)
  | star (P : Language α) : Constructor (Star P)

def fields : Constructor (α := α) P → Type 1
  | .zero | .universal | .epsilon | .atom _ => PUnit
  | .intersection P Q => Parser P × Parser Q
  | .scale A P => ULift.{1} (Decision A) × Parser P
  | .transport P _ _ => Parser P
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
  | zero : Prim PUnit (Parser (α := α) (fun _ => PEmpty))
  | universal : Prim PUnit (Parser (α := α) (fun _ => PUnit))
  | epsilon : Prim PUnit (Parser (α := α) epsilon)
  | atom (a : α) : Prim PUnit (Parser (atom a))
  | intersection {P Q : Language α} : Prim (Parser P × Parser Q) (Parser (fun w => P w × Q w))
  | scale {A : Type} {P : Language α} :
      Prim (ULift.{1} (Decision A) × Parser P) (Parser (fun w => A × P w))
  | prod {A B : Type} : Prim (ULift.{1} (Decision A) × ULift.{1} (Decision B))
      (ULift.{1} (Decision (A × B)))
  | map {A B : Type} (e : Iso A B) : Prim (ULift.{1} (Decision A)) (ULift.{1} (Decision B))
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
  | .zero, _ => .zero
  | .universal, _ => .universal
  | .epsilon, _ => .epsilon
  | .atom a, _ => .atom a
  | .intersection, (p,q) => .intersection p q
  | .scale, (d,p) => .scale d.down p
  | .prod, (p,q) => ⟨p.down.prod q.down⟩
  | .map e, p => ⟨p.down.map e⟩
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
  | .zero => fun _ => .zero
  | .universal => fun _ => .universal
  | .epsilon => fun _ => .epsilon
  | .atom a => fun _ => .atom a
  | .intersection _ _ => fun (p,q) => .intersection p q
  | .scale _ _ => fun (d,p) => .scale d.down p
  | .transport _ _ e => fun p => .transport e p
  | .union _ _ => fun (p,q) => .union p q
  | .concat _ _ => fun (p,q) => .concat p q
  | .star _ => fun p => .star p

def construction (c : Constructor (α := α) P) :
    Expr (Prim (α := α)) (Slot (fields c) PUnit) (Parser P) :=
  match c with
  | .zero => .prim .zero (.var .first)
  | .universal => .prim .universal (.var .first)
  | .epsilon => .prim .epsilon (.var .first)
  | .atom a => .prim (.atom a) (.var .first)
  | .intersection _ _ => .prim .intersection (.var .first)
  | .scale _ _ => .prim .scale (.var .first)
  | .transport _ _ e => .prim (.transport e) (.var .first)
  | .union _ _ => .prim .union (.var .first)
  | .concat _ _ => .prim .concat (.var .first)
  | .star _ => .prim .star (.var .first)

/-- The next/concat cell contains the unchanged right operand explicitly. -/
def equations : DataProgram (signature α) (Prim (α := α)) where
  body P d c := match d, c with
    | .nullable, .zero => .prim .nullable (construction .zero)
    | .nullable, .universal => .prim .nullable (construction .universal)
    | .nullable, .epsilon => .prim .nullable (construction .epsilon)
    | .nullable, .atom a => .prim .nullable (construction (.atom a))
    | .nullable, .intersection _ _ => .prim .prod
        (.pair (.prim .nullable (.fst (.var .first))) (.prim .nullable (.snd (.var .first))))
    | .nullable, .scale _ _ => .prim .prod
        (.pair (.fst (.var .first)) (.prim .nullable (.snd (.var .first))))
    | .nullable, .transport _ _ e => .prim (.map (e [])) (.prim .nullable (.var .first))
    | .derive _, .zero => construction .zero
    | .derive _, .universal => construction .universal
    | .derive a, .epsilon => .prim (.derive a) (construction .epsilon)
    | .derive a, .atom b => .prim (.derive a) (construction (.atom b))
    | .derive a, .intersection _ _ => .prim .intersection
        (.pair (.prim (.derive a) (.fst (.var .first))) (.prim (.derive a) (.snd (.var .first))))
    | .derive a, .scale _ _ => .prim .scale
        (.pair (.fst (.var .first)) (.prim (.derive a) (.snd (.var .first))))
    | .derive a, .transport _ _ e => .prim (.transport (fun w => e (a :: w)))
        (.prim (.derive a) (.var .first))
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

/-- Existing automatic combinators supply their own depth-recursion proofs. -/
theorem intersection_automatic (p : Parser (α := α) P) (q : Parser Q) (n : Nat) :
    methods.construct meaning (.intersection P Q) (p,q) (.snapshot n) PUnit.unit =
      WitnessTrie.intersection (WitnessTrie.unfold p n) (WitnessTrie.unfold q n) :=
  (methods_correct (.intersection P Q) (p,q) (.snapshot n)).trans
    (WitnessTrie.unfold_intersection p q n)

theorem scale_automatic {A : Type} (d : Decision A) (p : Parser (α := α) P) (n : Nat) :
    methods.construct meaning (.scale A P) (⟨d⟩,p) (.snapshot n) PUnit.unit =
      WitnessTrie.scale d (WitnessTrie.unfold p n) :=
  (methods_correct (.scale A P) (⟨d⟩,p) (.snapshot n)).trans
    (WitnessTrie.unfold_scale d p n)

theorem transport_automatic {P Q : Language α} (e : ∀ w, Iso (P w) (Q w)) (p : Parser (α := α) P) (n : Nat) :
    methods.construct meaning (.transport P Q e) p (.snapshot n) PUnit.unit =
      WitnessTrie.transport e (WitnessTrie.unfold p n) :=
  (methods_correct (.transport P Q e) p (.snapshot n)).trans
    (WitnessTrie.unfold_transport e p n)
end LanguageWitnesses.Transposition
