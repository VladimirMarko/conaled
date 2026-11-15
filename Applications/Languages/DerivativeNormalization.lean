import Applications.Languages.ExactRewrites

/-! Bounded transport-spine normalization of native derivative states.
The certificate retains the exact witness map. No semantic equality test or
intern table is used. Costs count syntax visits, not Lean allocation or time. -/
namespace LanguageWitnesses.DerivativeNormalization
variable {α : Type} {P Q : Language α}

def outerDepth : {P : Language α} → Parser P → Nat
  | _, .transport _ p => outerDepth p + 1
  | _, _ => 0

structure Packed (Q : Language α) where
  source : Language α
  base : Parser source
  witness : ∀ w, Iso (source w) (Q w)

def pack : {P : Language α} → Parser P → Packed P
  | _, .transport e p =>
      let s := pack p
      ⟨s.source, s.base, fun w => (s.witness w).trans (e w)⟩
  | P, p => ⟨P, p, fun w => Iso.refl (P w)⟩

def Packed.parser (s : Packed P) : Parser P := .transport s.witness s.base

def normalize (p : Parser P) : Parser P := (pack p).parser

/-- The packed state contains no further outer transport at its base. -/
theorem pack_base (p : Parser P) : outerDepth (pack p).base = 0 := by
  induction p <;> simp_all [pack, outerDepth]

theorem normalized_depth (p : Parser P) : outerDepth (normalize p) = 1 := by
  simp only [normalize, Packed.parser, outerDepth, pack_base]

/-- Fusion preserves the chosen witness, including the final identity map. -/
theorem normalize_exact [DecidableEq α] (p : Parser P) (w : List α) :
    (normalize p).parse w = p.parse w := by
  induction p generalizing w with
  | transport e p ih =>
    change (Parser.transport (fun w => ((pack p).witness w).trans (e w)) (pack p).base).parse w = _
    rw [← Parser.parse_transport_trans]
    have map_parse : ∀ {A B : Language α} (f : ∀ v, Iso (A v) (B v)) (q : Parser A) (v : List α),
        (Parser.transport f q).parse v = (q.parse v).map (f v) := by
      intro A B f q v
      induction v generalizing A B with
      | nil => rfl
      | cons a v ih => exact ih _ _
    rw [map_parse]
    rw [map_parse e p w]
    exact congrArg (fun d => d.map (e w)) (ih w)
  | _ => exact Parser.parse_transport_refl _ _

/-- Every supported finite context can use the normalized hole states. -/
theorem contextual [DecidableEq α] {P : Language α} {n}
    (context : SquareKit.IndexedCompositional.Term IndexedCompositional.signature
      IndexedCompositional.Source (P,n)) (w : List α) (hw : w.length ≤ n) :
    (SquareKit.IndexedCompositional.Term.fold IndexedCompositional.sourceAlgebra (fun _ p => p)
      (context.bind (fun _ p => .leaf (normalize p)))).parse w =
      (SquareKit.IndexedCompositional.Term.fold IndexedCompositional.sourceAlgebra (fun _ p => p)
        context).parse w := by
  have h := IndexedCompositional.contextual_exact
    (fun (j : IndexedCompositional.Index α) (p : IndexedCompositional.Source j) => .leaf (normalize p))
    (fun _ p => .leaf p)
    (fun j p word _ => by
      rcases j with ⟨Q,m⟩
      exact normalize_exact p word) context w hw
  simpa only [SquareKit.IndexedCompositional.Term.bind_leaf] using h

/-- Number of retained parser constructors; function closures are not counted. -/
def nodes : {P : Language α} → Parser P → Nat
  | _, .union p q | _, .intersection p q | _, .concat p q => nodes p + nodes q + 1
  | _, .scale _ p | _, .star p | _, .transport _ p => nodes p + 1
  | _, _ => 1

/-- Instrumented native derivative: one event for each recursive derive call.
Nullable evaluation and witness maps are separate work, not counted here. -/
def deriveCounted [DecidableEq α] : {P : Language α} → (p : Parser P) → (a : α) →
    Parser (derivative P a) × Nat
  | _, .union p q, a =>
      let x := deriveCounted p a; let y := deriveCounted q a
      (.union x.1 y.1, x.2 + y.2 + 1)
  | _, .intersection p q, a =>
      let x := deriveCounted p a; let y := deriveCounted q a
      (.intersection x.1 y.1, x.2 + y.2 + 1)
  | _, .scale d p, a =>
      let x := deriveCounted p a
      (.scale d x.1, x.2 + 1)
  | _, .concat p q, a =>
      let x := deriveCounted p a; let y := deriveCounted q a
      (.transport (fun w => (derivativeConcatIso _ _ a w).symm)
        (.union (.scale p.nullable y.1) (.concat x.1 q)), x.2 + y.2 + 1)
  | _, .star p, a =>
      let x := deriveCounted p a
      (.transport (fun w => (derivativeStarIso _ a w).symm)
        (.scale (.yes []) (.concat x.1 (.star p))), x.2 + 1)
  | _, .transport e p, a =>
      let x := deriveCounted p a
      (.transport (fun w => e (a :: w)) x.1, x.2 + 1)
  | _, p, a => (p.derive a, 1)

theorem deriveCounted_result [DecidableEq α] (p : Parser P) (a : α) :
    (deriveCounted p a).1 = p.derive a := by
  induction p <;> simp_all [deriveCounted, Parser.derive] <;> rfl

def runWork [DecidableEq α] : {P : Language α} → Parser P → List α → Nat
  | _, _, [] => 0
  | _, p, a :: w => let x := deriveCounted p a; x.2 + runWork x.1 w

/-- Each inspected node costs one; constructing a composite-isomorphism closure costs one more.
The final output-wrapper event is added by normalizationWork. -/
def packCounted : {P : Language α} → (p : Parser P) → Packed P × Nat
  | _, .transport e p =>
      let s := packCounted p
      (⟨s.1.source, s.1.base, fun w => (s.1.witness w).trans (e w)⟩, s.2 + 2)
  | P, p => (⟨P, p, fun w => Iso.refl (P w)⟩, 1)

theorem packCounted_result (p : Parser P) : (packCounted p).1 = pack p := by
  induction p with
  | transport e p ih =>
    change (⟨(packCounted p).1.source, (packCounted p).1.base, _⟩ : Packed _) = _
    rw [ih]
    rfl
  | _ => rfl

/-- Packing visits each outer transport and the first non-transport node once,
and constructs one composition closure per transport. It adds one output wrapper. -/
def normalizationWork (p : Parser P) : Nat := (packCounted p).2 + 1

theorem normalizationWork_formula (p : Parser P) :
    normalizationWork p = 2 * outerDepth p + 2 := by
  have h : (packCounted p).2 = 2 * outerDepth p + 1 := by
    induction p <;> simp_all [packCounted, outerDepth, Nat.mul_add, Nat.add_assoc]
  simp only [normalizationWork, h, Nat.add_assoc]

def identityChain : Nat → Parser P → Parser P
  | 0, p => p
  | n+1, p => .transport (fun w => Iso.refl (P w)) (identityChain n p)

end LanguageWitnesses.DerivativeNormalization
