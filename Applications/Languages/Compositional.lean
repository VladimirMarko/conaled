import SquareKit.CompositionalCoalgebra
import Applications.Languages.Coalgebra
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace LanguageCoalgebra.Compositional
open SquareKit.WordCoalgebra SquareKit.CompositionalCoalgebra
universe u v w

/-- The flag adds pointwise multiplication without changing the old operations. -/
inductive Op (R : Type v) : Bool → Type v
  | add {b} : Op R b
  | scale {b} : R → Op R b
  | concat {b} : Op R b
  | pointwise : Op R true

abbrev arity : Op R b → Nat
  | .add => 2
  | .scale _ => 1
  | .concat => 2
  | .pointwise => 2

abbrev Syntax (R : Type v) (b : Bool) (X : Type w) := Term (Op R b) arity X

def add (p q : Syntax R b X) : Syntax R b X := .node .add ![p,q]
def scale (r : R) (p : Syntax R b X) : Syntax R b X := .node (.scale r) ![p]
def concat (p q : Syntax R b X) : Syntax R b X := .node .concat ![p,q]
def pointwise (p q : Syntax R true X) : Syntax R true X := .node .pointwise ![p,q]

@[simp] theorem bind_add (f : X → Syntax R b Y) (p q : Syntax R b X) :
    Term.bind f (add p q) = add (Term.bind f p) (Term.bind f q) := by
  simp only [add, Term.bind, SquareKit.FinitaryTerm.bind]
  congr 1; funext i; fin_cases i <;> rfl

@[simp] theorem bind_scale (f : X → Syntax R b Y) (r : R) (p : Syntax R b X) :
    Term.bind f (scale r p) = scale r (Term.bind f p) := by
  simp only [scale, Term.bind, SquareKit.FinitaryTerm.bind]
  congr 1; funext i; fin_cases i; rfl

@[simp] theorem bind_concat (f : X → Syntax R b Y) (p q : Syntax R b X) :
    Term.bind f (concat p q) = concat (Term.bind f p) (Term.bind f q) := by
  simp only [concat, Term.bind, SquareKit.FinitaryTerm.bind]
  congr 1; funext i; fin_cases i <;> rfl

@[simp] theorem bind_pointwise (f : X → Syntax R true Y) (p q : Syntax R true X) :
    Term.bind f (pointwise p q) = pointwise (Term.bind f p) (Term.bind f q) := by
  simp only [pointwise, Term.bind, SquareKit.FinitaryTerm.bind]
  congr 1; funext i; fin_cases i <;> rfl

variable {A : Type u} {R : Type v} {X : Type w} [Semiring R]

def rule (b : Bool) : Rule (Op R b) arity A R where
  out op xs := match op with
    | .add => xs 0 + xs 1
    | .scale r => r * xs 0
    | .concat => xs 0 * xs 1
    | .pointwise => xs 0 * xs 1
  step op xs _ := match op with
    | .add => add (.leaf (.inr 0)) (.leaf (.inr 1))
    | .scale r => scale r (.leaf (.inr 0))
    | .concat => add (scale (xs 0) (.leaf (.inr 1)))
        (concat (.leaf (.inr 0)) (.leaf (.inl 1)))
    | .pointwise => pointwise (.leaf (.inr 0)) (.leaf (.inr 1))

def algebra : (op : Op R b) → (Fin (arity op) → Convolution.Series A R) → Convolution.Series A R
  | .add, xs => xs 0 + xs 1
  | .scale r, xs => Convolution.scale r (xs 0)
  | .concat, xs => xs 0 * xs 1
  | .pointwise, xs => ⟨fun w => xs 0 w * xs 1 w⟩

def observe : Coalgebra A R (Convolution.Series A R) :=
  fun s => (s [], fun a => Convolution.derivative a s)

/-- Only the four constructor equations are discharged here; composition is shared. -/
theorem compatible (b : Bool) : (rule (A := A) (R := R) b).Compatible algebra observe where
  output op xs := by cases op <;> rfl
  next op xs a := by
    cases op with
    | add => simpa [observe, algebra, rule, add, Term.fold] using
        Convolution.derivative_add a (xs 0) (xs 1)
    | scale r => rfl
    | concat => simpa [observe, algebra, rule, add, scale, concat, Term.fold] using
        Convolution.derivative_mul a (xs 0) (xs 1)
    | pointwise => rfl

def meaning (M : X → Convolution.Series A R) : Syntax R b X → Convolution.Series A R :=
  Term.fold algebra M

theorem interpretation (c : Coalgebra A R X) (M : X → Convolution.Series A R)
    (h : Morphism c final (fun x => (M x).coeff)) :
    Morphism ((rule b).lift c) final (fun t => (meaning M t).coeff) := by
  have hf : Morphism c observe M :=
    ⟨h.output, fun x a => Convolution.Series.ext (h.next x a)⟩
  have hm := (rule b).fold_morphism algebra observe (compatible b) c M hf
  exact ⟨hm.output, fun t a => congrArg Convolution.Series.coeff (hm.next t a)⟩

theorem correct (c : Coalgebra A R X) (M : X → Convolution.Series A R)
    (h : Morphism c final (fun x => (M x).coeff)) (t : Syntax R b X) (word : List A) :
    run ((rule b).lift c) t word = meaning M t word :=
  SquareKit.WordCoalgebra.correct _ _ (interpretation c M h) t word

@[simp] theorem next_add (c : Coalgebra A R X) (p q : Syntax R b X) (a : A) :
    (rule b).next c (add p q) a = add ((rule b).next c p a) ((rule b).next c q a) := by
  change Term.bind _ (add _ _) = _
  rw [bind_add]; rfl

@[simp] theorem next_scale (c : Coalgebra A R X) (r : R) (p : Syntax R b X) (a : A) :
    (rule b).next c (scale r p) a = scale r ((rule b).next c p a) := by
  change Term.bind _ (scale _ _) = _
  rw [bind_scale]; rfl

@[simp] theorem next_concat (c : Coalgebra A R X) (p q : Syntax R b X) (a : A) :
    (rule b).next c (concat p q) a =
      add (scale ((rule b).output c p) ((rule b).next c q a))
        (concat ((rule b).next c p a) q) := by
  change Term.bind _ (add _ _) = _
  rw [bind_add, bind_scale, bind_concat]; rfl

@[simp] theorem next_pointwise (c : Coalgebra A R X) (p q : Syntax R true X) (a : A) :
    (rule true).next c (pointwise p q) a = pointwise ((rule true).next c p a) ((rule true).next c q a) := by
  change Term.bind _ (pointwise _ _) = _
  rw [bind_pointwise]; rfl

/-- The pre-existing weighted syntax retains its direct interface. -/
def embed : Weighted.Term R X → Syntax R false X
  | .leaf x => .leaf x
  | .add p q => add (embed p) (embed q)
  | .scale r p => scale r (embed p)
  | .concat p q => concat (embed p) (embed q)

def embedExtended : Weighted.Extended R X → Syntax R true X
  | .leaf x => .leaf x
  | .add p q => add (embedExtended p) (embedExtended q)
  | .scale r p => scale r (embedExtended p)
  | .concat p q => concat (embedExtended p) (embedExtended q)
  | .pointwise p q => pointwise (embedExtended p) (embedExtended q)

theorem embed_meaning (M : X → Convolution.Series A R) (t : Weighted.Term R X) :
    meaning M (embed t) = Weighted.meaning M t := by
  induction t <;> simp_all [embed, meaning, Term.fold, algebra, add, scale, concat, Weighted.meaning]

theorem embed_output (c : Coalgebra A R X) (t : Weighted.Term R X) :
    (rule false).output c (embed t) = Weighted.output c t := by
  induction t <;> simp_all [embed, Rule.output, rule, add, scale, concat, Weighted.output]

theorem embed_next (c : Coalgebra A R X) (t : Weighted.Term R X) (a : A) :
    (rule false).next c (embed t) a = embed (Weighted.next c t a) := by
  induction t <;> simp_all only [embed, Weighted.next, next_add, next_scale, next_concat, embed_output]
  rfl

theorem embedExtended_meaning (M : X → Convolution.Series A R) (t : Weighted.Extended R X) :
    meaning M (embedExtended t) = Weighted.extMeaning M t := by
  induction t <;> simp_all [embedExtended, meaning, Term.fold, algebra, add, scale, concat,
    pointwise, Weighted.extMeaning]

theorem embedExtended_output (c : Coalgebra A R X) (t : Weighted.Extended R X) :
    (rule true).output c (embedExtended t) = Weighted.extOutput c t := by
  induction t <;> simp_all [embedExtended, Rule.output, rule, add, scale, concat,
    pointwise, Weighted.extOutput]

theorem embedExtended_next (c : Coalgebra A R X) (t : Weighted.Extended R X) (a : A) :
    (rule true).next c (embedExtended t) a = embedExtended (Weighted.extNext c t a) := by
  induction t <;> simp_all only [embedExtended, Weighted.extNext, next_add, next_scale, next_concat,
    next_pointwise, embedExtended_output]
  rfl

/-- Recover the original all-word theorem through the generic constructor-law proof. -/
theorem recovered (c : Coalgebra A R X) (M : X → Convolution.Series A R)
    (h : Morphism c final (fun x => (M x).coeff)) (t : Weighted.Term R X) (w : List A) :
    run (Weighted.coalgebra c) t w = Weighted.meaning M t w := by
  have he : ∀ t w, run ((rule false).lift c) (embed t) w = run (Weighted.coalgebra c) t w := by
    intro t w
    induction w generalizing t with
    | nil => exact embed_output c t
    | cons a w ih =>
      change run ((rule false).lift c) ((rule false).next c (embed t) a) w = _
      rw [embed_next]; exact ih _
  rw [← he, correct c M h, embed_meaning]

theorem recoveredExtended (c : Coalgebra A R X) (M : X → Convolution.Series A R)
    (h : Morphism c final (fun x => (M x).coeff)) (t : Weighted.Extended R X) (w : List A) :
    run (Weighted.extended c) t w = Weighted.extMeaning M t w := by
  have he : ∀ t w, run ((rule true).lift c) (embedExtended t) w = run (Weighted.extended c) t w := by
    intro t w
    induction w generalizing t with
    | nil => exact embedExtended_output c t
    | cons a w ih =>
      change run ((rule true).lift c) ((rule true).next c (embedExtended t) a) w = _
      rw [embedExtended_next]; exact ih _
  rw [← he, correct c M h, embedExtended_meaning]
/-- Adding pointwise multiplication reuses the same composite interpretation theorem. -/
theorem old_in_extended (c : Coalgebra A R X) (M : X → Convolution.Series A R)
    (h : Morphism c final (fun x => (M x).coeff)) (t : Weighted.Term R X) (w : List A) :
    run ((rule true).lift c) (embedExtended (Weighted.Extended.old t)) w =
      Weighted.meaning M t w := by
  rw [correct c M h, embedExtended_meaning, Weighted.old_meaning]

end LanguageCoalgebra.Compositional
