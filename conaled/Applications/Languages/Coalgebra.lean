import SquareKit.WordCoalgebra
import Applications.Languages.Machines
import Applications.Convolution.Series

namespace LanguageCoalgebra
open SquareKit.WordCoalgebra
universe u v w z z'

namespace Boolean
variable {A X : Type u}
def coalgebra (m : LanguageDerivatives.Machine A X) : Coalgebra A Bool X :=
  fun x => (m.nullable x, m.next x)

theorem run_eq (m : LanguageDerivatives.Machine A X) (x : X) (word : List A) :
    run (coalgebra m) x word = m.run x word := by
  induction word generalizing x with
  | nil => rfl
  | cons a word ih => exact ih _

/-- The existing Boolean recognition theorem is recovered without extra assumptions. -/
theorem recognizes {m : LanguageDerivatives.Machine A X} {meaning : X → Language A}
    (h : m.Correct meaning) (x : X) (word : List A) :
    run (coalgebra m) x word = true ↔ word ∈ meaning x := by
  rw [run_eq]
  exact m.run_correct h x word

example (m n : LanguageDerivatives.Machine A X) (x y : X) (word : List A) :
    run (zip (coalgebra m) (coalgebra n) Bool.or) (x,y) word =
      (m.run x word || n.run y word) := by rw [run_zip, run_eq, run_eq]

example (m n : LanguageDerivatives.Machine A X) (x y : X) (word : List A) :
    run (zip (coalgebra m) (coalgebra n) Bool.and) (x,y) word =
      (m.intersection n).run (x,y) word := by
  rw [run_zip, run_eq, run_eq]
  induction word generalizing x y with
  | nil => rfl
  | cons a word ih => exact ih _ _
end Boolean

namespace Weighted
variable {A : Type u} {R : Type v} {X : Type w}

/-- A bounded binding-free operation signature, with arbitrary leaf states. -/
inductive Term (R : Type v) (X : Type w) : Type (max v w)
  | leaf : X → Term R X
  | add : Term R X → Term R X → Term R X
  | scale : R → Term R X → Term R X
  | concat : Term R X → Term R X → Term R X

def Term.bind {Y : Type z} : Term R X → (X → Term R Y) → Term R Y
  | .leaf x, f => f x
  | .add p q, f => .add (p.bind f) (q.bind f)
  | .scale r p, f => .scale r (p.bind f)
  | .concat p q, f => .concat (p.bind f) (q.bind f)

theorem Term.bind_leaf {Y : Type z} (x : X) (f : X → Term R Y) :
    (Term.leaf x).bind f = f x := rfl

theorem Term.bind_id (t : Term R X) : t.bind Term.leaf = t := by
  induction t <;> simp_all [Term.bind]

theorem Term.bind_assoc {Y : Type z} {Z : Type z'} (t : Term R X)
    (f : X → Term R Y) (g : Y → Term R Z) :
    (t.bind f).bind g = t.bind (fun x => (f x).bind g) := by
  induction t <;> simp_all [Term.bind]

variable [Semiring R]

def meaning (M : X → Convolution.Series A R) : Term R X → Convolution.Series A R
  | .leaf x => M x
  | .add p q => meaning M p + meaning M q
  | .scale r p => Convolution.scale r (meaning M p)
  | .concat p q => meaning M p * meaning M q

def output (c : Coalgebra A R X) : Term R X → R
  | .leaf x => (c x).1
  | .add p q => output c p + output c q
  | .scale r p => r * output c p
  | .concat p q => output c p * output c q

def next (c : Coalgebra A R X) : Term R X → A → Term R X
  | .leaf x, a => .leaf ((c x).2 a)
  | .add p q, a => .add (next c p a) (next c q a)
  | .scale r p, a => .scale r (next c p a)
  | .concat p q, a => .add (.scale (output c p) (next c q a)) (.concat (next c p a) q)

def coalgebra (c : Coalgebra A R X) : Coalgebra A R (Term R X) :=
  fun t => (output c t, next c t)

variable {c : Coalgebra A R X} {M : X → Convolution.Series A R}
variable (h : Morphism c final (fun x => (M x).coeff))

include h in
theorem output_sound (t : Term R X) : output c t = meaning M t [] := by
  induction t with
  | leaf x => exact (h.output x).symm
  | add p q hp hq => exact congrArg₂ (· + ·) hp hq
  | scale r p hp => exact congrArg (r * ·) hp
  | concat p q hp hq => exact congrArg₂ (· * ·) hp hq

include h in
theorem next_sound (t : Term R X) (a : A) :
    meaning M (next c t a) = Convolution.derivative a (meaning M t) := by
  induction t with
  | leaf x => exact Convolution.Series.ext (h.next x a).symm
  | add p q hp hq => simp only [next, meaning, hp, hq, Convolution.derivative_add]
  | scale r p hp => rw [next, meaning, hp]; rfl
  | concat p q hp hq =>
    simp only [next, meaning, hp, hq, output_sound h p, Convolution.derivative_mul]

include h in
theorem interpretation : Morphism (coalgebra c) final (fun t => (meaning M t).coeff) where
  output t := (output_sound h t).symm
  next t a := congrArg Convolution.Series.coeff (next_sound h t a).symm

include h in
theorem run_correct (t : Term R X) (word : List A) :
    run (coalgebra c) t word = meaning M t word := correct _ _ (interpretation h) t word

/-- Extend the same signature by pointwise multiplication, distinct from convolution. -/
inductive Extended (R : Type v) (X : Type w) : Type (max v w)
  | leaf : X → Extended R X
  | add : Extended R X → Extended R X → Extended R X
  | scale : R → Extended R X → Extended R X
  | concat : Extended R X → Extended R X → Extended R X
  | pointwise : Extended R X → Extended R X → Extended R X

def Extended.old : Term R X → Extended R X
  | .leaf x => .leaf x
  | .add p q => .add (old p) (old q)
  | .scale r p => .scale r (old p)
  | .concat p q => .concat (old p) (old q)

def extMeaning (M : X → Convolution.Series A R) : Extended R X → Convolution.Series A R
  | .leaf x => M x
  | .add p q => extMeaning M p + extMeaning M q
  | .scale r p => Convolution.scale r (extMeaning M p)
  | .concat p q => extMeaning M p * extMeaning M q
  | .pointwise p q => ⟨fun word => extMeaning M p word * extMeaning M q word⟩

def extOutput (c : Coalgebra A R X) : Extended R X → R
  | .leaf x => (c x).1
  | .add p q => extOutput c p + extOutput c q
  | .scale r p => r * extOutput c p
  | .concat p q => extOutput c p * extOutput c q
  | .pointwise p q => extOutput c p * extOutput c q

def extNext (c : Coalgebra A R X) : Extended R X → A → Extended R X
  | .leaf x, a => .leaf ((c x).2 a)
  | .add p q, a => .add (extNext c p a) (extNext c q a)
  | .scale r p, a => .scale r (extNext c p a)
  | .concat p q, a => .add (.scale (extOutput c p) (extNext c q a)) (.concat (extNext c p a) q)
  | .pointwise p q, a => .pointwise (extNext c p a) (extNext c q a)

def extended (c : Coalgebra A R X) : Coalgebra A R (Extended R X) :=
  fun t => (extOutput c t, extNext c t)

theorem old_output (t : Term R X) : extOutput c (Extended.old t) = output c t := by
  induction t <;> simp_all [Extended.old, extOutput, output]

theorem old_next (t : Term R X) (a : A) :
    extNext c (Extended.old t) a = Extended.old (next c t a) := by
  induction t <;> simp_all [Extended.old, extNext, next, old_output]

theorem old_meaning (t : Term R X) : extMeaning M (Extended.old t) = meaning M t := by
  induction t <;> simp_all [Extended.old, extMeaning, meaning]

theorem old_morphism : Morphism (coalgebra c) (extended c) Extended.old :=
  ⟨old_output, old_next⟩

theorem old_recovered (t : Term R X) (word : List A) :
    run (extended c) (Extended.old t) word = run (coalgebra c) t word := by
  induction word generalizing t with
  | nil => exact old_output t
  | cons a word ih =>
    change run (extended c) (extNext c (Extended.old t) a) word = _
    rw [old_next]
    exact ih _

include h in
theorem ext_output_sound (t : Extended R X) : extOutput c t = extMeaning M t [] := by
  induction t with
  | leaf x => exact (h.output x).symm
  | add p q hp hq => exact congrArg₂ (· + ·) hp hq
  | scale r p hp => exact congrArg (r * ·) hp
  | concat p q hp hq => exact congrArg₂ (· * ·) hp hq
  | pointwise p q hp hq => exact congrArg₂ (· * ·) hp hq

include h in
theorem ext_next_sound (t : Extended R X) (a : A) :
    extMeaning M (extNext c t a) = Convolution.derivative a (extMeaning M t) := by
  induction t with
  | leaf x => exact Convolution.Series.ext (h.next x a).symm
  | add p q hp hq => simp only [extNext, extMeaning, hp, hq, Convolution.derivative_add]
  | scale r p hp => rw [extNext, extMeaning, hp]; rfl
  | concat p q hp hq =>
    simp only [extNext, extMeaning, hp, hq, ext_output_sound h p, Convolution.derivative_mul]
  | pointwise p q hp hq =>
    simp only [extNext, extMeaning, hp, hq]
    rfl

include h in
theorem extended_correct (t : Extended R X) (word : List A) :
    run (extended c) t word = extMeaning M t word :=
  correct (extended c) (fun t => (extMeaning M t).coeff) ⟨fun t => (ext_output_sound h t).symm,
    fun t a => congrArg Convolution.Series.coeff (ext_next_sound h t a).symm⟩ t word
end Weighted
end LanguageCoalgebra
