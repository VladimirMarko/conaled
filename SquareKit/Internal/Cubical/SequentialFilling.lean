import Mathlib.Data.Set.Basic
/-! Dependent sequential selection and its boundary and substitution laws. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.SequentialFilling
universe u v w x
/-- One box problem, with a dependent second stage over the first section. -/
structure Problem where
  FirstBox : Type u
  First : Type v
  firstBox : FirstBox
  firstFill : FirstBox → First
  FirstFills : FirstBox → First → Prop
  first_fills : ∀ b, FirstFills b (firstFill b)
  SecondBox : First → Type w
  Second : First → Type x
  secondBox : (a : First) → FirstFills firstBox a → SecondBox a
  secondFill : (a : First) → SecondBox a → Second a
  Whole : Type v
  pair : (a : First) → Second a → Whole

def Problem.fill (P : Problem.{u,v,w,x}) : P.Whole :=
  P.pair (P.firstFill P.firstBox)
    (P.secondFill _ (P.secondBox _ (P.first_fills P.firstBox)))

theorem Problem.fills (P : Problem.{u,v,w,x})
    (SecondFills : (a : P.First) → P.SecondBox a → P.Second a → Prop)
    (WholeFills : P.Whole → Prop)
    (second_fills : ∀ a b, SecondFills a b (P.secondFill a b))
    (pair_fills : ∀ a ha c, SecondFills a (P.secondBox a ha) c → WholeFills (P.pair a c)) :
    WholeFills P.fill := pair_fills _ _ _ (second_fills _ _)

/-- Primitive substitution data, separately for boxes, sections and pairing. -/
structure Substitution (P Q : Problem.{u,v,w,x}) where
  firstBox : P.FirstBox → Q.FirstBox
  first : P.First → Q.First
  firstBox_eq : Q.firstBox = firstBox P.firstBox
  first_uniform : ∀ b, Q.firstFill (firstBox b) = first (P.firstFill b)
  first_fills : ∀ a, P.FirstFills P.firstBox a → Q.FirstFills Q.firstBox (first a)
  secondBox : (a : P.First) → P.SecondBox a → Q.SecondBox (first a)
  second : (a : P.First) → P.Second a → Q.Second (first a)
  whole : P.Whole → Q.Whole
  secondBox_eq : ∀ a ha, Q.secondBox (first a) (first_fills a ha) = secondBox a (P.secondBox a ha)
  second_uniform : ∀ a b, Q.secondFill (first a) (secondBox a b) = second a (P.secondFill a b)
  pair_eq : ∀ a c, Q.pair (first a) (second a c) = whole (P.pair a c)

theorem Substitution.uniform {P Q : Problem.{u,v,w,x}} (s : Substitution P Q) :
    Q.fill = s.whole P.fill := by
  let a := P.firstFill P.firstBox
  let ha := P.first_fills P.firstBox
  have h : (⟨Q.firstFill Q.firstBox,Q.first_fills Q.firstBox⟩ : {z // Q.FirstFills Q.firstBox z}) =
      ⟨s.first a,s.first_fills a ha⟩ := by
    apply Subtype.ext
    change Q.firstFill Q.firstBox = s.first a
    rw [s.firstBox_eq, s.first_uniform]
  calc
    Q.fill = Q.pair (s.first a) (Q.secondFill _ (Q.secondBox _ (s.first_fills a ha))) :=
      congrArg (fun z : {z // Q.FirstFills Q.firstBox z} =>
        Q.pair z.val (Q.secondFill _ (Q.secondBox _ z.property))) h
    _ = _ := by rw [s.secondBox_eq, s.second_uniform, s.pair_eq]; rfl
end SquareKit.SequentialFilling
