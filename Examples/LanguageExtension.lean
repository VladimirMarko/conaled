import Applications.Sequences.FIFOExtension
import Examples.AbstractFIFO

/-! Recovery of old FIFO clients, a new rotating client, and an incompatible
primitive whose two related inputs force different observable sum tags. -/
namespace Examples.LanguageExtension
open CategoricalCompiler Sequences.AbstractFIFO Sequences.Symmetric SquareKit
open Examples.AbstractFIFO

/-- The old client still observes 2 after enlarging its primitive signature. -/
theorem old_client :
    (symmetric Nat).head ((compile
      (STLCRelations.target _ (Extension.primitives (symmetric Nat) _ (symmetric_correct Nat)))
      (STLCSignature.map Sum.inl (Syntax.program edits))).impl ((),nilSL)) = some 2 :=
  (Extension.old_observe _ _ (symmetric_correct Nat) edits ⟨inv_nilSL,rfl⟩).trans rfl

/-- Rotating [1,2,3] yields [2,3,1], then deleting yields [3,1]. -/
theorem rotated_client :
    (symmetric Nat).head ((compile
      (STLCRelations.target _ (Extension.primitives (symmetric Nat) _ (symmetric_correct Nat)))
      (Extension.program [.delete])).impl ((),leftLayout)) = some 3 :=
  (Extension.observe _ _ (symmetric_correct Nat) [.delete] left_related).trans rfl

example :
    (lists Nat).head ((compile
      (STLCRelations.target _ (Extension.primitives (lists Nat) Eq (lists_correct Nat)))
      (Extension.program [.delete])).impl ((),[1,2,3])) = some 3 :=
  (Extension.observe _ _ (lists_correct Nat) [.delete] rfl).trans rfl

example :
    (symmetric Nat).head ((compile
      (STLCRelations.target _ (Extension.primitives (symmetric Nat) _ (symmetric_correct Nat)))
      (Extension.program [])).impl ((),nilSL)) = none :=
  (Extension.observe _ _ (symmetric_correct Nat) [] ⟨inv_nilSL,rfl⟩).trans rfl

example :
    (symmetric Nat).head ((compile
      (STLCRelations.target _ (Extension.primitives (symmetric Nat) _ (symmetric_correct Nat)))
      (Extension.program [.delete])).impl ((),leftLayout)) =
    (symmetric Nat).head ((compile
      (STLCRelations.target _ (Extension.primitives (symmetric Nat) _ (symmetric_correct Nat)))
      (Extension.program [.delete])).impl ((),rightLayout)) :=
  Extension.representation_independent _ _ (symmetric_correct Nat) _ left_related right_related

/-- Relabeling through an identity signature map keeps an arbitrary old term. -/
example (t : Term (Syntax.Prim Nat) Γ a) :
    STLCSignature.map (fun p => p) (STLCSignature.map (Q := Extension.Prim Nat) Sum.inl t) =
      STLCSignature.map Sum.inl t := STLCSignature.map_id _
example (t : Term (Syntax.Prim Nat) Γ a) :
    STLCSignature.map (Q := Extension.Prim Nat) Sum.inl (STLCSignature.map (fun p => p) t) =
      STLCSignature.map Sum.inl t := STLCSignature.map_comp _ _ t

/-- A proposed runtime primitive reveals a private layout through public tags. -/
def revealFront (q : SymList Nat) : Sum Unit Unit :=
  if q.1.length = 1 then .inl () else .inr ()

/-- No semantic operation on sequences can validate this primitive's relation law. -/
theorem no_reveal_interpretation :
    ¬ ∃ f : List Nat → Sum Unit Unit,
      ∀ q xs, (representation Nat).Rel q xs →
        (STLCRelations.encoding (representation Nat) (.sum .unit .unit)).Rel (revealFront q) (f xs) := by
  rintro ⟨f,h⟩
  have hl := h leftLayout [1,2,3] left_related
  have hr := h rightLayout [1,2,3] right_related
  cases hf : f [1,2,3] <;>
    simp [revealFront, leftLayout, rightLayout, STLCRelations.encoding,
      STLCRelations.Encoding.sum, hf] at hl hr

/-- This is the actual missing primitive field, not a proof-search failure. -/
inductive Reveal : Ty → Ty → Type where
  | front : Reveal .base (.sum .unit .unit)

def revealMeaning (f : List Nat → Sum Unit Unit) :
    {a b : Ty} → Reveal a b → Val (List Nat) a → Val (List Nat) b
  | _, _, .front => f

theorem no_reveal_primitives (f : List Nat → Sum Unit Unit) :
    ¬ ∃ p : STLCRelations.Primitives (representation Nat) Reveal (revealMeaning f),
      p.impl .front = revealFront := by
  rintro ⟨p,hp⟩
  apply no_reveal_interpretation
  refine ⟨f, ?_⟩
  intro q xs h
  have hh := p.correct .front h
  rw [hp] at hh
  exact hh

end Examples.LanguageExtension
