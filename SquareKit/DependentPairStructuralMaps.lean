import SquareKit.DependentPairJudgments

/-! The common structural rules commute with independently supplied syntax maps. -/
namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps DependentPairPresentations
open Elimination (instantiate)

@[simp] theorem map_instantiate (F : SyntaxMap S T) (B : Expr S (Fin 1 ⊕ V)) (a : Expr S V) :
    F.act (instantiate B a) = instantiate (F.act B) (F.act a) := by
  rw [instantiate, F.substitution, instantiate]
  congr 1
  funext v
  cases v with
  | inl => rfl
  | inr => exact F.on_var _

def Schema.map (F : SyntaxMap S T) (r : Schema S) : Schema T where
  premises := r.premises.map (Judgment.map F)
  conclusion := Judgment.map F r.conclusion

namespace StructuralRule

def map (F : SyntaxMap S T) : StructuralRule S → StructuralRule T
  | .empty => .empty
  | .extend Γ A => .extend (Γ.map F) (F.act A)
  | .variable Γ v => .variable (Γ.map F) v
  | .weaken Γ A φ => .weaken (Γ.map F) (F.act A) (Judgment.mapForm F φ)
  | .typeRefl Γ A => .typeRefl (Γ.map F) (F.act A)
  | .typeSymm Γ A B => .typeSymm (Γ.map F) (F.act A) (F.act B)
  | .typeTrans Γ A B C => .typeTrans (Γ.map F) (F.act A) (F.act B) (F.act C)
  | .termRefl Γ a A => .termRefl (Γ.map F) (F.act a) (F.act A)
  | .termSymm Γ a b A => .termSymm (Γ.map F) (F.act a) (F.act b) (F.act A)
  | .termTrans Γ a b c A => .termTrans (Γ.map F) (F.act a) (F.act b) (F.act c) (F.act A)
  | .convert Γ a A B => .convert (Γ.map F) (F.act a) (F.act A) (F.act B)
  | .convertEq Γ a b A B => .convertEq (Γ.map F) (F.act a) (F.act b) (F.act A) (F.act B)
  | .familyCong Γ A B a b => .familyCong (Γ.map F) (F.act A) (F.act B) (F.act a) (F.act b)

@[simp] theorem schema_map (F : SyntaxMap S T) (r : StructuralRule S) :
    (r.map F).schema = r.schema.map F := by
  cases r with
  | weaken Γ A φ =>
    cases φ <;> simp [map, schema, Schema.map, Judgment.map, Judgment.mapForm,
      Judgment.ctx, Judgment.type, Context.map, Form.rename, F.rename]
  | «variable» Γ v =>
    simp [map, schema, Schema.map, Judgment.map, Judgment.mapForm,
      Judgment.ctx, Judgment.term, Context.map_lookup, F.on_var]
  | familyCong Γ A B a b =>
    simp [map, schema, Schema.map, Judgment.map, Judgment.mapForm,
      Judgment.ctx, Judgment.type, Judgment.typeEq, Judgment.termEq, Context.map]
  | _ => rfl
end StructuralRule

/-- An equality of local rule tables gives a replay certificate, preserving
premise occurrences even when their judgments coincide. -/
def replayMap {S T : Signature} {L M : Type 1}
    (s : L → Schema S) (t : M → Schema T) (F : SyntaxMap S T)
    (labels : L → M) (correct : ∀ r, t (labels r) = (s r).map F) :
    TheoryMap (rulesOf s) (rulesOf t) (Judgment.map F) where
  certificate r := by
    have hc : (rulesOf t).conclusion (labels r) = Judgment.map F ((rulesOf s).conclusion r) := by
      change (t (labels r)).conclusion = _
      rw [correct r]
      rfl
    rw [← hc]
    apply Derivation.rule (R := rulesOf t) (labels r)
    intro i
    have hn : (rulesOf t).count (labels r) = (rulesOf s).count r := by
      change (t (labels r)).premises.length = (s r).premises.length
      rw [correct r]
      exact List.length_map _
    refine Derivation.hyp ⟨⟨i.val, hn ▸ i.isLt⟩, ?_⟩
    change Judgment.map F ((s r).premises.get _) = (t (labels r)).premises.get i
    simp [List.get_eq_getElem, correct r, Schema.map]

def structuralMap (F : SyntaxMap S T) :
    TheoryMap (rulesOf (StructuralRule.schema (S := S)))
      (rulesOf (StructuralRule.schema (S := T))) (Judgment.map F) :=
  replayMap _ _ F (StructuralRule.map F) (StructuralRule.schema_map F)

end SquareKit.DependentPairJudgments
