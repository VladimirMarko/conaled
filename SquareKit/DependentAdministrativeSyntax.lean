import SquareKit.DependentTypedSubstitution

/-! Syntax naturality for administrative typed-substitution proof nodes.
These equations concern their complete judgments, including the types of the
substitution arguments; they do not assume any proof-transport coherence. -/
namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps

namespace Judgment
variable {S T : Signature}

/-- Mapping a judgment form commutes with simultaneous capture-avoiding
substitution, including all endpoints of typed equality. -/
theorem mapForm_subst (F : SyntaxMap S T) (φ : Form S V)
    (σ : V → Expr S W) :
    mapForm F (φ.subst σ) = (mapForm F φ).subst (fun v => F.act (σ v)) := by
  cases φ <;> simp only [mapForm, Form.subst, F.substitution]

/-- The conclusion of an administrative substitution is preserved by syntax
translation. Both routes use the same target context. -/
theorem map_substituted (F : SyntaxMap S T) (j : Judgment S)
    (Δ : Context S W) (σ : j.Scope → Expr S W) :
    (Judgment.mk W Δ (j.form.subst σ)).map F =
      ⟨W, Δ.map F, (j.map F).form.subst (fun v => F.act (σ v))⟩ := by
  simp only [map, mapForm_subst]

/-- Every typed substitution argument maps to an argument of the translated
source context. Lookup and substitution both participate in this equation. -/
theorem map_substitution_argument (F : SyntaxMap S T) (j : Judgment S)
    (Δ : Context S W) (σ : j.Scope → Expr S W) (v : j.Scope) :
    (Judgment.term Δ (σ v) (Expr.subst σ (j.context.lookup v))).map F =
      Judgment.term (Δ.map F) (F.act (σ v))
        (Expr.subst (fun v => F.act (σ v)) ((j.map F).context.lookup v)) := by
  simp only [map, term, mapForm, Context.map_lookup, F.substitution]

end Judgment
end SquareKit.DependentPairJudgments
