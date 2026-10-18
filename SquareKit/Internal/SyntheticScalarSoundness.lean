import SquareKit.Internal.SyntheticScalar

/-! Experimental shared scalar-rule induction. The algebraic and geometric
adapters discharge these local interpretation laws with their constructed KL
Taylor theorem. The source judgments remain independent of either model. -/
namespace SquareKit.Internal.SyntheticScalar

/-- Every admitted equality rule is sound under its local ring interpretation.
The hypotheses are individual generator laws, never a product rule. -/
theorem sound_eval {n : ℕ} {R : Type*} [CommRing R] (ρ : Atom n → R)
    (hn : ρ .epsilon * ρ .epsilon = 0)
    (ht : ∀ f, ρ (.shifted f) = ρ (.base f) + ρ (.base (.derivative f)) * ρ .epsilon)
    (ha : ∀ f g, ρ (.base (.add f g)) = ρ (.base f) + ρ (.base g))
    (hm : ∀ f g, ρ (.base (.mul f g)) = ρ (.base f) * ρ (.base g))
    (hs : ∀ f g, ρ (.shifted (.mul f g)) = ρ (.shifted f) * ρ (.shifted g))
    {a b : Expr n} (h : Derives a b) : Expr.eval ρ a = Expr.eval ρ b := by
  induction h with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ij => exact ih.trans ij
  | add _ _ ih ij => exact congrArg₂ (·+·) ih ij
  | mul _ _ ih ij => exact congrArg₂ (·*·) ih ij
  | neg _ ih => exact congrArg Neg.neg ih
  | ring hc => rw [Expr.eval_polynomial, Expr.eval_polynomial, hc]
  | nilsquare => simpa [Expr.eval] using hn
  | taylor f => exact ht f
  | base_add f g => exact ha f g
  | base_mul f g => exact hm f g
  | shifted_mul f g => exact hs f g

end SquareKit.Internal.SyntheticScalar
