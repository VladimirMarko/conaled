import SquareKit.Internal.Cubical.FaceEndpoints

/-! Canonical substitutions associated with partial endpoint assignments. -/
namespace SquareKit.Cubical
open CategoryTheory
namespace Face

def restrictionExpr {n : ℕ} (ρ : Assignment n) (i : Fin n) : Expr (Fin n) :=
  match ρ i with
  | none => .var i
  | some false => .zero
  | some true => .one

def restriction {I : Cube} (ρ : Assignment I.dimension) : Cube.Hom I I := Cube.ofRaw (restrictionExpr ρ)

theorem assignmentMap_restriction_none {I : Cube} (ρ : Assignment I.dimension) :
    assignmentMap (restriction ρ) (fun _ => none) = ρ := by
  funext i
  change PartialDimension.eval (fun _ => none) (restrictionExpr ρ i) = ρ i
  cases h : ρ i with
  | none => simp [restrictionExpr,h,PartialDimension.eval]
  | some b => cases b <;> simp [restrictionExpr,h,PartialDimension.eval]

theorem restriction_fixes {I J : Cube} (f : Cube.Hom I J) :
    Cube.comp f (restriction (assignmentMap f (fun _ => none))) = f := by
  refine Quotient.inductionOn f ?_
  intro f
  apply Quotient.sound
  intro i
  change Expr.Conv (Expr.subst f (restrictionExpr (fun i => PartialDimension.eval (fun _ => none) (f i)) i)) (f i)
  cases h : PartialDimension.eval (fun _ => none) (f i) with
  | none => simp only [restrictionExpr,h,Expr.subst]; exact .refl _
  | some b =>
    cases b
    · simpa [restrictionExpr,h,Expr.subst,PartialDimension.endpointExpr] using (PartialDimension.eval_endpoint_reflects (f i) false h).symm
    · simpa [restrictionExpr,h,Expr.subst,PartialDimension.endpointExpr] using (PartialDimension.eval_endpoint_reflects (f i) true h).symm

theorem restriction_after {I J : Cube} (f : Cube.Hom I J) (ρ : Assignment I.dimension) :
    Cube.comp (Cube.comp (restriction ρ) f) (restriction (assignmentMap f ρ)) =
      Cube.comp (restriction ρ) f := by
  have h := restriction_fixes (Cube.comp (restriction ρ) f)
  rw [assignmentMap_comp,assignmentMap_restriction_none] at h
  exact h

theorem restriction_idempotent {I : Cube} (ρ : Assignment I.dimension) :
    Cube.comp (restriction ρ) (restriction ρ) = restriction ρ := by
  have h := restriction_fixes (restriction ρ)
  rw [assignmentMap_restriction_none] at h
  exact h

theorem restriction_refinement {I : Cube} (ρ τ : Assignment I.dimension) (h : Refines ρ τ) :
    Cube.comp (restriction τ) (restriction ρ) = restriction τ := by
  apply Quotient.sound
  intro i
  change Expr.Conv (Expr.subst (restrictionExpr τ) (restrictionExpr ρ i)) (restrictionExpr τ i)
  cases hr : ρ i with
  | none => simp only [restrictionExpr,hr,Expr.subst]; exact .refl _
  | some b =>
    have ht : τ i = some b := by
      rcases h i with hn | he
      · simp [hr] at hn
      · exact he.symm.trans hr
    cases b <;> simp only [restrictionExpr,hr,ht,Expr.subst] <;> exact .refl _

end Face
end SquareKit.Cubical
