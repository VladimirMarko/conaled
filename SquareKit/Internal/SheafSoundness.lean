import SquareKit.Internal.SheafFormula
import SquareKit.Internal.Frobenius

/-! Experimental soundness of the existing regular calculus in sheaves.
Elimination uses closed-target local-image adjunction, never global witnesses.
-/
namespace SquareKit.Internal.SheafContexts
open CategoryTheory Opposite
universe u v w
variable {J : Type v} [SmallCategory J] {K : GrothendieckTopology J}
variable {S : Type u} {F P : S → S → Type u}
variable (M : Presheaf.Model.{u,v,w} (J := J) F P)
variable (hM : ∀ s, Presieve.IsSheaf K (M.carrier s))

/-- Weakening is inverse image along the context projection. -/
theorem formula_shift (p : Formula F Γ P) :
    formula M hM (p.shift (s := s)) =
      (formula M hM p).preimage (projection M hM).hom :=
  formula_substitution M hM p (fun i => .var (.succ i))

/-- Instantiation substitutes the actual interpreted term, including under binders. -/
theorem formula_instantiate (p : Formula F (s :: Γ) P) (t : Term F Γ s) :
    formula M hM (p.instantiate t) =
      (formula M hM p).preimage (substitution M hM (single t)).hom :=
  formula_substitution M hM p (single t)

/-- Every current source derivation preserves interpreted sheaf predicates. -/
theorem sound
    (hR : ∀ {s t} (r : P s t), Presieve.IsSheaf K (M.relation r).toFunctor)
    (d : Derives p q) : Valid M hM p q := by
  induction d with
  | ident => exact le_rfl
  | cut _ _ hp hq => exact hp.trans hq
  | left => exact inf_le_left
  | right => exact inf_le_right
  | pair _ _ hp hq => exact le_inf hp hq
  | refl => intro j ρ _; rfl
  | symm _ ih => intro j ρ h; exact (ih j h).symm
  | trans _ _ hp hq => intro j ρ h; exact (hp j h).trans (hq j h)
  | congr _ ih => intro j ρ h; exact congrArg ((M.fiber j).arrow _) (ih j h)
  | intro p t =>
    intro j ρ h
    rw [formula_instantiate] at h
    exact (Subfunctor.le_sheafify _ _ _) ⟨(M.substitution (single t)).app j ρ, h, rfl⟩
  | subst σ _ ih =>
    unfold Valid at *
    rw [formula_substitution, formula_substitution]
    intro j ρ h
    exact ih j h
  | @elimWith Γ s p h q _ ih =>
    unfold Valid at *
    change formula M hM h ⊓ SquareKit.SheafImage.localImage (formula M hM p)
      (projection M hM) ≤ formula M hM q
    rw [inf_comm, ← SquareKit.SheafImage.frobenius _ _ _ (formula_isSheaf M hM hR h)]
    apply (SquareKit.SheafImage.adjunction _ _ _ (formula_isSheaf M hM hR q)).mpr
    change formula M hM h.shift ⊓ formula M hM p ≤ formula M hM q.shift at ih
    rw [formula_shift, formula_shift, inf_comm] at ih
    exact ih
  | @elim Γ s p q _ ih =>
    unfold Valid at *
    apply (SquareKit.SheafImage.adjunction _ _ _ (formula_isSheaf M hM hR q)).mpr
    change formula M hM p ≤ formula M hM q.shift at ih
    rw [formula_shift] at ih
    exact ih

/-- Source Frobenius is interpreted through soundness in both directions. -/
theorem frobenius_valid
    (hR : ∀ {s t} (r : P s t), Presieve.IsSheaf K (M.relation r).toFunctor)
    (h : Formula F Γ P) (p : Formula F (s :: Γ) P) :
    formula M hM (.conj h (.ex p)) = formula M hM (.ex (.conj h.shift p)) :=
  le_antisymm (sound M hM hR (Frobenius.forward h p))
    (sound M hM hR (Frobenius.backward h p))

/-- Separate semantic comparison: weakening is preimage, conjunction intersection. -/
theorem frobenius_semantic_comparison
    (hR : ∀ {s t} (r : P s t), Presieve.IsSheaf K (M.relation r).toFunctor)
    (h : Formula F Γ P) (p : Formula F (s :: Γ) P) :
    formula M hM (.ex (.conj h.shift p)) =
      formula M hM h ⊓ SquareKit.SheafImage.localImage (formula M hM p) (projection M hM) := by
  change SquareKit.SheafImage.localImage (formula M hM h.shift ⊓ formula M hM p) (projection M hM (s := s) (Γ := Γ)) = _
  rw [formula_shift]
  calc
    _ = SquareKit.SheafImage.localImage
        (formula M hM p ⊓ (formula M hM h).preimage (projection M hM).hom)
        (projection M hM) := congrArg (fun Q => SquareKit.SheafImage.localImage Q
          (projection M hM)) (inf_comm _ _)
    _ = _ := (SquareKit.SheafImage.frobenius (A := context M hM (s :: Γ)) (B := context M hM Γ) (formula M hM p) (projection M hM)
      (formula M hM h) (formula_isSheaf M hM hR h)).trans (inf_comm _ _)

end SquareKit.Internal.SheafContexts
