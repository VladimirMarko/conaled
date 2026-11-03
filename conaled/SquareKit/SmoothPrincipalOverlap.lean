import SquareKit.SmoothPrincipalCover

/-! Experimental algebraic overlaps of principal smooth localizations.
Their universal squares have the opposite variance of geometric pullbacks. -/
noncomputable section
namespace SquareKit.SmoothAlgebra.PresentedLocalization
variable {n m : ℕ}

private theorem product_units (r : Fin m → Free n) (p q : Free n) :
    IsUnit (base r (p*q) (Presentation.projection r p)) ∧
      IsUnit (base r (p*q) (Presentation.projection r q)) := by
  have h := base_isUnit r (p*q)
  rw [(Presentation.projection r).map_mul,(base r (p*q)).map_mul,IsUnit.mul_iff] at h
  exact h

def overlapLeft (r : Fin m → Free n) (p q : Free n) : Hom (Carrier r p) (Carrier r (p*q)) :=
  lift r p (base r (p*q)) (product_units r p q).1

def overlapRight (r : Fin m → Free n) (p q : Free n) : Hom (Carrier r q) (Carrier r (p*q)) :=
  lift r q (base r (p*q)) (product_units r p q).2

theorem overlapLeft_base (r : Fin m → Free n) (p q : Free n) :
    Hom.comp (overlapLeft r p q) (base r p) = base r (p*q) := lift_base _ _ _ _
theorem overlapRight_base (r : Fin m → Free n) (p q : Free n) :
    Hom.comp (overlapRight r p q) (base r q) = base r (p*q) := lift_base _ _ _ _

variable {B : Type*} [CommRing B] [Algebra ℝ B] [Structure B]

/-- All compatible maps into arbitrary smooth algebras factor uniquely through the overlap. -/
theorem overlap_pushout (r : Fin m → Free n) (p q : Free n)
    (u : Hom (Carrier r p) B) (v : Hom (Carrier r q) B)
    (hc : Hom.comp u (base r p) = Hom.comp v (base r q)) :
    ∃! h : Hom (Carrier r (p*q)) B,
      Hom.comp h (overlapLeft r p q) = u ∧ Hom.comp h (overlapRight r p q) = v := by
  let a := Hom.comp u (base r p)
  have hp : IsUnit (a (Presentation.projection r p)) := (base_isUnit r p).map u.toAlgHom
  have hq : IsUnit (a (Presentation.projection r q)) := by
    have h := (base_isUnit r q).map v.toAlgHom
    change IsUnit ((Hom.comp v (base r q)) (Presentation.projection r q)) at h
    rw [← hc] at h
    exact h
  have hu : IsUnit (a (Presentation.projection r (p*q))) := by
    rw [(Presentation.projection r).map_mul,a.map_mul]
    exact hp.mul hq
  let h := lift r (p*q) a hu
  have hb : Hom.comp h (base r (p*q)) = a := lift_base _ _ _ _
  refine ⟨h,⟨?_,?_⟩,?_⟩
  · apply unique r p
    rw [← Hom.comp_assoc,overlapLeft_base,hb]
  · apply unique r q
    rw [← Hom.comp_assoc,overlapRight_base,hb]
    exact hc
  · intro h' hh
    apply unique r (p*q)
    rw [hb,← overlapLeft_base r p q,Hom.comp_assoc,hh.1]

end SquareKit.SmoothAlgebra.PresentedLocalization
