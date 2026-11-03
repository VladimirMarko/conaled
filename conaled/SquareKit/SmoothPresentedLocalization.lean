import SquareKit.SmoothPresentation

/-! Experimental localization of actual finite smooth presentations.
Representatives supply the finite relation list; the universal maps remove their choice. -/
noncomputable section
namespace SquareKit.SmoothAlgebra.PresentedLocalization
open Presentation
variable {n m : ℕ}

def equation (p : Free n) : Free (n+1) := Localization.extend (k := 1) p * generator (Fin.last n) - 1
abbrev Carrier (r : Fin m → Free n) (p : Free n) := Adjoin r (equation p)
abbrev base (r : Fin m → Free n) (p : Free n) : Hom (Presentation.Carrier r) (Carrier r p) := inclusion r (equation p)
abbrev inverse (r : Fin m → Free n) (p : Free n) : Carrier r p := coordinate r (equation p)

theorem inverse_relation (r : Fin m → Free n) (p : Free n) : base r p (Presentation.projection r p) * inverse r p = 1 := by
  have he := adjoin_relation r (equation p)
  change (Presentation.projection (relations r (equation p))).toAlgHom (Localization.extend p * generator (Fin.last n) - 1) = 0 at he
  rw [map_sub,map_mul,map_one,sub_eq_zero] at he
  exact he

theorem base_isUnit (r : Fin m → Free n) (p : Free n) : IsUnit (base r p (Presentation.projection r p)) :=
  ⟨⟨_,inverse r p,inverse_relation r p,(mul_comm _ _).trans (inverse_relation r p)⟩,rfl⟩

variable {B C : Type*} [CommRing B] [Algebra ℝ B] [Structure B]
  [CommRing C] [Algebra ℝ C] [Structure C]

def lift (r : Fin m → Free n) (p : Free n) (h : Hom (Presentation.Carrier r) B)
    (hu : IsUnit (h (Presentation.projection r p))) : Hom (Carrier r p) B :=
  Presentation.lift r (equation p) h (Ring.inverse (h (Presentation.projection r p))) (by
    change (evaluate (coordinates r h (Ring.inverse (h (Presentation.projection r p))))).toAlgHom
      (Localization.extend p * generator (Fin.last n) - 1) = 0
    rw [map_sub,map_mul,map_one]
    change evaluate (coordinates r h (Ring.inverse (h (Presentation.projection r p)))) (Localization.extend p) *
      evaluate (coordinates r h (Ring.inverse (h (Presentation.projection r p)))) (generator (Fin.last n)) - 1 = 0
    rw [show evaluate (coordinates r h (Ring.inverse (h (Presentation.projection r p)))) (Localization.extend p) = h (Presentation.projection r p) from evaluate_extend _ _ _ _]
    rw [show evaluate (coordinates r h (Ring.inverse (h (Presentation.projection r p)))) (generator (Fin.last n)) = Ring.inverse (h (Presentation.projection r p)) from
      (evaluate_generator _ _).trans (Fin.snoc_last _ _)]
    rw [Ring.mul_inverse_cancel _ hu,sub_self])

@[simp] theorem lift_base (r : Fin m → Free n) (p : Free n) (h : Hom (Presentation.Carrier r) B)
    (hu : IsUnit (h (Presentation.projection r p))) : Hom.comp (lift r p h hu) (base r p) = h :=
  Presentation.lift_inclusion _ _ _ _ _

@[simp] theorem lift_inverse (r : Fin m → Free n) (p : Free n) (h : Hom (Presentation.Carrier r) B)
    (hu : IsUnit (h (Presentation.projection r p))) : lift r p h hu (inverse r p) = Ring.inverse (h (Presentation.projection r p)) :=
  Presentation.lift_coordinate _ _ _ _ _

theorem unique (r : Fin m → Free n) (p : Free n) (h k : Hom (Carrier r p) B)
    (he : Hom.comp h (base r p) = Hom.comp k (base r p)) : h=k := by
  apply Presentation.unique r (equation p) h k he
  apply Localization.inverse_unique (a := h (base r p (Presentation.projection r p)))
  · rw [← h.map_mul,inverse_relation]
    exact h.toAlgHom.map_one
  · have hh := congrArg (fun l : Hom (Presentation.Carrier r) B => l (Presentation.projection r p)) he
    change h (base r p (Presentation.projection r p)) = k (base r p (Presentation.projection r p)) at hh
    rw [hh,← k.map_mul,inverse_relation]
    exact k.toAlgHom.map_one

def homEquiv (r : Fin m → Free n) (p : Free n) :
    Hom (Carrier r p) B ≃ {h : Hom (Presentation.Carrier r) B // IsUnit (h (Presentation.projection r p))} where
  toFun h := ⟨Hom.comp h (base r p),(base_isUnit r p).map h.toAlgHom⟩
  invFun h := lift r p h.val h.property
  left_inv h := unique r p _ h (lift_base _ _ _ _)
  right_inv h := Subtype.ext (lift_base r p h.val h.property)

theorem lift_natural (r : Fin m → Free n) (p : Free n) (h : Hom (Presentation.Carrier r) B)
    (hu : IsUnit (h (Presentation.projection r p))) (k : Hom B C) :
    Hom.comp k (lift r p h hu) = lift r p (Hom.comp k h) (hu.map k.toAlgHom) := by
  apply unique r p
  rw [← Hom.comp_assoc,lift_base]
  exact (lift_base r p (Hom.comp k h) (hu.map k.toAlgHom)).symm

/-- An arbitrary quotient element supplies a representative internally. -/
def representative (r : Fin m → Free n) (s : Presentation.Carrier r) : Free n :=
  Classical.choose (Ideal.Quotient.mk_surjective s)
@[simp] theorem representative_eq (r : Fin m → Free n) (s : Presentation.Carrier r) :
    Presentation.projection r (representative r s) = s := Classical.choose_spec (Ideal.Quotient.mk_surjective s)

abbrev At (r : Fin m → Free n) (s : Presentation.Carrier r) := Carrier r (representative r s)
abbrev atBase (r : Fin m → Free n) (s : Presentation.Carrier r) : Hom (Presentation.Carrier r) (At r s) := base r (representative r s)

abbrev atInverse (r : Fin m → Free n) (s : Presentation.Carrier r) : At r s := inverse r (representative r s)

theorem at_inverse_relation (r : Fin m → Free n) (s : Presentation.Carrier r) :
    atBase r s s * atInverse r s = 1 := by
  have h := inverse_relation r (representative r s)
  simpa only [representative_eq] using h

theorem atBase_isUnit (r : Fin m → Free n) (s : Presentation.Carrier r) : IsUnit (atBase r s s) := by
  have h := base_isUnit r (representative r s)
  simpa only [representative_eq] using h

def atHomEquiv (r : Fin m → Free n) (s : Presentation.Carrier r) :
    Hom (At r s) B ≃ {h : Hom (Presentation.Carrier r) B // IsUnit (h s)} :=
  (homEquiv r (representative r s)).trans {
    toFun h := ⟨h.val,by simpa using h.property⟩
    invFun h := ⟨h.val,by simpa using h.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }

end SquareKit.SmoothAlgebra.PresentedLocalization
