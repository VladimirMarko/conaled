import SquareKit.Internal.PathTransport.TwoIdentityMateFunctoriality
/-! The genuine endpoint square used by coherent path contraction. -/
namespace SquareKit.Internal.PathTransport.TwoIdentityTransport
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
variable {B : Type u} [Bicategory.{w,v} B] [Bicategory.Strict B]
variable [IsLocallyGroupoid B]
/-- Move a path-family cell across an invertible first endpoint. -/
noncomputable def pathSquare {a b c d : B} (u : a ⟶ b) [IsIso u]
    (h : a ⟶ c) (v : c ⟶ d) (q : b ⟶ d) (ρ : inv u ≫ h ≫ v ⟶ q) :
    u ≫ q ⟶ h ≫ v :=
  u ◁ inv ρ ≫ eqToHom (by simp)
/-- Transporting the endpoint square back recovers the original inverse cell. -/
theorem pathSquare_cancel {a b c d : B} (u : a ⟶ b) [IsIso u]
    (h : a ⟶ c) (v : c ⟶ d) (q : b ⟶ d) (ρ : inv u ≫ h ≫ v ⟶ q) :
    HEq (inv u ◁ pathSquare u h v q ρ) (inv ρ) := by
  simp only [pathSquare, whiskerLeft_comp, whiskerLeft_eqToHom]
  apply HEq.trans (comp_eqToHom_heq _ _)
  have hh := heq_of_eq (comp_whiskerLeft (inv u) u (inv ρ))
  simp only [Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv,
    heq_eqToHom_comp_iff, heq_comp_eqToHom_iff] at hh
  apply HEq.trans hh.symm
  rw [IsIso.inv_hom_id]
  simp only [id_whiskerLeft, Strict.leftUnitor_eqToIso, eqToIso.hom, eqToIso.inv]
  apply HEq.trans (eqToHom_comp_heq _ _)
  exact comp_eqToHom_heq _ _
end SquareKit.Internal.PathTransport.TwoIdentityTransport
