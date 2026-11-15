import Applications.Orbifold.LocalDisplacement.Alignment

/-! Optional orbit/groupoid wrapper for a fixed selected relative alignment.
Independent changes of representatives still require relabeling that alignment. -/
noncomputable section
open CategoryTheory
namespace Orbifold.LocalDisplacement
open QuarterTurn (C4)

theorem endpoint_diagonal (g h : C4) (a b : ℂ) :
    endpoint g (phase h*a) (phase h*b) = phase h*endpoint g a b := by
  unfold endpoint
  rw [show phase g*(phase h*b) = phase h*(phase g*b) by ring,diagonal]

theorem aligned_diagonal (g h : C4) {a b : ℂ} (hab : Aligned g a b) :
    Aligned g (phase h*a) (phase h*b) := by
  unfold Aligned
  rw [show phase g*(phase h*b) = phase h*(phase g*b) by ring]
  exact rotate_admissible h hab

/-- Both representatives are retained; g is the selected relative alignment. -/
def Input (g : C4) := {p : ℂ × ℂ // Aligned g p.1 p.2}

instance (g : C4) : MulAction C4 (Input g) where
  smul h p := ⟨(phase h*p.val.1,phase h*p.val.2),aligned_diagonal g h p.property⟩
  one_smul p := by
    apply Subtype.ext
    change (phase 1*p.val.1,phase 1*p.val.2) = p.val
    simp [phase]
  mul_smul h k p := by
    apply Subtype.ext
    change (phase (h*k)*p.val.1,phase (h*k)*p.val.2) =
      (phase h*(phase k*p.val.1),phase h*(phase k*p.val.2))
    simp [phase,mul_assoc]

def output (g : C4) (p : Input g) : Disk :=
  ⟨endpoint g p.val.1 p.val.2,(disk_mem _).mpr (mem_disk p.property.2.2)⟩

theorem output_equivariant (g h : C4) (p : Input g) : output g (h • p) = h • output g p := by
  apply Subtype.ext
  exact endpoint_diagonal g h p.val.1 p.val.2

def endpointFunctor (g : C4) : ActionCategory C4 (Input g) ⥤ ActionCategory C4 Disk :=
  Orbifolds.actionFunctor (MonoidHom.id C4) (output g) (output_equivariant g)

theorem endpointFunctor_label (g : C4) {p q : ActionCategory C4 (Input g)} (f : p ⟶ q) :
    ((endpointFunctor g).map f).hom = f.hom := rfl

/-- Descent is for simultaneously relabeled admitted pairs, not a product of
independent position quotients. -/
def endpointSquare (g : C4) :=
  Orbifolds.orbitSquare (MonoidHom.id C4) (output g) (output_equivariant g)

end Orbifold.LocalDisplacement
