import Examples.AtlasTransport

/-! Closing arrows are retained independently of their tangent observations. -/
noncomputable section
open CategoryTheory MulAction
open scoped Manifold
namespace Examples.AtlasIsotropy
open Orbifold Orbifold.DiskTransport Orbifold.FrameGauge Orbifolds.QuarterTurn

/-- The kernel factor is the two-element permutation group. -/
abbrev C2 := Equiv.Perm (Fin 2)
abbrev Ineffective := C4 × C2

local instance : MulAction Ineffective Orbifold.Disk := MulAction.compHom Orbifold.Disk (MonoidHom.fst C4 C2)

def kernel : C2 := Equiv.swap 0 1

def close (k : C2) : (↑origin : ActionCategory Ineffective Orbifold.Disk) ⟶
    (↑origin : ActionCategory Ineffective Orbifold.Disk) :=
  Functor.Elements.homMk (quarterTurn, k) (by
    apply Subtype.ext
    change (quarterTurn.val : ℂ) * (0 : ℂ) = 0
    simp)

/-- This is the actual derivative of the product action, whose second factor
acts ineffectively; it is not a faithful replacement of the label group. -/
theorem product_tangent (g : Ineffective) (x : Orbifold.Disk) (v : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : Orbifold.Disk => g • z) x v = (g.1.val : ℂ) * v :=
  disk_tangent g.1 x v

def selectedLabel (k : C2) : Ineffective := (close k).hom

def closed (k : C2) (v : ℂ) : ℂ :=
  mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : Orbifold.Disk => selectedLabel k • z) origin
    (AtlasTransport.apexAtlas.transport v)

theorem different_closings : close 1 ≠ close kernel := by
  intro h
  have he := congrArg (fun a => a.hom.2 (0 : Fin 2)) h
  norm_num [close, kernel, Equiv.swap_apply_def] at he

theorem same_observation (v : ℂ) : closed 1 v = closed kernel v := by
  simp only [closed, product_tangent]
  rfl

example : closed kernel 1 = Complex.I := by
  rw [closed, product_tangent, AtlasPath.agreement]
  simp [selectedLabel, close, AtlasTransport.apexAtlas, PathTransport.apexClosed,
    DiskTransport.Path.transport, Segment.hold_transport]

example : Nat.card C2 = 2 := by simp [Nat.card_eq_fintype_card, Fintype.card_perm]

def originArrows : ((↑origin : ActionCategory C4 Orbifold.Disk) ⟶
    (↑origin : ActionCategory C4 Orbifold.Disk)) ≃ C4 where
  toFun f := f.hom
  invFun g := Functor.Elements.homMk g (by
    apply Subtype.ext
    change (g.val : ℂ) * (0 : ℂ) = 0
    simp)
  left_inv _ := Functor.Elements.Hom.ext rfl
  right_inv _ := rfl

theorem origin_four_arrows : Nat.card ((↑origin : ActionCategory C4 Orbifold.Disk) ⟶
    (↑origin : ActionCategory C4 Orbifold.Disk)) = 4 :=
  (Nat.card_congr originArrows).trans card_C4

theorem regular_arrow_identity (x : Orbifold.Disk) (hx : (x : ℂ) ≠ 0)
    (f : (↑x : ActionCategory C4 Orbifold.Disk) ⟶ (↑x : ActionCategory C4 Orbifold.Disk)) :
    f = 𝟙 _ := by
  have hm : (show C4 from f.hom) ∈ stabilizer C4 x := f.map_val
  rw [nonzero_stabilizer x hx] at hm
  apply Functor.Elements.Hom.ext
  exact hm

/-- Effective isotropy is unchanged by the atlas transport construction. -/
example : Nat.card C4 = 4 ∧ stabilizer C4 origin = ⊤ := ⟨card_C4, origin_stabilizer⟩

example (x : Orbifold.Disk) (hx : (x : ℂ) ≠ 0) : stabilizer C4 x = ⊥ := nonzero_stabilizer x hx

/-- A closing map goes from the lifted endpoint to the source. Reversing the
selected quarter-turn produces the opposite observed tangent at the apex. -/
example : AtlasPath.closed PathTransport.apexClosed AtlasTransport.apexAtlas 1 ≠
    ((quarterTurn⁻¹).val : ℂ) * AtlasTransport.apexAtlas.transport 1 := by
  rw [AtlasPath.closed_agreement, AtlasPath.agreement]
  simp only [PathTransport.apexClosed, DiskTransport.Path.ClosedLift.endomorphism,
    DiskTransport.Path.ClosedLift.label, DiskTransport.Path.transport,
    Segment.hold_transport, quarterTurn, Units.val_inv_eq_inv_val]
  intro h
  have hi := congrArg Complex.im h
  norm_num at hi

end Examples.AtlasIsotropy
