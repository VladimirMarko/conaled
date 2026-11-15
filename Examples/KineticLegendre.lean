import Applications.Orbifold.Kinetic.NativeComparison

noncomputable section
namespace Examples.KineticLegendre
open Orbifold Orbifold.Kinetic Orbifold.DiskConnection

/-- A real analytic client acquires an open inverse neighborhood at every admitted rest state. -/
theorem acquired_minus_neighborhood (h : ℝ) (x : ℂ) (hh : 0 < h)
    (hx : Complex.normSq x < 1) :
    ∃ U : Set (ℂ × ℂ), IsOpen U ∧ (x,x) ∈ U ∧ U ⊆ endpointDomain ∧
      ∀ p ∈ U, (minusBranch h x hh hx).symm (legendreMinus h p) = p := by
  refine ⟨(minusBranch h x hh hx).source,(minusBranch h x hh hx).open_source,
    minusBranch_contains h x hh hx,?_,fun p hp => minusBranch_inverse h x hh hx hp⟩
  intro p hp
  rw [minusBranch,OpenPartialHomeomorph.restr_source' _ _ endpointDomain_open] at hp
  exact hp.2

/-- At every target admitted by the branch, the inverse actually solves the phase equation. -/
theorem branch_solves_phase (h : ℝ) (x : ℂ) (hh : 0 < h) (hx : Complex.normSq x < 1)
    (q : ℂ × ℂ) (hq : q ∈ (minusBranch h x hh hx).target) :
    legendreMinus h ((minusBranch h x hh hx).symm q) = q :=
  (minusBranch h x hh hx).right_inv hq

example : (0,0) ∈ (minusBranch 1 0 (by norm_num) (by norm_num)).source :=
  minusBranch_contains 1 0 (by norm_num) (by norm_num)

example : ¬ discreteEL 1 0 (1/2) (4/5) := midpoint_rational_not_DEL
example : exactD2 1 0 (1/2) + exactD1 1 (1/2) (4/5) = 0 := rational_exact_DEL

/-- The native selected lift starts at the apex with a nonzero physical velocity. -/
theorem apex_velocity (d : ℂ) (hd : Complex.normSq d = 1) (s : ℝ) (hs : s ≠ 0) :
    (DiskTransport.move Pose.identity d hd s 0).a = 0 ∧
    (DiskTransport.move Pose.identity d hd s 0).frame (d*(s : ℂ)) ≠ 0 := by
  rw [DiskTransport.move_initial]
  constructor
  · rfl
  · have hd0 : d ≠ 0 := by intro H; simp [H] at hd
    simp [Pose.frame,Pose.identity,hd0,hs]

/-- Reuse the actual native parallel-transport theorem for every selected frame vector. -/
theorem selected_frame_retained (p : Pose) (d : ℂ) (hd : Complex.normSq d = 1)
    (s T : ℝ) (hT : 0 ≤ T) (w : ℂ) :
    (DiskTransport.moveSegment p d hd s T hT).transport (p.frame w) =
      (DiskTransport.move p d hd s T).frame w :=
  DiskTransport.move_transport p d hd s T hT w

example : EulerLagrangeAt (fun t => (DiskTransport.move Pose.identity 1 (by norm_num) 0 t).a)
    (fun t => (DiskTransport.move Pose.identity 1 (by norm_num) 0 t).frame 0) 0 := by
  simpa using native_eulerLagrange Pose.identity 1 (by norm_num) 0 0

/-- The C4 label is retained as an input; it rotates the chosen incoming lift. -/
theorem rotated_diameter (g : Orbifold.QuarterTurn.C4) (d : ℂ)
    (hd : Complex.normSq d = 1) (s t : ℝ) :
    EulerLagrangeAt
      (fun r => (DiskTransport.move Pose.identity (Orbifold.LocalDisplacement.phase g*d)
        (by simpa [map_mul,Orbifold.LocalDisplacement.phase_norm] using hd) s r).a)
      (fun r => (DiskTransport.move Pose.identity (Orbifold.LocalDisplacement.phase g*d)
        (by simpa [map_mul,Orbifold.LocalDisplacement.phase_norm] using hd) s r).frame
          ((Orbifold.LocalDisplacement.phase g*d)*(s : ℂ))) t :=
  native_eulerLagrange _ _ _ _ _

end Examples.KineticLegendre
