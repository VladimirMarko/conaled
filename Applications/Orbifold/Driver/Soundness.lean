import Applications.Orbifold.Driver.Execution

namespace Orbifold.DiskTransport.Numerical.Driver
open Set

/-- Reuse the backend's conservative margin and exact trajectory-domain theorem. -/
theorem checked_exact_domain {c : Tick} {q r : Packet} {p : Pose}
    (hr : checkedStep c q = some r) (hp : Approx q p) :
    ∀ t ∈ Icc (0 : ℝ) c.duration, Domain (coordinates (c.control.decode.trajectory p t)) := by
  have hc : Admissible c q := by
    unfold checkedStep at hr
    split at hr
    · assumption
    · contradiction
  have hv : ‖c.control.decode.velocity‖ ≤ 1 := by
    rw [← Input.decode_velocity]
    simpa only [Rat.cast_one] using norm_decode_of_sq (by norm_num : (0 : ℚ) ≤ 1)
      (by simpa using hc.1)
  have hz : ‖p.a‖ ≤ (q.state.position.size : ℝ)+q.error := by
    have hdiff := (norm_fst_le (q.state.decode-coordinates p)).trans hp
    have ht := norm_add_le (p.a-q.state.position.decode) q.state.position.decode
    rw [sub_add_cancel,norm_sub_rev] at ht
    have hs := QComplex.norm_decode_le_size q.state.position
    change ‖q.state.position.decode-p.a‖ ≤ (q.error : ℝ) at hdiff
    linarith
  have hmargin : ‖p.a‖+(c.duration : ℝ)/2 ≤ 1/2 := by
    have H := (Rat.cast_le (K := ℝ)).mpr hc.2.2.2.1
    norm_num at H
    linarith
  exact fun t ht => trajectory_domain c.control.decode p hv hmargin ht

def ExactDomains : Pose → List Tick → Prop
  | _, [] => True
  | p, c::cs =>
    (∀ t ∈ Icc (0 : ℝ) c.duration, Domain (coordinates (c.control.decode.trajectory p t))) ∧
      ExactDomains (c.decode.finish p) cs

theorem run_exact_domains {cs : List Tick} {q : Packet} {r : Result} {p : Pose}
    (hr : Numerical.run cs q = some r) (hp : Approx q p) : ExactDomains p cs := by
  induction cs generalizing q r p with
  | nil => trivial
  | cons c cs ih =>
    simp only [Numerical.run] at hr
    cases hs : checkedStep c q with
    | none => simp [hs] at hr
    | some s =>
      cases ht : Numerical.run cs s with
      | none => simp [hs,ht] at hr
      | some out =>
        exact ⟨checked_exact_domain hs hp,ih ht (checkedStep_correct hs hp).1⟩

def SampleSound (p : Pose) : Observation → Prop
  | .relabel _ _ => True
  | .command c n _ r =>
    List.Forall₂ Approx r.samples (endpoints p (schedule c n)) ∧
    List.Forall (fun s => Domain s.state.decode) r.samples ∧ ExactDomains p (schedule c n)

def TraceSound : Pose → List Observation → Prop
  | _, [] => True
  | p, o::os => SampleSound p o ∧ TraceSound (o.event.finish p) os

theorem chain_correct {q final : Packet} {os : List Observation} (hc : Chain q os final)
    {p : Pose} (hp : Approx q p) :
    Approx final (executeEvents (os.map Observation.event) p) ∧ TraceSound p os := by
  induction os generalizing q p with
  | nil => cases hc; exact ⟨hp,trivial⟩
  | cons o os ih =>
    obtain ⟨hs,ho,ht⟩ := hc
    have hp' : Approx o.incoming p := by rwa [hs]
    have H := ih ht (observation_correct o ho hp')
    refine ⟨H.1,?_,H.2⟩
    cases o with
    | relabel k q => trivial
    | command c n q r =>
      have hc' := Numerical.run_correct ho hp'
      exact ⟨hc'.2.1,hc'.2.2,run_exact_domains ho hp'⟩

theorem chain_clock {q final : Packet} {os : List Observation} (hc : Chain q os final) :
    (os.map Observation.elapsed).sum = eventClock (os.map Observation.event) := by
  induction os generalizing q with
  | nil => rfl
  | cons o os ih =>
    obtain ⟨_,ho,ht⟩ := hc
    simp only [List.map_cons,List.sum_cons,eventClock]
    rw [observation_clock o ho]
    exact congrArg (o.event.duration + ·) (ih ht)

theorem success_sound (limits : Limits) (tolerance : ℚ) (es : List Event)
    (q : Packet) (fuel index : Nat) {p : Pose} (hp : Approx q p)
    (hs : (drive limits tolerance es q fuel index).failure = none) :
    Approx (drive limits tolerance es q fuel index).final (executeEvents es p) ∧
    TraceSound p (drive limits tolerance es q fuel index).observations ∧
    (drive limits tolerance es q fuel index).final.error ≤ tolerance := by
  have H := chain_correct (drive_chain limits tolerance es q fuel index) hp
  have HP := drive_partition limits tolerance es q fuel index
  have HC := drive_success limits tolerance es q fuel index hs
  rw [HC.1,List.append_nil] at HP
  rw [HP] at H
  exact ⟨H.1,H.2,HC.2⟩

end Orbifold.DiskTransport.Numerical.Driver
