import Applications.Orbifold.CheckedMotion

/-! Finite execution preserves coordinate error and command-local observations. -/
namespace Orbifold.DiskTransport.Numerical

structure Result where
  final : Packet
  samples : List Packet
  elapsed : ℚ
  deriving DecidableEq, Repr

/-- Samples are the successive endpoints, with the input ticks retaining their
controls and local durations. A failed tick rejects the whole execution. -/
def run : List Tick → Packet → Option Result
  | [], q => some ⟨q, [], 0⟩
  | c :: cs, q => do
    let r ← checkedStep c q
    let result ← run cs r
    pure ⟨result.final, r :: result.samples, c.duration+result.elapsed⟩

noncomputable def endpoints (p : Pose) : List Tick → List Pose
  | [] => []
  | c :: cs => c.decode.finish p :: endpoints (c.decode.finish p) cs

def clock (cs : List Tick) : ℚ := (cs.map Tick.duration).sum

theorem clock_decode (cs : List Tick) : (clock cs : ℝ) = elapsed (cs.map Tick.decode) := by
  induction cs with
  | nil => simp [clock, elapsed]
  | cons c cs ih => simpa [clock, elapsed, Tick.decode] using congrArg ((c.duration : ℝ) + ·) ih

theorem run_correct {cs : List Tick} {q : Packet} {r : Result} {p : Pose}
    (h : run cs q = some r) (hp : Approx q p) :
    Approx r.final (execute p (cs.map Tick.decode)) ∧
    List.Forall₂ Approx r.samples (endpoints p cs) ∧
    List.Forall (fun s => Domain s.state.decode) r.samples := by
  induction cs generalizing q r p with
  | nil =>
    simp only [run, Option.some.injEq] at h
    subst r
    exact ⟨hp, .nil, trivial⟩
  | cons c cs ih =>
    simp only [run] at h
    cases hs : checkedStep c q with
    | none => simp [hs] at h
    | some s =>
      cases hr : run cs s with
      | none => simp [hs, hr] at h
      | some t =>
        simp [hs, hr] at h
        subst r
        obtain ⟨hp', hd⟩ := checkedStep_correct hs hp
        obtain ⟨hf, ht, hv⟩ := ih hr hp'
        exact ⟨hf, .cons hp' ht, (List.forall_cons _ _ _).mpr ⟨hd, hv⟩⟩

theorem run_append (cs ds : List Tick) (q : Packet) :
    run (cs++ds) q = (do
      let a ← run cs q
      let b ← run ds a.final
      pure ⟨b.final, a.samples++b.samples, a.elapsed+b.elapsed⟩) := by
  induction cs generalizing q with
  | nil =>
    simp only [List.nil_append, run]
    cases h : run ds q <;> simp [h]
  | cons c cs ih =>
    simp only [List.cons_append, run, ih]
    cases checkedStep c q <;> simp
    rename_i s
    cases run cs s <;> simp
    rename_i r
    cases run ds r.final <;> simp [add_assoc]

/-- The budget is updated even when a subsequent control changes direction. -/
def errorAfter : List Tick → ℚ → ℚ
  | [], e => e
  | c::cs, e => errorAfter cs (budget c.duration e)

theorem run_error {cs : List Tick} {q : Packet} {r : Result} (h : run cs q = some r) :
    r.final.error = errorAfter cs q.error := by
  induction cs generalizing q r with
  | nil => simpa [run, errorAfter] using congrArg (fun x => x.final.error) (Option.some.inj h).symm
  | cons c cs ih =>
    unfold run at h
    unfold checkedStep at h
    split at h
    · cases hr : run cs (advance c q) with
      | none => simp [hr] at h
      | some t =>
        simp [hr] at h
        subst r
        exact ih hr
    · simp at h

theorem run_clock {cs : List Tick} {q : Packet} {r : Result} (h : run cs q = some r) :
    r.elapsed = clock cs := by
  induction cs generalizing q r with
  | nil =>
    simp only [run, Option.some.injEq] at h
    subst r
    rfl
  | cons c cs ih =>
    unfold run at h
    cases hs : checkedStep c q with
    | none => simp [hs] at h
    | some s =>
      cases hr : run cs s with
      | none => simp [hs, hr] at h
      | some t =>
        simp [hs, hr] at h
        subst r
        change c.duration+t.elapsed = _
        rw [ih hr]
        simp [clock]

/-- Pair each local clock and control with its actual starting and ending
packets. The preceding numerical endpoint supplies the next starting packet. -/
def observations : List Tick → Packet → List Packet → List (Input × ℚ × Packet × Packet)
  | c::cs, q, r::rs => (c.control,c.duration,q,r)::observations cs r rs
  | _, _, _ => []

theorem trajectory_add (c : Control) (p : Pose) (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    c.trajectory p (a+t) = c.trajectory (c.trajectory p a) t := by
  apply c.unique (c.trajectory p a) t ht (fun s => c.trajectory p (a+s)) (by simp)
    (fun s _ => ?_) (fun s _ w => ?_) ⟨ht, le_rfl⟩
  · have hd : HasDerivAt (fun r : ℝ => a+r) 1 s := by
      simpa using (hasDerivAt_id s).const_add a
    simpa using! (c.position_equation p (a+s)).scomp s hd
  · have hd : HasDerivAt (fun r : ℝ => a+r) 1 s := by
      simpa using (hasDerivAt_id s).const_add a
    simpa using! (c.frame_equation p (a+s) w).scomp s hd

/-- Subdividing a constant control retains its original trajectory and clock. -/
theorem execute_replicate (c : Tick) (n : ℕ) (p : Pose) :
    execute p ((List.replicate n c).map Tick.decode) =
      c.control.decode.trajectory p (n*(c.duration : ℝ)) := by
  induction n generalizing p with
  | zero => simp [execute]
  | succ n ih =>
    simp only [List.replicate_succ, List.map_cons, execute, ih]
    change c.control.decode.trajectory (c.control.decode.trajectory p c.duration)
      (n*(c.duration : ℝ)) = _
    rw [← trajectory_add _ _ _ (mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast c.nonneg))]
    congr 1
    push_cast
    ring

theorem run_interval_correct (c : Tick) (n : ℕ) {q : Packet} {r : Result} {p : Pose}
    (h : run (List.replicate n c) q = some r) (hp : Approx q p) :
    Approx r.final (c.control.decode.trajectory p (n*(c.duration : ℝ))) := by
  simpa only [execute_replicate] using (run_correct h hp).1

end Orbifold.DiskTransport.Numerical
