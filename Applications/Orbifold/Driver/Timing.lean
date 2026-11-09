import Applications.Orbifold.Driver.RequestReplay

namespace Orbifold.DiskTransport.Numerical.Driver

theorem run_samples_length {cs : List Tick} {q : Packet} {r : Result}
    (h : Numerical.run cs q = some r) : r.samples.length = cs.length := by
  induction cs generalizing q r with
  | nil =>
    simp only [Numerical.run,Option.some.injEq] at h
    subst r
    rfl
  | cons c cs ih =>
    cases hs : checkedStep c q with
    | none => simp [Numerical.run,hs] at h
    | some s =>
      cases hr : Numerical.run cs s with
      | none => simp [Numerical.run,hs,hr] at h
      | some t =>
        simp [Numerical.run,hs,hr] at h
        subst r
        simpa using congrArg Nat.succ (ih hr)

theorem selected_samples_length {c q tolerance} (s : Selected c q tolerance) :
    s.execution.samples.length = s.subdivisions :=
  (run_samples_length s.ran).trans (schedule_length _ _)

/-- The local timestamp assigned to each retained sample is inside its command.
The count is certified by `selected_samples_length`, not guessed by the serializer. -/
theorem sample_clock_bounds (c : Tick) (n i : Nat) (hi : i < n+1) :
    0 ≤ (i+1 : Nat) * (subTick c n).duration ∧
    (i+1 : Nat) * (subTick c n).duration ≤ c.duration := by
  have hn : (0 : ℚ) < (n+1 : Nat) := by positivity
  have hd := (subTick c n).nonneg
  constructor
  · positivity
  · have hm : (i+1 : ℚ) ≤ (n+1 : Nat) := by exact_mod_cast hi
    calc
      (i+1 : Nat) * (subTick c n).duration ≤ (n+1 : Nat) * (subTick c n).duration :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hd
      _ = c.duration := by simp [subTick]; field_simp

theorem last_sample_clock (c : Tick) (n : Nat) :
    (n+1 : Nat) * (subTick c n).duration = c.duration := by
  simp [subTick]
  field_simp

theorem endpoints_length (p : Pose) (cs : List Tick) :
    (endpoints p cs).length = cs.length := by
  induction cs generalizing p with
  | nil => rfl
  | cons c cs ih => simp [endpoints,ih]

/-- Each serialized local endpoint clock refers to the corresponding exact point
on the original constant-control trajectory, rather than just an ordered sample. -/
theorem endpoints_replicate_get (c : Tick) (n i : Nat) (p : Pose) (hi : i < n) :
    (endpoints p (List.replicate n c))[i]'(by simpa [endpoints_length] using hi) =
      c.control.decode.trajectory p ((i+1 : Nat)*(c.duration : ℝ)) := by
  induction n generalizing p i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [List.replicate_succ,endpoints,Tick.decode,Command.finish]
    | succ i =>
      have h : i < n := by omega
      simp only [List.replicate_succ,endpoints,List.getElem_cons_succ]
      rw [ih i (c.decode.finish p) h]
      change c.control.decode.trajectory (c.control.decode.trajectory p c.duration)
        ((i+1 : Nat)*(c.duration : ℝ)) = _
      rw [← trajectory_add _ _ _ (mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast c.nonneg))]
      congr 1
      push_cast
      ring

end Orbifold.DiskTransport.Numerical.Driver
