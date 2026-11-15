import Applications.Orbifold.MeasuredNumericalExecution
import Applications.Orbifold.NumericalSymmetry

namespace Orbifold.DiskTransport.Numerical.Driver

/-- n is the predecessor of the positive subdivision count. -/
def subTick (c : Tick) (n : ℕ) : Tick :=
  ⟨c.control,c.duration/(n+1),div_nonneg c.nonneg (by positivity)⟩

def schedule (c : Tick) (n : ℕ) : List Tick := List.replicate (n+1) (subTick c n)

theorem schedule_length (c : Tick) (n : ℕ) : (schedule c n).length = n+1 := by
  simp [schedule]

theorem schedule_control (c : Tick) (n : ℕ) {t : Tick} (ht : t ∈ schedule c n) :
    t.control = c.control := by
  have H := List.eq_of_mem_replicate ht
  subst t
  rfl

theorem schedule_clock (c : Tick) (n : ℕ) : clock (schedule c n) = c.duration := by
  simp [clock,schedule,subTick,List.sum_replicate,nsmul_eq_mul]
  field_simp

theorem schedule_execute (c : Tick) (n : ℕ) (p : Pose) :
    execute p ((schedule c n).map Tick.decode) = c.decode.finish p := by
  rw [schedule,execute_replicate]
  have H : ((n+1 : ℕ) : ℝ) * ((c.duration / (n+1) : ℚ) : ℝ) = c.duration := by
    push_cast
    field_simp
  change c.control.decode.trajectory p (((n+1 : ℕ) : ℝ)*((c.duration/(n+1) : ℚ) : ℝ)) = _
  rw [H]
  rfl

def initial : Packet := ⟨⟨(-1/4096,0),((1-(1/4096)^2)/2,0)⟩,0⟩

noncomputable def initialPose : Pose :=
  ⟨-1/4096,1,by norm_num [Complex.normSq_apply],by norm_num⟩

theorem initial_exact : initial.state.decode = coordinates initialPose := by
  apply Prod.ext <;> apply Complex.ext <;>
    norm_num [initial,initialPose,State.decode,QComplex.decode,coordinates,
      Pose.frame,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]

theorem initial_approx : Approx initial initialPose := by
  unfold Approx
  rw [initial_exact,sub_self,norm_zero]
  norm_num [initial]

end Orbifold.DiskTransport.Numerical.Driver
