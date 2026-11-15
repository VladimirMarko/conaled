import Applications.Probability.BinaryBlock
import Applications.Probability.Results
import Mathlib.Data.Nat.Log

/-!
# Uniform sampling below a positive bound

Read a positive-width binary block, accepting codes below the bound and retrying
otherwise. Each transition reads one bit, retaining the partial numeric prefix.
For bound one the value is always zero, but one-bit blocks can still be rejected.
Arithmetic within a transition is not a claim about host runtime or bit complexity.
-/
namespace Applications.Probability.BoundedUniform
open CoinPaths BinaryBlock

/-- The smallest covering bit width, except that zero-width blocks are excluded. -/
def width (n : ℕ) : ℕ := max 1 (Nat.clog 2 n)

theorem width_pos (n : ℕ) : 0 < width n := by unfold width; omega

theorem bound_le_capacity (n : ℕ) : n ≤ 2^width n := by
  exact (Nat.le_pow_clog (by decide) n).trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))

/-- No wider positive block is chosen when a smaller one already covers the bound. -/
theorem width_minimal (n k : ℕ) (hk : 0<k) (hn : n ≤ 2^k) : width n ≤ k := by
  exact max_le hk ((Nat.clog_le_iff_le_pow (by decide)).mpr hn)

/-- The block capacity is at most twice the positive bound, including bound one. -/
theorem capacity_le_double (n : ℕ) (hn : 0<n) : 2^width n ≤ 2*n := by
  by_cases h1 : n=1
  · subst n; norm_num [width]
  have hn' : 1<n := by omega
  have hc := Nat.clog_pos (by decide : 1<2) hn'
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1<2) hn'
  have he : (Nat.clog 2 n).pred+1=Nat.clog 2 n := Nat.succ_pred_eq_of_pos hc
  rw [width,max_eq_right hc,← he,pow_succ]
  omega

/-- Cursor, number of remaining bits, and already accumulated numeric prefix. -/
abbrev State := ℕ × ℕ × ℕ
abbrev Return (n : ℕ) := Fin n × ℕ

def start (n s : ℕ) : State := (s,width n,0)

/-- Inspect exactly one bit, then continue the block or accept/reject its code. -/
def step (n : ℕ) (ω : Tape) : Progress.Machine State (Return n) := fun (s,left,v) =>
  let u := 2*v + if ω s then 1 else 0
  if left ≤ 1 then
    if h : u<n then .inl (⟨u,h⟩,s+1) else .inr (start n (s+1))
  else .inr (s+1,left-1,u)

/-- Rejected blocks followed by the selected accepted code. -/
def Accept (n : ℕ) (ω : Tape) (s : ℕ) : ℕ → Fin n → Prop
  | 0,a => read ω s (width n)=a.val
  | r+1,a => n ≤ read ω s (width n) ∧ Accept n ω (s+width n) r a

private theorem evaluates_next_iff {S A : Type} {f : Progress.Machine S A}
    {s t : S} {a : A} {k : ℕ} (e : f s=.inr t) :
    Progress.Evaluates f s a k ↔ ∃ j, Progress.Evaluates f t a j ∧ k=j+1 := by
  constructor
  · intro h
    cases h with
    | done h => simp [e] at h
    | next h j => have he := Sum.inr.inj (e.symm.trans h); subst he; exact ⟨_,j,rfl⟩
  · rintro ⟨j,h,rfl⟩; exact .next e h

private theorem evaluates_done_iff {S A : Type} {f : Progress.Machine S A}
    {s : S} {a b : A} {k : ℕ} (e : f s=.inl a) :
    Progress.Evaluates f s b k ↔ b=a ∧ k=1 := by
  constructor
  · intro h; exact h.unique (.done e)
  · rintro ⟨rfl,rfl⟩; exact .done e

/-- Unroll the remaining part of a block. A rejection continues at the next
block boundary, while acceptance returns after precisely these bit inspections. -/
theorem evaluates_block_iff (n : ℕ) (ω : Tape) (s l v : ℕ) (a : Fin n) (t k : ℕ) :
    Progress.Evaluates (step n ω) (s,l+1,v) (a,t) k ↔
    let u := v*2^(l+1)+read ω s (l+1)
    (u=a.val ∧ t=s+(l+1) ∧ k=l+1) ∨
    (n ≤ u ∧ ∃ j, Progress.Evaluates (step n ω) (start n (s+(l+1))) (a,t) j ∧ k=l+1+j) := by
  induction l generalizing s v k with
  | zero =>
    simp only [Nat.zero_add,pow_one,read_succ,read_zero,pow_zero,Nat.add_zero]
    by_cases hu : 2*v+(if ω s then 1 else 0)<n
    · rw [evaluates_done_iff (show step n ω (s,0+1,v)=.inl (⟨_,hu⟩,s+1) by simp [step,hu])]
      simp only [Prod.mk.injEq,Fin.ext_iff]
      have ha := a.isLt
      constructor <;> intro h <;> simp_all [Nat.mul_comm]; omega
    · rw [evaluates_next_iff (show step n ω (s,0+1,v)=.inr (start n (s+1)) by simp [step,hu])]
      have ha := a.isLt
      have hne : v*2+(if ω s then 1 else 0) ≠ a.val := by omega
      have hge : n ≤ v*2+(if ω s then 1 else 0) := by omega
      simp only [hne,false_and,false_or,hge,true_and]
      constructor
      · rintro ⟨j,h,hk⟩; exact ⟨j,h,by omega⟩
      · rintro ⟨j,h,hk⟩; exact ⟨j,h,by omega⟩
  | succ l ih =>
    have e : step n ω (s,l+1+1,v)=.inr (s+1,l+1,2*v+(if ω s then 1 else 0)) := by
      simp [step]
    rw [evaluates_next_iff e]
    simp only [ih]
    have hu : v*2^(l+1+1)+read ω s (l+1+1) =
        (2*v+(if ω s then 1 else 0))*2^(l+1)+read ω (s+1) (l+1) := by
      rw [read_succ,pow_succ]
      cases ω s <;> simp <;> ring
    rw [hu]
    constructor
    · rintro ⟨j,(⟨hv,ht,hj⟩ | ⟨hn,i,hi,hj⟩),hk⟩
      · left; exact ⟨hv,by omega,by omega⟩
      · right; refine ⟨hn,i,?_,by omega⟩
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi
    · rintro (⟨hv,ht,hk⟩ | ⟨hn,i,hi,hk⟩)
      · exact ⟨l+1,Or.inl ⟨hv,by omega,rfl⟩,by omega⟩
      · refine ⟨l+1+i,Or.inr ⟨hn,i,?_,rfl⟩,by omega⟩
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi

/-- One complete block at a sampler boundary. -/
theorem evaluates_start_iff (n : ℕ) (ω : Tape) (s : ℕ) (a : Fin n) (t k : ℕ) :
    Progress.Evaluates (step n ω) (start n s) (a,t) k ↔
    (read ω s (width n)=a.val ∧ t=s+width n ∧ k=width n) ∨
    (n ≤ read ω s (width n) ∧ ∃ j,
      Progress.Evaluates (step n ω) (start n (s+width n)) (a,t) j ∧ k=width n+j) := by
  have hw : width n-1+1=width n := Nat.sub_add_cancel (width_pos n)
  simpa only [hw,Nat.zero_mul,Nat.zero_add,start] using
    evaluates_block_iff n ω s (width n-1) 0 a t k

/-- Every accepted sequence supplies a derivation of the executable machine. -/
theorem evaluates_of_accept {n : ℕ} {ω : Tape} {s r : ℕ} {a : Fin n}
    (h : Accept n ω s r a) :
    Progress.Evaluates (step n ω) (start n s) (a,s+width n*(r+1)) (width n*(r+1)) := by
  induction r generalizing s with
  | zero =>
    apply (evaluates_start_iff _ _ _ _ _ _).mpr
    exact Or.inl ⟨h,by omega,by omega⟩
  | succ r ih =>
    obtain ⟨hn,hr⟩ := h
    apply (evaluates_start_iff _ _ _ _ _ _).mpr
    right
    refine ⟨hn,width n*(r+1),?_,by ring⟩
    convert ih hr using 1; congr 1; ring

/-- Every finite machine return identifies its retry count, code and exact work. -/
theorem accept_of_evaluates {n : ℕ} {ω : Tape} {s : ℕ} {a : Fin n} {t k : ℕ}
    (h : Progress.Evaluates (step n ω) (start n s) (a,t) k) :
    ∃ r, Accept n ω s r a ∧ t=s+width n*(r+1) ∧ k=width n*(r+1) := by
  induction k using Nat.strong_induction_on generalizing s with
  | h k ih =>
    rcases (evaluates_start_iff _ _ _ _ _ _).mp h with ⟨ha,ht,hk⟩ | ⟨hn,j,hj,hk⟩
    · exact ⟨0,ha,by omega,by omega⟩
    · obtain ⟨r,hr,ht,hj'⟩ := ih j (by have := width_pos n; omega) hj
      refine ⟨r+1,⟨hn,hr⟩,?_,?_⟩ <;> simp_all only [Nat.mul_add,Nat.mul_one] <;> omega

theorem evaluates_iff (n : ℕ) (ω : Tape) (s r : ℕ) (a : Fin n) :
    Progress.Evaluates (step n ω) (start n s) (a,s+width n*(r+1)) (width n*(r+1)) ↔
      Accept n ω s r a := by
  constructor
  · intro h
    obtain ⟨j,hj,_,hk⟩ := accept_of_evaluates h
    have he : j=r := by have := width_pos n; nlinarith
    simpa [he] using hj
  · exact evaluates_of_accept

theorem measurableSteps (n : ℕ) : ProbabilityProgress.MeasurableSteps (step n) := by
  intro q r
  have he : {ω | step n ω q=r} =
      ({ω : Tape | ω q.1=false} ∩ {ω | step n (fun _ => false) q=r}) ∪
      ({ω : Tape | ω q.1=true} ∩ {ω | step n (fun _ => true) q=r}) := by
    ext ω
    cases hb : ω q.1 <;> simp [step,hb]
  rw [he]
  have hm : Measurable (fun ω : Tape => ω q.1) := measurable_pi_apply q.1
  exact ((hm (measurableSet_singleton false)).inter (MeasurableSet.const _)).union
    ((hm (measurableSet_singleton true)).inter (MeasurableSet.const _))

/-- The first `r` complete blocks were rejected. -/
def Reject (n : ℕ) (ω : Tape) (s : ℕ) : ℕ → Prop
  | 0 => True
  | r+1 => n ≤ read ω s (width n) ∧ Reject n ω (s+width n) r

theorem reject_iff_no_accept (n : ℕ) (ω : Tape) (s r : ℕ) :
    Reject n ω s r ↔ ∀ i, i<r → ∀ a, ¬ Accept n ω s i a := by
  induction r generalizing s with
  | zero => simp [Reject]
  | succ r ih =>
    constructor
    · rintro ⟨hn,hr⟩ i hi a ha
      cases i with
      | zero => have := a.isLt; simp only [Accept] at ha; omega
      | succ i => exact (ih _).mp hr i (by omega) a ha.2
    · intro h
      have hn : n ≤ read ω s (width n) := by
        by_contra hlt
        exact h 0 (by omega) ⟨read ω s (width n),Nat.lt_of_not_ge hlt⟩ rfl
      refine ⟨hn,(ih _).mpr ?_⟩
      intro i hi a ha
      exact h (i+1) (by omega) a ⟨hn,ha⟩

/-- Exact fuel exhaustion, including partial blocks: only complete inspected
blocks can accept. `none` remains finite-fuel exhaustion, not divergence. -/
theorem search_none_iff (n : ℕ) (ω : Tape) (s fuel : ℕ) :
    Progress.search (step n ω) fuel (start n s)=none ↔
      Reject n ω s (fuel / width n) := by
  rw [← ProbabilityProgress.timeout_iff_search_none (step n) ω (start n s) fuel,
    ProbabilityProgress.timeout,reject_iff_no_accept]
  constructor
  · intro h i hi a ha
    apply h
    refine ⟨(a,s+width n*(i+1)),width n*(i+1),?_,evaluates_of_accept ha⟩
    have := (Nat.le_div_iff_mul_le (width_pos n)).mp (show i+1 ≤ fuel/width n by omega)
    simpa [Nat.mul_comm] using this
  · intro h ⟨⟨a,t⟩,k,hk,he⟩
    obtain ⟨r,hr,_,hkr⟩ := accept_of_evaluates he
    apply h r _ a hr
    have := (Nat.le_div_iff_mul_le (width_pos n)).mpr
      (show (r+1)*width n ≤ fuel by nlinarith)
    omega

end Applications.Probability.BoundedUniform
