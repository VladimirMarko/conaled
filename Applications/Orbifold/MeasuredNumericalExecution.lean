import Applications.Orbifold.NumericalExecution
import Applications.Resources.AttemptCounts

/-! Checked numerical execution retains attempted work even when the whole run fails. -/
namespace Orbifold.DiskTransport.Numerical.Measured
open Resources

/-- Retain the actual accepted endpoint and command duration only on whole-run success. -/
def prepend (c : Tick) (q : Packet) (r : Result) : Result :=
  ⟨r.final,q::r.samples,c.duration+r.elapsed⟩

/-- Rejected checked steps stop recursion; their attempt and prior work remain observable. -/
def run : List Tick → Packet → Resources.Measured (Option Result) AttemptCounts
  | [], q => (some ⟨q,[],0⟩,0)
  | c::cs, q =>
    match checkedStep c q with
    | none => (none,rejectedAttempt)
    | some r =>
      let rest := run cs r
      (rest.1.map (prepend c r),acceptedAttempt+rest.2)

theorem run_erases (cs : List Tick) (q : Packet) : (run cs q).1 = Numerical.run cs q := by
  induction cs generalizing q with
  | nil => rfl
  | cons c cs ih =>
    cases hs : checkedStep c q with
    | none => simp [run, Numerical.run, hs]
    | some s =>
      cases hr : Numerical.run cs s <;> simp [run, Numerical.run, hs, ih, hr, prepend]

def erasureSquare (cs : List Tick) := Resources.erasureSquare (run cs) (Numerical.run cs) (run_erases cs)

def combine (a b : Result) : Result := ⟨b.final,a.samples++b.samples,a.elapsed+b.elapsed⟩

/-- Failure has no continuation; success retains the preceding samples and clock. -/
def continueWith (ds : List Tick) : Option Result → Resources.Measured (Option Result) AttemptCounts
  | none => (none,0)
  | some a => let b := run ds a.final; (b.1.map (combine a),b.2)

theorem run_append (cs ds : List Tick) (q : Packet) :
    run (cs++ds) q = Resources.bind (run cs q) (continueWith ds) := by
  induction cs generalizing q with
  | nil =>
    simp only [List.nil_append, run, Resources.bind, continueWith]
    cases h : run ds q with
    | mk out cost => cases out <;> simp [combine]
  | cons c cs ih =>
    simp only [List.cons_append, run]
    cases hs : checkedStep c q with
    | none => simp [Resources.bind, continueWith]
    | some s =>
      simp only []
      rw [ih]
      cases ha : run cs s with
      | mk a cost =>
        cases a with
        | none => simp [Resources.bind, continueWith]
        | some a =>
          cases hb : run ds a.final with
          | mk b price =>
            cases b <;> simp [Resources.bind, continueWith, hb, prepend, combine, add_assoc]

theorem reweight_append {C : Type} [AddMonoid C] (h : AttemptCounts →+ C)
    (cs ds : List Tick) (q : Packet) :
    reweight h (run (cs++ds) q) =
      Resources.bind (reweight h (run cs q)) (fun a => reweight h (continueWith ds a)) := by
  rw [run_append, reweight_bind]

theorem run_correct {cs : List Tick} {q : Packet} {r : Result} {p : Pose}
    (h : (run cs q).1 = some r) (hp : Approx q p) :
    Approx r.final (execute p (cs.map Tick.decode)) ∧
    List.Forall₂ Approx r.samples (endpoints p cs) ∧
    List.Forall (fun s => Domain s.state.decode) r.samples :=
  Numerical.run_correct ((run_erases cs q).symm.trans h) hp

theorem run_error {cs : List Tick} {q : Packet} {r : Result} (h : (run cs q).1 = some r) :
    r.final.error = errorAfter cs q.error := Numerical.run_error ((run_erases cs q).symm.trans h)

theorem run_clock {cs : List Tick} {q : Packet} {r : Result} (h : (run cs q).1 = some r) :
    r.elapsed = clock cs := Numerical.run_clock ((run_erases cs q).symm.trans h)

theorem run_counts (cs : List Tick) (q : Packet) :
    (run cs q).2.1 = (run cs q).2.2.1 + (run cs q).2.2.2 ∧
    (run cs q).2.2.2 ≤ 1 ∧ (run cs q).2.1 ≤ cs.length := by
  induction cs generalizing q with
  | nil => simp [run]
  | cons c cs ih =>
    simp only [run]
    cases h : checkedStep c q with
    | none => simp [rejectedAttempt]
    | some s =>
      have hi := ih s
      simp only [acceptedAttempt, Prod.fst_add, Prod.snd_add, List.length_cons]
      omega

theorem run_success_counts {cs : List Tick} {q : Packet} {r : Result}
    (h : (run cs q).1 = some r) : (run cs q).2 = (cs.length,(cs.length,0)) := by
  induction cs generalizing q r with
  | nil => rfl
  | cons c cs ih =>
    simp only [run] at h ⊢
    cases hs : checkedStep c q with
    | none => simp [hs] at h
    | some s =>
      simp only [hs] at h
      obtain ⟨a,ha,_⟩ := Option.map_eq_some_iff.mp h
      simp only []
      rw [ih ha]
      simp [acceptedAttempt, Nat.add_comm]

/-- Counts stop at the first failed invocation, independently of the unused suffix. -/
theorem run_first_failure (cs ds : List Tick) (q : Packet) (a : Result) (c : Tick)
    (hs : (run cs q).1 = some a) (hf : checkedStep c a.final = none) :
    run (cs++c::ds) q = (none,(cs.length+1,(cs.length,1))) := by
  rw [run_append]
  simp [Resources.bind, continueWith, hs, run, hf, run_success_counts hs, rejectedAttempt]

end Orbifold.DiskTransport.Numerical.Measured
