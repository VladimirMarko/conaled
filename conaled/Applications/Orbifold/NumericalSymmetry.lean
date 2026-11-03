import Applications.Orbifold.NumericalExecution
import Mathlib.Algebra.Group.Action.Option

/-! Quarter-turn changes act on numerical position and frame together.
Controls, durations, budgets, and rejection behavior are unchanged. -/
namespace Orbifold.DiskTransport.Numerical
open MulAction CategoryTheory

def State.turn (q : State) : State := ⟨q.position.turn, q.frame.turn⟩
def Packet.turn (q : Packet) : Packet := ⟨q.state.turn, q.error⟩

theorem State.decode_injective : Function.Injective State.decode := by
  intro q r h
  have hz := QComplex.decode_injective (congrArg Prod.fst h)
  have hh := QComplex.decode_injective (congrArg Prod.snd h)
  cases q; cases r; simp_all

theorem step_turn (c : Input) (d : ℚ) (q : State) :
    step c d q.turn = (step c d q).turn := by
  cases q with
  | mk z h =>
    dsimp only [step, State.turn, field]
    congr 1 <;> apply Prod.ext <;>
      simp [QComplex.turn, QComplex.add, QComplex.mul,
        QComplex.scale, QComplex.conj, QComplex.normSq] <;> ring_nf <;> simp

@[simp] theorem normSq_turn (z : QComplex) : z.turn.normSq = z.normSq := by
  simp [QComplex.turn, QComplex.normSq, add_comm]
@[simp] theorem size_turn (z : QComplex) : z.turn.size = z.size := by
  simp [QComplex.turn, QComplex.size, add_comm]

theorem advance_turn (c : Tick) (q : Packet) : advance c q.turn = (advance c q).turn := by
  simp [advance, Packet.turn, step_turn]

theorem admissible_turn (c : Tick) (q : Packet) : Admissible c q.turn ↔ Admissible c q := by
  unfold Admissible
  rw [advance_turn]
  simp [Packet.turn, State.turn]

theorem checkedStep_turn (c : Tick) (q : Packet) :
    checkedStep c q.turn = (checkedStep c q).map Packet.turn := by
  simp only [checkedStep, admissible_turn, advance_turn]
  split <;> rfl

def State.rotate (k : ℕ) (q : State) : State := (State.turn^[k]) q
def Packet.rotate (k : ℕ) (q : Packet) : Packet := ⟨q.state.rotate k, q.error⟩

theorem rotate_decode (k : ℕ) (q : State) :
    (q.rotate k).decode = (Complex.I^k*q.position.decode, Complex.I^k*q.frame.decode) := by
  induction k generalizing q with
  | zero => simp [State.rotate, State.decode]
  | succ k ih =>
    simp only [State.rotate, Function.iterate_succ_apply']
    change (State.turn (q.rotate k)).decode = _
    simp only [State.turn, State.decode, QComplex.decode_turn]
    have hz := congrArg Prod.fst (ih q)
    have hh := congrArg Prod.snd (ih q)
    dsimp [State.decode] at hz hh
    rw [hz, hh, pow_succ]
    congr 1 <;> ring

noncomputable def State.act (g : QuarterTurn.C4) (q : State) : State :=
  q.rotate (Orbifolds.QuarterTurn.scalar_eq_pow g).choose

theorem act_decode (g : QuarterTurn.C4) (q : State) :
    (q.act g).decode = ((g.val : ℂ)*q.position.decode, (g.val : ℂ)*q.frame.decode) := by
  rw [State.act, rotate_decode, (Orbifolds.QuarterTurn.scalar_eq_pow g).choose_spec.2]

noncomputable instance : MulAction QuarterTurn.C4 State where
  smul := State.act
  one_smul q := by
    apply State.decode_injective
    change (State.act 1 q).decode = _
    rw [act_decode]
    simp [State.decode]
  mul_smul g h q := by
    apply State.decode_injective
    change (State.act (g*h) q).decode = (State.act g (State.act h q)).decode
    rw [act_decode, act_decode]
    have hz := congrArg Prod.fst (act_decode h q)
    have hh := congrArg Prod.snd (act_decode h q)
    dsimp [State.decode] at hz hh
    rw [hz, hh]
    simp [mul_assoc]

theorem smul_decode (g : QuarterTurn.C4) (q : State) :
    (g • q).decode = ((g.val : ℂ)*q.position.decode, (g.val : ℂ)*q.frame.decode) :=
  act_decode g q

theorem quarterTurn_state (q : State) : Orbifolds.QuarterTurn.quarterTurn • q = q.turn := by
  apply State.decode_injective
  rw [smul_decode]
  simp [State.turn, State.decode]

noncomputable instance : MulAction QuarterTurn.C4 Packet where
  smul g q := ⟨g • q.state, q.error⟩
  one_smul q := by
    change Packet.mk (1 • q.state) q.error = q
    rw [one_smul]
  mul_smul g h q := by
    change Packet.mk ((g*h) • q.state) q.error = Packet.mk (g • h • q.state) q.error
    rw [mul_smul]

theorem checkedStep_rotate (c : Tick) (k : ℕ) (q : Packet) :
    checkedStep c (q.rotate k) = (checkedStep c q).map (Packet.rotate k) := by
  induction k generalizing q with
  | zero =>
    have he : Packet.rotate 0 = id := by funext q; cases q; rfl
    rw [he]
    simp
  | succ k ih =>
    have he (q : Packet) : q.rotate (k+1) = (q.rotate k).turn := by
      simp [Packet.rotate, State.rotate, Packet.turn, Function.iterate_succ_apply']
    simp only [he, checkedStep_turn, ih, Option.map_map]
    congr 1
    funext q
    exact (he q).symm

theorem checkedStep_equivariant (c : Tick) (g : QuarterTurn.C4) (q : Packet) :
    checkedStep c (g • q) = (checkedStep c q).map (g • ·) :=
  checkedStep_rotate c (Orbifolds.QuarterTurn.scalar_eq_pow g).choose q

theorem approx_equivariant (g : QuarterTurn.C4) (q : Packet) (p : Pose) :
    Approx (g • q) (g • p) ↔ Approx q p := by
  change ‖(g • q.state).decode-coordinates (g • p)‖ ≤ (q.error : ℝ) ↔ _
  rw [smul_decode]
  have hz : (g • p).a = (g.val : ℂ)*p.a := rfl
  have hn : ‖(g.val : ℂ)‖ = 1 := Complex.norm_eq_one_of_mem_rootsOfUnity g.property
  simp [coordinates, hz, representative_frame, Prod.norm_def,
    ← mul_sub, hn, one_mul, Approx, State.decode]

/-- A successful representative change retains the original action label and
endpoint evidence; the action is not inserted into the timed control word. -/
theorem success_arrow (c : Tick) {q r s t : Packet} (g : QuarterTurn.C4)
    (hqr : g • q = r) (hqs : checkedStep c q = some s)
    (hrt : checkedStep c r = some t) : g • s = t := by
  rw [← hqr, checkedStep_equivariant, hqs] at hrt
  exact Option.some.inj hrt

noncomputable instance : MulAction QuarterTurn.C4 Result where
  smul g r := ⟨g • r.final, r.samples.map (g • ·), r.elapsed⟩
  one_smul r := by
    change Result.mk (1 • r.final) (r.samples.map (1 • ·)) r.elapsed = r
    simp only [one_smul]
    change Result.mk r.final (r.samples.map id) r.elapsed = r
    rw [List.map_id]
  mul_smul g h r := by
    change Result.mk ((g*h) • r.final) (r.samples.map ((g*h) • ·)) r.elapsed =
      Result.mk (g • h • r.final) ((r.samples.map (h • ·)).map (g • ·)) r.elapsed
    simp [mul_smul, List.map_map, Function.comp_def]

theorem run_equivariant (cs : List Tick) (g : QuarterTurn.C4) (q : Packet) :
    run cs (g • q) = g • run cs q := by
  induction cs generalizing q with
  | nil => rfl
  | cons c cs ih =>
    simp only [run, checkedStep_equivariant]
    cases hs : checkedStep c q with
    | none => rfl
    | some s =>
      simp only [Option.map_some]
      change ((run cs (g • s)).bind fun r => some (Result.mk r.final ((g • s)::r.samples)
        (c.duration+r.elapsed))) = g • ((run cs s).bind fun r =>
          some (Result.mk r.final (s::r.samples) (c.duration+r.elapsed)))
      rw [ih]
      cases hr : run cs s <;> rfl

/-- The partial execution functor includes rejection and preserves C4 labels. -/
noncomputable def executionFunctor (cs : List Tick) :
    ActionCategory QuarterTurn.C4 Packet ⥤ ActionCategory QuarterTurn.C4 (Option Result) :=
  Orbifolds.actionFunctor (MonoidHom.id _) (run cs) (run_equivariant cs)

theorem execution_label (cs : List Tick)
    {p q : ActionCategory QuarterTurn.C4 Packet} (f : p ⟶ q) :
    ((executionFunctor cs).map f).hom = f.hom := rfl

theorem execution_arrow_evidence (cs : List Tick)
    {p q : ActionCategory QuarterTurn.C4 Packet} (f : p ⟶ q) :
    @SMul.smul QuarterTurn.C4 (Option Result) inferInstance f.hom (run cs p.back) = run cs q.back :=
  ((executionFunctor cs).map f).map_val

end Orbifold.DiskTransport.Numerical
