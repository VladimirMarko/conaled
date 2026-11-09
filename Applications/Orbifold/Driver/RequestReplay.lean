import Applications.Orbifold.Driver.Replay

namespace Orbifold.DiskTransport.Numerical.Driver
open Orbifold.QuarterTurn

noncomputable def Observation.act (g : C4) : Observation → Observation
  | .command c n q r => .command c n (g • q) (g • r)
  | .relabel k q => .relabel k (g • q)

noncomputable def Report.act (g : C4) (r : Report) : Report :=
  { r with final := g • r.final, observations := r.observations.map (Observation.act g) }

theorem rotate_commutes (g : C4) (k : Label) (q : Packet) :
    (g • q).rotate k.val = g • q.rotate k.val := by
  rw [rotate_action,rotate_action,← mul_smul,← mul_smul,mul_comm]

theorem drive_action (g : C4) (limits : Limits) (tolerance : ℚ) (es : List Event)
    (q : Packet) (fuel index : Nat) :
    drive limits tolerance es (g • q) fuel index = (drive limits tolerance es q fuel index).act g := by
  induction es generalizing q fuel index with
  | nil => simp [drive,Report.act]
  | cons e es ih =>
    cases e with
    | relabel k =>
      simp only [drive]
      split
      · rfl
      · rw [rotate_commutes,ih]
        rfl
    | command c =>
      simp only [drive,searchInterval_action]
      split
      · rfl
      · cases ha : (searchInterval limits tolerance fuel c q).accepted with
        | none => simp [SearchReport.act,ha,Report.act,stopped]
        | some s =>
          simp only [SearchReport.act,ha,Option.map_some,Selected.act,result_action_final]
          rw [ih]
          rfl

/-- Insert this event at any saved incoming packet. The entire subsequent driver
search is replayed, including failures, subdivision choices and spent retry work. -/
theorem inserted_event_replay (k : Label) (limits : Limits) (tolerance : ℚ) (es : List Event)
    (q : Packet) (fuel index : Nat) :
    drive limits tolerance (.relabel k::es) q (fuel+1) index =
      { prepend (.relabel k q) ((drive limits tolerance es q fuel (index+1)).act k.decode) with
        charged := 1+(drive limits tolerance es q fuel (index+1)).charged } := by
  simp only [drive,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false,Nat.add_sub_cancel]
  rw [rotate_action,drive_action]
  rfl

end Orbifold.DiskTransport.Numerical.Driver
