import Applications.Orbifold.Driver.Interval

namespace Orbifold.DiskTransport.Numerical.Driver

abbrev Label := Fin 4

noncomputable def Label.decode (k : Label) : Orbifold.QuarterTurn.C4 :=
  Orbifolds.QuarterTurn.quarterTurn^k.val

theorem rotate_action (k : Label) (q : Packet) : q.rotate k.val = k.decode • q := by
  cases q with
  | mk s e =>
    change Packet.mk (s.rotate k.val) e = Packet.mk (k.decode • s) e
    congr 1
    apply State.decode_injective
    rw [rotate_decode,smul_decode]
    simp [Label.decode]

theorem rotate_approx (k : Label) (q : Packet) (p : Pose) :
    Approx (q.rotate k.val) (k.decode • p) ↔ Approx q p := by
  rw [rotate_action]
  exact approx_equivariant k.decode q p

inductive Event where
  | command (c : Tick)
  | relabel (k : Label)
  deriving Repr

noncomputable def Event.finish : Event → Pose → Pose
  | .command c, p => c.decode.finish p
  | .relabel k, p => k.decode • p

def Event.duration : Event → ℚ
  | .command c => c.duration
  | .relabel _ => 0

noncomputable def executeEvents : List Event → Pose → Pose
  | [], p => p
  | e::es, p => executeEvents es (e.finish p)

def eventClock (es : List Event) : ℚ := (es.map Event.duration).sum

inductive Observation where
  | command (c : Tick) (predecessor : Nat) (incoming : Packet) (execution : Result)
  | relabel (k : Label) (incoming : Packet)
  deriving Repr

def Observation.event : Observation → Event
  | .command c _ _ _ => .command c
  | .relabel k _ => .relabel k

def Observation.incoming : Observation → Packet
  | .command _ _ q _ => q
  | .relabel _ q => q

def Observation.outgoing : Observation → Packet
  | .command _ _ _ r => r.final
  | .relabel k q => q.rotate k.val

def Observation.elapsed : Observation → ℚ
  | .command _ _ _ r => r.elapsed
  | .relabel _ _ => 0

/-- Retains a selected numerical execution, not merely the existence of an endpoint. -/
def Observation.Valid : Observation → Prop
  | .command c n q r => Numerical.run (schedule c n) q = some r
  | .relabel _ _ => True

theorem observation_correct (o : Observation) (ho : o.Valid) {p : Pose}
    (hp : Approx o.incoming p) : Approx o.outgoing (o.event.finish p) := by
  cases o with
  | command c n q r => simpa [Observation.outgoing,Observation.event,Event.finish,schedule_execute]
      using (Numerical.run_correct ho hp).1
  | relabel k q => exact (rotate_approx k q p).mpr hp

theorem observation_clock (o : Observation) (ho : o.Valid) : o.elapsed = o.event.duration := by
  cases o with
  | command c n q r => exact (Numerical.run_clock ho).trans (schedule_clock c n)
  | relabel k q => rfl

/-- Replay of the unchanged physical suffix commutes with the retained finite label. -/
theorem replay_after_event (k : Label) (cs : List Tick) (q : Packet) :
    Numerical.run cs (q.rotate k.val) = k.decode • Numerical.run cs q := by
  rw [rotate_action]
  exact run_equivariant cs k.decode q

theorem event_error (k : Label) (q : Packet) : (q.rotate k.val).error = q.error := rfl

end Orbifold.DiskTransport.Numerical.Driver
