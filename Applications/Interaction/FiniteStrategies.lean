import Applications.Interaction.FiniteQueries

/-! Finite serial forwarding strategies, with explicit interaction and hiding.
This is a restricted protocol model, not the full AJM category of games. -/
namespace Interaction.FiniteStrategies
open FiniteQueries

/-- A finite path in a partial deterministic transition system. -/
inductive Path (step : S → M → Option S) : S → List M → S → Prop where
  | nil : Path step s [] s
  | cons : step s m = some t → Path step t ms u → Path step s (m :: ms) u

namespace Path
theorem append (h : Path step s xs t) (k : Path step t ys u) :
    Path step s (xs ++ ys) u := by
  induction h with
  | nil => exact k
  | cons hs _ ih => exact .cons hs (ih k)

theorem deterministic (h : Path step s xs t) (k : Path step s xs u) : t = u := by
  induction h generalizing u with
  | nil => cases k; rfl
  | cons hs ht ih =>
    cases k with
    | cons ks kt =>
      have e := Option.some.inj (hs.symm.trans ks)
      cases e
      exact ih kt

theorem take_prefix (h : Path step s (xs ++ ys) u) : ∃ t, Path step s xs t := by
  induction xs generalizing s with
  | nil => exact ⟨s, .nil⟩
  | cons x xs ih =>
    cases h with
    | cons hs ht =>
      obtain ⟨t, hp⟩ := ih ht
      exact ⟨t, .cons hs hp⟩

/-- A local step simulation, allowing hidden moves, lifts to every finite play. -/
theorem project (mapState : S → T) (move : M → List N)
    (localLaw : ∀ s m t, step s m = some t → Path target (mapState s) (move m) (mapState t))
    (h : Path step s xs t) :
    Path target (mapState s) (xs.flatMap move) (mapState t) := by
  induction h with
  | nil => exact .nil
  | cons hs ht ih => exact (localLaw _ _ _ hs).append ih
end Path

inductive RelayMove where
  | leftAsk | rightAsk | rightReply (b : Bool) | leftReply (b : Bool)
  deriving DecidableEq, Repr
inductive Phase where
  | idle | requested | waiting | answered (b : Bool)
  deriving DecidableEq, Repr

/-- The forwarding policy maps a service reply to a client reply. -/
def relayStep (f : Bool → Bool) : Phase → RelayMove → Option Phase
  | .idle, .leftAsk => some .requested
  | .requested, .rightAsk => some .waiting
  | .waiting, .rightReply b => some (.answered (f b))
  | .answered b, .leftReply c => if b = c then some .idle else none
  | _, _ => none

/-- All finite legal positions, including administrative and unanswered prefixes. -/
def RelayPlay (f : Bool → Bool) (xs : List RelayMove) : Prop :=
  ∃ p, Path (relayStep f) .idle xs p

theorem relay_nonempty (f : Bool → Bool) : RelayPlay f [] := ⟨.idle, .nil⟩
theorem relay_prefix (h : RelayPlay f (xs ++ ys)) : RelayPlay f xs := by
  obtain ⟨_, hp⟩ := h
  exact hp.take_prefix

def relayRound (f : Bool → Bool) (b : Bool) : List RelayMove :=
  [.leftAsk, .rightAsk, .rightReply b, .leftReply (f b)]

theorem relay_round (f : Bool → Bool) (b : Bool) :
    Path (relayStep f) .idle (relayRound f b) .idle := by
  exact .cons rfl (.cons rfl (.cons rfl (.cons (by simp [relayStep]) .nil)))

/-- Three channel names; B is the matched internal interface. -/
inductive WireMove where
  | aAsk | bAsk | cAsk | cReply (b : Bool) | bReply (b : Bool) | aReply (b : Bool)
  deriving DecidableEq, Repr
inductive Stage where
  | idle | aAsked | bAsked | waiting | cAnswered (b : Bool) | bAnswered (b : Bool)
  deriving DecidableEq, Repr

/-- Sequential interaction: the same B event is received by both components. -/
def wireStep (f g : Bool → Bool) : Stage → WireMove → Option Stage
  | .idle, .aAsk => some .aAsked
  | .aAsked, .bAsk => some .bAsked
  | .bAsked, .cAsk => some .waiting
  | .waiting, .cReply b => some (.cAnswered b)
  | .cAnswered b, .bReply c => if c = g b then some (.bAnswered b) else none
  | .bAnswered b, .aReply c => if c = f (g b) then some .idle else none
  | _, _ => none

def leftState (f g : Bool → Bool) : Stage → Phase
  | .idle => .idle | .aAsked => .requested
  | .bAsked | .waiting | .cAnswered _ => .waiting
  | .bAnswered b => .answered (f (g b))
def rightState (g : Bool → Bool) : Stage → Phase
  | .idle | .aAsked | .bAnswered _ => .idle
  | .bAsked => .requested | .waiting => .waiting
  | .cAnswered b => .answered (g b)
def outerState (f g : Bool → Bool) : Stage → Phase
  | .idle => .idle | .aAsked | .bAsked => .requested
  | .waiting => .waiting
  | .cAnswered b | .bAnswered b => .answered (f (g b))

def leftMoves : WireMove → List RelayMove
  | .aAsk => [.leftAsk] | .bAsk => [.rightAsk]
  | .bReply b => [.rightReply b] | .aReply b => [.leftReply b]
  | _ => []
def rightMoves : WireMove → List RelayMove
  | .bAsk => [.leftAsk] | .cAsk => [.rightAsk]
  | .cReply b => [.rightReply b] | .bReply b => [.leftReply b]
  | _ => []
def hideMiddle : WireMove → List RelayMove
  | .aAsk => [.leftAsk] | .cAsk => [.rightAsk]
  | .cReply b => [.rightReply b] | .aReply b => [.leftReply b]
  | _ => []

theorem left_local (h : wireStep f g s m = some t) :
    Path (relayStep f) (leftState f g s) (leftMoves m) (leftState f g t) := by
  cases s <;> cases m <;> cases t <;> simp_all [wireStep, leftState, leftMoves]
  all_goals first | exact .nil | exact .cons (by simp [relayStep]) .nil

theorem right_local (h : wireStep f g s m = some t) :
    Path (relayStep g) (rightState g s) (rightMoves m) (rightState g t) := by
  cases s <;> cases m <;> cases t <;> simp_all [wireStep, rightState, rightMoves]
  all_goals first | exact .nil | exact .cons (by simp [relayStep]) .nil

theorem hide_local (h : wireStep f g s m = some t) :
    Path (relayStep (f ∘ g)) (outerState f g s) (hideMiddle m) (outerState f g t) := by
  cases s <;> cases m <;> cases t <;> simp_all [wireStep, outerState, hideMiddle]
  all_goals first | exact .nil | exact .cons (by simp [relayStep]) .nil

/-- Both projected component plays synchronize on the very same B moves. -/
theorem components (h : Path (wireStep f g) .idle xs t) :
    RelayPlay f (xs.flatMap leftMoves) ∧ RelayPlay g (xs.flatMap rightMoves) :=
  ⟨⟨_, h.project (leftState f g) leftMoves (fun _ _ _ => left_local)⟩,
   ⟨_, h.project (rightState g) rightMoves (fun _ _ _ => right_local)⟩⟩

theorem hide_legal (h : Path (wireStep f g) .idle xs t) :
    RelayPlay (f ∘ g) (xs.flatMap hideMiddle) :=
  ⟨_, h.project (outerState f g) hideMiddle (fun _ _ _ => hide_local)⟩

def wireRound (f g : Bool → Bool) (b : Bool) : List WireMove :=
  [.aAsk, .bAsk, .cAsk, .cReply b, .bReply (g b), .aReply (f (g b))]

theorem wire_round (f g : Bool → Bool) (b : Bool) :
    Path (wireStep f g) .idle (wireRound f g b) .idle := by
  exact .cons rfl (.cons rfl (.cons rfl (.cons rfl
    (.cons (t := .bAnswered b) (by simp [wireStep]) (.cons (by simp [wireStep]) .nil)))))

@[simp] theorem hide_round (f g : Bool → Bool) (b : Bool) :
    (wireRound f g b).flatMap hideMiddle = relayRound (f ∘ g) b := rfl

/-- Player's next move is unique; Opponent's reply is not predetermined. -/
theorem player_deterministic (hp : p = .requested ∨ ∃ b, p = .answered b)
    (h : relayStep f p m = some t) (h' : relayStep f p m' = some t') : m = m' := by
  cases p <;> cases m <;> cases m' <;> cases t <;> cases t' <;>
    simp_all [relayStep]

/-- A chosen internal state realizing each external phase. -/
inductive Align (f g : Bool → Bool) : Phase → Stage → Prop where
  | idle : Align f g .idle .idle
  | requested : Align f g .requested .bAsked
  | waiting : Align f g .waiting .waiting
  | answered (b : Bool) : Align f g (.answered (f (g b))) (.bAnswered b)

def insertMiddle (g : Bool → Bool) : RelayMove → List WireMove
  | .leftAsk => [.aAsk, .bAsk]
  | .rightAsk => [.cAsk]
  | .rightReply b => [.cReply b, .bReply (g b)]
  | .leftReply b => [.aReply b]

theorem lift_local (a : Align f g p s) (h : relayStep (f ∘ g) p m = some q) :
    ∃ t, Path (wireStep f g) s (insertMiddle g m) t ∧ Align f g q t := by
  cases a <;> cases m <;> cases q <;> simp_all [relayStep]
  all_goals subst_vars
  · exact ⟨_, .cons rfl (.cons rfl .nil), .requested⟩
  · exact ⟨_, .cons rfl .nil, .waiting⟩
  · rename_i b
    exact ⟨.bAnswered b, .cons rfl (.cons (by simp [wireStep]) .nil), .answered b⟩
  · exact ⟨_, .cons (by simp [wireStep]) .nil, .idle⟩

theorem lift_path (h : Path (relayStep (f ∘ g)) p xs q) (a : Align f g p s) :
    ∃ t, Path (wireStep f g) s (xs.flatMap (insertMiddle g)) t ∧ Align f g q t := by
  induction h generalizing s with
  | nil => exact ⟨_, .nil, a⟩
  | cons hs ht ih =>
    obtain ⟨v, hv, av⟩ := lift_local a hs
    obtain ⟨t, htail, afinal⟩ := ih av
    exact ⟨t, hv.append htail, afinal⟩

theorem hide_insert (g : Bool → Bool) (xs : List RelayMove) :
    (xs.flatMap (insertMiddle g)).flatMap hideMiddle = xs := by
  induction xs with
  | nil => rfl
  | cons m xs ih => cases m <;> simp [insertMiddle, hideMiddle, ih]

/-- Composition is interaction followed by hiding, not composition of native evaluators. -/
def CompositePlay (f g : Bool → Bool) (xs : List RelayMove) : Prop :=
  ∃ wire t, Path (wireStep f g) .idle wire t ∧ wire.flatMap hideMiddle = xs

/-- Exact equality of all finite external positions, not just the frozen examples. -/
theorem compose_exact : CompositePlay f g xs ↔ RelayPlay (f ∘ g) xs := by
  constructor
  · rintro ⟨wire, t, h, rfl⟩
    exact hide_legal h
  · rintro ⟨q, h⟩
    obtain ⟨t, ht, _⟩ := lift_path h .idle
    exact ⟨_, t, ht, hide_insert g xs⟩

theorem identity_left : CompositePlay id f xs ↔ RelayPlay f xs := compose_exact
theorem identity_right : CompositePlay f id xs ↔ RelayPlay f xs := compose_exact

theorem policy_associative : RelayPlay ((f ∘ g) ∘ h) xs ↔ RelayPlay (f ∘ (g ∘ h)) xs := Iff.rfl

/-- Associativity at the hidden finite-play boundary of this policy family. -/
theorem composite_associative :
    CompositePlay (f ∘ g) h xs ↔ CompositePlay f (g ∘ h) xs :=
  compose_exact.trans (policy_associative.trans compose_exact.symm)

/-- Role labels are relative to the forwarding component. -/
def playerMove : RelayMove → Bool
  | .leftAsk | .rightReply _ => false
  | .rightAsk | .leftReply _ => true

def playerTurn : Phase → Bool
  | .idle | .waiting => false
  | .requested | .answered _ => true

theorem roles_alternate (h : relayStep f p m = some q) :
    playerMove m = playerTurn p ∧ playerTurn q = !playerTurn p := by
  cases p <;> cases m <;> cases q <;>
    simp_all [relayStep, playerMove, playerTurn]

/-- Executing a path is useful for rejecting malformed concrete plays. -/
def execute (step : S → M → Option S) : S → List M → Option S
  | s, [] => some s
  | s, m :: ms => (step s m).bind (fun t => execute step t ms)

theorem Path.execute_eq (h : Path step s xs t) : execute step s xs = some t := by
  induction h with
  | nil => rfl
  | cons hs ht ih => simp [execute, hs, ih]

theorem rejected_not_play (h : execute (relayStep f) .idle xs = none) : ¬ RelayPlay f xs := by
  rintro ⟨t, ht⟩
  have bad := h.symm.trans ht.execute_eq
  contradiction

end Interaction.FiniteStrategies
