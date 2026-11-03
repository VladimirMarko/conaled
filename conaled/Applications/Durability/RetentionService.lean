import Applications.Durability.RetentionBanks

namespace Durability.Retention

/-- The kernel shares lifecycle rules, not storage or history observations.
The ghost instance below reads the full history directly. -/
structure Operations (α : Type) where
  position : α → Nat
  count : α → Nat
  pastParity : α → Bool
  item : α → Nat → Option Bool
  total : α → Bool
  read : α → Nat → Nat → Reply
  classify : α → Nat → Nat → Bool → Reply
  append : α → Bool → α

def ghostOps (c : Config) : Operations (List Bool) where
  position := List.length
  count h := min c.window h.length
  pastParity h := parity (h.take (h.length - c.window))
  item h i := h[h.length - c.window + i]?
  total := parity
  read := specRead c
  classify := specClassify c
  append h p := h ++ [p]

def snapshotOps (c : Config) : Operations Snapshot where
  position := Snapshot.position
  count s := s.items.length
  pastParity := Snapshot.pastParity
  item s i := s.items[i]?
  total := Snapshot.total
  read := read
  classify := classify c
  append := append c

def bankOps (c : Config) : Operations Banks where
  position d := d.root.position
  count d := d.root.items.length
  pastParity d := d.root.pastParity
  item d i := d.root.items[i]?
  total d := d.root.total
  read d := read d.root
  classify d := classify c d.root
  append d p := ((replacement (append c d.root p)).foldl primitive ⟨d, empty⟩).disk

structure Control where
  online : Bool := true
  pending : Option Bool := none
  committed : Bool := false
  pinned : Bool := false
  scanIndex : Nat := 0
  scanParity : Bool := false
  delayed : Option (Nat × Bool) := none
  recovering : Nat := 0
  output : List Bool := []
  deriving DecidableEq, Repr

structure Service (α : Type) where
  store : α
  control : Control := {}

inductive Command where
  | append (incarnation id : Nat) (payload : Bool)
  | publish | acknowledge | crash | recover
  | read (start stop : Nat) | summary | pin
  | release (currentConnection : Bool)
  | scan (currentConnection : Bool)
  | stream (currentConnection : Bool)
  | view (minimum : Nat)
  | consume
  deriving DecidableEq, Repr

def viewReply (c : Config) (ctl : Control) (minimum : Nat) : Reply :=
  match ctl.delayed with
  | none => .notReady
  | some (n, b) => if minimum ≤ n then .summary c.incarnation n b else .notReady

/-- Stuck readers or outstanding output impose backpressure. A published
pending request must be acknowledged or lost to a crash before another starts. -/
def command (c : Config) (ops : Operations α) (s : Service α) (cmd : Command) : Reply × Service α :=
  let ctl := s.control
  match cmd with
  | .crash => (.unavailable, { s with control := { online := false } })
  | .consume => (.released, { s with control := { ctl with output := [] } })
  | .release false | .scan false | .stream false => (.invalidHandle, s)
  | .recover =>
      if ctl.online then (.busy, s)
      else match ops.item s.store ctl.recovering with
        | some _ => (.unavailable, { s with control := { ctl with recovering := ctl.recovering + 1 } })
        | none => (.summary c.incarnation (ops.position s.store) (ops.total s.store),
            { s with control := {} })
  | _ =>
    if !ctl.online then (.unavailable, s)
    else match cmd with
    | .publish =>
      match ctl.pending with
      | none => (.busy, s)
      | some p =>
        if ctl.committed || !(ops.position s.store < c.limit) then (.busy, s)
        else (.reserved, ⟨ops.append s.store p, { ctl with committed := true }⟩)
    | .acknowledge =>
      if ctl.pending.isSome && ctl.committed then
        (.acknowledged c.incarnation (ops.position s.store - 1),
          { s with control := { ctl with pending := none, committed := false } })
      else (.busy, s)
    | .append e i p =>
      if ctl.pending.isSome || ctl.pinned || !ctl.output.isEmpty then (.busy, s)
      else let reply := ops.classify s.store e i p
           if reply = .reserved then
             (reply, { s with control := { ctl with pending := some p, committed := false } })
           else (reply, s)
    | .read a z =>
      if ctl.pending.isSome || ctl.pinned || !ctl.output.isEmpty then (.busy, s)
      else match ops.read s.store a z with
        | .records xs => (.records xs, { s with control := { ctl with output := xs } })
        | reply => (reply, s)
    | .summary =>
      if ctl.pending.isSome || !ctl.output.isEmpty then (.busy, s)
      else (.summary c.incarnation (ops.position s.store) (ops.total s.store), s)
    | .pin =>
      if ctl.pending.isSome || ctl.pinned || !ctl.output.isEmpty then (.busy, s)
      else (.pinned, { s with control := { ctl with pinned := true, scanIndex := 0, scanParity := ops.pastParity s.store } })
    | .release true =>
      if ctl.pinned then (.released, { s with control := { ctl with pinned := false, scanIndex := 0, scanParity := false } }) else (.invalidHandle, s)
    | .scan true =>
      if !ctl.pinned then (.invalidHandle, s)
      else match ops.item s.store ctl.scanIndex with
        | some p => (.pinned, { s with control := { ctl with scanIndex := ctl.scanIndex + 1, scanParity := xor ctl.scanParity p } })
        | none => (.summary c.incarnation (ops.position s.store) ctl.scanParity,
            { s with control := { ctl with pinned := false, scanIndex := 0, scanParity := false, delayed := some (ops.position s.store, ctl.scanParity) } })
    | .stream true =>
      if !ctl.pinned then (.invalidHandle, s)
      else if !ctl.output.isEmpty then (.busy, s)
      else match ops.item s.store ctl.scanIndex with
        | some p => (.records [p], { s with control := { ctl with scanIndex := ctl.scanIndex + 1, scanParity := xor ctl.scanParity p, output := [p] } })
        | none => (.released, { s with control := { ctl with pinned := false, scanIndex := 0, scanParity := false } })
    | .view minimum => (viewReply c ctl minimum, s)
    | _ => (.busy, s)

/-- Storage simulation obligations. These compare independently defined
operations; they do not assume service or trace refinement. -/
structure Simulates (c : Config) (source : Operations α) (target : Operations β)
    (R : β → α → Prop) : Prop where
  position : ∀ t a, R t a → target.position t = source.position a
  count : ∀ t a, R t a → target.count t = source.count a
  pastParity : ∀ t a, R t a → target.pastParity t = source.pastParity a
  item : ∀ t a, R t a → ∀ i, target.item t i = source.item a i
  total : ∀ t a, R t a → target.total t = source.total a
  read : ∀ t a, R t a → ∀ i j, target.read t i j = source.read a i j
  classify : ∀ t a, R t a → ∀ e i p, target.classify t e i p = source.classify a e i p
  append : ∀ t a, R t a → target.position t < c.limit → ∀ p,
    R (target.append t p) (source.append a p)

def RelatedService (R : β → α → Prop) (t : Service β) (a : Service α) : Prop :=
  R t.store a.store ∧ t.control = a.control

theorem command_refines {c : Config} {source : Operations α} {target : Operations β}
    {R : β → α → Prop} (sim : Simulates c source target R)
    {t : Service β} {a : Service α} (rel : RelatedService R t a) (cmd : Command) :
    (command c target t cmd).1 = (command c source a cmd).1 ∧
    RelatedService R (command c target t cmd).2 (command c source a cmd).2 := by
  obtain ⟨hr, hc⟩ := rel
  have hn := sim.position _ _ hr
  have hb := sim.pastParity _ _ hr
  have hi := sim.item _ _ hr
  have hp := sim.total _ _ hr
  have hread := sim.read _ _ hr
  have hclass := sim.classify _ _ hr
  cases cmd
  case release b =>
    cases b <;> simp only [command, hc, RelatedService]
    all_goals repeat' split
    all_goals simp_all
  case scan b =>
    cases b <;> simp only [command, hc, hn, hi, RelatedService]
    all_goals repeat' split
    all_goals simp_all
  case stream b =>
    cases b <;> simp only [command, hc, hi, RelatedService]
    all_goals repeat' split
    all_goals simp_all
  all_goals simp only [command, hc, hn, hb, hi, hp, hread, hclass, RelatedService]
  all_goals repeat' split
  all_goals simp_all
  all_goals exact sim.append _ _ hr (by omega) _

def execute (c : Config) (ops : Operations α) : Service α → List Command → List Reply × Service α
  | s, [] => ([], s)
  | s, cmd :: cmds =>
      let (reply, next) := command c ops s cmd
      let (replies, last) := execute c ops next cmds
      (reply :: replies, last)

theorem execute_refines {c : Config} {source : Operations α} {target : Operations β}
    {R : β → α → Prop} (sim : Simulates c source target R)
    {t : Service β} {a : Service α} (rel : RelatedService R t a) (cmds : List Command) :
    (execute c target t cmds).1 = (execute c source a cmds).1 ∧
    RelatedService R (execute c target t cmds).2 (execute c source a cmds).2 := by
  induction cmds generalizing t a with
  | nil => exact ⟨rfl, rel⟩
  | cons cmd cmds ih =>
    obtain ⟨he, hr⟩ := command_refines sim rel cmd
    obtain ⟨hes, hrs⟩ := ih hr
    exact ⟨by simp only [execute, he, hes], hrs⟩

theorem Represents.pastParity {c : Config} {s : Snapshot} {h : List Bool}
    (r : Represents c s h) : s.pastParity = parity (h.take (h.length - c.window)) := by
  obtain ⟨hn, hk, hl, pre, rfl, hp⟩ := r
  have len : (pre ++ s.items).length - c.window = pre.length := by
    simp only [List.length_append] at hn ⊢
    omega
  rw [len]
  simp [hp]

theorem snapshot_simulates (c : Config) :
    Simulates c (ghostOps c) (snapshotOps c) (Represents c) where
  position _ _ r := r.1
  count _ _ r := by dsimp [snapshotOps, ghostOps]; rw [r.2.2.1, r.1]
  pastParity _ _ r := r.pastParity
  item s h r i := by
    dsimp [snapshotOps, ghostOps]
    rw [← r.suffix, List.getElem?_drop, r.lower]
  total _ _ r := r.total
  read _ _ r := read_refines r
  classify _ _ r := classify_refines r
  append _ _ r room p := append_represents r room p

theorem bank_simulates (c : Config) :
    Simulates c (ghostOps c) (bankOps c) (fun d h => Represents c d.root h) where
  position _ _ r := r.1
  count _ _ r := (snapshot_simulates c).count _ _ r
  pastParity _ _ r := r.pastParity
  item _ _ r := (snapshot_simulates c).item _ _ r
  total _ _ r := r.total
  read _ _ r := read_refines r
  classify _ _ r := classify_refines r
  append d h r room p := by
    dsimp [bankOps]
    rw [replacement_root]
    exact append_represents r room p

end Durability.Retention
