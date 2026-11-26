import Applications.FRP.PendingCrash.Frame
import Applications.Durability.Executions
import Applications.Durability.Clients

/-! Direct append-only durability realization for complete stable frames.
The operational disk is a list; native durability certificates live in proofs. -/
namespace FRPSpec.PendingCrash
open Durability

abbrev Cells := List (Nat × Cell Frame)

def cellLookup (address : Nat) : Cells → Option (Cell Frame) × List Work
  | [] => (none, [])
  | (key, cell) :: rest =>
    if key = address then (some cell, [.cellProbe key])
    else let r := cellLookup address rest
         (r.1, .cellProbe key :: r.2)

def cellHeap (cells : Cells) : Heap (Cell Frame) := fun address => (cellLookup address cells).1

theorem cellHeap_cons (cells : Cells) (address : Nat) (cell : Cell Frame) :
    cellHeap ((address,cell) :: cells) = put (cellHeap cells) address cell := by
  funext i
  by_cases h : i = address
  · subst i; simp [cellHeap, cellLookup, put]
  · simp [cellHeap, cellLookup, put, h, Ne.symm h]

structure Journal where
  machine : Machine Frame
  cells : Cells
  nextAddress : Nat
  disk_eq : machine.disk = cellHeap cells
  fresh : ∀ i, nextAddress ≤ i → machine.disk i = none ∧ i ∉ machine.used
  logRoot : machine.root.checkpoint = none
  pendingRoot : ∀ p, machine.pending = some p → p.root.checkpoint = none
  support : ∀ p, machine.pending = some p → ∀ i c, p.writes i = some c → i < nextAddress
  singleton : ∀ p, machine.pending = some p → ∀ i, i ≠ nextAddress - 1 → p.writes i = none
  safe : ∃ a, Related machine a

def initialJournal : Journal where
  machine := Durability.initial
  cells := []
  nextAddress := 0
  disk_eq := rfl
  fresh := by intro i _; exact ⟨rfl, by simp [Durability.initial]⟩
  logRoot := rfl
  pendingRoot := by simp [Durability.initial]
  support := by simp [Durability.initial]
  singleton := by simp [Durability.initial]
  safe := ⟨_, related_initial⟩

structure JournalResult (before : Journal) where
  journal : Journal
  event : Durability.Event Frame
  native : Durability.Step event before.machine journal.machine
  work : List Work

inductive JournalAttempt (before : Journal) where
  | failed (work : List Work)
  | done (result : JournalResult before)

def JournalAttempt.work {before : Journal} : JournalAttempt before → List Work
  | .failed work => work
  | .done result => result.work

def JournalAttempt.after {before : Journal} : JournalAttempt before → Journal
  | .failed _ => before
  | .done result => result.journal

private theorem advance_safe (s : Journal) {t : Machine Frame} {event : Durability.Event Frame}
    (h : Durability.Step event s.machine t) : ∃ a, Related t a := by
  obtain ⟨a, ha⟩ := s.safe
  obtain ⟨b, _, hb⟩ := h.simulation ha
  exact ⟨b,hb⟩

private theorem cache_rep (s : Journal) (history : List (Record Frame))
    (h : s.machine.cache = some history) : Represents s.machine.disk s.machine.root history := by
  obtain ⟨a, ha⟩ := s.safe
  rw [(ha.ready h).2]
  exact ha.root

/-- Journal identities are allocation names, separate from request identities.
Repeated records for one request therefore have distinct journal keys. -/
def journalInvoke (s : Journal) (f : Frame) : JournalAttempt s :=
  match hc : s.machine.cache with
  | none => .failed [.attempt 0]
  | some _history =>
    if hi : s.machine.active = none then
      if hp : s.machine.pending = none then
        let e : Record Frame := ⟨0,s.nextAddress,f⟩
        let t := invokeState s.machine e
        let step : Durability.Step (.invoke e) s.machine t := .invoke hc hi hp
        .done ⟨{s with machine := t, safe := advance_safe s step}, .invoke e, step, []⟩
      else .failed [.attempt 0]
    else .failed [.attempt 0]

instance (history : List (Record Frame)) (e : Record Frame) : Decidable (Fresh history e) :=
  inferInstanceAs (Decidable (∀ r ∈ history, r.key ≠ e.key))

/-- Checked list traversals expose unsuccessful as well as successful work. -/
def checkFresh (e : Record Frame) : List (Record Frame) → Bool × List Work
  | [] => (true, [])
  | r :: rest =>
    if r.key = e.key then (false, [.recordCheck r.id])
    else let tail := checkFresh e rest
         (tail.1, .recordCheck r.id :: tail.2)

theorem checkFresh_correct (e : Record Frame) (history : List (Record Frame)) :
    (checkFresh e history).1 = true ↔ Fresh history e := by
  induction history with
  | nil => simp [checkFresh, Fresh]
  | cons r rest ih =>
    by_cases he : r.key = e.key
    · simp [checkFresh, Fresh, he]
    · simp only [checkFresh, ite_eq_right he, ih, Fresh, List.mem_cons, forall_eq_or_imp]
      simp [he]

def checkContains (e : Record Frame) : List (Record Frame) → Bool × List Work
  | [] => (false, [])
  | r :: rest =>
    if r = e then (true, [.recordCheck r.id])
    else let tail := checkContains e rest
         (tail.1, .recordCheck r.id :: tail.2)

theorem checkContains_correct (e : Record Frame) (history : List (Record Frame)) :
    (checkContains e history).1 = true ↔ e ∈ history := by
  induction history with
  | nil => simp [checkContains]
  | cons r rest ih =>
    by_cases he : r = e
    · simp [checkContains, he]
    · simp [checkContains, he, ih, Ne.symm he]

/-- Preparation uses the existing appendPlan builder and reserves its fresh
cell even if this attempt is later interrupted. -/
def journalPrepare (s : Journal) : JournalAttempt s :=
  match hc : s.machine.cache, he : s.machine.active with
  | some history, some e =>
    if hn : s.machine.pending = none then
      let checked := checkFresh e history
      if hf : checked.1 = true then
        have freshHistory : Fresh history e := (checkFresh_correct e history).mp hf
        let address := s.nextAddress
        let p := appendPlan s.machine.disk s.machine.root history (cache_rep s history hc)
          address e (s.fresh address (Nat.le_refl _)).1
        let t := prepareState s.machine p
        have step : Durability.Step .internal s.machine t := by
          apply Durability.Step.prepare (p := p) hc hn rfl rfl he.symm
          · intro r hr
            have eq : e = r := Option.some.inj hr
            subst r; exact freshHistory
          · intro i c hw
            by_cases hi : i = address
            · subst i; exact (s.fresh address (Nat.le_refl _)).2
            · simp [p, appendPlan, put, hi] at hw
        .done ⟨{
          machine := t
          cells := s.cells
          nextAddress := s.nextAddress + 1
          disk_eq := s.disk_eq
          fresh := by
            intro i hi
            obtain ⟨hd, hu⟩ := s.fresh i (by omega)
            refine ⟨hd, ?_⟩
            simp only [t, Set.mem_union, Set.mem_ofPred_eq, not_or]
            refine ⟨hu, ?_⟩
            rintro ⟨c,hc⟩
            have ne : i ≠ address := by dsimp [address]; omega
            simp [p, appendPlan, put, ne] at hc
          logRoot := s.logRoot
          pendingRoot := by
            intro q hq
            have eq : p = q := Option.some.inj hq
            subst q
            exact s.logRoot
          support := by
            intro q hq i c hw
            have eq : p = q := Option.some.inj hq
            subst q
            by_cases hi : i = address
            · dsimp [address] at hi; omega
            · simp [p, appendPlan, put, hi] at hw
          singleton := by
            intro q hq i hi
            have eq : p = q := Option.some.inj hq
            subst q
            simpa [p, appendPlan, put, address] using hi
          safe := advance_safe s step
        }, .internal, step, checked.2 ++ [.attempt 1, .allocate (history.length + 2), .copy history.length]⟩
      else .failed (checked.2 ++ [.attempt 0])
    else .failed [.attempt 0]
  | _, _ => .failed [.attempt 0]


def journalWrite (s : Journal) : JournalAttempt s :=
  match hp : s.machine.pending with
  | none => .failed [.attempt 0]
  | some p =>
    let address := s.nextAddress - 1
    match hw : p.writes address with
    | none => .failed [.attempt 0]
    | some c =>
      let t := writeState s.machine address c
      let step : Durability.Step .internal s.machine t := .write hp hw
      .done ⟨{s with machine := t, safe := advance_safe s step},
        .internal, step, [.cellWrite address]⟩

def journalPersist (s : Journal) : JournalAttempt s :=
  match hp : s.machine.pending with
  | none => .failed [.attempt 0]
  | some p =>
    let address := s.nextAddress - 1
    match hw : p.writes address with
    | none => .failed [.attempt 0]
    | some c =>
      if hb : s.machine.buffered address = some c then
        let found := cellLookup address s.cells
        if hd : found.1 = none then
          have empty : s.machine.disk address = none := by rw [s.disk_eq]; exact hd
          let t := persistState s.machine address c
          let step : Durability.Step .internal s.machine t := .persist hp hw hb (Or.inl empty)
          .done ⟨{s with
            machine := t
            cells := (address,c) :: s.cells
            disk_eq := by
              change put s.machine.disk address c = _
              rw [s.disk_eq, cellHeap_cons]
            fresh := by
              intro i hi
              have smaller := s.support p hp address c hw
              have ne : i ≠ address := by omega
              simpa only [t, persistState, put, ite_eq_right ne] using s.fresh i hi
            safe := advance_safe s step},
            .internal, step, found.2 ++ [.cellPersist address]⟩
        else .failed (found.2 ++ [.attempt 0])
      else .failed [.attempt 0]

def journalPublish (s : Journal) : JournalAttempt s :=
  match hp : s.machine.pending with
  | none => .failed [.attempt 0]
  | some p =>
    let address := s.nextAddress - 1
    match hw : p.writes address with
    | none => .failed [.attempt 0]
    | some c =>
      let found := cellLookup address s.cells
      if hd : found.1 = some c then
        have ext : Extends p.writes s.machine.disk := by
          intro i d hi
          by_cases he : i = address
          · subst i
            have eq : c = d := Option.some.inj (hw.symm.trans hi)
            subst d
            rw [s.disk_eq]; exact hd
          · rw [s.singleton p hp i he] at hi
            contradiction
        let t := publishState s.machine p
        let event : Durability.Event Frame := match p.appended with | none => Durability.Event.internal | some e => .commit e
        let step : Durability.Step event s.machine t := by
          have h := Durability.Step.publish (p := p) hp ext
          cases ha : p.appended <;> simpa only [event, t, Durability.publishState, ha] using h
        .done ⟨{s with
          machine := t
          logRoot := s.pendingRoot p hp
          pendingRoot := by simp [t]
          support := by simp [t]
          singleton := by simp [t]
          safe := advance_safe s step},
          event, step, found.2 ++ [.rootPublish, .release p.before.length]⟩
      else .failed (found.2 ++ [.attempt 0])

def journalAcknowledge (s : Journal) : JournalAttempt s :=
  match hc : s.machine.cache, he : s.machine.active with
  | some history, some e =>
    if hp : s.machine.pending = none then
      let checked := checkContains e history
      if hm : checked.1 = true then
        have member : e ∈ history := (checkContains_correct e history).mp hm
        let t := acknowledgeState s.machine
        let step : Durability.Step (.acknowledge e) s.machine t := .acknowledge hc he hp member
        .done ⟨{s with machine := t, safe := advance_safe s step}, .acknowledge e, step, checked.2⟩
      else .failed (checked.2 ++ [.attempt 0])
    else .failed [.attempt 0]
  | _, _ => .failed [.attempt 0]

def journalCrash (s : Journal) : JournalResult s :=
  let t := crashState s.machine
  let step : Durability.Step .crash s.machine t := .crash
  ⟨{s with
    machine := t
    pendingRoot := by simp [t]
    support := by simp [t]
    singleton := by simp [t]
    safe := advance_safe s step}, .crash, step,
    [.release ((s.machine.cache.map List.length).getD 0 +
      (s.machine.pending.map (fun p => p.after.length)).getD 0 +
      (s.machine.cursor.map (fun c => match c with
        | .prefixCells todo seen _ => todo.length + seen.length
        | .tailCells _ pre suffix => pre.length + suffix.length
        | .done history => history.length)).getD 0)]⟩

def journalStartRead (s : Journal) : JournalAttempt s :=
  if hc : s.machine.cache = none then
    if hr : s.machine.cursor = none then
      let cursor := Cursor.tailCells s.machine.root.tail [] []
      let t := {s.machine with cursor := some cursor}
      let step : Durability.Step .internal s.machine t := .startRead hc hr (.log s.logRoot)
      .done ⟨{s with machine := t, safe := advance_safe s step}, .internal, step, [.reconstruct]⟩
    else .failed [.attempt 0]
  else .failed [.attempt 0]

def journalRead (s : Journal) : JournalAttempt s :=
  if hc : s.machine.cache = none then
    match hr : s.machine.cursor with
    | some (.tailCells none pre suffix) =>
      let t := {s.machine with cursor := some (.done (pre ++ suffix))}
      let step : Durability.Step .internal s.machine t := .read hc hr .finish
      .done ⟨{s with machine := t, safe := advance_safe s step},
        .internal, step, [.copy pre.length]⟩
    | some (.tailCells (some address) pre suffix) =>
      let found := cellLookup address s.cells
      match hl : found.1 with
      | some (.node previous e) =>
        let t := {s.machine with cursor := some (.tailCells previous pre (e :: suffix))}
        have lookup : s.machine.disk address = some (.node previous e) := by
          rw [s.disk_eq]; exact hl
        let step : Durability.Step .internal s.machine t := .read hc hr (.node lookup)
        .done ⟨{s with machine := t, safe := advance_safe s step},
          .internal, step, found.2 ++ [.allocate 1, .reconstruct]⟩
      | _ => .failed (found.2 ++ [.attempt 0])
    | _ => .failed [.attempt 0]
  else .failed [.attempt 0]

def journalRecover (s : Journal) : JournalAttempt s :=
  if hc : s.machine.cache = none then
    match hr : s.machine.cursor with
    | some (.done history) =>
      let t := {s.machine with cache := some history, cursor := none}
      let step : Durability.Step (.recover history) s.machine t := .recover hc hr
      .done ⟨{s with machine := t, safe := advance_safe s step}, .recover history, step, []⟩
    | _ => .failed [.attempt 0]
  else .failed [.attempt 0]

inductive JournalCommand where
  | invoke (frame : Frame)
  | prepare | write | persist | publish | acknowledge | crash | startRead | read | recover
  deriving DecidableEq, Repr

def journalStep (s : Journal) : JournalCommand → JournalAttempt s
  | .invoke f => journalInvoke s f
  | .prepare => journalPrepare s
  | .write => journalWrite s
  | .persist => journalPersist s
  | .publish => journalPublish s
  | .acknowledge => journalAcknowledge s
  | .crash => .done (journalCrash s)
  | .startRead => journalStartRead s
  | .read => journalRead s
  | .recover => journalRecover s

structure JournalExecution where
  journal : Journal
  events : List (Durability.Event Frame)
  work : List Work

def journalExecute : Journal → List JournalCommand → JournalExecution
  | s, [] => ⟨s, [], []⟩
  | s, command :: commands =>
    match journalStep s command with
    | .failed work =>
      let rest := journalExecute s commands
      {rest with work := work ++ rest.work}
    | .done result =>
      let rest := journalExecute result.journal commands
      ⟨rest.journal, result.event :: rest.events, result.work ++ rest.work⟩

/-- Every executed write/persist/publication/recovery cut is a native step.
Failed commands retain their work but do not invent a commit event. -/
theorem journalExecute_native (s : Journal) (commands : List JournalCommand) :
    Interaction.Events.Interpret Durability.Step (journalExecute s commands).events
      s.machine (journalExecute s commands).journal.machine := by
  induction commands generalizing s with
  | nil => rfl
  | cons command commands ih =>
    simp only [journalExecute]
    cases h : journalStep s command with
    | failed work => exact ih s
    | done result => exact ⟨result.journal.machine, result.native, ih result.journal⟩

theorem journalExecute_simulation (s : Journal) (commands : List JournalCommand)
    (a : Durability.Abstract Frame) (related : Durability.Related s.machine a) :
    ∃ b, Interaction.Events.Interpret Durability.SpecStep (journalExecute s commands).events a b ∧
      Durability.Related (journalExecute s commands).journal.machine b :=
  Durability.script_simulation _ related (journalExecute_native s commands)

/-- Ordered committed prefix survives arbitrary future command traces,
including incomplete writes and interrupted reconstruction. -/
theorem journalExecute_prefix (s : Journal) (commands : List JournalCommand)
    (a : Durability.Abstract Frame) (related : Durability.Related s.machine a) :
    ∃ b suffix, Durability.Related (journalExecute s commands).journal.machine b ∧
      b.history = a.history ++ suffix := by
  obtain ⟨b, run, relation⟩ := journalExecute_simulation s commands a related
  obtain ⟨suffix, eq⟩ := Durability.spec_script_prefix run
  exact ⟨b, suffix, relation, eq⟩

/-- The actual adapter journal's acknowledged frames survive every suffix.
The statement retains the complete frame payload and its ordered prefix. -/
theorem journalExecute_acknowledged (s : Journal) (commands : List JournalCommand)
    (a b : Durability.Abstract Frame) (e : Durability.Record Frame)
    (ack : Durability.SpecStep (.acknowledge e) a b)
    (related : Durability.Related s.machine b) :
    ∃ c suffix, Durability.Related (journalExecute s commands).journal.machine c ∧
      e ∈ c.history ∧ c.history = a.history ++ suffix := by
  obtain ⟨c, run, relation⟩ := journalExecute_simulation s commands b related
  obtain ⟨member, suffix, eq⟩ := Durability.acknowledged_survives ack run
  exact ⟨c, suffix, relation, member, eq⟩

end FRPSpec.PendingCrash
