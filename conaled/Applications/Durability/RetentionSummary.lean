import Applications.Durability.RetentionService

namespace Durability.Retention

/-- The summary implementation stores one cumulative bit and one optional last
payload. Its public command type contains no historical range operation. -/
structure SummaryStore where
  position : Nat
  total : Bool
  last : Option Bool
  deriving DecidableEq, Repr

def SummaryStore.decode (s : SummaryStore) : Snapshot :=
  ⟨s.position, xor s.total (parity s.last.toList), s.last.toList⟩

def SummaryStore.append (s : SummaryStore) (p : Bool) : SummaryStore :=
  ⟨s.position + 1, xor s.total p, some p⟩

def singleWindow (c : Config) : Config :=
  { c with window := 1, positive := by omega, bounded := by have := c.positive; have := c.bounded; omega }

theorem SummaryStore.decode_append (c : Config) (s : SummaryStore) (p : Bool) :
    (s.append p).decode = Durability.Retention.append (singleWindow c) s.decode p := by
  cases s with | mk n b last =>
    cases last with
    | none => cases b <;> cases p <;> rfl
    | some old => cases b <;> cases old <;> cases p <;> rfl

@[simp] theorem SummaryStore.decode_total (s : SummaryStore) : s.decode.total = s.total := by
  cases s with | mk n b last =>
    cases last with
    | none => cases b <;> rfl
    | some old => cases b <;> cases old <;> rfl

def summaryOps (c : Config) : Operations SummaryStore where
  position := SummaryStore.position
  count s := s.last.toList.length
  pastParity s := s.decode.pastParity
  item s i := s.last.toList[i]?
  total := SummaryStore.total
  read s := read s.decode
  classify s := classify (singleWindow c) s.decode
  append := SummaryStore.append

theorem summary_simulates (c : Config) :
    Simulates (singleWindow c) (ghostOps (singleWindow c)) (summaryOps c)
      (fun s h => Represents (singleWindow c) s.decode h) where
  position _ _ r := r.1
  count _ _ r := (snapshot_simulates (singleWindow c)).count _ _ r
  pastParity _ _ r := r.pastParity
  item _ _ r := (snapshot_simulates (singleWindow c)).item _ _ r
  total s _ r := by simpa [summaryOps, ghostOps] using r.total
  read _ _ r := read_refines r
  classify _ _ r := classify_refines r
  append s h r room p := by
    dsimp [summaryOps]
    rw [SummaryStore.decode_append]
    exact append_represents r room p

inductive SummaryCommand where
  | append (incarnation id : Nat) (payload : Bool)
  | publish | acknowledge | crash | recover | summary
  deriving DecidableEq, Repr

def SummaryCommand.command : SummaryCommand → Command
  | .append e i p => .append e i p
  | .publish => .publish
  | .acknowledge => .acknowledge
  | .crash => .crash
  | .recover => .recover
  | .summary => .summary

def summaryExecute (c : Config) (s : Service SummaryStore) (cmds : List SummaryCommand) :=
  execute (singleWindow c) (summaryOps c) s (cmds.map SummaryCommand.command)

/-- Both realizations produce exactly the same observable replies on the
restricted W=1 contract. The relation is to a common independent history. -/
theorem summary_window_trace (c : Config) (s : Service SummaryStore) (w : Service Banks)
    (a : Service (List Bool)) (rs : RelatedService (fun s h => Represents (singleWindow c) s.decode h) s a)
    (rw : RelatedService (fun d h => Represents (singleWindow c) d.root h) w a)
    (cmds : List SummaryCommand) :
    (summaryExecute c s cmds).1 =
      (execute (singleWindow c) (bankOps (singleWindow c)) w
        (cmds.map SummaryCommand.command)).1 := by
  exact (execute_refines (summary_simulates c) rs _).1.trans
    (execute_refines (bank_simulates (singleWindow c)) rw _).1.symm

/-- Two fixed typed summary descriptors and one selector. A descriptor contains
only position, cumulative parity, and the optional last payload. -/
structure SummaryDisk where
  cells : Bool → SummaryStore
  selected : Bool

def SummaryDisk.root (s : SummaryDisk) := s.cells s.selected

def SummaryDisk.install (s : SummaryDisk) (value : SummaryStore) : SummaryDisk :=
  ⟨fun b => if b = !s.selected then value else s.cells b, !s.selected⟩

@[simp] theorem SummaryDisk.install_root (s : SummaryDisk) (value : SummaryStore) :
    (s.install value).root = value := by simp [SummaryDisk.install, SummaryDisk.root]

structure SummaryCopy where
  disk : SummaryDisk
  buffered : SummaryStore

/-- Cut zero precedes the buffered write, cut one precedes persistence, cut two
precedes selector publication, and cut three follows it. Inactive descriptor
contents are ignored on every restart. -/
def summaryCut (disk : SummaryDisk) (p : Bool) (count : Nat) : SummaryCopy :=
  let target := disk.root.append p
  if count = 0 then ⟨disk, ⟨0,false,none⟩⟩
  else if count = 1 then ⟨disk, target⟩
  else if count = 2 then
    ⟨⟨fun b => if b = !disk.selected then target else disk.cells b, disk.selected⟩, target⟩
  else ⟨disk.install target, target⟩

theorem summary_cut_old_or_new (disk : SummaryDisk) (p : Bool) (count : Nat) :
    (summaryCut disk p count).disk.root = disk.root ∨
    (summaryCut disk p count).disk.root = disk.root.append p := by
  unfold summaryCut
  split_ifs <;> try exact Or.inl rfl
  · left
    cases hs : disk.selected <;> simp [SummaryDisk.root, hs]
  · right
    exact SummaryDisk.install_root _ _

def summaryDiskOps (c : Config) : Operations SummaryDisk where
  position d := d.root.position
  count d := d.root.last.toList.length
  pastParity d := d.root.decode.pastParity
  item d i := d.root.last.toList[i]?
  total d := d.root.total
  read d := read d.root.decode
  classify d := classify (singleWindow c) d.root.decode
  append d p := d.install (d.root.append p)

theorem summary_disk_simulates (c : Config) :
    Simulates (singleWindow c) (ghostOps (singleWindow c)) (summaryDiskOps c)
      (fun d h => Represents (singleWindow c) d.root.decode h) where
  position _ _ r := r.1
  count _ _ r := (summary_simulates c).count _ _ r
  pastParity _ _ r := r.pastParity
  item _ _ r := (summary_simulates c).item _ _ r
  total d _ r := by simpa [summaryDiskOps, ghostOps] using r.total
  read _ _ r := read_refines r
  classify _ _ r := classify_refines r
  append d h r room p := by
    dsimp [summaryDiskOps]
    rw [SummaryDisk.install_root, SummaryStore.decode_append]
    exact append_represents r room p

def summaryDiskExecute (c : Config) (s : Service SummaryDisk) (cmds : List SummaryCommand) :=
  execute (singleWindow c) (summaryDiskOps c) s (cmds.map SummaryCommand.command)

theorem summary_disk_window_trace (c : Config) (s : Service SummaryDisk) (w : Service Banks)
    (a : Service (List Bool)) (rs : RelatedService (fun d h => Represents (singleWindow c) d.root.decode h) s a)
    (rw : RelatedService (fun d h => Represents (singleWindow c) d.root h) w a)
    (cmds : List SummaryCommand) :
    (summaryDiskExecute c s cmds).1 =
      (execute (singleWindow c) (bankOps (singleWindow c)) w
        (cmds.map SummaryCommand.command)).1 := by
  exact (execute_refines (summary_disk_simulates c) rs _).1.trans
    (execute_refines (bank_simulates (singleWindow c)) rw _).1.symm

def SummaryDisk.Bounded (c : Config) (d : SummaryDisk) : Prop :=
  ∀ b, (d.cells b).position ≤ c.limit

theorem SummaryDisk.install_bounded {c : Config} {d : SummaryDisk} {value : SummaryStore}
    (hd : d.Bounded c) (hv : value.position ≤ c.limit) : (d.install value).Bounded c := by
  intro b
  dsimp [SummaryDisk.install]
  split
  · exact hv
  · exact hd b

theorem summary_disk_command_bounded {c : Config} {s : Service SummaryDisk}
    (hs : s.store.Bounded c) (cmd : SummaryCommand) :
    (command (singleWindow c) (summaryDiskOps c) s cmd.command).2.store.Bounded c := by
  cases cmd <;> simp only [SummaryCommand.command, command]
  all_goals repeat' split
  all_goals try exact hs
  all_goals apply SummaryDisk.install_bounded hs
  all_goals simp_all [SummaryStore.append, summaryDiskOps, singleWindow]
  all_goals have := of_decide_eq_true (And.right ‹_ ∧ _›)
  all_goals omega

theorem summary_disk_execution_bounded {c : Config} {s : Service SummaryDisk}
    (hs : s.store.Bounded c) (cmds : List SummaryCommand) :
    (summaryDiskExecute c s cmds).2.store.Bounded c := by
  induction cmds generalizing s with
  | nil => exact hs
  | cons cmd cmds ih => exact ih (summary_disk_command_bounded hs cmd)

/-- Each summary descriptor has at most one retry payload. Reserved durable
payload slots are therefore two, independent of the number of commits. -/
theorem summary_payload_bound (d : SummaryDisk) :
    (d.cells false).last.toList.length + (d.cells true).last.toList.length ≤ 2 := by
  cases (d.cells false).last <;> cases (d.cells true).last <;> simp

end Durability.Retention
