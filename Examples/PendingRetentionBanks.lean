import Applications.FRP.PendingRetention.Banks
import Applications.Durability.RetentionBanks

/-! Both consumers retain their native payloads while sharing cell persistence.
These are mechanical bank examples; service provenance is a separate theorem. -/
namespace Examples.PendingRetentionBanks
open FRPSpec.PendingRetention Durability

/-- A nonempty target changes metadata and records together. -/
def localTarget : LocalSnapshot :=
  { frame := { FRPSpec.PendingCrash.initialFrame with nextIdentity := 2 }
    floor := 1, pending := some 1
    outcomes := [⟨0,true,some (.published true false),true⟩,
      ⟨1,false,some (.prevented false),true⟩] }

def localCopy := LocalBanks.initial.begin localTarget

def progressN (n : Nat) (b : LocalBanks) : LocalBanks :=
  n.rec b (fun _ b => b.progress.1)

theorem local_progress_cuts (n : Nat) :
    (progressN n localCopy).AtCut localCopy.state.disk localSeed := by
  induction n with
  | zero => exact SnapshotBanks.begin_atCut _ _ _
  | succ n ih => exact SnapshotBanks.Worker.progress_atCut _ _ _ ih

example (n : Nat) :
    (progressN n localCopy).state.disk.root = localCopy.state.disk.root ∨
      (progressN n localCopy).state.disk.root = (progressN n localCopy).target :=
  SnapshotBanks.Worker.root_old_or_new _ _ _ (local_progress_cuts n)

/-- Every intermediate bank, including stale inactive and volatile regions,
stays within two record slots in this worked copy. -/
theorem local_regions (n : Nat) :
    (progressN n localCopy).Bounded (fun _ => True) (fun _ => True) 2 := by
  induction n with
  | zero =>
    apply SnapshotBanks.begin_bounded
    · trivial
    · intro bank
      cases bank <;> exact ⟨trivial,by decide,by intro r hr; trivial⟩
    · exact ⟨trivial,by decide,by intro r hr; trivial⟩
  | succ n ih => exact SnapshotBanks.Worker.progress_bounded _ _ _ _ ih


example : (progressN 6 localCopy).selected = {} := by decide
example : (progressN 7 localCopy).selected = localTarget := by decide
example : (progressN 6 localCopy).crash.selected = {} := by decide
example : (progressN 7 localCopy).crash.selected = localTarget := by decide
example : (progressN 7 localCopy).busy = false := by decide

/-- The direct consumer has exactly the generic model's independent crash cuts. -/
example (n : Nat) :
    let r := directLocalCut (fun _ => {}) false localTarget n
    r.cells r.selector = {} ∨ r.cells r.selector = localTarget :=
  directLocal_old_or_new _ _ _ n

example (target : PeerSnapshot) (n : Nat) :
    let r := directPeerCut (fun _ => {}) true target n
    r.cells r.selector = {} ∨ r.cells r.selector = target :=
  directPeer_old_or_new _ _ _ n

def peerTarget : PeerSnapshot :=
  {floor := 1,pending := some 1, entries := [(0,.published true false),(1,.cancelled false)]}

example :
    let r := directPeerCut (fun _ => {}) true peerTarget 6
    r.cells r.selector = {} := by decide
example :
    let r := directPeerCut (fun _ => {}) true peerTarget 7
    r.cells r.selector = peerTarget := by decide

example : SnapshotBanks.Allowed localCopy.state (SnapshotBanks.replacement localTarget.encode) :=
  local_replacement_allowed _ _
example : (SnapshotBanks.Access.mutation false).safeOverwrite true :=
  (inactive_overwrite false).1

/-- An arbitrary torn inactive payload cannot satisfy publication permission. -/
example : ¬SnapshotBanks.Permitted
    (⟨⟨fun _ => ({ } : LocalSnapshot).encode,false⟩,localTarget.encode⟩ :
      SnapshotBanks.CopyState LocalHeader Outcome) .publish := by
  unfold SnapshotBanks.Permitted
  decide


/-- Boolean policy and signatures are unchanged; shared cut laws discharge the
same full-history refinement, including interrupted reuse of stale banks. -/
def booleanConfig : Retention.Config := ⟨7,2,3,by decide,by decide⟩
def booleanDisk : Retention.Banks := ⟨fun _ => Retention.empty,false⟩
example (n : Nat) :
    Retention.Represents booleanConfig
      (Retention.cut booleanDisk (Retention.append booleanConfig Retention.empty true) n).disk.root [] ∨
    Retention.Represents booleanConfig
      (Retention.cut booleanDisk (Retention.append booleanConfig Retention.empty true) n).disk.root [true] :=
  Retention.crash_cut_refines (Retention.represents_empty booleanConfig) (by decide) true n

example : (Retention.cut booleanDisk (Retention.append booleanConfig Retention.empty true) 4).disk.root =
    Retention.empty := by decide
example : (Retention.cut booleanDisk (Retention.append booleanConfig Retention.empty true) 5).disk.root =
    Retention.append booleanConfig Retention.empty true := by decide

end Examples.PendingRetentionBanks
