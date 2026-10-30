import Applications.Durability.RetentionMachine

namespace Durability.Retention

def Snapshot.Fits (c : Config) (s : Snapshot) : Prop :=
  s.items.length ≤ c.window ∧ s.position ≤ c.limit

def Banks.Fits (c : Config) (d : Banks) : Prop := ∀ b, (d.cells b).Fits c

def CopyState.Fits (c : Config) (s : CopyState) : Prop := s.disk.Fits c ∧ s.buffer.Fits c

theorem Represents.fits {c : Config} {s : Snapshot} {h : List Bool}
    (r : Represents c s h) : s.Fits c := ⟨by rw [r.2.2.1]; omega, r.2.1⟩

theorem empty_fits (c : Config) : empty.Fits c := by simp [Snapshot.Fits, empty]

theorem putInactive_fits {c : Config} {d : Banks} {s : Snapshot}
    (hd : d.Fits c) (hs : s.Fits c) : (d.putInactive s).Fits c := by
  intro b
  simp only [Banks.putInactive]
  split
  · exact hs
  · exact hd b

def Primitive.Bounded (c : Config) : Primitive → Prop
  | .writeRecord i _ | .persistRecord i _ => i < c.window
  | .writeDescriptor n _ | .persistDescriptor n _ => n ≤ c.limit
  | .publish => True

theorem primitive_fits {c : Config} {s : CopyState} {op : Primitive}
    (hs : s.Fits c) (hop : op.Bounded c) : (primitive s op).Fits c := by
  obtain ⟨hd, hb⟩ := hs
  cases op with
  | writeRecord i p =>
    refine ⟨hd, ?_, hb.2⟩
    simp only [primitive, List.length_append, List.length_take, List.length_singleton]
    dsimp [Primitive.Bounded] at hop
    omega
  | persistRecord i p =>
    refine ⟨putInactive_fits hd ⟨?_, (hd _).2⟩, hb⟩
    simp only [List.length_append, List.length_take, List.length_singleton]
    dsimp [Primitive.Bounded] at hop
    omega
  | writeDescriptor n b => exact ⟨hd, hb.1, hop⟩
  | persistDescriptor n b => exact ⟨putInactive_fits hd ⟨hb.1, hop⟩, hb⟩
  | publish => exact ⟨hd, hb⟩

theorem fold_fits {c : Config} (ops : List Primitive) {s : CopyState}
    (hs : s.Fits c) (hops : ∀ op ∈ ops, op.Bounded c) :
    (ops.foldl primitive s).Fits c := by
  induction ops generalizing s with
  | nil => exact hs
  | cons op ops ih =>
    exact ih (primitive_fits hs (hops _ (by simp))) (by intro o ho; exact hops o (by simp [ho]))

theorem recordOps_bounded {c : Config} (xs : List Bool) (i : Nat)
    (h : i + xs.length ≤ c.window) : ∀ op ∈ recordOps xs i, op.Bounded c := by
  induction xs generalizing i with
  | nil => simp [recordOps]
  | cons p ps ih =>
    intro op hop
    simp only [recordOps, List.mem_cons] at hop
    rcases hop with rfl | rfl | hop
    · dsimp [Primitive.Bounded]; simp only [List.length_cons] at h; omega
    · dsimp [Primitive.Bounded]; simp only [List.length_cons] at h; omega
    · exact ih (i + 1) (by simp only [List.length_cons] at h; omega) op hop

theorem replacement_bounded {c : Config} {target : Snapshot} (h : target.Fits c) :
    ∀ op ∈ replacement target, op.Bounded c := by
  intro op hop
  simp only [replacement, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with hop | rfl | rfl | rfl
  · exact recordOps_bounded target.items 0 (by simpa using h.1) op hop
  · exact h.2
  · exact h.2
  · trivial

theorem cut_fits {c : Config} {disk : Banks} {target : Snapshot}
    (hd : disk.Fits c) (ht : target.Fits c) (count : Nat) : (cut disk target count).Fits c := by
  exact fold_fits _ ⟨hd, empty_fits c⟩ (by
    intro op hop
    exact replacement_bounded ht op (List.mem_of_mem_take hop))

theorem cut_succ_fits {c : Config} {disk : Banks} {target : Snapshot}
    (ht : target.Fits c) (count : Nat) (hc : (cut disk target count).Fits c) :
    (cut disk target (count + 1)).Fits c := by
  unfold cut at *
  rw [List.take_add_one, List.foldl_append]
  apply fold_fits _ hc
  intro op hop
  have hm : op ∈ replacement target := by
    cases eq : (replacement target)[count]? with
    | none => simp [eq] at hop
    | some x =>
      simp only [eq, Option.toList_some, List.mem_singleton] at hop
      subst op
      exact List.mem_of_getElem? eq
  exact replacement_bounded ht op hm

theorem pcAt_bounded {c : Config} {length : Nat} (h : length ≤ c.window) (count : Nat) :
    match pcAt length count with
    | .record i _ => i < c.window
    | _ => True := by
  unfold pcAt
  split_ifs <;> try trivial
  omega

/-- Fixed bank addresses admit a finite slot encoding. Bounds apply to live
contents too, including a partially overwritten inactive bank. -/
theorem bank_live_bound {c : Config} {disk : Banks} (h : disk.Fits c) :
    (disk.cells false).items.length + (disk.cells true).items.length ≤ 2 * c.window := by
  have := (h false).1
  have := (h true).1
  omega

def durableAddress (c : Config) := Bool × Fin c.window

def boundedPosition (c : Config) := Fin (c.limit + 1)

theorem fits_position_encoding {c : Config} {s : Snapshot} (h : s.Fits c) :
    ∃ n : boundedPosition c, n.val = s.position := ⟨⟨s.position, by have := h.2; omega⟩, rfl⟩

def outputBound (c : Config) (ctl : Control) : Prop := ctl.output.length ≤ c.window

theorem read_output_bound {c : Config} {s : Snapshot} {a z : Nat} {xs : List Bool}
    (h : s.Fits c) (eq : read s a z = .records xs) : xs.length ≤ c.window := by
  unfold read at eq
  split_ifs at eq; simp_all
  subst xs
  simp only [range, List.length_take, List.length_drop]
  have := h.1
  omega

theorem command_output_bound {c : Config} {s : Service Banks}
    (hs : s.store.root.Fits c) (hc : outputBound c s.control) (cmd : Command) :
    outputBound c (command c (bankOps c) s cmd).2.control := by
  cases cmd
  case release b =>
    cases b <;> simp only [command]
    all_goals repeat' split
    all_goals exact hc
  case scan b =>
    cases b <;> simp only [command]
    all_goals repeat' split
    all_goals exact hc
  case stream b =>
    cases b <;> simp only [command]
    all_goals repeat' split
    all_goals first | exact hc | (change 1 ≤ c.window; have := c.positive; omega)
  all_goals simp only [command]
  all_goals repeat' split
  all_goals first | exact hc | exact Nat.zero_le _ | (apply read_output_bound hs; assumption)

theorem bank_command_fits {c : Config} {s : Service Banks}
    (hs : s.store.Fits c) {h : List Bool} (r : Represents c s.store.root h)
    (cmd : Command) : (command c (bankOps c) s cmd).2.store.Fits c := by
  cases cmd
  case release b =>
    cases b <;> simp only [command]
    all_goals repeat' split
    all_goals exact hs
  case scan b =>
    cases b <;> simp only [command]
    all_goals repeat' split
    all_goals exact hs
  case stream b =>
    cases b <;> simp only [command]
    all_goals repeat' split
    all_goals exact hs
  all_goals simp only [command]
  all_goals repeat' split
  all_goals try exact hs
  all_goals
    apply And.left (b := ((replacement (append c s.store.root _)).foldl primitive ⟨s.store, empty⟩).buffer.Fits c)
    apply fold_fits _ ⟨hs, empty_fits c⟩
    apply replacement_bounded
    apply Represents.fits (append_represents r ?_ _)
    simp_all [bankOps]
    exact of_decide_eq_true (And.right ‹_ ∧ _›)

/-- All changing metadata counters admit the fixed 0..K encoding. The service
uses no per-acquisition generation counter; ownership names are proof-side. -/
def MetaBound (c : Config) (ctl : Control) : Prop :=
  ctl.scanIndex ≤ c.window ∧ ctl.recovering ≤ c.window ∧
  ∀ v, ctl.delayed = some v → v.1 ≤ c.limit

theorem command_meta_bound {c : Config} {s : Service Banks}
    (hs : s.store.root.Fits c) (hc : MetaBound c s.control) (cmd : Command) :
    MetaBound c (command c (bankOps c) s cmd).2.control := by
  have countBound := hs.1
  have positionBound := hs.2
  have item : ∀ i p, s.store.root.items[i]? = some p → i + 1 ≤ c.window := by
    intro i p eq
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp eq
    have := hs.1
    omega
  cases cmd
  case release b =>
    cases b <;> simp only [command]
    all_goals repeat' split
    all_goals simp_all [MetaBound]
  case scan b =>
    cases b <;> simp only [command]
    all_goals repeat' split
    all_goals simp_all [MetaBound, bankOps]
    all_goals (have hb := (List.getElem?_eq_some_iff.mp ‹s.store.root.items[s.control.scanIndex]? = some _›).choose; omega)
  case stream b =>
    cases b <;> simp only [command]
    all_goals repeat' split
    all_goals simp_all [MetaBound, bankOps]
    all_goals (have hb := (List.getElem?_eq_some_iff.mp ‹s.store.root.items[s.control.scanIndex]? = some _›).choose; omega)
  all_goals simp only [command]
  all_goals repeat' split
  all_goals simp_all [MetaBound, bankOps]
  all_goals first | omega | (have hb := (List.getElem?_eq_some_iff.mp ‹s.store.root.items[s.control.recovering]? = some _›).choose; omega)

/-- Allocation counts refer to reserved typed record slots. The target suffix
and write buffer each use at most W; output owns at most W; pending owns one.
The reader borrows selected storage and does not copy a fourth snapshot. -/
def volatileRecords : Machine → Nat
  | .idle s => s.control.output.length + s.control.pending.toList.length
  | .copying cells target ctl _ =>
      target.items.length + cells.buffer.items.length + ctl.output.length + ctl.pending.toList.length

def ResourceInv (c : Config) (m : Machine) : Prop :=
  m.disk.Fits c ∧ outputBound c m.control ∧
  match m with
  | .idle _ => True
  | .copying cells target _ pc => cells.buffer.Fits c ∧ target.Fits c ∧
      match pc with
      | .record i _ => i < c.window
      | _ => True

theorem resource_bound {c : Config} {m : Machine} (h : ResourceInv c m) :
    (m.disk.cells false).items.length + (m.disk.cells true).items.length ≤ 2 * c.window ∧
    volatileRecords m ≤ 3 * c.window + 1 := by
  refine ⟨bank_live_bound h.1, ?_⟩
  cases m with
  | idle s =>
    have out := h.2.1
    dsimp [outputBound, Machine.control] at out
    cases hp : s.control.pending <;> simp [volatileRecords, hp] <;> omega
  | copying cells target ctl pc =>
    have hb := h.2.2.1.1
    have ht := h.2.2.2.1.1
    have out := h.2.1
    dsimp [outputBound, Machine.control] at out
    cases hp : ctl.pending <;> simp [volatileRecords, hp] <;> omega

theorem copyingAt_resources {c : Config} {s : Service Banks} {h : List Bool}
    (disk : s.store.Fits c) (out : outputBound c s.control)
    (r : Represents c s.store.root h) (p : Bool) (room : s.store.root.position < c.limit)
    (count : Nat) : ResourceInv c (copyingAt c s p count) := by
  have ht := (append_represents r room p).fits
  have hc := cut_fits disk ht count
  refine ⟨hc.1, out, hc.2, ht, ?_⟩
  dsimp [copyingAt, pcAt]
  split_ifs with before desc desc'
  · have := ht.1
    omega
  all_goals trivial

theorem resources_preserved {c : Config} {m n : Machine} {event : Label}
    (step : MachineStep c event m n) {a : Service (List Bool)}
    (rel : MachineRelated c m a) (res : ResourceInv c m) : ResourceInv c n := by
  cases step with
  | command notPublish =>
    exact ⟨bank_command_fits res.1 rel.1 _, command_output_bound rel.1.fits res.2.1 _, trivial⟩
  | begin allowed => exact copyingAt_resources res.1 res.2.1 rel.1 _ allowed.2.2.2 0
  | @copy s p count allowed bound =>
    have root := copyingAt_root c s p count (by omega)
    have r : Represents c s.store.root a.store := by rw [← root]; exact rel.1
    have ht := (append_represents r allowed.2.2.2 p).fits
    have cf : (cut s.store (append c s.store.root p) (count + 1)).Fits c :=
      cut_succ_fits ht count ⟨res.1, res.2.2.1⟩
    exact ⟨cf.1, res.2.1, cf.2, ht, pcAt_bounded ht.1 _⟩
  | @publish s p allowed =>
    have r : Represents c s.store.root a.store := by
      simpa only [copyingAt_root _ _ _ _ (le_refl _)] using rel.1
    have ht := (append_represents r allowed.2.2.2 p).fits
    have cf := cut_succ_fits ht (beforePublish (append c s.store.root p)).length
      (And.intro res.1 res.2.2.1)
    have len : (beforePublish (append c s.store.root p)).length + 1 =
        (replacement (append c s.store.root p)).length := by
      simp [beforePublish, replacement]
    rw [len] at cf
    simp only [cut, List.take_length] at cf
    exact ⟨cf.1, res.2.1, trivial⟩
  | crash => exact ⟨res.1, Nat.zero_le _, trivial⟩
  | busy _ _ => exact res
  | fenced _ => exact res
  | view _ => exact res

theorem metadata_preserved {c : Config} {m n : Machine} {event : Label}
    (step : MachineStep c event m n) {a : Service (List Bool)}
    (rel : MachineRelated c m a) (metadata : MetaBound c m.control) : MetaBound c n.control := by
  cases step with
  | command _ => exact command_meta_bound rel.1.fits metadata _
  | begin _ => exact metadata
  | copy _ _ => exact metadata
  | publish _ => exact metadata
  | crash => simp [Machine.control, crashed, MetaBound]
  | busy _ _ => exact metadata
  | fenced _ => exact metadata
  | view _ => exact metadata

def initialBanks : Banks := ⟨fun _ => empty, false⟩
def initialMachine : Machine := .idle ⟨initialBanks, {}⟩
def initialGhost : Service (List Bool) := ⟨[], {}⟩

theorem initial_related (c : Config) : MachineRelated c initialMachine initialGhost :=
  idle_related ⟨represents_empty c, rfl⟩

theorem initial_resources (c : Config) : ResourceInv c initialMachine :=
  ⟨fun _ => empty_fits c, Nat.zero_le _, trivial⟩

theorem initial_metadata (c : Config) : MetaBound c initialMachine.control := by
  simp [initialMachine, Machine.control, MetaBound]

/-- The storage and metadata conclusions hold for every finite execution,
including repeated interrupted copies and recovery crashes. -/
theorem reachable_resources {c : Config} {m : Machine} {events : List Label}
    (run : Execution (MachineStep c) events initialMachine m) :
    ResourceInv c m ∧ MetaBound c m.control := by
  have general : ∀ {start stop : Machine} {es : List Label},
      Execution (MachineStep c) es start stop → ∀ {a}, MachineRelated c start a →
      ResourceInv c start → MetaBound c start.control → ResourceInv c stop ∧ MetaBound c stop.control := by
    intro start stop es steps
    induction steps with
    | nil => intro a rel res metadata; exact ⟨res, metadata⟩
    | cons step tail ih =>
      intro a rel res metadata
      obtain ⟨b, _, rb⟩ := machine_step_refines step rel
      exact ih rb (resources_preserved step rel res) (metadata_preserved step rel metadata)
  exact general run (initial_related c) (initial_resources c) (initial_metadata c)

theorem reachable_bounds {c : Config} {m : Machine} {events : List Label}
    (run : Execution (MachineStep c) events initialMachine m) :
    (m.disk.cells false).items.length + (m.disk.cells true).items.length ≤ 2 * c.window ∧
    volatileRecords m ≤ 3 * c.window + 1 := resource_bound (reachable_resources run).1

end Durability.Retention
