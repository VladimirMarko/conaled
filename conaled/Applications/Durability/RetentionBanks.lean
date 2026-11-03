import Applications.Durability.Retention

/-! Two reusable typed banks. A transaction has a fixed finite list of writes.
`cut` exposes every write/persist/publication boundary, including interrupted
copies. The atomic selector is the only step that changes the durable root. -/
namespace Durability.Retention

structure Banks where
  cells : Bool → Snapshot
  selected : Bool

def Banks.root (d : Banks) : Snapshot := d.cells d.selected

def Banks.putInactive (d : Banks) (v : Snapshot) : Banks :=
  { d with cells := fun b => if b = !d.selected then v else d.cells b }

@[simp] theorem putInactive_root (d : Banks) (v : Snapshot) :
    (d.putInactive v).root = d.root := by
  cases hs : d.selected <;> simp [Banks.putInactive, Banks.root, hs]

@[simp] theorem putInactive_target (d : Banks) (v : Snapshot) :
    (d.putInactive v).cells (!d.selected) = v := by simp [Banks.putInactive]

/-- Record persistence is ordered. A descriptor is persisted only after all
records, then the selector is replaced atomically and durably. -/
inductive Primitive where
  | writeRecord (index : Nat) (payload : Bool)
  | persistRecord (index : Nat) (payload : Bool)
  | writeDescriptor (position : Nat) (pastParity : Bool)
  | persistDescriptor (position : Nat) (pastParity : Bool)
  | publish
  deriving DecidableEq, Repr

/-- The buffer is one bounded staging bank. `record` is a typed cell operation;
no serialization premise is needed for this target. -/
structure CopyState where
  disk : Banks
  buffer : Snapshot

def primitive (s : CopyState) : Primitive → CopyState
  | .writeRecord i p => { s with buffer := { s.buffer with items := s.buffer.items.take i ++ [p] } }
  | .persistRecord i p =>
      let old := s.disk.cells (!s.disk.selected)
      let next := { old with items := old.items.take i ++ [p] }
      { s with disk := s.disk.putInactive next }
  | .writeDescriptor n b => { s with buffer := { s.buffer with position := n, pastParity := b } }
  | .persistDescriptor n b =>
      { s with disk := s.disk.putInactive { s.buffer with position := n, pastParity := b } }
  | .publish => { s with disk := { s.disk with selected := !s.disk.selected } }

/-- The ordered completion law permits persisting only the exact buffered cell. -/
def Permitted (s : CopyState) : Primitive → Prop
  | .writeRecord i _ => i ≤ s.buffer.items.length
  | .persistRecord i p => s.buffer.items[i]? = some p
  | .writeDescriptor _ _ => True
  | .persistDescriptor n b => s.buffer.position = n ∧ s.buffer.pastParity = b ∧
      (s.disk.cells (!s.disk.selected)).items.take s.buffer.items.length = s.buffer.items
  | .publish => s.disk.cells (!s.disk.selected) = s.buffer

/-- Inactive-bank writes cannot damage the selected root. This does not assume
an unbounded used-address set, and holds on every reuse of either bank. -/
theorem primitive_root {s : CopyState} {op : Primitive} (noPublish : op ≠ .publish) :
    (primitive s op).disk.root = s.disk.root := by
  cases op <;> simp_all [primitive]

theorem publish_root {s : CopyState} (persisted : Permitted s .publish) :
    (primitive s .publish).disk.root = s.buffer := persisted

/-- No active reader, recovery cursor, or obsolete plan may cross a mutation
boundary. These are target/driver obligations, separate from cell persistence. -/
structure Access where
  reader : Option Bool
  cursor : Option Bool
  plan : Option Bool
  deriving DecidableEq, Repr

def Access.mutation (selected : Bool) : Access := ⟨none, none, some (!selected)⟩

def Access.safeOverwrite (a : Access) (bank : Bool) : Prop :=
  a.reader ≠ some bank ∧ a.cursor ≠ some bank ∧
  (a.plan = none ∨ a.plan = some bank)

theorem mutation_safe (selected : Bool) :
    (Access.mutation selected).safeOverwrite (!selected) ∧ selected ≠ !selected := by
  cases selected <;> simp [Access.mutation, Access.safeOverwrite]

/-- A plan contains no pointers to the retired bank after publication. Crash
cancels the plan; a restarted process constructs a new one from the selector. -/
def Access.afterPublication : Access := ⟨none, none, none⟩

theorem retired_safe (selected : Bool) :
    Access.afterPublication.safeOverwrite selected := by
  simp [Access.afterPublication, Access.safeOverwrite]

/-- Concrete paired write/persist operations, one pair per retained record. -/
def recordOps (xs : List Bool) (i : Nat := 0) : List Primitive :=
  match xs with
  | [] => []
  | p :: ps => .writeRecord i p :: .persistRecord i p :: recordOps ps (i + 1)

def replacement (target : Snapshot) : List Primitive :=
  recordOps target.items ++ [.writeDescriptor target.position target.pastParity,
    .persistDescriptor target.position target.pastParity, .publish]

@[simp] theorem recordOps_length (xs : List Bool) (i : Nat) :
    (recordOps xs i).length = 2 * xs.length := by
  induction xs generalizing i <;> simp_all [recordOps]; omega

theorem replacement_work (target : Snapshot) :
    (replacement target).length = 2 * target.items.length + 3 := by
  simp [replacement]

/-- Copying a prefix into a recycled bank overwrites its old contents from slot
zero. At a cut, only the already-persisted prefix is relevant in that bank. -/
def cut (disk : Banks) (target : Snapshot) (count : Nat) : CopyState :=
  (replacement target).take count |>.foldl primitive ⟨disk, empty⟩

/-- Every cut before selector replacement has the old committed snapshot. -/
theorem fold_root (s : CopyState) (ops : List Primitive)
    (h : ∀ op ∈ ops, op ≠ .publish) :
    (ops.foldl primitive s).disk.root = s.disk.root := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    rw [List.foldl_cons, ih (primitive s op) (by intro x hx; exact h x (by simp [hx]))]
    exact primitive_root (h op (by simp))

theorem recordOps_no_publish (xs : List Bool) (i : Nat) :
    ∀ op ∈ recordOps xs i, op ≠ .publish := by
  induction xs generalizing i with
  | nil => simp [recordOps]
  | cons p ps ih =>
    simp only [recordOps, List.mem_cons]
    intro op h
    rcases h with rfl | rfl | h
    · simp
    · simp
    · exact ih (i + 1) op h

def beforePublish (target : Snapshot) : List Primitive :=
  recordOps target.items ++ [.writeDescriptor target.position target.pastParity,
    .persistDescriptor target.position target.pastParity]

theorem beforePublish_no_publish (target : Snapshot) :
    ∀ op ∈ beforePublish target, op ≠ .publish := by
  intro op h
  simp only [beforePublish, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | rfl | rfl
  · exact recordOps_no_publish _ _ _ h
  · simp
  · simp

/-- Inductive prefix copy equation. The old inactive contents do not occur on
the right: addresses may be reused for arbitrarily many finite transactions. -/
theorem recordOps_buffer (xs : List Bool) (s : CopyState) (pre : List Bool)
    (hb : s.buffer.items = pre) :
    ((recordOps xs pre.length).foldl primitive s).buffer.items = pre ++ xs := by
  induction xs generalizing s pre with
  | nil => simpa [recordOps] using hb
  | cons p ps ih =>
    simp only [recordOps, List.foldl_cons]
    have one : (primitive (primitive s (.writeRecord pre.length p))
      (.persistRecord pre.length p)).buffer.items = pre ++ [p] := by
      simp [primitive, hb]
    have eq := ih _ (pre ++ [p]) one
    simpa [List.length_append, List.append_assoc] using eq

theorem replacement_root (disk : Banks) (target : Snapshot) :
    ((replacement target).foldl primitive ⟨disk, empty⟩).disk.root = target := by
  have hb := recordOps_buffer target.items (⟨disk, empty⟩ : CopyState) [] rfl
  simp only [List.length_nil, List.nil_append] at hb
  simp only [replacement, List.foldl_append, List.foldl_cons, List.foldl_nil, primitive,
    Banks.root, Banks.putInactive]
  simp only [↓reduceIte]
  cases target
  simp_all

/-- Every operation must satisfy the persistence capability's local rule. -/
def Allowed : CopyState → List Primitive → Prop
  | _, [] => True
  | s, op :: ops => Permitted s op ∧ Allowed (primitive s op) ops

theorem allowed_append (s : CopyState) (xs ys : List Primitive) :
    Allowed s (xs ++ ys) ↔ Allowed s xs ∧ Allowed (xs.foldl primitive s) ys := by
  induction xs generalizing s with
  | nil => simp [Allowed]
  | cons x xs ih => simp [Allowed, ih, and_assoc]

theorem copy_records (xs pre : List Bool) (s : CopyState)
    (hb : s.buffer.items = pre)
    (hd : (s.disk.cells (!s.disk.selected)).items.take pre.length = pre) :
    Allowed s (recordOps xs pre.length) ∧
    ((recordOps xs pre.length).foldl primitive s).buffer.items = pre ++ xs ∧
    (((recordOps xs pre.length).foldl primitive s).disk.cells
      (!((recordOps xs pre.length).foldl primitive s).disk.selected)).items.take
      (pre ++ xs).length = pre ++ xs := by
  induction xs generalizing pre s with
  | nil => simpa [Allowed, recordOps] using And.intro trivial (And.intro hb hd)
  | cons p ps ih =>
    let t := primitive (primitive s (.writeRecord pre.length p)) (.persistRecord pre.length p)
    have tb : t.buffer.items = pre ++ [p] := by simp [t, primitive, hb]
    have td : (t.disk.cells (!t.disk.selected)).items = pre ++ [p] := by
      simp [t, primitive, Banks.putInactive, hd]
    have next := ih (pre ++ [p]) t tb (by rw [td]; simp)
    refine ⟨?_, ?_, ?_⟩
    · simp only [recordOps, Allowed]
      refine ⟨by simp [Permitted, hb], ?_, ?_⟩
      · simp [Permitted, primitive, hb]
      · simpa only [List.length_append, List.length_singleton] using next.1
    · simpa [recordOps, List.append_assoc, t] using next.2.1
    · simpa [recordOps, List.append_assoc, t] using next.2.2

theorem replacement_allowed (disk : Banks) (target : Snapshot) :
    Allowed ⟨disk, empty⟩ (replacement target) := by
  have h := copy_records target.items [] (⟨disk, empty⟩ : CopyState) rfl (by simp)
  simp only [List.length_nil, List.nil_append] at h
  rw [replacement, allowed_append]
  refine ⟨h.1, ?_⟩
  simp only [Allowed, Permitted, primitive]
  refine ⟨trivial, ⟨trivial, trivial, ?_⟩, ?_, trivial⟩
  · simpa only [h.2.1] using h.2.2
  · simp [Banks.putInactive]

theorem allowed_suffix {s : CopyState} {ops : List Primitive} (h : Allowed s ops) (n : Nat) :
    Allowed ((ops.take n).foldl primitive s) (ops.drop n) := by
  have eq : ops.take n ++ ops.drop n = ops := List.take_append_drop n ops
  have hh : Allowed s (ops.take n ++ ops.drop n) := by rw [eq]; exact h
  have := (allowed_append s (ops.take n) (ops.drop n)).mp hh
  exact this.2

/-- An actual cut successor is exactly one permitted typed-cell operation. -/
theorem cut_successor (disk : Banks) (target : Snapshot) (n : Nat)
    (bound : n < (replacement target).length) :
    ∃ op, op = (replacement target)[n] ∧ Permitted (cut disk target n) op ∧
      cut disk target (n + 1) = primitive (cut disk target n) op := by
  refine ⟨(replacement target)[n], rfl, ?_, ?_⟩
  · have h := allowed_suffix (replacement_allowed disk target) n
    have eq : (replacement target).drop n = (replacement target)[n] :: (replacement target).drop (n + 1) :=
      List.drop_eq_getElem_cons bound
    rw [eq] at h
    exact h.1
  · unfold cut
    rw [List.take_succ_eq_append_getElem bound]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem before_cut_root (disk : Banks) (target : Snapshot) (n : Nat) :
    (((beforePublish target).take n).foldl primitive ⟨disk, empty⟩).disk.root = disk.root := by
  apply fold_root
  intro op hm
  exact beforePublish_no_publish target op (List.mem_of_mem_take hm)

theorem cut_old_or_new (disk : Banks) (target : Snapshot) (n : Nat) :
    (cut disk target n).disk.root = disk.root ∨ (cut disk target n).disk.root = target := by
  by_cases bound : n ≤ (beforePublish target).length
  · left
    have eq : replacement target = beforePublish target ++ [.publish] := by
      simp [replacement, beforePublish, List.append_assoc]
    unfold cut
    rw [eq, List.take_append_of_le_length bound]
    exact before_cut_root disk target n
  · right
    have len : (replacement target).length ≤ n := by
      simp [replacement, beforePublish] at bound ⊢
      omega
    simp only [cut, List.take_of_length_le len]
    exact replacement_root disk target

/-- Every crash cut refines either no commit or one append. There is no torn
combination of boundary, payload suffix and cumulative parity. -/
theorem crash_cut_refines {c : Config} {disk : Banks} {h : List Bool}
    (r : Represents c disk.root h) (room : disk.root.position < c.limit)
    (p : Bool) (n : Nat) :
    Represents c (cut disk (append c disk.root p) n).disk.root h ∨
    Represents c (cut disk (append c disk.root p) n).disk.root (h ++ [p]) := by
  rcases cut_old_or_new disk (append c disk.root p) n with old | new
  · left
    rw [old]
    exact r
  · rw [new]
    exact Or.inr (append_represents r room p)

/-- Crash erases volatile copy state and preserves the disk. Recovery only reads
selected cells, so crashing during recovery has exactly the same durable root. -/
def restart (disk : Banks) : CopyState := ⟨disk, empty⟩

@[simp] theorem restart_root (disk : Banks) : (restart disk).disk.root = disk.root := rfl

/-- A fixed layout reserves both banks, including all interrupted copies. -/
def durableRecordSlots (c : Config) := 2 * c.window

def durableMetadataSlots : Nat := 3

theorem fixed_layout (c : Config) : durableRecordSlots c = 2 * c.window ∧
    durableMetadataSlots = 2 + 1 := ⟨rfl, rfl⟩

end Durability.Retention
