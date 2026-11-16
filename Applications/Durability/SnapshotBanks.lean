import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

/-! Typed paired-bank persistence, independent of payload semantics.
`cut` observes every write/persist/publication boundary, including interrupted
copies. Worker executes that schedule with a finite cursor and no stored
instruction list. Only atomic selector publication changes the durable root. -/
namespace Durability.SnapshotBanks

universe u v

structure Snapshot (H : Type u) (R : Type v) where
  header : H
  items : List R
  deriving DecidableEq, Repr

variable {H : Type u} {R : Type v}

def empty (header : H) : Snapshot H R := ⟨header, []⟩

structure Banks (H : Type u) (R : Type v) where
  cells : Bool → Snapshot H R
  selected : Bool

def Banks.root (d : Banks H R) : Snapshot H R := d.cells d.selected

def Banks.putInactive (d : Banks H R) (v : Snapshot H R) : Banks H R :=
  { d with cells := fun b => if b = !d.selected then v else d.cells b }

@[simp] theorem putInactive_root (d : Banks H R) (v : Snapshot H R) :
    (d.putInactive v).root = d.root := by
  cases hs : d.selected <;> simp [Banks.putInactive, Banks.root, hs]

@[simp] theorem putInactive_target (d : Banks H R) (v : Snapshot H R) :
    (d.putInactive v).cells (!d.selected) = v := by simp [Banks.putInactive]

/-- Record persistence is ordered. A descriptor is persisted only after all
records, then the selector is replaced atomically and durably. -/
inductive Primitive (H : Type u) (R : Type v) where
  | writeRecord (index : Nat) (payload : R)
  | persistRecord (index : Nat) (payload : R)
  | writeHeader (header : H)
  | persistHeader (header : H)
  | publish
  deriving DecidableEq, Repr

/-- The buffer is one bounded staging bank. `record` is a typed cell operation;
no serialization premise is needed for this target. -/
structure CopyState (H : Type u) (R : Type v) where
  disk : Banks H R
  buffer : Snapshot H R

def primitive (s : CopyState H R) : Primitive H R → CopyState H R
  | .writeRecord i p => { s with buffer := { s.buffer with items := s.buffer.items.take i ++ [p] } }
  | .persistRecord i p =>
      let old := s.disk.cells (!s.disk.selected)
      let next := { old with items := old.items.take i ++ [p] }
      { s with disk := s.disk.putInactive next }
  | .writeHeader h => { s with buffer := { s.buffer with header := h } }
  | .persistHeader h =>
      { s with disk := s.disk.putInactive { s.buffer with header := h } }
  | .publish => { s with disk := { s.disk with selected := !s.disk.selected } }

/-- The ordered completion law permits persisting only the exact buffered cell. -/
def Permitted (s : CopyState H R) : Primitive H R → Prop
  | .writeRecord i _ => i ≤ s.buffer.items.length
  | .persistRecord i p => s.buffer.items[i]? = some p
  | .writeHeader _ => True
  | .persistHeader h => s.buffer.header = h ∧
      (s.disk.cells (!s.disk.selected)).items.take s.buffer.items.length = s.buffer.items
  | .publish => s.disk.cells (!s.disk.selected) = s.buffer

/-- Inactive-bank writes cannot damage the selected root. This does not assume
an unbounded used-address set, and holds on every reuse of either bank. -/
theorem primitive_root {s : CopyState H R} {op : Primitive H R} (noPublish : op ≠ .publish) :
    (primitive s op).disk.root = s.disk.root := by
  cases op <;> simp_all [primitive]

theorem publish_root {s : CopyState H R} (persisted : Permitted s .publish) :
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
def recordOps (xs : List R) (i : Nat := 0) : List (Primitive H R) :=
  match xs with
  | [] => []
  | p :: ps => .writeRecord i p :: .persistRecord i p :: recordOps ps (i + 1)

def replacement (target : Snapshot H R) : List (Primitive H R) :=
  recordOps target.items ++ [.writeHeader target.header,
    .persistHeader target.header, .publish]

@[simp] theorem recordOps_length (xs : List R) (i : Nat) :
    (recordOps (H := H) xs i).length = 2 * xs.length := by
  induction xs generalizing i <;> simp_all [recordOps]; omega

theorem replacement_work (target : Snapshot H R) :
    (replacement target).length = 2 * target.items.length + 3 := by
  simp [replacement]

/-- Copying a prefix into a recycled bank overwrites its old contents from slot
zero. At a cut, only the already-persisted prefix is relevant in that bank. -/
def cut (disk : Banks H R) (target : Snapshot H R) (seed : H) (count : Nat) : CopyState H R :=
  (replacement target).take count |>.foldl primitive ⟨disk, empty seed⟩

/-- Every cut before selector replacement has the old committed snapshot. -/
theorem fold_root (s : CopyState H R) (ops : List (Primitive H R))
    (h : ∀ op ∈ ops, op ≠ .publish) :
    (ops.foldl primitive s).disk.root = s.disk.root := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    rw [List.foldl_cons, ih (primitive s op) (by intro x hx; exact h x (by simp [hx]))]
    exact primitive_root (h op (by simp))

theorem recordOps_no_publish (xs : List R) (i : Nat) :
    ∀ op ∈ recordOps (H := H) xs i, op ≠ .publish := by
  induction xs generalizing i with
  | nil => simp [recordOps]
  | cons p ps ih =>
    simp only [recordOps, List.mem_cons]
    intro op h
    rcases h with rfl | rfl | h
    · simp
    · simp
    · exact ih (i + 1) op h

def beforePublish (target : Snapshot H R) : List (Primitive H R) :=
  recordOps target.items ++ [.writeHeader target.header,
    .persistHeader target.header]

theorem beforePublish_no_publish (target : Snapshot H R) :
    ∀ op ∈ beforePublish target, op ≠ .publish := by
  intro op h
  simp only [beforePublish, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | rfl | rfl
  · exact recordOps_no_publish _ _ _ h
  · simp
  · simp

/-- Inductive prefix copy equation. The old inactive contents do not occur on
the right: addresses may be reused for arbitrarily many finite transactions. -/
theorem recordOps_buffer (xs : List R) (s : CopyState H R) (pre : List R)
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

theorem replacement_root (disk : Banks H R) (target : Snapshot H R) (seed : H) :
    ((replacement target).foldl primitive ⟨disk, empty seed⟩).disk.root = target := by
  have hb := recordOps_buffer target.items (⟨disk, empty seed⟩ : CopyState H R) [] rfl
  simp only [List.length_nil, List.nil_append] at hb
  simp only [replacement, List.foldl_append, List.foldl_cons, List.foldl_nil, primitive,
    Banks.root, Banks.putInactive]
  simp only [↓reduceIte]
  cases target
  simp_all

/-- Every operation must satisfy the persistence capability's local rule. -/
def Allowed : CopyState H R → List (Primitive H R) → Prop
  | _, [] => True
  | s, op :: ops => Permitted s op ∧ Allowed (primitive s op) ops

theorem allowed_append (s : CopyState H R) (xs ys : List (Primitive H R)) :
    Allowed s (xs ++ ys) ↔ Allowed s xs ∧ Allowed (xs.foldl primitive s) ys := by
  induction xs generalizing s with
  | nil => simp [Allowed]
  | cons x xs ih => simp [Allowed, ih, and_assoc]

theorem copy_records (xs pre : List R) (s : CopyState H R)
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

theorem replacement_allowed (disk : Banks H R) (target : Snapshot H R) (seed : H) :
    Allowed ⟨disk, empty seed⟩ (replacement target) := by
  have h := copy_records target.items [] (⟨disk, empty seed⟩ : CopyState H R) rfl (by simp)
  simp only [List.length_nil, List.nil_append] at h
  rw [replacement, allowed_append]
  refine ⟨h.1, ?_⟩
  simp only [Allowed, Permitted, primitive]
  refine ⟨trivial, ⟨trivial, ?_⟩, ?_, trivial⟩
  · simpa only [h.2.1] using h.2.2
  · simp [Banks.putInactive]

theorem allowed_suffix {s : CopyState H R} {ops : List (Primitive H R)} (h : Allowed s ops) (n : Nat) :
    Allowed ((ops.take n).foldl primitive s) (ops.drop n) := by
  have eq : ops.take n ++ ops.drop n = ops := List.take_append_drop n ops
  have hh : Allowed s (ops.take n ++ ops.drop n) := by rw [eq]; exact h
  have := (allowed_append s (ops.take n) (ops.drop n)).mp hh
  exact this.2

/-- An actual cut successor is exactly one permitted typed-cell operation. -/
theorem cut_successor (disk : Banks H R) (target : Snapshot H R) (seed : H) (n : Nat)
    (bound : n < (replacement target).length) :
    ∃ op, op = (replacement target)[n] ∧ Permitted (cut disk target seed n) op ∧
      cut disk target seed (n + 1) = primitive (cut disk target seed n) op := by
  refine ⟨(replacement target)[n], rfl, ?_, ?_⟩
  · have h := allowed_suffix (replacement_allowed disk target seed) n
    have eq : (replacement target).drop n = (replacement target)[n] :: (replacement target).drop (n + 1) :=
      List.drop_eq_getElem_cons bound
    rw [eq] at h
    exact h.1
  · unfold cut
    rw [List.take_succ_eq_append_getElem bound]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem before_cut_root (disk : Banks H R) (target : Snapshot H R) (seed : H) (n : Nat) :
    (((beforePublish target).take n).foldl primitive ⟨disk, empty seed⟩).disk.root = disk.root := by
  apply fold_root
  intro op hm
  exact beforePublish_no_publish target op (List.mem_of_mem_take hm)

theorem cut_old_or_new (disk : Banks H R) (target : Snapshot H R) (seed : H) (n : Nat) :
    (cut disk target seed n).disk.root = disk.root ∨ (cut disk target seed n).disk.root = target := by
  by_cases bound : n ≤ (beforePublish target).length
  · left
    have eq : replacement target = beforePublish target ++ [.publish] := by
      simp [replacement, beforePublish, List.append_assoc]
    unfold cut
    rw [eq, List.take_append_of_le_length bound]
    exact before_cut_root disk target seed n
  · right
    have len : (replacement target).length ≤ n := by
      simp [replacement, beforePublish] at bound ⊢
      omega
    simp only [cut, List.take_of_length_le len]
    exact replacement_root disk target seed


/-- The runtime selects one operation by a finite cursor; it never stores the
observer's instruction list. The traversal reads the existing staging records. -/
def scheduleAt (xs : List R) (header : H) (index count : Nat) : Option (Primitive H R) :=
  match xs, count with
  | [], 0 => some (.writeHeader header)
  | [], 1 => some (.persistHeader header)
  | [], 2 => some .publish
  | [], _ => none
  | x :: _, 0 => some (.writeRecord index x)
  | x :: _, 1 => some (.persistRecord index x)
  | _ :: xs, n + 2 => scheduleAt xs header (index + 1) n

theorem scheduleAt_eq (xs : List R) (header : H) (index count : Nat) :
    scheduleAt xs header index count =
      (recordOps xs index ++ [.writeHeader header,.persistHeader header,.publish])[count]? := by
  induction xs generalizing index count with
  | nil => cases count with
    | zero => rfl
    | succ n => cases n with
      | zero => rfl
      | succ n => cases n <;> rfl
  | cons x xs ih => cases count with
    | zero => rfl
    | succ n => cases n with
      | zero => rfl
      | succ n => simpa [scheduleAt,recordOps] using ih (index + 1) n

def operationAt (target : Snapshot H R) (count : Nat) : Option (Primitive H R) :=
  scheduleAt target.items target.header 0 count

theorem operationAt_eq (target : Snapshot H R) (count : Nat) :
    operationAt target count = (replacement target)[count]? :=
  scheduleAt_eq _ _ _ _

/-- Two persistent banks, one staging target, one recovery/copy buffer. The
cursor is finite and no full operation trace belongs to this runtime state. -/
structure Worker (H : Type u) (R : Type v) where
  state : CopyState H R
  target : Snapshot H R
  cursor : Fin (2 * target.items.length + 4)

variable (seed : H)

def begin (disk : Banks H R) (target : Snapshot H R) : Worker H R :=
  ⟨⟨disk,empty seed⟩, target, ⟨0, by omega⟩⟩

def Worker.busy (w : Worker H R) : Bool := w.cursor.val < 2 * w.target.items.length + 3

def Worker.progress (w : Worker H R) : Worker H R × Bool :=
  if h : w.cursor.val < 2 * w.target.items.length + 3 then
    match operationAt w.target w.cursor.val with
    | none => (w,false)
    | some op =>
      (⟨primitive w.state op,w.target,⟨w.cursor.val + 1,by omega⟩⟩,
        match op with | .publish => true | _ => false)
  else (w,false)

/-- Proof-side cut characterization; the starting disk is not retained by Worker. -/
def Worker.AtCut (w : Worker H R) (start : Banks H R) (seed : H) : Prop :=
  w.state = cut start w.target seed w.cursor.val

theorem begin_atCut (disk : Banks H R) (target : Snapshot H R) :
    (begin seed disk target).AtCut disk seed := rfl


theorem Worker.progress_target (w : Worker H R) : w.progress.1.target = w.target := by
  unfold Worker.progress
  split
  · split <;> rfl
  · rfl

theorem Worker.progress_atCut (w : Worker H R) (start : Banks H R)
    (hcut : w.AtCut start seed) : w.progress.1.AtCut start seed := by
  unfold Worker.progress
  split
  · rename_i h
    have hl : w.cursor.val < (replacement w.target).length := by
      rw [replacement_work]; exact h
    rw [operationAt_eq,List.getElem?_eq_getElem hl]
    obtain ⟨op,hop,_,hc⟩ := cut_successor start w.target seed w.cursor.val hl
    subst op
    simp only [Worker.AtCut] at hcut ⊢
    rw [hcut]
    exact hc.symm
  · exact hcut

theorem Worker.root_old_or_new (w : Worker H R) (start : Banks H R)
    (hcut : w.AtCut start seed) : w.state.disk.root = start.root ∨
      w.state.disk.root = w.target := by
  rw [Worker.AtCut] at hcut
  rw [hcut]
  exact cut_old_or_new start w.target seed w.cursor.val


/-- Payload bounds remain caller properties, independent of persistence laws. -/
def Snapshot.Bounded (hb : H → Prop) (rb : R → Prop) (capacity : Nat)
    (s : Snapshot H R) : Prop :=
  hb s.header ∧ s.items.length ≤ capacity ∧ ∀ r ∈ s.items, rb r

def CopyState.Bounded (hb : H → Prop) (rb : R → Prop) (capacity : Nat)
    (s : CopyState H R) : Prop :=
  (∀ bank, (s.disk.cells bank).Bounded hb rb capacity) ∧ s.buffer.Bounded hb rb capacity

def Primitive.Bounded (hb : H → Prop) (rb : R → Prop) (capacity : Nat) : Primitive H R → Prop
  | .writeRecord i r | .persistRecord i r => i < capacity ∧ rb r
  | .writeHeader h | .persistHeader h => hb h
  | .publish => True

theorem primitive_bounded (hb : H → Prop) (rb : R → Prop) (capacity : Nat)
    (s : CopyState H R) (op : Primitive H R) (hs : s.Bounded hb rb capacity)
    (ho : op.Bounded hb rb capacity) : (primitive s op).Bounded hb rb capacity := by
  have replace (v : Snapshot H R) (i : Nat) (r : R)
      (hv : v.Bounded hb rb capacity) (hi : i < capacity) (hr : rb r) :
      ({v with items := v.items.take i ++ [r]} : Snapshot H R).Bounded hb rb capacity := by
    refine ⟨hv.1,?_,?_⟩
    · simp only [List.length_append,List.length_take,List.length_singleton]; omega
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hv.2.2 x (List.mem_of_mem_take hx)
      · simpa using (List.mem_singleton.mp hx ▸ hr)
  cases op with
  | writeRecord i r => exact ⟨hs.1,replace _ _ _ hs.2 ho.1 ho.2⟩
  | persistRecord i r =>
    refine ⟨?_,hs.2⟩
    intro bank
    simp only [primitive,Banks.putInactive]
    split
    · exact replace _ _ _ (hs.1 _) ho.1 ho.2
    · exact hs.1 bank
  | writeHeader h => exact ⟨hs.1,ho,hs.2.2⟩
  | persistHeader h =>
    refine ⟨?_,hs.2⟩
    intro bank
    simp only [primitive,Banks.putInactive]
    split
    · exact ⟨ho,hs.2.2⟩
    · exact hs.1 bank
  | publish => exact hs

theorem scheduleAt_bounded (hb : H → Prop) (rb : R → Prop) (capacity : Nat)
    (xs : List R) (header : H) (index count : Nat) (op : Primitive H R)
    (hh : hb header) (hr : ∀ r ∈ xs,rb r) (hi : index + xs.length ≤ capacity)
    (ho : scheduleAt xs header index count = some op) : op.Bounded hb rb capacity := by
  induction xs generalizing index count with
  | nil =>
    cases count with
    | zero => cases ho; exact hh
    | succ n => cases n with
      | zero => cases ho; exact hh
      | succ n => cases n with
        | zero => cases ho; trivial
        | succ n => simp [scheduleAt] at ho
  | cons x xs ih =>
    cases count with
    | zero => cases ho; exact ⟨by simp at hi; omega,hr x (by simp)⟩
    | succ n => cases n with
      | zero => cases ho; exact ⟨by simp at hi; omega,hr x (by simp)⟩
      | succ n =>
        exact ih (index + 1) n (fun r h => hr r (by simp [h]))
          (by simp at hi; omega) ho

def Worker.Bounded (hb : H → Prop) (rb : R → Prop) (capacity : Nat)
    (w : Worker H R) : Prop :=
  w.state.Bounded hb rb capacity ∧ w.target.Bounded hb rb capacity

theorem Worker.progress_bounded (hb : H → Prop) (rb : R → Prop) (capacity : Nat)
    (w : Worker H R) (hw : w.Bounded hb rb capacity) :
    w.progress.1.Bounded hb rb capacity := by
  unfold Worker.progress
  split
  · split
    · exact hw
    · rename_i op hop
      exact ⟨primitive_bounded hb rb capacity w.state op hw.1
        (scheduleAt_bounded hb rb capacity w.target.items w.target.header 0 w.cursor.val op
          hw.2.1 hw.2.2.2 (by simpa using hw.2.2.1) hop),hw.2⟩
  · exact hw


theorem begin_bounded (hb : H → Prop) (rb : R → Prop) (capacity : Nat)
    (disk : Banks H R) (target : Snapshot H R) (hs : hb seed)
    (hd : ∀ bank,(disk.cells bank).Bounded hb rb capacity)
    (ht : target.Bounded hb rb capacity) : (begin seed disk target).Bounded hb rb capacity := by
  exact ⟨⟨hd,hs,Nat.zero_le _,by intro r hr; exact False.elim (List.not_mem_nil hr)⟩,ht⟩


theorem scheduleAt_publish (xs : List R) (header : H) (index count : Nat) :
    scheduleAt xs header index count = some .publish ↔ count = 2 * xs.length + 2 := by
  induction xs generalizing index count with
  | nil => cases count with
    | zero => simp [scheduleAt]
    | succ n => cases n with
      | zero => simp [scheduleAt]
      | succ n => cases n <;> simp [scheduleAt]
  | cons x xs ih => cases count with
    | zero => simp [scheduleAt]
    | succ n => cases n with
      | zero => simp [scheduleAt]
      | succ n => rw [scheduleAt,ih]; simp; omega

theorem Worker.progress_stutters (w : Worker H R) (h : w.progress.2 = false) :
    w.progress.1.state.disk.root = w.state.disk.root := by
  unfold Worker.progress at h ⊢
  split
  · split
    · rfl
    · rename_i op hop
      apply primitive_root
      intro eq
      subst op
      simp_all
  · rfl

theorem Worker.progress_publishes (w : Worker H R) (start : Banks H R)
    (hc : w.AtCut start seed) (h : w.progress.2 = true) :
    w.progress.1.state.disk.root = w.target := by
  have hn := Worker.progress_atCut seed w start hc
  unfold Worker.progress at h hn ⊢
  split
  · split
    · simp_all
    · rename_i op hop
      cases op <;> simp_all
      have n := (scheduleAt_publish w.target.items w.target.header 0 w.cursor.val).mp hop
      simp only [Worker.AtCut] at hn
      rw [hn]
      have len : (replacement w.target).length ≤ w.cursor.val + 1 := by
        rw [replacement_work]; omega
      simp only [cut,List.take_of_length_le len]
      exact replacement_root start w.target seed
  · simp_all


end Durability.SnapshotBanks
