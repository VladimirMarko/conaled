import SquareKit.InteractionContracts
import Mathlib.Data.List.Nodup

/-!
# Immutable retained cells for the accepted-history experiment

Experimental semantic model for #240. Atomic durable roots and stable immutable
cells are target capabilities, not claims about a filesystem or ordinary RAM.
-/
namespace Durability

abbrev Heap (C : Type) := Nat → Option C

def Extends {C : Type} (a b : Heap C) : Prop :=
  ∀ i c, a i = some c → b i = some c

theorem Extends.refl {C : Type} (a : Heap C) : Extends a a := fun _ _ h => h

theorem Extends.trans {C : Type} {a b c : Heap C}
    (h : Extends a b) (k : Extends b c) : Extends a c :=
  fun i x hx => k i x (h i x hx)

def put {C : Type} (s : Heap C) (a : Nat) (c : C) : Heap C :=
  fun i => if i = a then some c else s i

theorem extends_put {C : Type} (s : Heap C) (a : Nat) (c : C)
    (fresh : s a = none) : Extends s (put s a c) := by
  intro i x hx
  by_cases h : i = a
  · subst i; simp [fresh] at hx
  · simp [put, h, hx]

structure Record (P : Type) where
  session : Nat
  id : Nat
  payload : P
  deriving DecidableEq

def Record.key {P : Type} (r : Record P) : Nat × Nat := (r.session, r.id)

inductive Cell (P : Type) where
  | node (previous : Option Nat) (record : Record P)
  | flat (record : Record P)
  | index (addresses : List Nat)
  deriving DecidableEq

structure Root where
  checkpoint : Option Nat
  tail : Option Nat
  deriving DecidableEq

def emptyRoot : Root := ⟨none, none⟩

inductive Chain {P : Type} (s : Heap (Cell P)) : Option Nat → List (Record P) → Prop
  | nil : Chain s none []
  | snoc {a prev h e} : s a = some (.node prev e) → Chain s prev h →
      Chain s (some a) (h ++ [e])

inductive Array {P : Type} (s : Heap (Cell P)) : List Nat → List (Record P) → Prop
  | nil : Array s [] []
  | cons {a as e es} : s a = some (.flat e) → Array s as es →
      Array s (a :: as) (e :: es)

inductive Prefix {P : Type} (s : Heap (Cell P)) : Option Nat → List (Record P) → Prop
  | nil : Prefix s none []
  | block {a as h} : s a = some (.index as) → Array s as h → Prefix s (some a) h

/-- The two layouts share a root protocol. A log has no prefix block;
a checkpoint has a flat prefix and an independent linked suffix. -/
def Represents {P : Type} (s : Heap (Cell P)) (root : Root) (h : List (Record P)) : Prop :=
  ∃ pre tail, Prefix s root.checkpoint pre ∧ Chain s root.tail tail ∧ h = pre ++ tail

theorem Chain.mono {P : Type} {s t : Heap (Cell P)} (ext : Extends s t)
    {r h} (rep : Chain s r h) : Chain t r h := by
  induction rep with
  | nil => exact .nil
  | snoc lookup _ ih => exact .snoc (ext _ _ lookup) ih

theorem Array.mono {P : Type} {s t : Heap (Cell P)} (ext : Extends s t)
    {r h} (rep : Array s r h) : Array t r h := by
  induction rep with
  | nil => exact .nil
  | cons lookup _ ih => exact .cons (ext _ _ lookup) ih

theorem Prefix.mono {P : Type} {s t : Heap (Cell P)} (ext : Extends s t)
    {r h} (rep : Prefix s r h) : Prefix t r h := by
  cases rep with
  | nil => exact .nil
  | block lookup arr => exact .block (ext _ _ lookup) (arr.mono ext)

theorem Represents.mono {P : Type} {s t : Heap (Cell P)} (ext : Extends s t)
    {r h} (rep : Represents s r h) : Represents t r h := by
  obtain ⟨pre, tail, hp, ht, eq⟩ := rep
  exact ⟨pre, tail, hp.mono ext, ht.mono ext, eq⟩

theorem Chain.unique {P : Type} {s : Heap (Cell P)} {r h k}
    (a : Chain s r h) (b : Chain s r k) : h = k := by
  induction a generalizing k with
  | nil => cases b; rfl
  | snoc ha _ ih =>
    cases b with
    | snoc hb hb' =>
      have eq := ha.symm.trans hb
      cases eq
      rw [ih hb']

theorem Array.unique {P : Type} {s : Heap (Cell P)} {r h k}
    (a : Array s r h) (b : Array s r k) : h = k := by
  induction a generalizing k with
  | nil => cases b; rfl
  | cons ha _ ih =>
    cases b with
    | cons hb hb' =>
      have eq := ha.symm.trans hb
      cases eq
      rw [ih hb']

theorem Prefix.unique {P : Type} {s : Heap (Cell P)} {r h k}
    (a : Prefix s r h) (b : Prefix s r k) : h = k := by
  cases a with
  | nil => cases b; rfl
  | block ha arr =>
    cases b with
    | block hb arr' =>
      have eq := ha.symm.trans hb
      cases eq
      exact arr.unique arr'

theorem Represents.unique {P : Type} {s : Heap (Cell P)} {r h k}
    (a : Represents s r h) (b : Represents s r k) : h = k := by
  obtain ⟨p, t, hp, ht, rfl⟩ := a
  obtain ⟨q, u, hq, hu, rfl⟩ := b
  rw [hp.unique hq, ht.unique hu]

theorem empty_rep {P : Type} (s : Heap (Cell P)) : Represents s emptyRoot [] :=
  ⟨[], [], .nil, .nil, rfl⟩

/-- Append changes only the independent suffix. The prefix is not traversed by
suffix nodes, so later checkpoint reclamation cannot leave hidden links. -/
theorem append_rep {P : Type} {s : Heap (Cell P)} {r h}
    (rep : Represents s r h) (a : Nat) (e : Record P) (fresh : s a = none) :
    Represents (put s a (.node r.tail e)) ⟨r.checkpoint, some a⟩ (h ++ [e]) := by
  obtain ⟨p, t, hp, ht, rfl⟩ := rep
  have ext := extends_put s a (.node r.tail e) fresh
  exact ⟨p, t ++ [e], hp.mono ext,
    .snoc (by simp [put]) (ht.mono ext), by simp [List.append_assoc]⟩

/-- Fresh sequential addresses for a full ordered checkpoint. -/
def addresses (start : Nat) (h : List (Record P)) : List Nat :=
  List.range' start h.length

def copy (start : Nat) (h : List (Record P)) (s : Heap (Cell P)) : Heap (Cell P) :=
  match h with
  | [] => s
  | e :: es => put (copy (start + 1) es s) start (.flat e)

theorem copy_outside {P : Type} (h : List (Record P)) (s : Heap (Cell P))
    (start i : Nat) (outside : i < start ∨ start + h.length ≤ i) :
    copy start h s i = s i := by
  induction h generalizing start with
  | nil => rfl
  | cons e es ih =>
    have ne : i ≠ start := by simp only [List.length_cons] at outside; omega
    simp only [copy, put, ite_eq_right ne]
    apply ih
    simp only [List.length_cons] at outside
    omega

theorem Array.congr {P : Type} {s t : Heap (Cell P)} {as h}
    (rep : Array s as h) (eq : ∀ a ∈ as, t a = s a) : Array t as h := by
  induction rep with
  | nil => exact .nil
  | cons ha rest ih =>
    exact .cons ((eq _ (by simp)).trans ha)
      (ih (fun a mem => eq a (by simp [mem])))

theorem copy_array {P : Type} (h : List (Record P)) (s : Heap (Cell P)) (start : Nat) :
    Array (copy start h s) (addresses start h) h := by
  induction h generalizing start with
  | nil => exact .nil
  | cons e es ih =>
    simp only [addresses, List.length_cons, List.range'_succ, copy]
    apply Array.cons (by simp [put])
    apply (ih (start + 1)).congr
    intro a mem
    obtain ⟨j, hj, heq⟩ := List.mem_range'.mp mem
    simp only [Nat.one_mul] at heq
    have ne : a ≠ start := by omega
    simp [put, ne]

theorem Array.lookup {P : Type} {s : Heap (Cell P)} {as h}
    (arr : Array s as h) {a} (mem : a ∈ as) : ∃ e, s a = some (.flat e) := by
  induction arr with
  | nil => simp at mem
  | cons ha rest ih =>
    simp only [List.mem_cons] at mem
    rcases mem with rfl | mem
    · exact ⟨_, ha⟩
    · exact ih mem

inductive LinkNeeds {P : Type} (s : Heap (Cell P)) : Option Nat → Nat → Prop
  | here {a} : LinkNeeds s (some a) a
  | next {tip prev e a} : s tip = some (.node prev e) → LinkNeeds s prev a →
      LinkNeeds s (some tip) a

def RootNeeds {P : Type} (s : Heap (Cell P)) (r : Root) (a : Nat) : Prop :=
  (∃ i, r.checkpoint = some i ∧ (a = i ∨ ∃ as, s i = some (.index as) ∧ a ∈ as)) ∨
    LinkNeeds s r.tail a

/-- Reclamation inspects pointer reachability, not equality to a desired history. -/
def KeepsRoot {P : Type} (s t : Heap (Cell P)) (r : Root) : Prop :=
  ∀ a c, RootNeeds s r a → s a = some c → t a = some c

theorem Chain.keep {P : Type} {s t : Heap (Cell P)} {tip h}
    (rep : Chain s tip h)
    (keep : ∀ a c, LinkNeeds s tip a → s a = some c → t a = some c) : Chain t tip h := by
  induction rep with
  | nil => exact .nil
  | snoc lookup prev ih =>
    exact .snoc (keep _ _ .here lookup)
      (ih (fun a c needed found => keep a c (.next lookup needed) found))

theorem Represents.keep {P : Type} {s t : Heap (Cell P)} {r h}
    (rep : Represents s r h) (keep : KeepsRoot s t r) : Represents t r h := by
  obtain ⟨pre, tail, hp, ht, rfl⟩ := rep
  refine ⟨pre, tail, ?_, ht.keep (fun a c needed found => keep a c (Or.inr needed) found), rfl⟩
  cases r with
  | mk cp tip =>
    cases hp with
    | nil => exact .nil
    | @block i as h lookup ar =>
      apply Prefix.block (as := as) (keep i _ (Or.inl ⟨i, rfl, Or.inl rfl⟩) lookup)
      apply ar.congr
      intro a mem
      obtain ⟨e, he⟩ := ar.lookup mem
      exact (keep a _ (Or.inl ⟨i, rfl, Or.inr ⟨as, lookup, mem⟩⟩) he).trans he.symm

def overlay {C : Type} (new old : Heap C) : Heap C := fun a =>
  match new a with
  | some c => some c
  | none => old a

theorem overlay_extends {C : Type} {new old target : Heap C}
    (hn : Extends new target) (ho : Extends old target) :
    Extends (overlay new old) target := by
  intro a c hc
  cases eq : new a with
  | none => exact ho a c (by simpa [overlay, eq] using hc)
  | some d =>
    have : d = c := by simpa [overlay, eq] using hc
    subst d
    exact hn a c eq

/-- A layout construction certificate, discharged by the concrete builders below.
It says nothing about when a protocol may publish this root. -/
structure Plan (P : Type) where
  source : Heap (Cell P)
  writes : Heap (Cell P)
  root : Root
  before : List (Record P)
  appended : Option (Record P)
  after : List (Record P)
  shape : after = before ++ appended.toList
  valid : Represents (overlay writes source) root after

/-- The one new linked node is a real storage object. -/
def appendPlan {P : Type} (s : Heap (Cell P)) (r : Root) (h : List (Record P))
    (rep : Represents s r h) (a : Nat) (e : Record P) (fresh : s a = none) : Plan P where
  source := s
  writes := put (fun _ => none) a (.node r.tail e)
  root := ⟨r.checkpoint, some a⟩
  before := h
  appended := some e
  after := h ++ [e]
  shape := rfl
  valid := by
    have eq : overlay (put (fun _ => none) a (.node r.tail e)) s =
        put s a (.node r.tail e) := by
      funext i; by_cases hi : i = a <;> simp [overlay, put, hi]
    rw [eq]
    exact append_rep rep a e fresh

/-- A full-prefix checkpoint has no suffix. Later appends start a disjoint chain.
All record cells and the index cell are freshly allocated. -/
def checkpointWrites (start : Nat) (h : List (Record P)) : Heap (Cell P) :=
  put (copy start h (fun _ => none)) (start + h.length) (.index (addresses start h))

theorem checkpoint_rep {P : Type} (start : Nat) (h : List (Record P))
    (old : Heap (Cell P)) :
    Represents (overlay (checkpointWrites start h) old)
      ⟨some (start + h.length), none⟩ h := by
  refine ⟨h, [], ?_, .nil, by simp⟩
  apply Prefix.block (as := addresses start h) (by simp [overlay, checkpointWrites, put])
  apply (copy_array h (fun _ => none) start).congr
  intro a mem
  obtain ⟨j, hj, eq⟩ := List.mem_range'.mp mem
  simp only [Nat.one_mul] at eq
  have ne : a ≠ start + h.length := by omega
  obtain ⟨e, he⟩ := (copy_array h (fun _ => none) start).lookup mem
  simp [overlay, checkpointWrites, put, ne, he]

def checkpointPlan {P : Type} (s : Heap (Cell P)) (h : List (Record P))
    (start : Nat) : Plan P where
  source := s
  writes := checkpointWrites start h
  root := ⟨some (start + h.length), none⟩
  before := h
  appended := none
  after := h
  shape := by simp
  valid := checkpoint_rep start h s

end Durability
