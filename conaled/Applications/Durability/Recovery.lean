import Applications.Durability.Storage

namespace Durability

/-- Volatile read cursor; crashes discard it. Tail records are collected in
reverse traversal order, restoring original chronological order. -/
inductive Cursor (P : Type) where
  | prefixCells (todo : List Nat) (seen : List (Record P)) (tail : Option Nat)
  | tailCells (tip : Option Nat) (pre suffix : List (Record P))
  | done (history : List (Record P))
  deriving DecidableEq

inductive CursorRep {P : Type} (s : Heap (Cell P)) : Cursor P → List (Record P) → Prop
  | prefixCells {as seen tip rest tail} : Array s as rest → Chain s tip tail →
      CursorRep s (.prefixCells as seen tip) (seen ++ rest ++ tail)
  | tailCells {tip pre suffix rest} : Chain s tip rest →
      CursorRep s (.tailCells tip pre suffix) (pre ++ rest ++ suffix)
  | done {h} : CursorRep s (.done h) h

inductive Read {P : Type} (s : Heap (Cell P)) : Cursor P → Cursor P → Prop
  | flat {a as seen tip e} : s a = some (.flat e) →
      Read s (.prefixCells (a :: as) seen tip) (.prefixCells as (seen ++ [e]) tip)
  | boundary {seen tip} : Read s (.prefixCells [] seen tip) (.tailCells tip seen [])
  | node {a prev e pre suffix} : s a = some (.node prev e) →
      Read s (.tailCells (some a) pre suffix) (.tailCells prev pre (e :: suffix))
  | finish {pre suffix} : Read s (.tailCells none pre suffix) (.done (pre ++ suffix))

theorem Read.preserves {P : Type} {s : Heap (Cell P)} {a b h}
    (step : Read s a b) (rep : CursorRep s a h) : CursorRep s b h := by
  cases step with
  | @flat a as seen tip e lookup =>
    cases rep with
    | prefixCells ar ch =>
      cases ar with
      | cons lookup' ar' =>
        have eq := lookup.symm.trans lookup'
        cases eq
        simpa [List.append_assoc] using CursorRep.prefixCells (seen := seen ++ [e]) ar' ch
  | boundary =>
    cases rep with
    | prefixCells ar ch =>
      cases ar
      simpa using CursorRep.tailCells (suffix := []) ch
  | node lookup =>
    cases rep with
    | tailCells ch =>
      cases ch with
      | snoc lookup' ch' =>
        have eq := lookup.symm.trans lookup'
        cases eq
        simpa [List.append_assoc] using CursorRep.tailCells (suffix := _ :: _) ch'
  | finish =>
    cases rep with
    | tailCells ch =>
      cases ch
      simpa using CursorRep.done (h := _ ++ _)

inductive StartRead {P : Type} (s : Heap (Cell P)) (r : Root) : Cursor P → Prop
  | log (empty : r.checkpoint = none) : StartRead s r (.tailCells r.tail [] [])
  | checkpoint {a as} (ptr : r.checkpoint = some a) (lookup : s a = some (.index as)) :
      StartRead s r (.prefixCells as [] r.tail)

theorem StartRead.correct {P : Type} {s : Heap (Cell P)} {r c h}
    (start : StartRead s r c) (rep : Represents s r h) : CursorRep s c h := by
  obtain ⟨pre, tail, hp, ht, rfl⟩ := rep
  cases start with
  | log empty =>
    rw [empty] at hp
    cases hp
    simpa using CursorRep.tailCells (pre := []) (suffix := []) ht
  | checkpoint ptr lookup =>
    rw [ptr] at hp
    cases hp with
    | block lookup' ar =>
      have eq := lookup.symm.trans lookup'
      cases eq
      simpa using CursorRep.prefixCells (seen := []) ar ht

theorem StartRead.exists {P : Type} {s : Heap (Cell P)} {r h}
    (rep : Represents s r h) : ∃ c, StartRead s r c := by
  obtain ⟨pre, tail, hp, ht, heq⟩ := rep
  cases r with
  | mk cp tip =>
    cases hp with
    | nil => exact ⟨_, .log rfl⟩
    | block lookup ar => exact ⟨_, .checkpoint rfl lookup⟩

/-- Finite, fault-free scheduled reads suffice. This does not assert fairness or
a response deadline when crashes or scheduling delays continue. -/
theorem CursorRep.completes {P : Type} {s : Heap (Cell P)} {c h}
    (rep : CursorRep s c h) : Relation.ReflTransGen (Read s) c (.done h) := by
  have tailComplete : ∀ {tip rest} (ch : Chain s tip rest) (pre suffix),
      Relation.ReflTransGen (Read s) (.tailCells tip pre suffix)
        (.done (pre ++ rest ++ suffix)) := by
    intro tip rest ch
    induction ch with
    | nil => intro pre suffix; simpa using Relation.ReflTransGen.single (Read.finish (pre := pre) (suffix := suffix))
    | snoc lookup ch ih =>
      intro pre suffix
      apply Relation.ReflTransGen.head (.node lookup)
      simpa [List.append_assoc] using ih pre (_ :: suffix)
  cases rep with
  | done => exact .refl
  | tailCells ch => exact tailComplete ch _ _
  | @prefixCells as seen tip rest tail ar ch =>
    induction ar generalizing seen with
    | nil =>
      apply Relation.ReflTransGen.head .boundary
      simpa using tailComplete ch seen []
    | @cons addr as e es lookup ar ih =>
      apply Relation.ReflTransGen.head (.flat lookup)
      simpa [List.append_assoc] using (ih (seen := seen ++ [e]))

end Durability
