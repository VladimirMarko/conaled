import SquareKit.DependentOperation.Local
import SquareKit.Relations

/-! A bounded cursor comparison with genuinely changing fibers. -/
namespace Examples.IndexedRelationalTransfer

@[ext] structure Cursor (n : Nat) where
  position : Fin n
  history : List Bool

/-- Native operations, specified before registering a rule language. -/
def step (b : Bool) (x : Cursor n) : Cursor (n + 1) :=
  ⟨if b then x.position.succ else x.position.castSucc, x.history ++ [b]⟩

def reserve (k : Nat) (x : Cursor n) : Cursor (k + n) :=
  ⟨⟨x.position.val, by have := x.position.isLt; omega⟩, x.history⟩

def direct (x : Cursor n) : Cursor (n + 3) := step true (step false (step true x))

theorem reserve_step (k : Nat) (b : Bool) (x : Cursor n) :
    step b (reserve k x) = reserve k (step b x) := by
  cases b <;> apply Cursor.ext <;> rfl

theorem direct_reserve (k : Nat) (x : Cursor n) :
    direct (reserve k x) = reserve k (direct x) := by
  unfold direct
  rw [reserve_step, reserve_step, reserve_step]

def start : Cursor 2 := ⟨1, []⟩

example : (direct start).position.val = 3 ∧
    (direct start).history = [true, false, true] := by decide

/-- Relation of selected fiber data. Index admissibility is separate. -/
def Related (x : Cursor n) (y : Cursor m) : Prop :=
  x.position.val = y.position.val ∧ x.history = y.history

def IndexRelated (k n m : Nat) : Prop := m = k + n

theorem reserve_related (k : Nat) (x : Cursor n) : Related x (reserve k x) := ⟨rfl, rfl⟩

theorem related_trans {x : Cursor n} {y : Cursor m} {z : Cursor l}
    (h : Related x y) (h' : Related y z) : Related x z :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

/-- Each side retains its own dependent carrier. -/
def fiberRep (n m : Nat) : Relational.RelRep :=
  ⟨Cursor n, Cursor m, Related⟩

def stepSquare (b : Bool) (n m : Nat) :
    Relational.RelSquare (fiberRep n m) (fiberRep (n+1) (m+1)) where
  impl := step b
  spec := step b
  preserves := by
    intro x y h
    obtain ⟨hp, hh⟩ := h
    cases b <;> constructor
    · exact hp
    · exact congrArg (fun xs => xs ++ [false]) hh
    · exact congrArg Nat.succ hp
    · exact congrArg (fun xs => xs ++ [true]) hh

/-- Ordinary relational composition is usable once its varying carriers match. -/
def directSquare (n m : Nat) :
    Relational.RelSquare (fiberRep n m) (fiberRep (n+3) (m+3)) :=
  Relational.compose (stepSquare true (n+2) (m+2))
    (Relational.compose (stepSquare false (n+1) (m+1)) (stepSquare true n m))

theorem direct_related {x : Cursor n} {y : Cursor m} (h : Related x y) :
    Related (direct x) (direct y) := (directSquare n m).preserves h

open SquareKit.DependentBranchTheoryMaps

/-- One local command increases capacity by one. -/
def rules : Rules Nat where
  Label := Nat × Bool
  Arity _ := Unit
  premise r _ := r.1
  conclusion r := r.1 + 1

def cursorModel : Model rules Cursor where
  rule r xs := step r.2 (xs ())

abbrev Term (n : Nat) := Derivation rules Cursor n

def command (b : Bool) (t : Term n) : Term (n + 1) :=
  .rule (R := rules) (n, b) (fun _ => t)

def program (x : Cursor n) : Term (n + 3) :=
  command true (command false (command true (.hyp x)))

def evaluate (t : Term n) : Cursor n := t.interpret cursorModel (fun _ => id)

theorem program_direct (x : Cursor n) : evaluate (program x) = direct x := rfl

/-- Local certificate only: the transformed premise is used exactly once. -/
def expansion (k : Nat) : TheoryMap rules rules (fun n => k + n) where
  certificate r := .rule (R := rules) (k + r.1, r.2) (fun _ => .hyp ⟨(), rfl⟩)

theorem expansion_local (k : Nat) :
    (expansion k).LocalMeaning cursorModel cursorModel (fun _ => reserve k) := by
  intro r xs
  exact reserve_step k r.2 (xs ())

def expand (k : Nat) (t : Term n) : Term (k + n) :=
  (expansion k).transport (fun _ => reserve k) t

theorem expand_selected (k : Nat) (t : Term n) :
    evaluate (expand k t) = reserve k (evaluate t) :=
  (expansion k).interpret_transport cursorModel cursorModel (fun _ => reserve k)
    (expansion_local k) (fun _ => reserve k) (fun _ => id) (fun _ => id)
    (fun _ _ => rfl) t

theorem expand_related (k : Nat) (t : Term n) :
    IndexRelated k n (k+n) ∧ Related (evaluate t) (evaluate (expand k t)) := by
  rw [expand_selected]
  exact ⟨rfl, reserve_related k _⟩

/-- Existing indexed certificate composition retains the actual derivation. -/
theorem twice_terms (k l : Nat) (t : Term n) :
    ((expansion k).comp (expansion l)).transport
      (fun _ x => reserve l (reserve k x)) t = expand l (expand k t) :=
  (expansion k).comp_transport (expansion l) (fun _ => reserve k)
    (fun _ => reserve l) t

theorem twice_selected (k l : Nat) (t : Term n) :
    evaluate (expand l (expand k t)) = reserve l (reserve k (evaluate t)) := by
  rw [expand_selected, expand_selected]

theorem generated_direct (k l : Nat) (x : Cursor n) :
    evaluate (expand l (expand k (program x))) = direct (reserve l (reserve k x)) := by
  rw [twice_selected, program_direct, direct_reserve, direct_reserve]

/-- The generated certificate retains the whole chosen cursor in its output fiber. -/
def generatedCertificate (k l : Nat) (x : Cursor n) :
    { y : Cursor (l + (k + (n+3))) // Related (direct x) y } :=
  ⟨evaluate (expand l (expand k (program x))), by
    rw [twice_selected, program_direct]
    exact related_trans (reserve_related k _) (reserve_related l _)⟩

def directCertificate (k l : Nat) (x : Cursor n) :
    { y : Cursor (l + (k + (n+3))) // Related (direct x) y } :=
  ⟨direct (reserve l (reserve k x)), by
    rw [direct_reserve, direct_reserve]
    exact related_trans (reserve_related k _) (reserve_related l _)⟩

theorem certificates_agree (k l : Nat) (x : Cursor n) :
    generatedCertificate k l x = directCertificate k l x :=
  Subtype.ext (generated_direct k l x)

example : (evaluate (expand 3 (expand 2 (program start)))).position.val = 3 ∧
    (evaluate (expand 3 (expand 2 (program start)))).history = [true,false,true] := by
  rw [generated_direct]
  decide

/-- An explicit index equality allows transport of the entire selected record. -/
theorem cast_related (h : n = m) (x : Cursor n) : Related x (h ▸ x) := by
  cases h
  exact ⟨rfl, rfl⟩

/-- Associating capacities requires a cast, and preserves the selected record. -/
theorem reserve_twice (k l : Nat) (x : Cursor n) :
    (Nat.add_assoc l k n).symm ▸ reserve l (reserve k x) = reserve (l+k) x := by
  apply Cursor.ext
  · apply Fin.ext
    exact (cast_related (Nat.add_assoc l k n).symm (reserve l (reserve k x))).1.symm
  · exact (cast_related (Nat.add_assoc l k n).symm (reserve l (reserve k x))).2.symm

/-- Both fibers really contain data, and the index change is not equality. -/
example : Nonempty (Cursor 2) ∧ Nonempty (Cursor 5) ∧ (2 : Nat) ≠ 5 :=
  ⟨⟨start⟩, ⟨direct start⟩, by decide⟩

def other : Cursor 2 := ⟨0, []⟩

/-- Mere existence cannot recover even the selected position. -/
example : Nonempty (Cursor 2) ∧ ¬ Related start other := by
  exact ⟨⟨start⟩, by unfold Related; decide⟩

/-- Unmatched middle values defeat relational composition. -/
example : Related start start ∧ Related other other ∧ ¬ Related start other := by
  unfold Related
  decide

/-- Equal capacity alone does not imply the local operation law. -/
example : ¬ Related (step true start) (step false start) := by unfold Related; decide

/-- Equal positions alone cannot justify an index cast. -/
example : Related start (reserve 1 start) ∧ ¬ ((2 : Nat) = 1+2) := by
  exact ⟨reserve_related 1 start, by decide⟩

/-- Enlarging capacity is not an equivalence onto the target fiber. -/
example : ¬ ∃ x : Cursor 2, reserve 1 x = (⟨2, []⟩ : Cursor 3) := by
  rintro ⟨x, h⟩
  have hv := congrArg (fun y => y.position.val) h
  change x.position.val = 2 at hv
  have := x.position.isLt
  omega

/-- Equality transport changes presentations of indices, never the relation. -/
theorem transport_equalities {x : Cursor n} {y : Cursor m}
    (hn : n = n') (hm : m = m') (h : Related x y) :
    Related (hn ▸ x) (hm ▸ y) := by
  cases hn
  cases hm
  exact h

end Examples.IndexedRelationalTransfer
