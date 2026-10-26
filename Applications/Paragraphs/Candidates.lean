import Applications.OrderedPartitions.Enumeration

/-! Character-list width and independently fitting ordered paragraphs. -/
set_option autoImplicit false
set_option warningAsError true
namespace Paragraphs
open OrderedPartitions

abbrev Word := List Char
abbrev Text := List Word
abbrev Line := List Word
abbrev Para := List Line

/-- Literal specialization of the source nonempty foldrn clauses; [] is an extension. -/
def width : Line → Nat
  | [] => 0
  | [w] => w.length
  | w :: v :: ws => w.length + 1 + width (v :: ws)

/-- Independent occupied-character and separating-space bound. -/
def FitsLine (maximum : Nat) (line : Line) : Prop :=
  (line.map List.length).sum + (line.length - 1) ≤ maximum

def fits (maximum : Nat) (line : Line) : Bool := decide (width line ≤ maximum)

def AllWordsFit (maximum : Nat) (ws : Text) : Prop :=
  ∀ w ∈ ws, w.length ≤ maximum

def SourceWord (w : Word) : Prop := w ≠ [] ∧ ∀ c ∈ w, c ≠ ' '

def SourceInput (maximum : Nat) (ws : Text) : Prop :=
  ws ≠ [] ∧ (∀ w ∈ ws, SourceWord w) ∧ AllWordsFit maximum ws

instance (maximum : Nat) (line : Line) : Decidable (FitsLine maximum line) :=
  inferInstanceAs (Decidable ((line.map List.length).sum + (line.length - 1) ≤ maximum))

instance (maximum : Nat) (ws : Text) : Decidable (AllWordsFit maximum ws) :=
  inferInstanceAs (Decidable (∀ w ∈ ws, w.length ≤ maximum))

instance (w : Word) : Decidable (SourceWord w) :=
  inferInstanceAs (Decidable (w ≠ [] ∧ ∀ c ∈ w, c ≠ ' '))

instance (maximum : Nat) (ws : Text) : Decidable (SourceInput maximum ws) :=
  inferInstanceAs (Decidable (ws ≠ [] ∧ (∀ w ∈ ws, SourceWord w) ∧ AllWordsFit maximum ws))

theorem width_formula (line : Line) :
    width line = (line.map List.length).sum + (line.length - 1) := by
  induction line with
  | nil => rfl
  | cons w ws ih =>
    cases ws with
    | nil => simp [width]
    | cons v vs =>
      simp only [width, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      omega

@[simp] theorem width_nil : width [] = 0 := rfl

@[simp] theorem width_singleton (w : Word) : width [w] = w.length := rfl

theorem width_append (left right : Line) (hl : left ≠ []) (hr : right ≠ []) :
    width (left ++ right) = width left + 1 + width right := by
  have hll := List.length_pos_iff.mpr hl
  have hrl := List.length_pos_iff.mpr hr
  simp only [width_formula, List.map_append, List.sum_append, List.length_append]
  omega

theorem width_append_singleton (line : Line) (w : Word) (hl : line ≠ []) :
    width (line ++ [w]) = width line + 1 + w.length := by
  rw [width_append line [w] hl (by simp), width_singleton]

theorem width_prefix (left right : Line) : width left ≤ width (left ++ right) := by
  simp only [width_formula, List.map_append, List.sum_append, List.length_append]
  omega

theorem width_suffix (left right : Line) : width right ≤ width (left ++ right) := by
  simp only [width_formula, List.map_append, List.sum_append, List.length_append]
  omega

theorem fits_iff (maximum : Nat) (line : Line) :
    fits maximum line = true ↔ FitsLine maximum line := by
  simp only [fits, decide_eq_true_eq, width_formula, FitsLine]

theorem fits_prefixClosed (maximum : Nat) : PrefixClosed (fits maximum) := by
  intro left right h
  simp only [fits, decide_eq_true_eq] at h ⊢
  exact Nat.le_trans (width_prefix left right) h

theorem fits_suffixClosed (maximum : Nat) : SuffixClosed (fits maximum) := by
  intro left right h
  simp only [fits, decide_eq_true_eq] at h ⊢
  exact Nat.le_trans (width_suffix left right) h

@[simp] theorem fits_singleton (maximum : Nat) (w : Word) :
    fits maximum [w] = decide (w.length ≤ maximum) := rfl

theorem allWordsFit_append (maximum : Nat) (xs ys : Text) :
    AllWordsFit maximum (xs ++ ys) ↔ AllWordsFit maximum xs ∧ AllWordsFit maximum ys := by
  simp [AllWordsFit, or_imp, forall_and]

/-- Complete independent paragraph specification; no generator or optimizer occurs here. -/
def FitPartition (maximum : Nat) (ws : Text) (p : Para) : Prop :=
  IsPartition ws p ∧ ∀ line ∈ p, FitsLine maximum line

instance (maximum : Nat) (ws : Text) (p : Para) : Decidable (FitPartition maximum ws p) :=
  inferInstanceAs (Decidable ((p.flatten = ws ∧ (∀ line ∈ p, line ≠ [])) ∧
    ∀ line ∈ p, FitsLine maximum line))

/-- The actual snoc-before-bind, last-line-filtered source extension. -/
def fitExtend (maximum : Nat) (w : Word) (p : Para) : List Para :=
  (extendRight w p).filter (lastOk (fits maximum))

def fitStep (maximum : Nat) (ps : List Para) (w : Word) : List Para :=
  ps.flatMap (fitExtend maximum w)

def fitParts (maximum : Nat) (ws : Text) : List Para :=
  ws.foldl (fitStep maximum) [[]]

theorem fitParts_eq_pruned (maximum : Nat) (ws : Text) :
    fitParts maximum ws = prunedPartsRight (fits maximum) ws := rfl

theorem fitParts_eq_filtered (maximum : Nat) (ws : Text) :
    fitParts maximum ws = (partsRight ws).filter (allOk (fits maximum)) :=
  (filter_partsRight (fits maximum) (fits_prefixClosed maximum) ws).symm

theorem mem_fitParts (maximum : Nat) (ws : Text) (p : Para) :
    p ∈ fitParts maximum ws ↔ FitPartition maximum ws p := by
  rw [fitParts_eq_pruned, mem_prunedPartsRight _ (fits_prefixClosed maximum)]
  simp only [FitPartition, fits_iff]

theorem fitParts_nodup (maximum : Nat) (ws : Text) : (fitParts maximum ws).Nodup :=
  prunedPartsRight_nodup (fits maximum) (fits_prefixClosed maximum) ws

@[simp] theorem fitParts_nil (maximum : Nat) : fitParts maximum [] = [[]] := rfl

theorem fitParts_append_singleton (maximum : Nat) (ws : Text) (w : Word) :
    fitParts maximum (ws ++ [w]) = (fitParts maximum ws).flatMap (fitExtend maximum w) := by
  simp [fitParts, fitStep]

theorem fitExtend_preserves (maximum : Nat) (ws : Text) (p q : Para) (w : Word)
    (hp : FitPartition maximum ws p) (hq : q ∈ fitExtend maximum w p) :
    FitPartition maximum (ws ++ [w]) q := by
  apply (mem_fitParts maximum (ws ++ [w]) q).mp
  rw [fitParts_append_singleton]
  exact List.mem_flatMap.mpr ⟨p, (mem_fitParts maximum ws p).mpr hp, hq⟩


end Paragraphs
