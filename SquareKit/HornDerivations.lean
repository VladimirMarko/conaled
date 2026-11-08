import SquareKit.HornSupport
import SquareKit.DependentTheoryMaps
import Mathlib.Data.List.OfFn
import Mathlib.Data.Finset.Image

/-! Optional selected trees for Horn support. A fixed ambient table gives each
label its immutable ordered signature; finite active-label sets select bases.
No part of `HornSupport` depends on this data layer. -/
namespace SquareKit.HornSupport
open DependentTheoryMaps
universe u v

structure LabelledRule (Atom : Type u) where
  premises : List Atom
  distinct : premises.Nodup
  conclusion : Atom

namespace LabelledRule
variable {Atom : Type u} {Label : Type v}
variable (table : Label → LabelledRule Atom)

def erase [DecidableEq Atom] (r : LabelledRule Atom) : Rule Atom := ⟨r.premises.toFinset, r.conclusion⟩

def base [DecidableEq Atom] (L : Finset Label) : Base Atom := L.image (fun l => (table l).erase)

abbrev rules (L : Finset Label) : Rules Atom where
  Label := {l // l ∈ L}
  count l := (table l).premises.length
  premise l := (table l).premises.get
  conclusion l := (table l).conclusion

abbrev Tree (L : Finset Label) (a : Atom) := Derivation (rules table L) (fun _ => Empty) a

variable {table} {L M N : Finset Label}

/-- Copies a selected tree without making a new selection. -/
def map (i : L ⊆ M) : Tree table L a → Tree table M a
  | .hyp h => nomatch h
  | .rule l ds => .rule (R := rules table M) ⟨l.val, i l.property⟩ (fun j => map i (ds j))

@[simp] theorem map_identity (t : Tree table L a) : map (fun _ h => h) t = t := by
  induction t with
  | hyp h => exact nomatch h
  | rule l ds ih => simp only [map]; congr 1; funext j; exact ih j

@[simp] theorem map_comp (i : L ⊆ M) (j : M ⊆ N) (t : Tree table L a) :
    map j (map i t) = map (Finset.Subset.trans i j) t := by
  induction t with
  | hyp h => exact nomatch h
  | rule l ds ih => simp only [map]; congr 1; funext k; exact ih k

/-- Ordered postorder traversal, counting every use of a rule. -/
def trace : Tree table L a → List Label
  | .hyp h => nomatch h
  | .rule l ds => (List.ofFn (fun j => trace (ds j))).flatten ++ [l.val]

/-- One trace entry per node. -/
def size (t : Tree table L a) : Nat := (trace t).length

theorem size_pos (t : Tree table L a) : 0 < size t := by
  cases t with
  | hyp h => exact nomatch h
  | rule l ds => simp [size, trace]

@[simp] theorem trace_map (i : L ⊆ M) (t : Tree table L a) : trace (map i t) = trace t := by
  induction t with
  | hyp h => exact nomatch h
  | rule l ds ih => simp only [map, trace]; congr 2; congr 1; funext j; exact ih j

@[simp] theorem size_map (i : L ⊆ M) (t : Tree table L a) : size (map i t) = size t := by
  simp [size]

variable [DecidableEq Atom]

theorem base_mono (i : L ⊆ M) : base table L ⊆ base table M := Finset.image_subset_image i

theorem eraseTree (t : Tree table L a) : Derivable (base table L) a := by
  induction t with
  | hyp h => exact nomatch h
  | rule l ds ih =>
    apply Derivable.rule (table l.val).erase (Finset.mem_image.mpr ⟨l.val, l.property, rfl⟩)
    intro a ha
    have hm : a ∈ (table l.val).premises := List.mem_toFinset.mp ha
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
    exact hj ▸ ih j

/-- The square compares proofs of the same atomic proposition, not trees. -/
theorem erase_map (i : L ⊆ M) (t : Tree table L a) :
    eraseTree (map i t) = (eraseTree t).weaken (base_mono i) := rfl

/-- No function of a support proof can recover every selected trace when two
actual trees at that fixed base have different traces. Canonical choice remains possible. -/
theorem no_trace_recovery (s t : Tree table L a) (hne : trace s ≠ trace t) :
    ¬ ∃ recover : Derivable (base table L) a → List Label,
      ∀ d : Tree table L a, recover (eraseTree d) = trace d := by
  rintro ⟨recover, h⟩
  apply hne
  exact (h s).symm.trans (h t)

/-- Minimum node count, with no claim that the selected minimum is natural. -/
def Shortest (t : Tree table L a) : Prop := ∀ s : Tree table L a, size t ≤ size s
end LabelledRule
end SquareKit.HornSupport
