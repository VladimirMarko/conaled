import Applications.Search.RedBlack.Observations
import Applications.Representations.SignedComparison

/-!
# Raw red-black source operations

These cases fix constructor outputs before abstraction: the source tests
right-left before right-right, calls the full matcher after either descent,
and retains malformed search behavior. Generic cases use the public raw
observation theorems with separate key and payload universes.
-/
set_option autoImplicit false
set_option warningAsError true

/- 01-balance-overlap -/
namespace Examples.RedBlackTrees
open RBTree RBNode RBColor

-- The source chooses right-left before right-right on this overlapping raw input.
example : Search.RedBlack.balance black (nil : RBNode (Int × Nat)) 0 100
      (node red (node red nil (1, 101) nil) (2, 102) (node red nil (3, 103) nil)) =
    node red (node black nil (0, 100) nil) (1, 101)
      (node black nil (2, 102) (node red nil (3, 103) nil)) := by
  rfl

end Examples.RedBlackTrees

/- 02-balance-constructors -/
namespace Examples.RedBlackTrees
open RBTree RBNode RBColor
open Search.RedBlack (balance)

private abbrev r (key : Int) (value : Nat) : Search.RedBlack.Tree Int Nat :=
  node red nil (key, value) nil
private abbrev b (key : Int) (value : Nat) : Search.RedBlack.Tree Int Nat :=
  node black nil (key, value) nil

theorem balance_empty_children (color : RBColor) :
    balance color (nil : RBNode (Int × Nat)) 1 101 nil = node color nil (1, 101) nil := by
  cases color <;> rfl

theorem balance_shallow_left (color child : RBColor) :
    balance color (node child nil (0, 100) nil : Search.RedBlack.Tree Int Nat) 1 101 nil =
      node color (node child nil (0, 100) nil) (1, 101) nil := by
  cases color <;> cases child <;> rfl

theorem balance_shallow_right (color child : RBColor) :
    balance color (nil : RBNode (Int × Nat)) 1 101 (node child nil (2, 102) nil) =
      node color nil (1, 101) (node child nil (2, 102) nil) := by
  cases color <;> cases child <;> rfl

theorem balance_shallow_both (color leftColor rightColor : RBColor) :
    balance color (node leftColor nil (0, 100) nil : Search.RedBlack.Tree Int Nat) 1 101
        (node rightColor nil (2, 102) nil) =
      node color (node leftColor nil (0, 100) nil) (1, 101)
        (node rightColor nil (2, 102) nil) := by
  cases color <;> cases leftColor <;> cases rightColor <;> rfl

theorem four_isolated_rotations :
    balance black (node red (r 0 100) (1, 101) nil) 2 102 nil =
        node red (b 0 100) (1, 101) (b 2 102) ∧
    balance black (node red nil (0, 100) (r 1 101)) 2 102 nil =
        node red (b 0 100) (1, 101) (b 2 102) ∧
    balance black nil 0 100 (node red (r 1 101) (2, 102) nil) =
        node red (b 0 100) (1, 101) (b 2 102) ∧
    balance black nil 0 100 (node red nil (1, 101) (r 2 102)) =
        node red (b 0 100) (1, 101) (b 2 102) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem left_overlap_priority :
    balance black (node red (r 0 100) (1, 101) (r 2 102)) 3 103 nil =
      node red (b 0 100) (1, 101) (node black (r 2 102) (3, 103) nil) := rfl

theorem both_sides_priority :
    balance black (node red (r 0 100) (1, 101) nil) 3 103
        (node red (r 4 104) (5, 105) nil) =
      node red (b 0 100) (1, 101)
        (node black nil (3, 103) (node red (r 4 104) (5, 105) nil)) := rfl

theorem red_bypass :
    balance red (node red (r 0 100) (1, 101) nil) 2 102 nil =
      node red (node red (r 0 100) (1, 101) nil) (2, 102) nil := rfl

theorem nested_color_fallback :
    balance black (node black (r 0 100) (1, 101) nil) 2 102 nil =
        node black (node black (r 0 100) (1, 101) nil) (2, 102) nil ∧
    balance black (node red (b 0 100) (1, 101) (b 2 102)) 3 103 nil =
        node black (node red (b 0 100) (1, 101) (b 2 102)) (3, 103) nil :=
  ⟨rfl, rfl⟩

def rightOverlap : Search.RedBlack.Tree Int Nat :=
  node black nil (0, 100) (node red (r 1 101) (2, 102) (r 3 103))

theorem right_overlap_source :
    balance black nil 0 100 (node red (r 1 101) (2, 102) (r 3 103)) =
      node red (b 0 100) (1, 101) (node black nil (2, 102) (r 3 103)) := rfl

theorem right_overlap_provider :
    RBNode.balance2 nil (0, 100) (node red (r 1 101) (2, 102) (r 3 103)) =
      node red (node black nil (0, 100) (r 1 101)) (2, 102) (b 3 103) := rfl

theorem right_overlap_source_ne_provider :
    balance black nil 0 100 (node red (r 1 101) (2, 102) (r 3 103)) ≠
      RBNode.balance2 nil (0, 100) (node red (r 1 101) (2, 102) (r 3 103)) := by
  intro same
  have roots := congrArg RBNode.root? same
  have impossible : (1 : Int) = 2 := congrArg (fun p => p.map Prod.fst) roots |>
    Option.some.inj
  exact (by decide : (1 : Int) ≠ 2) impossible

end Examples.RedBlackTrees

/- 03-lookup -/
namespace Examples.RedBlackTrees
open RBTree RBNode RBColor
open Representations.SignedComparison (intLtb)

private abbrev lookupInput : Search.RedBlack.Tree Int Nat :=
  node black (node red nil (-3, 7) nil) (0, 0) (node black nil (4, 8) nil)

example : Search.RedBlack.lookup? intLtb (-3) lookupInput = some 7 ∧
    Search.RedBlack.lookup? intLtb 0 lookupInput = some 0 ∧
    Search.RedBlack.lookup? intLtb 4 lookupInput = some 8 ∧
    Search.RedBlack.lookup? intLtb 2 lookupInput = none ∧
    Search.RedBlack.lookup intLtb 99 0 lookupInput = 0 ∧
    Search.RedBlack.lookup intLtb 99 2 lookupInput = 99 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Examples.RedBlackTrees

/- 04-erasure -/
namespace Examples.RedBlackTrees
open RBTree RBNode RBColor
universe u v

example (P : Int → Nat → Prop) :
    Search.RedBlack.ForallT P
        (node black (node red nil (-2, 7) nil) (0, 8) (node black nil (3, 9) nil)) ↔
      P 0 8 ∧ (P (-2) 7 ∧ True ∧ True) ∧ (P 3 9 ∧ True ∧ True) := Iff.rfl

example : Search.RedBlack.eraseColors
        (node black (node red nil (-2, 7) nil) (0, 8) (node black nil (3, 9) nil) :
          Search.RedBlack.Tree Int Nat) =
      BinaryTree.node (0, 8) (BinaryTree.node (-2, 7) .nil .nil)
        (BinaryTree.node (3, 9) .nil .nil) := rfl

example {κ : Type u} {ν : Type v} (color : RBColor) (left right : Search.RedBlack.Tree κ ν)
    (key : κ) (value : ν) :
    Search.RedBlack.eraseColors (node color left (key, value) right) =
      BinaryTree.node (key, value) (Search.RedBlack.eraseColors left)
        (Search.RedBlack.eraseColors right) :=
  Search.RedBlack.eraseColors_node color left key value right

example {κ : Type u} {ν : Type v} (P : κ → ν → Prop)
    (color : RBColor) (left right : Search.RedBlack.Tree κ ν) (key : κ) (value : ν) :
    Search.RedBlack.ForallT P (node color left (key, value) right) ↔
      P key value ∧ Search.RedBlack.ForallT P left ∧ Search.RedBlack.ForallT P right :=
  Search.RedBlack.forallT_node P color left key value right

end Examples.RedBlackTrees

/- 05-traversal-blackening -/
namespace Examples.RedBlackTrees
open RBTree RBNode RBColor
universe u v

private abbrev traversalInput : Search.RedBlack.Tree Int Nat :=
  node red (node black nil (4, 104) nil) (5, 105) (node red nil (2, 102) nil)

example (suffix : List (Int × Nat)) :
    Search.RedBlack.elementsAux traversalInput suffix =
      [(4, 104), (5, 105), (2, 102)] ++ suffix := rfl

example : Search.RedBlack.elements traversalInput = [(4, 104), (5, 105), (2, 102)] := rfl

example : Search.RedBlack.makeBlack traversalInput =
    node black (node black nil (4, 104) nil) (5, 105) (node red nil (2, 102) nil) := rfl

example : Search.RedBlack.makeBlack (nil : Search.RedBlack.Tree Int Nat) = nil := rfl

example {κ : Type u} {ν : Type v} (color : RBColor) (left right : Search.RedBlack.Tree κ ν)
    (key : κ) (value : ν) (suffix : List (κ × ν)) :
    Search.RedBlack.elementsAux (node color left (key, value) right) suffix =
      Search.RedBlack.elementsAux left ((key, value) :: Search.RedBlack.elementsAux right suffix) :=
  Search.RedBlack.elementsAux_node color left key value right suffix

example {κ : Type u} {ν : Type v} (color : RBColor) (left right : Search.RedBlack.Tree κ ν)
    (key : κ) (value : ν) :
    Search.RedBlack.makeBlack (node color left (key, value) right) =
      node black left (key, value) right :=
  Search.RedBlack.makeBlack_node color left key value right

end Examples.RedBlackTrees

/- 06-forallT-erasure -/
namespace Examples.RedBlackTrees
open RBTree RBNode RBColor
universe u v

example {κ : Type u} {ν : Type v} (P : κ → ν → Prop)
    (t : Search.RedBlack.Tree κ ν) :
    Search.OrderedMap.DecodedKeys.ForallT P (Search.RedBlack.eraseColors t) ↔
      Search.RedBlack.ForallT P t :=
  Search.RedBlack.eraseColors_forallT P t

example (P : Int → Nat → Prop)
    (h4 : P 4 104) (h5 : P 5 105) (h2 : P 2 102) :
    Search.OrderedMap.DecodedKeys.ForallT P
      (Search.RedBlack.eraseColors
        (node black (node red (node red nil (4, 104) nil) (5, 105) nil) (2, 102) nil)) := by
  apply (Search.RedBlack.eraseColors_forallT P _).mpr
  exact ⟨h2, ⟨h5, ⟨h4, trivial, trivial⟩, trivial⟩, trivial⟩

end Examples.RedBlackTrees

/- 07-insertion -/
namespace Examples.RedBlackTrees
open RBTree RBNode RBColor
open Representations.SignedComparison (intLtb)
universe u v

private abbrev insertionRed (key : Int) (value : Nat) : Search.RedBlack.Tree Int Nat :=
  node red nil (key, value) nil
private abbrev insertionBlack (key : Int) (value : Nat) : Search.RedBlack.Tree Int Nat :=
  node black nil (key, value) nil

example : Search.RedBlack.ins intLtb 1 101 nil = insertionRed 1 101 ∧
    Search.RedBlack.insert intLtb 1 101 nil = insertionBlack 1 101 := ⟨rfl, rfl⟩

example : Search.RedBlack.ins intLtb 0 100 (insertionRed 1 101) =
      node red (insertionRed 0 100) (1, 101) nil ∧
    Search.RedBlack.ins intLtb 2 102 (insertionRed 1 101) =
      node red nil (1, 101) (insertionRed 2 102) ∧
    Search.RedBlack.ins intLtb 0 100 (insertionBlack 1 101) =
      node black (insertionRed 0 100) (1, 101) nil ∧
    Search.RedBlack.ins intLtb 2 102 (insertionBlack 1 101) =
      node black nil (1, 101) (insertionRed 2 102) := ⟨rfl, rfl, rfl, rfl⟩

example : Search.RedBlack.ins (fun (_ _ : Int) => false) 7 707
      (node black (node red (insertionRed 0 100) (1, 101) nil) (2, 102)
        (insertionRed 3 103)) =
    node black (node red (insertionRed 0 100) (1, 101) nil) (7, 707)
      (insertionRed 3 103) := rfl

example : Search.RedBlack.ins (fun (_ _ : Int) => true) 7 707 (insertionBlack 1 101) =
      node black (insertionRed 7 707) (1, 101) nil ∧
    Search.RedBlack.lookup (fun (_ _ : Int) => true) 999 1 (insertionBlack 1 101) = 999 :=
  ⟨rfl, rfl⟩

/-- Descending right still tests the pre-existing left-left source pattern. -/
example : Search.RedBlack.ins intLtb 4 104
      (node black (node red (insertionRed 0 100) (1, 101) nil) (3, 103) nil) =
    node red (insertionBlack 0 100) (1, 101)
      (node black nil (3, 103) (insertionRed 4 104)) := rfl

/-- Descending left still tests the pre-existing right-left source pattern. -/
example : Search.RedBlack.ins intLtb 0 100
      (node black nil (1, 101) (node red (insertionRed 2 102) (3, 103) nil)) =
    node red (node black (insertionRed 0 100) (1, 101) nil) (2, 102)
      (insertionBlack 3 103) := rfl

private abbrev malformedInsertionInput : Search.RedBlack.Tree Int Nat :=
  node black (node red (insertionRed 4 104) (5, 105) nil) (2, 102) nil

example : Search.RedBlack.ins intLtb 3 303 malformedInsertionInput =
      node red (insertionBlack 4 104) (5, 105)
        (node black nil (2, 102) (insertionRed 3 303)) ∧
    Search.RedBlack.insert intLtb 3 303 malformedInsertionInput =
      node black (insertionBlack 4 104) (5, 105)
        (node black nil (2, 102) (insertionRed 3 303)) ∧
    Search.RedBlack.lookup? intLtb 3
      (Search.RedBlack.insert intLtb 3 303 malformedInsertionInput) = none ∧
    Search.RedBlack.lookup intLtb 999 3
      (Search.RedBlack.insert intLtb 3 303 malformedInsertionInput) = 999 ∧
    Search.RedBlack.elements (Search.RedBlack.insert intLtb 3 303 malformedInsertionInput) =
      [(4, 104), (5, 105), (2, 102), (3, 303)] := ⟨rfl, rfl, rfl, rfl, rfl⟩

example {κ : Type u} {ν : Type v} (ltb : κ → κ → Bool) (key old : κ)
    (value previous : ν) (color : RBColor) (left right : Search.RedBlack.Tree κ ν) :
    Search.RedBlack.ins ltb key value (node color left (old, previous) right) =
      if ltb key old then Search.RedBlack.balance color (Search.RedBlack.ins ltb key value left)
        old previous right
      else if ltb old key then Search.RedBlack.balance color left old previous
        (Search.RedBlack.ins ltb key value right)
      else node color left (key, value) right :=
  Search.RedBlack.ins_node ltb key value color left old previous right

example {κ : Type u} {ν : Type v} (ltb : κ → κ → Bool) (key : κ) (value : ν)
    (t : Search.RedBlack.Tree κ ν) :
    Search.RedBlack.insert ltb key value t =
      Search.RedBlack.makeBlack (Search.RedBlack.ins ltb key value t) :=
  Search.RedBlack.insert_eq_makeBlack_ins ltb key value t

end Examples.RedBlackTrees

/- 08-nonempty -/
namespace Examples.RedBlackTrees
open RBTree RBNode RBColor
universe u v

example {κ : Type u} {ν : Type v} (color : RBColor)
    (left right : Search.RedBlack.Tree κ ν) (key : κ) (value : ν) :
    Search.RedBlack.balance color left key value right ≠ nil :=
  Search.RedBlack.balance_ne_nil color left key value right

example {κ : Type u} {ν : Type v} (t : Search.RedBlack.Tree κ ν) (h : t ≠ nil) :
    Search.RedBlack.makeBlack t ≠ nil :=
  Search.RedBlack.makeBlack_ne_nil h

example {κ : Type u} {ν : Type v} (ltb : κ → κ → Bool) (key : κ) (value : ν)
    (t : Search.RedBlack.Tree κ ν) :
    Search.RedBlack.ins ltb key value t ≠ nil ∧
      Search.RedBlack.insert ltb key value t ≠ nil :=
  ⟨Search.RedBlack.ins_ne_nil ltb key value t,
    Search.RedBlack.insert_ne_nil ltb key value t⟩

example (ltb : Int → Int → Bool) :
    Search.RedBlack.insert ltb (-3) ("payload", [1, 2]) nil ≠ nil :=
  Search.RedBlack.insert_ne_nil ltb (-3) ("payload", [1, 2]) nil

end Examples.RedBlackTrees

/- 09-balance-inorder -/
namespace Examples.RedBlackTrees
open RBTree RBNode RBColor
universe u v

example (suffix : List (Int × Nat)) :
    Search.RedBlack.elementsAux
      (Search.RedBlack.balance black nil 0 100
        (node red (node red nil (1, 101) nil) (2, 102) (node red nil (3, 103) nil))) suffix =
      [(0, 100), (1, 101), (2, 102), (3, 103)] ++ suffix := by
  rw [Search.RedBlack.elementsAux_eq, Search.RedBlack.balance_elements]
  rfl

example {κ : Type u} {ν : Type v} (color : RBColor)
    (left right : Search.RedBlack.Tree κ ν) (key : κ) (value : ν) :
    Search.RedBlack.elements (Search.RedBlack.balance color left key value right) =
      Search.RedBlack.elements left ++ (key, value) :: Search.RedBlack.elements right :=
  Search.RedBlack.balance_elements color left key value right

example {κ : Type u} {ν : Type v} (color : RBColor)
    (left right : Search.RedBlack.Tree κ ν) (key : κ) (value : ν) :
    Search.RedBlack.elements (node color left (key, value) right) =
      Search.RedBlack.elements left ++ (key, value) :: Search.RedBlack.elements right :=
  Search.RedBlack.elements_node color left key value right

end Examples.RedBlackTrees

/- 10-all-predicates -/
namespace Examples.RedBlackTrees
open RBTree RBNode RBColor
universe u v

example {κ : Type u} {ν : Type v} (P : κ → ν → Prop) (t : Search.RedBlack.Tree κ ν) :
    Search.RedBlack.ForallT P t ↔
      ∀ binding ∈ Search.RedBlack.elements t, P binding.1 binding.2 :=
  Search.RedBlack.forallT_elements_iff P t

example {κ : Type u} {ν : Type v} (P : κ → ν → Prop) (color : RBColor)
    (left right : Search.RedBlack.Tree κ ν) (key : κ) (value : ν) :
    Search.RedBlack.ForallT P (Search.RedBlack.balance color left key value right) ↔
      P key value ∧ Search.RedBlack.ForallT P left ∧ Search.RedBlack.ForallT P right :=
  Search.RedBlack.balance_forallT P color left key value right

example {κ : Type u} {ν : Type v} (ltb : κ → κ → Bool) (P : κ → ν → Prop)
    (key : κ) (value : ν) (t : Search.RedBlack.Tree κ ν)
    (written : P key value) (all : Search.RedBlack.ForallT P t) :
    Search.RedBlack.ForallT P (Search.RedBlack.ins ltb key value t) :=
  Search.RedBlack.ins_forallT ltb P key value t written all

example {κ : Type u} {ν : Type v} (P Q : κ → ν → Prop) (t : Search.RedBlack.Tree κ ν)
    (implication : ∀ key value, P key value → Q key value) (all : Search.RedBlack.ForallT P t) :
    Search.RedBlack.ForallT Q t := Search.RedBlack.forallT_imp implication all

example (ltb : Int → Int → Bool) (P : Int → Nat → Prop)
    (h4 : P 4 104) (h5 : P 5 105) (h2 : P 2 102) (h3 : P 3 303) :
    Search.RedBlack.ForallT P
      (Search.RedBlack.insert ltb 3 303
        (node black (node red (node red nil (4, 104) nil) (5, 105) nil) (2, 102) nil)) := by
  apply Search.RedBlack.insert_forallT ltb P 3 303 _ h3
  exact ⟨h2, ⟨h5, ⟨h4, trivial, trivial⟩, trivial⟩, trivial⟩

example {κ : Type u} {ν : Type v} (P : κ → ν → Prop) (t : Search.RedBlack.Tree κ ν) :
    Search.RedBlack.ForallT P (Search.RedBlack.makeBlack t) ↔ Search.RedBlack.ForallT P t :=
  Search.RedBlack.makeBlack_forallT P t

end Examples.RedBlackTrees

/- 11-erasure-observations -/
namespace Examples.RedBlackTrees
open RBTree RBNode RBColor
universe u v

example {κ : Type u} {ν : Type v} (ltb : κ → κ → Bool) (query : κ)
    (t : Search.RedBlack.Tree κ ν) :
    Search.OrderedMap.DecodedKeys.lookup? ltb query (Search.RedBlack.eraseColors t) =
      Search.RedBlack.lookup? ltb query t :=
  Search.RedBlack.eraseColors_lookup? ltb query t

example {κ : Type u} {ν : Type v} (ltb : κ → κ → Bool) (default : ν) (query : κ)
    (t : Search.RedBlack.Tree κ ν) :
    Search.OrderedMap.DecodedKeys.lookup ltb default query (Search.RedBlack.eraseColors t) =
      Search.RedBlack.lookup ltb default query t :=
  Search.RedBlack.eraseColors_lookup ltb default query t

example {κ : Type u} {ν : Type v} (t : Search.RedBlack.Tree κ ν) (suffix : List (κ × ν)) :
    Search.OrderedMap.DecodedKeys.elementsAux (Search.RedBlack.eraseColors t) suffix =
      Search.RedBlack.elementsAux t suffix :=
  Search.RedBlack.eraseColors_elementsAux t suffix

example {κ : Type u} {ν : Type v} (t : Search.RedBlack.Tree κ ν) :
    Search.OrderedMap.DecodedKeys.elements (Search.RedBlack.eraseColors t) =
      Search.RedBlack.elements t :=
  Search.RedBlack.eraseColors_elements t

example (suffix : List (Int × Nat)) :
    Search.OrderedMap.DecodedKeys.elementsAux
      (Search.RedBlack.eraseColors
        (node black (node red (node red nil (4, 104) nil) (5, 105) nil) (2, 102) nil)) suffix =
      [(4, 104), (5, 105), (2, 102)] ++ suffix := by
  rw [Search.RedBlack.eraseColors_elementsAux]
  rfl

end Examples.RedBlackTrees

/- 12-erasure-dimensions -/
namespace Examples.RedBlackTrees
open RBTree RBNode RBColor
universe u v

example {κ : Type u} {ν : Type v} (t : Search.RedBlack.Tree κ ν) :
    BinaryTree.height (Search.RedBlack.eraseColors t) = RBTree.RBNode.depth t :=
  Search.RedBlack.eraseColors_height t

example {κ : Type u} {ν : Type v} (t : Search.RedBlack.Tree κ ν) :
    BinaryTree.numNodes (Search.RedBlack.eraseColors t) = RBTree.RBNode.size t :=
  Search.RedBlack.eraseColors_numNodes t

private abbrev dimensionInput : Search.RedBlack.Tree Int Nat :=
  node black (node red nil (-2, 7) nil) (0, 8)
    (node black nil (3, 9) (node red nil (4, 10) nil))

example : BinaryTree.height (Search.RedBlack.eraseColors dimensionInput) = 3 ∧
    BinaryTree.numNodes (Search.RedBlack.eraseColors dimensionInput) = 4 := by
  rw [Search.RedBlack.eraseColors_height, Search.RedBlack.eraseColors_numNodes]
  exact ⟨rfl, rfl⟩

example : BinaryTree.height (Search.RedBlack.eraseColors (nil : Search.RedBlack.Tree Int Nat)) = 0 ∧
    BinaryTree.numNodes (Search.RedBlack.eraseColors (nil : Search.RedBlack.Tree Int Nat)) = 0 :=
  ⟨rfl, rfl⟩

end Examples.RedBlackTrees

/- 13-blackening-observations -/
namespace Examples.RedBlackTrees
open RBTree RBNode RBColor
universe u v

example {κ : Type u} {ν : Type v} (ltb : κ → κ → Bool) (query : κ) (default : ν)
    (t : Search.RedBlack.Tree κ ν) :
    Search.RedBlack.lookup? ltb query (Search.RedBlack.makeBlack t) =
      Search.RedBlack.lookup? ltb query t ∧
    Search.RedBlack.lookup ltb default query (Search.RedBlack.makeBlack t) =
      Search.RedBlack.lookup ltb default query t :=
  ⟨Search.RedBlack.lookup?_makeBlack ltb query t,
    Search.RedBlack.lookup_makeBlack ltb default query t⟩

example {κ : Type u} {ν : Type v} (t : Search.RedBlack.Tree κ ν) (suffix : List (κ × ν)) :
    Search.RedBlack.elements (Search.RedBlack.makeBlack t) = Search.RedBlack.elements t ∧
    Search.RedBlack.elementsAux (Search.RedBlack.makeBlack t) suffix =
      Search.RedBlack.elementsAux t suffix :=
  ⟨Search.RedBlack.makeBlack_elements t, Search.RedBlack.makeBlack_elementsAux t suffix⟩

example {κ : Type u} {ν : Type v} (t : Search.RedBlack.Tree κ ν) :
    Search.RedBlack.eraseColors (Search.RedBlack.makeBlack t) = Search.RedBlack.eraseColors t :=
  Search.RedBlack.eraseColors_makeBlack t

end Examples.RedBlackTrees

/- 14-provider-boundaries -/
namespace Examples.RedBlackTrees
open RBTree RBNode RBColor
open Representations.SignedComparison (intLtb)

/-- Provider insertion leaves the new root red when its input is empty. -/
example (cmp : Int × Nat → Int × Nat → Ordering) (ltb : Int → Int → Bool) :
    RBTree.RBNode.insert cmp nil (1, 101) = node red nil (1, 101) nil ∧
    Search.RedBlack.insert ltb 1 101 nil = node black nil (1, 101) nil := ⟨rfl, rfl⟩

example (cmp : Int × Nat → Int × Nat → Ordering) (ltb : Int → Int → Bool) :
    RBTree.RBNode.insert cmp nil (1, 101) ≠ Search.RedBlack.insert ltb 1 101 nil := by
  intro same
  change node red nil (1, 101) nil = node black nil (1, 101) nil at same
  cases same

private abbrev providerCrossRight : Search.RedBlack.Tree Int Nat :=
  node black (node red (node red nil (0, 100) nil) (1, 101) nil) (3, 103) nil

/-- The provider's one-side repair retains root 3 where the source promotes root 1. -/
example : RBTree.RBNode.ins (fun (a b : Int × Nat) => compare a.1 b.1)
      (4, 104) providerCrossRight =
    node black (node red (node red nil (0, 100) nil) (1, 101) nil) (3, 103)
      (node red nil (4, 104) nil) := rfl

example : Search.RedBlack.ins intLtb 4 104 providerCrossRight ≠
    RBTree.RBNode.ins (fun (a b : Int × Nat) => compare a.1 b.1) (4, 104) providerCrossRight := by
  intro same
  have roots := congrArg RBTree.RBNode.root? same
  have keys := congrArg (Option.map Prod.fst) roots
  have wrong : (1 : Int) = 3 := Option.some.inj keys
  cases wrong

/-- An ordinary suffix is appended literally, without a sorting or deduplication phase. -/
example : Search.RedBlack.elementsAux
      (node black (node red nil (4, 104) nil) (5, 105) (node red nil (2, 102) nil))
      [(99, 909), (-1, 808)] =
    [(4, 104), (5, 105), (2, 102), (99, 909), (-1, 808)] := rfl

end Examples.RedBlackTrees
