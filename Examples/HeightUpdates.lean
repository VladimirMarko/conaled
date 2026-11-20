import Applications.Trees.AVL.Updates
import Examples.HeightRebalance

/-! Connected cached-update cases U01–U28, with the retained paper's expected
shapes and complete-summary observations. Expectations and their attribution are
recorded in `docs/research/fdsa-height-updates.md`. Finite computations establish
literal premises; the contracts below consume the public update theorems.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.HeightUpdates
open Trees
universe u v
variable {α : Type u} {σ : Type v}

private def balancedDecidable (d : Nat) :
    (t : BinaryTree α) → Decidable (HeightBalance.BalancedD d t)
  | .nil => isTrue trivial
  | .node _ l r => by
      letI := balancedDecidable d l
      letI := balancedDecidable d r
      exact inferInstanceAs (Decidable
        (HeightBalance.BalancedD d l ∧ HeightBalance.BalancedD d r ∧
          l.height ≤ r.height + d ∧ r.height ≤ l.height + d))

private def cacheDecidable [DecidableEq σ] (ann : HeightBalance.HeightAnnotation α σ) :
    (t : BinaryTree (α × σ)) → Decidable (HeightBalance.CacheValid ann t)
  | .nil => isTrue (HeightBalance.cacheValid_nil ann)
  | .node (a, s) l r => by
      letI := cacheDecidable ann l
      letI := cacheDecidable ann r
      exact inferInstanceAs (Decidable
        (HeightBalance.CacheValid ann l ∧ HeightBalance.CacheValid ann r ∧
          s = ann.combine (Cached.read ann.empty l) a (Cached.read ann.empty r)))

local instance (d : Nat) (t : BinaryTree α) :
    Decidable (HeightBalance.BalancedD d t) := balancedDecidable d t
local instance [DecidableEq σ] (ann : HeightBalance.HeightAnnotation α σ)
    (t : BinaryTree (α × σ)) : Decidable (HeightBalance.CacheValid ann t) :=
  cacheDecidable ann t
local instance [DecidableEq σ] (ann : HeightBalance.HeightAnnotation α σ) (d : Nat)
    (t : BinaryTree (α × σ)) : Decidable (HeightBalance.ValidD ann d t) :=
  inferInstanceAs (Decidable
    (HeightBalance.BalancedD d (Cached.erase t) ∧ HeightBalance.CacheValid ann t))
local instance (t : BinaryTree α) : Decidable (AVL.Balanced t) :=
  decidable_of_iff (HeightBalance.BalancedD 1 t) (AVL.balancedD_one_iff t)
local instance (t : BinaryTree (α × Nat)) : Decidable (AVL.CacheValid t) :=
  cacheDecidable AVL.heightAnnotation t
local instance (t : BinaryTree (α × Nat)) : Decidable (AVL.Valid t) :=
  decidable_of_iff (HeightBalance.ValidD AVL.heightAnnotation 1 t) (AVL.validD_one_iff t)
local instance (xs : List Nat) : Decidable (Search.OrderedList.Strict xs) :=
  inferInstanceAs (Decidable (xs.Pairwise (· < ·)))

abbrev HTree := BinaryTree (Nat × Nat)
abbrev payloads (t : BinaryTree (α × σ)) : List α := inorder (Cached.erase t)
def heightNode (a : Nat) (l r : HTree) : HTree := AVL.node l a r
def heightSingleton (a : Nat) : HTree := heightNode a .nil .nil
def base : HTree := heightNode 4 (heightSingleton 2) (heightNode 6 (heightSingleton 5) .nil)
def withSeven : HTree := heightNode 4 (heightSingleton 2) (heightNode 6 (heightSingleton 5) (heightSingleton 7))
def perfectSeven : HTree := heightNode 4 (heightNode 2 (heightSingleton 1) (heightSingleton 3)) (heightNode 6 (heightSingleton 5) (heightSingleton 7))

private theorem ordinary_insert_example (x : Nat) (t out : HTree)
    (he : AVL.insert x t = out) (hv : AVL.Valid t)
    (hs : Search.OrderedList.Strict (payloads t)) :
    AVL.insert x t = out ∧ AVL.Valid out ∧
      (out.height = t.height ∨ out.height = t.height + 1) ∧
      payloads out = Search.OrderedList.insert x (payloads t) := by
  have h := AVL.valid_insert x t hv
  refine ⟨he, ?_, ?_, ?_⟩
  · simpa only [he] using h.1
  · simpa only [he] using h.2
  · simpa only [he] using AVL.inorder_insert x t hs

private theorem ordinary_delete_example (x : Nat) (t out : HTree)
    (he : AVL.delete x t = out) (hv : AVL.Valid t)
    (hs : Search.OrderedList.Strict (payloads t)) :
    AVL.delete x t = out ∧ AVL.Valid out ∧
      (t.height = out.height ∨ t.height = out.height + 1) ∧
      payloads out = Search.OrderedList.delete x (payloads t) := by
  have h := AVL.valid_delete x t hv
  refine ⟨he, ?_, ?_, ?_⟩
  · simpa only [he] using h.1
  · simpa only [he] using h.2
  · simpa only [he] using AVL.inorder_delete x t hs

private theorem generic_insert_example (ann : HeightBalance.HeightAnnotation Nat σ)
    (d x : Nat) (t out : BinaryTree (Nat × σ))
    (he : HeightBalance.insert ann d x t = out) (hd : 1 ≤ d)
    (hv : HeightBalance.ValidD ann d t)
    (hs : Search.OrderedList.Strict (payloads t)) :
    HeightBalance.insert ann d x t = out ∧ HeightBalance.ValidD ann d out ∧
      (out.height = t.height ∨ out.height = t.height + 1) ∧
      payloads out = Search.OrderedList.insert x (payloads t) := by
  have h := HeightBalance.validD_insert ann d x t hd hv
  refine ⟨he, ?_, ?_, ?_⟩
  · simpa only [he] using h.1
  · simpa only [he] using h.2
  · simpa only [he] using HeightBalance.inorder_insert ann d x t hs

private theorem generic_delete_example (ann : HeightBalance.HeightAnnotation Nat σ)
    (d x : Nat) (t out : BinaryTree (Nat × σ))
    (he : HeightBalance.delete ann d x t = out) (hd : 1 ≤ d)
    (hv : HeightBalance.ValidD ann d t)
    (hs : Search.OrderedList.Strict (payloads t)) :
    HeightBalance.delete ann d x t = out ∧ HeightBalance.ValidD ann d out ∧
      (t.height = out.height ∨ t.height = out.height + 1) ∧
      payloads out = Search.OrderedList.delete x (payloads t) := by
  have h := HeightBalance.validD_delete ann d x t hd hv
  refine ⟨he, ?_, ?_, ?_⟩
  · simpa only [he] using h.1
  · simpa only [he] using h.2
  · simpa only [he] using HeightBalance.inorder_delete ann d x t hs

private theorem ordinary_split_example (t out : HTree) (m : Nat)
    (he : AVL.splitMaxOption t = some (out, m)) (hv : AVL.Valid t) :
    AVL.splitMaxOption t = some (out, m) ∧ AVL.Valid out ∧
      (t.height = out.height ∨ t.height = out.height + 1) ∧
      payloads out ++ [m] = payloads t :=
  ⟨he, (AVL.valid_splitMaxOption t out m he hv).1,
    (AVL.valid_splitMaxOption t out m he hv).2,
    AVL.inorder_splitMaxOption t out m he⟩

/-! U01–U06: raw recurrence, no-op and semantic-assumption boundaries. -/
theorem empty_insertion :
    AVL.insert 5 (.nil : HTree) = heightSingleton 5 ∧ AVL.Valid (heightSingleton 5) ∧
      ((heightSingleton 5).height = 0 ∨ (heightSingleton 5).height = 1) ∧
      payloads (heightSingleton 5) = Search.OrderedList.insert 5 [] :=
  ordinary_insert_example 5 .nil (heightSingleton 5) (AVL.insert_nil 5) AVL.valid_nil
    Search.OrderedList.strict_nil

theorem empty_insertion_cache : AVL.ht (AVL.insert 5 (.nil : HTree)) = 1 := by
  rw [AVL.insert_nil]
  rfl

def rawDuplicate : HTree := .node (5, 99) .nil .nil
theorem raw_duplicate_identity : AVL.insert 5 rawDuplicate = rawDuplicate :=
  AVL.insert_of_not_lt_of_not_lt 5 5 99 .nil .nil (by decide) (by decide)
theorem raw_duplicate_not_repaired :
    AVL.ht (AVL.insert 5 rawDuplicate) = 99 ∧
      ¬ AVL.CacheValid (AVL.insert 5 rawDuplicate) := by
  rw [raw_duplicate_identity]
  decide

theorem deep_duplicate :
    AVL.insert 5 base = base ∧ AVL.Valid base ∧
      (base.height = base.height ∨ base.height = base.height + 1) ∧
      payloads base = Search.OrderedList.insert 5 (payloads base) :=
  ordinary_insert_example 5 base base (by decide) (by decide) (by decide)

theorem absent_deletion :
    AVL.delete 9 base = base ∧ AVL.Valid base ∧
      (base.height = base.height ∨ base.height = base.height + 1) ∧
      payloads base = Search.OrderedList.delete 9 (payloads base) :=
  ordinary_delete_example 9 base base (by decide) (by decide) (by decide)

theorem duplicate_and_absent_observations :
    base.height = 3 ∧ payloads base = [2, 4, 5, 6] ∧
      Search.OrderedList.delete 9 (payloads base) = payloads base ∧
      Search.OrderedList.Strict (payloads (AVL.insert 5 base)) ∧
      Search.OrderedList.Strict (payloads (AVL.delete 9 base)) :=
  ⟨by decide, by decide, Search.OrderedList.delete_of_not_mem 9 (by decide),
    AVL.strict_inorder_insert 5 base (by decide),
    AVL.strict_inorder_delete 9 base (by decide)⟩

def rawAbsent : HTree := .node (4, 99) (.node (2, 2) .nil .nil) .nil
theorem raw_absent_rotates : AVL.delete 9 rawAbsent = heightNode 2 .nil (heightSingleton 4) := by
  unfold rawAbsent
  rw [AVL.delete_of_gt 9 4 99 (.node (2, 2) .nil .nil) .nil (by decide) (by decide),
    AVL.delete_nil]
  exact AVL.balL_single .nil 2 2 .nil 4 .nil (by decide) (by decide)

theorem raw_absent_semantics :
    payloads (AVL.delete 9 rawAbsent) = Search.OrderedList.delete 9 (payloads rawAbsent) ∧
      payloads (AVL.delete 9 rawAbsent) = [2, 4] ∧
      AVL.delete 9 rawAbsent ≠ rawAbsent ∧ ¬ AVL.CacheValid rawAbsent :=
  ⟨AVL.inorder_delete 9 rawAbsent (by decide), by rw [raw_absent_rotates]; decide,
    by rw [raw_absent_rotates]; decide, by decide⟩

def unordered : HTree := heightNode 5 (heightSingleton 9) .nil
theorem unordered_still_valid :
    AVL.Valid unordered ∧ AVL.Valid (AVL.insert 9 unordered) ∧ AVL.Valid (AVL.delete 9 unordered) :=
  ⟨by decide, (AVL.valid_insert 9 unordered (by decide)).1,
    (AVL.valid_delete 9 unordered (by decide)).1⟩

theorem strictness_is_needed :
    payloads (AVL.insert 9 unordered) = [9, 5, 9] ∧
      Search.OrderedList.insert 9 (payloads unordered) = [9, 5] ∧
      payloads (AVL.delete 9 unordered) = [9, 5] ∧
      Search.OrderedList.delete 9 (payloads unordered) = [5] ∧
      ¬ Search.OrderedList.Strict (payloads unordered) := by decide

/-! U07: all four ordinary insertion paths have the same independently fixed output. -/
def three : HTree := heightNode 2 (heightSingleton 1) (heightSingleton 3)
theorem insert_left_single :
    AVL.insert 1 (heightNode 3 (heightSingleton 2) .nil) = three ∧ AVL.Valid three ∧
      (three.height = (heightNode 3 (heightSingleton 2) .nil).height ∨
        three.height = (heightNode 3 (heightSingleton 2) .nil).height + 1) ∧
      payloads three = Search.OrderedList.insert 1 (payloads (heightNode 3 (heightSingleton 2) .nil)) :=
  ordinary_insert_example 1 _ three (by decide) (by decide) (by decide)
theorem insert_right_single :
    AVL.insert 3 (heightNode 1 .nil (heightSingleton 2)) = three ∧ AVL.Valid three ∧
      (three.height = (heightNode 1 .nil (heightSingleton 2)).height ∨
        three.height = (heightNode 1 .nil (heightSingleton 2)).height + 1) ∧
      payloads three = Search.OrderedList.insert 3 (payloads (heightNode 1 .nil (heightSingleton 2))) :=
  ordinary_insert_example 3 _ three (by decide) (by decide) (by decide)
theorem insert_left_double :
    AVL.insert 2 (heightNode 3 (heightSingleton 1) .nil) = three ∧ AVL.Valid three ∧
      (three.height = (heightNode 3 (heightSingleton 1) .nil).height ∨
        three.height = (heightNode 3 (heightSingleton 1) .nil).height + 1) ∧
      payloads three = Search.OrderedList.insert 2 (payloads (heightNode 3 (heightSingleton 1) .nil)) :=
  ordinary_insert_example 2 _ three (by decide) (by decide) (by decide)
theorem insert_right_double :
    AVL.insert 2 (heightNode 1 .nil (heightSingleton 3)) = three ∧ AVL.Valid three ∧
      (three.height = (heightNode 1 .nil (heightSingleton 3)).height ∨
        three.height = (heightNode 1 .nil (heightSingleton 3)).height + 1) ∧
      payloads three = Search.OrderedList.insert 2 (payloads (heightNode 1 .nil (heightSingleton 3))) :=
  ordinary_insert_example 2 _ three (by decide) (by decide) (by decide)
theorem ordinary_insertion_observations :
    three.height = 2 ∧ AVL.ht three = 2 ∧ payloads three = [1, 2, 3] := by decide

/-! U08: the annotation changes even when neither affected height grows. -/
abbrev maximumAnnotation := HeightRebalance.maximumAnnotation
abbrev wordAnnotation := HeightRebalance.wordAnnotation
abbrev MTree := HeightRebalance.MTree
abbrev WTree := HeightRebalance.WTree
def maximumBase : MTree := Cached.annotate maximumAnnotation.empty maximumAnnotation.combine
  (Cached.erase base)
def maximumWithSeven : MTree := Cached.annotate maximumAnnotation.empty maximumAnnotation.combine
  (Cached.erase withSeven)
def wordBase : WTree := Cached.annotate (wordAnnotation Nat).empty (wordAnnotation Nat).combine
  (Cached.erase base)
def wordWithSeven : WTree := Cached.annotate (wordAnnotation Nat).empty (wordAnnotation Nat).combine
  (Cached.erase withSeven)

theorem same_height_maximum_insert :
    HeightBalance.insert maximumAnnotation 1 7 maximumBase = maximumWithSeven ∧
      HeightBalance.ValidD maximumAnnotation 1 maximumWithSeven ∧
      (maximumWithSeven.height = maximumBase.height ∨
        maximumWithSeven.height = maximumBase.height + 1) ∧
      payloads maximumWithSeven = Search.OrderedList.insert 7 (payloads maximumBase) :=
  generic_insert_example maximumAnnotation 1 7 maximumBase maximumWithSeven
    (by decide) (by decide) (by decide) (by decide)

theorem same_height_word_insert :
    HeightBalance.insert (wordAnnotation Nat) 1 7 wordBase = wordWithSeven ∧
      HeightBalance.ValidD (wordAnnotation Nat) 1 wordWithSeven ∧
      (wordWithSeven.height = wordBase.height ∨ wordWithSeven.height = wordBase.height + 1) ∧
      payloads wordWithSeven = Search.OrderedList.insert 7 (payloads wordBase) :=
  generic_insert_example (wordAnnotation Nat) 1 7 wordBase wordWithSeven
    (by decide) (by decide) (by decide) (by decide)

theorem inserted_maximum_semantics :
    (Cached.read maximumAnnotation.empty
      (HeightBalance.insert maximumAnnotation 1 7 maximumBase)).2 =
      (payloads (HeightBalance.insert maximumAnnotation 1 7 maximumBase)).max? :=
  HeightRebalance.maximum_reader_eq_list_maximum _
    (HeightBalance.cacheValid_insert maximumAnnotation 1 7 maximumBase (by decide))

theorem inserted_word_semantics :
    (Cached.read (wordAnnotation Nat).empty
      (HeightBalance.insert (wordAnnotation Nat) 1 7 wordBase)).2 =
      payloads (HeightBalance.insert (wordAnnotation Nat) 1 7 wordBase) :=
  HeightRebalance.word_reader_eq_inorder _
    (HeightBalance.cacheValid_insert (wordAnnotation Nat) 1 7 wordBase (by decide))

theorem same_height_insert_readers :
    maximumBase.height = 3 ∧ maximumWithSeven.height = 3 ∧
      Cached.read maximumAnnotation.empty maximumBase = (3, some 6) ∧
      Cached.read maximumAnnotation.empty maximumWithSeven = (3, some 7) ∧
      Cached.read (wordAnnotation Nat).empty wordBase = (3, [2, 4, 5, 6]) ∧
      Cached.read (wordAnnotation Nat).empty wordWithSeven = (3, [2, 4, 5, 6, 7]) := by decide


/-! U09–U11 and U23–U24: literal larger-tolerance shapes, tied to universal contracts. -/

/-- U09: this fixture fixes the expected payload positions independently of the program. -/
def insertD2SingleLeftInput : HTree := heightNode 4 (heightNode 3 (heightSingleton 2) .nil) .nil
def insertD2SingleLeftOutput : HTree := heightNode 3 (heightNode 2 (heightSingleton 1) .nil) (heightSingleton 4)
theorem insert_d2_single_left :
    HeightBalance.insert AVL.heightAnnotation 2 1 insertD2SingleLeftInput = insertD2SingleLeftOutput ∧
      HeightBalance.ValidD AVL.heightAnnotation 2 insertD2SingleLeftOutput ∧
      (insertD2SingleLeftOutput.height = insertD2SingleLeftInput.height ∨ insertD2SingleLeftOutput.height = insertD2SingleLeftInput.height + 1) ∧
      payloads insertD2SingleLeftOutput = Search.OrderedList.insert 1 (payloads insertD2SingleLeftInput) :=
  generic_insert_example AVL.heightAnnotation 2 1 insertD2SingleLeftInput insertD2SingleLeftOutput
    (by decide) (by decide) (by decide) (by decide)

/-- U09: this fixture fixes the expected payload positions independently of the program. -/
def insertD3SingleLeftInput : HTree := heightNode 5 (heightNode 4 (heightNode 3 (heightSingleton 2) .nil) .nil) .nil
def insertD3SingleLeftOutput : HTree := heightNode 4 (heightNode 3 (heightNode 2 (heightSingleton 1) .nil) .nil) (heightSingleton 5)
theorem insert_d3_single_left :
    HeightBalance.insert AVL.heightAnnotation 3 1 insertD3SingleLeftInput = insertD3SingleLeftOutput ∧
      HeightBalance.ValidD AVL.heightAnnotation 3 insertD3SingleLeftOutput ∧
      (insertD3SingleLeftOutput.height = insertD3SingleLeftInput.height ∨ insertD3SingleLeftOutput.height = insertD3SingleLeftInput.height + 1) ∧
      payloads insertD3SingleLeftOutput = Search.OrderedList.insert 1 (payloads insertD3SingleLeftInput) :=
  generic_insert_example AVL.heightAnnotation 3 1 insertD3SingleLeftInput insertD3SingleLeftOutput
    (by decide) (by decide) (by decide) (by decide)

/-- U09: this fixture fixes the expected payload positions independently of the program. -/
def insertD2SingleRightInput : HTree := heightNode 1 .nil (heightNode 2 .nil (heightSingleton 3))
def insertD2SingleRightOutput : HTree := heightNode 2 (heightSingleton 1) (heightNode 3 .nil (heightSingleton 4))
theorem insert_d2_single_right :
    HeightBalance.insert AVL.heightAnnotation 2 4 insertD2SingleRightInput = insertD2SingleRightOutput ∧
      HeightBalance.ValidD AVL.heightAnnotation 2 insertD2SingleRightOutput ∧
      (insertD2SingleRightOutput.height = insertD2SingleRightInput.height ∨ insertD2SingleRightOutput.height = insertD2SingleRightInput.height + 1) ∧
      payloads insertD2SingleRightOutput = Search.OrderedList.insert 4 (payloads insertD2SingleRightInput) :=
  generic_insert_example AVL.heightAnnotation 2 4 insertD2SingleRightInput insertD2SingleRightOutput
    (by decide) (by decide) (by decide) (by decide)

/-- U09: this fixture fixes the expected payload positions independently of the program. -/
def insertD3SingleRightInput : HTree := heightNode 1 .nil (heightNode 2 .nil (heightNode 3 .nil (heightSingleton 4)))
def insertD3SingleRightOutput : HTree := heightNode 2 (heightSingleton 1) (heightNode 3 .nil (heightNode 4 .nil (heightSingleton 5)))
theorem insert_d3_single_right :
    HeightBalance.insert AVL.heightAnnotation 3 5 insertD3SingleRightInput = insertD3SingleRightOutput ∧
      HeightBalance.ValidD AVL.heightAnnotation 3 insertD3SingleRightOutput ∧
      (insertD3SingleRightOutput.height = insertD3SingleRightInput.height ∨ insertD3SingleRightOutput.height = insertD3SingleRightInput.height + 1) ∧
      payloads insertD3SingleRightOutput = Search.OrderedList.insert 5 (payloads insertD3SingleRightInput) :=
  generic_insert_example AVL.heightAnnotation 3 5 insertD3SingleRightInput insertD3SingleRightOutput
    (by decide) (by decide) (by decide) (by decide)

/-- U10: this fixture fixes the expected payload positions independently of the program. -/
def insertD2MiddleLeftInput : HTree := heightNode 5 (heightNode 1 .nil (heightSingleton 3)) .nil
def insertD2MiddleLeftOutput : HTree := heightNode 3 (heightNode 1 .nil (heightSingleton 2)) (heightSingleton 5)
theorem insert_d2_middle_left :
    HeightBalance.insert AVL.heightAnnotation 2 2 insertD2MiddleLeftInput = insertD2MiddleLeftOutput ∧
      HeightBalance.ValidD AVL.heightAnnotation 2 insertD2MiddleLeftOutput ∧
      (insertD2MiddleLeftOutput.height = insertD2MiddleLeftInput.height ∨ insertD2MiddleLeftOutput.height = insertD2MiddleLeftInput.height + 1) ∧
      payloads insertD2MiddleLeftOutput = Search.OrderedList.insert 2 (payloads insertD2MiddleLeftInput) :=
  generic_insert_example AVL.heightAnnotation 2 2 insertD2MiddleLeftInput insertD2MiddleLeftOutput
    (by decide) (by decide) (by decide) (by decide)

/-- U10: this fixture fixes the expected payload positions independently of the program. -/
def insertD2MiddleRightInput : HTree := heightNode 5 (heightNode 1 .nil (heightSingleton 3)) .nil
def insertD2MiddleRightOutput : HTree := heightNode 3 (heightSingleton 1) (heightNode 5 (heightSingleton 4) .nil)
theorem insert_d2_middle_right :
    HeightBalance.insert AVL.heightAnnotation 2 4 insertD2MiddleRightInput = insertD2MiddleRightOutput ∧
      HeightBalance.ValidD AVL.heightAnnotation 2 insertD2MiddleRightOutput ∧
      (insertD2MiddleRightOutput.height = insertD2MiddleRightInput.height ∨ insertD2MiddleRightOutput.height = insertD2MiddleRightInput.height + 1) ∧
      payloads insertD2MiddleRightOutput = Search.OrderedList.insert 4 (payloads insertD2MiddleRightInput) :=
  generic_insert_example AVL.heightAnnotation 2 4 insertD2MiddleRightInput insertD2MiddleRightOutput
    (by decide) (by decide) (by decide) (by decide)

/-- U11: this fixture fixes the expected payload positions independently of the program. -/
def insertD3MiddleRightInput : HTree := heightNode 7 (heightNode 1 .nil (heightNode 3 .nil (heightSingleton 5))) .nil
def insertD3MiddleRightOutput : HTree := heightNode 3 (heightSingleton 1) (heightNode 7 (heightNode 5 (heightSingleton 4) .nil) .nil)
theorem insert_d3_middle_right :
    HeightBalance.insert AVL.heightAnnotation 3 4 insertD3MiddleRightInput = insertD3MiddleRightOutput ∧
      HeightBalance.ValidD AVL.heightAnnotation 3 insertD3MiddleRightOutput ∧
      (insertD3MiddleRightOutput.height = insertD3MiddleRightInput.height ∨ insertD3MiddleRightOutput.height = insertD3MiddleRightInput.height + 1) ∧
      payloads insertD3MiddleRightOutput = Search.OrderedList.insert 4 (payloads insertD3MiddleRightInput) :=
  generic_insert_example AVL.heightAnnotation 3 4 insertD3MiddleRightInput insertD3MiddleRightOutput
    (by decide) (by decide) (by decide) (by decide)

/-- U11 supplemental: this fixture fixes the expected payload positions independently of the program. -/
def insertD3MiddleLeftInput : HTree := heightNode 7 (heightNode 1 .nil (heightNode 5 (heightSingleton 3) .nil)) .nil
def insertD3MiddleLeftOutput : HTree := heightNode 5 (heightNode 1 .nil (heightNode 3 .nil (heightSingleton 4))) (heightSingleton 7)
theorem insert_d3_middle_left :
    HeightBalance.insert AVL.heightAnnotation 3 4 insertD3MiddleLeftInput = insertD3MiddleLeftOutput ∧
      HeightBalance.ValidD AVL.heightAnnotation 3 insertD3MiddleLeftOutput ∧
      (insertD3MiddleLeftOutput.height = insertD3MiddleLeftInput.height ∨ insertD3MiddleLeftOutput.height = insertD3MiddleLeftInput.height + 1) ∧
      payloads insertD3MiddleLeftOutput = Search.OrderedList.insert 4 (payloads insertD3MiddleLeftInput) :=
  generic_insert_example AVL.heightAnnotation 3 4 insertD3MiddleLeftInput insertD3MiddleLeftOutput
    (by decide) (by decide) (by decide) (by decide)

/-- U23: this fixture fixes the expected payload positions independently of the program. -/
def deleteD2TieInput : HTree := heightNode 8 (heightNode 4 (heightNode 2 (heightSingleton 1) (heightSingleton 3)) (heightNode 6 (heightSingleton 5) (heightSingleton 7))) (heightSingleton 9)
def deleteD2TieOutput : HTree := heightNode 4 (heightNode 2 (heightSingleton 1) (heightSingleton 3)) (heightNode 8 (heightNode 6 (heightSingleton 5) (heightSingleton 7)) .nil)
theorem delete_d2_tie :
    HeightBalance.delete AVL.heightAnnotation 2 9 deleteD2TieInput = deleteD2TieOutput ∧
      HeightBalance.ValidD AVL.heightAnnotation 2 deleteD2TieOutput ∧
      (deleteD2TieInput.height = deleteD2TieOutput.height ∨ deleteD2TieInput.height = deleteD2TieOutput.height + 1) ∧
      payloads deleteD2TieOutput = Search.OrderedList.delete 9 (payloads deleteD2TieInput) :=
  generic_delete_example AVL.heightAnnotation 2 9 deleteD2TieInput deleteD2TieOutput
    (by decide) (by decide) (by decide) (by decide)

/-- U23: this fixture fixes the expected payload positions independently of the program. -/
def deleteD2StrictSingleInput : HTree := heightNode 6 (heightNode 4 (heightNode 2 (heightSingleton 1) (heightSingleton 3)) (heightSingleton 5)) (heightSingleton 7)
def deleteD2StrictSingleOutput : HTree := heightNode 4 (heightNode 2 (heightSingleton 1) (heightSingleton 3)) (heightNode 6 (heightSingleton 5) .nil)
theorem delete_d2_strict_single :
    HeightBalance.delete AVL.heightAnnotation 2 7 deleteD2StrictSingleInput = deleteD2StrictSingleOutput ∧
      HeightBalance.ValidD AVL.heightAnnotation 2 deleteD2StrictSingleOutput ∧
      (deleteD2StrictSingleInput.height = deleteD2StrictSingleOutput.height ∨ deleteD2StrictSingleInput.height = deleteD2StrictSingleOutput.height + 1) ∧
      payloads deleteD2StrictSingleOutput = Search.OrderedList.delete 7 (payloads deleteD2StrictSingleInput) :=
  generic_delete_example AVL.heightAnnotation 2 7 deleteD2StrictSingleInput deleteD2StrictSingleOutput
    (by decide) (by decide) (by decide) (by decide)

/-- U23: this fixture fixes the expected payload positions independently of the program. -/
def deleteD2MiddleLeftInput : HTree := heightNode 5 (heightNode 1 .nil (heightNode 3 (heightSingleton 2) .nil)) (heightSingleton 6)
def deleteD2MiddleLeftOutput : HTree := heightNode 3 (heightNode 1 .nil (heightSingleton 2)) (heightSingleton 5)
theorem delete_d2_middle_left :
    HeightBalance.delete AVL.heightAnnotation 2 6 deleteD2MiddleLeftInput = deleteD2MiddleLeftOutput ∧
      HeightBalance.ValidD AVL.heightAnnotation 2 deleteD2MiddleLeftOutput ∧
      (deleteD2MiddleLeftInput.height = deleteD2MiddleLeftOutput.height ∨ deleteD2MiddleLeftInput.height = deleteD2MiddleLeftOutput.height + 1) ∧
      payloads deleteD2MiddleLeftOutput = Search.OrderedList.delete 6 (payloads deleteD2MiddleLeftInput) :=
  generic_delete_example AVL.heightAnnotation 2 6 deleteD2MiddleLeftInput deleteD2MiddleLeftOutput
    (by decide) (by decide) (by decide) (by decide)

/-- U23: this fixture fixes the expected payload positions independently of the program. -/
def deleteD2MiddleRightInput : HTree := heightNode 5 (heightNode 1 .nil (heightNode 3 .nil (heightSingleton 4))) (heightSingleton 6)
def deleteD2MiddleRightOutput : HTree := heightNode 3 (heightSingleton 1) (heightNode 5 (heightSingleton 4) .nil)
theorem delete_d2_middle_right :
    HeightBalance.delete AVL.heightAnnotation 2 6 deleteD2MiddleRightInput = deleteD2MiddleRightOutput ∧
      HeightBalance.ValidD AVL.heightAnnotation 2 deleteD2MiddleRightOutput ∧
      (deleteD2MiddleRightInput.height = deleteD2MiddleRightOutput.height ∨ deleteD2MiddleRightInput.height = deleteD2MiddleRightOutput.height + 1) ∧
      payloads deleteD2MiddleRightOutput = Search.OrderedList.delete 6 (payloads deleteD2MiddleRightInput) :=
  generic_delete_example AVL.heightAnnotation 2 6 deleteD2MiddleRightInput deleteD2MiddleRightOutput
    (by decide) (by decide) (by decide) (by decide)

/-- U24: this fixture fixes the expected payload positions independently of the program. -/
def deleteD3MiddleRightInput : HTree := heightNode 7 (heightNode 1 .nil (heightNode 3 .nil (heightNode 5 (heightSingleton 4) .nil))) (heightSingleton 8)
def deleteD3MiddleRightOutput : HTree := heightNode 3 (heightSingleton 1) (heightNode 7 (heightNode 5 (heightSingleton 4) .nil) .nil)
theorem delete_d3_middle_right :
    HeightBalance.delete AVL.heightAnnotation 3 8 deleteD3MiddleRightInput = deleteD3MiddleRightOutput ∧
      HeightBalance.ValidD AVL.heightAnnotation 3 deleteD3MiddleRightOutput ∧
      (deleteD3MiddleRightInput.height = deleteD3MiddleRightOutput.height ∨ deleteD3MiddleRightInput.height = deleteD3MiddleRightOutput.height + 1) ∧
      payloads deleteD3MiddleRightOutput = Search.OrderedList.delete 8 (payloads deleteD3MiddleRightInput) :=
  generic_delete_example AVL.heightAnnotation 3 8 deleteD3MiddleRightInput deleteD3MiddleRightOutput
    (by decide) (by decide) (by decide) (by decide)

/-- U24 supplemental: this fixture fixes the expected payload positions independently of the program. -/
def deleteD3MiddleLeftInput : HTree := heightNode 7 (heightNode 1 .nil (heightNode 5 (heightNode 3 .nil (heightSingleton 4)) .nil)) (heightSingleton 8)
def deleteD3MiddleLeftOutput : HTree := heightNode 5 (heightNode 1 .nil (heightNode 3 .nil (heightSingleton 4))) (heightSingleton 7)
theorem delete_d3_middle_left :
    HeightBalance.delete AVL.heightAnnotation 3 8 deleteD3MiddleLeftInput = deleteD3MiddleLeftOutput ∧
      HeightBalance.ValidD AVL.heightAnnotation 3 deleteD3MiddleLeftOutput ∧
      (deleteD3MiddleLeftInput.height = deleteD3MiddleLeftOutput.height ∨ deleteD3MiddleLeftInput.height = deleteD3MiddleLeftOutput.height + 1) ∧
      payloads deleteD3MiddleLeftOutput = Search.OrderedList.delete 8 (payloads deleteD3MiddleLeftInput) :=
  generic_delete_example AVL.heightAnnotation 3 8 deleteD3MiddleLeftInput deleteD3MiddleLeftOutput
    (by decide) (by decide) (by decide) (by decide)

/-- U23 supplemental: this fixture fixes the expected payload positions independently of the program. -/
def deleteD3TieInput : HTree := heightNode 8 (heightNode 4 (heightNode 3 (heightNode 2 (heightSingleton 1) .nil) .nil) (heightNode 7 (heightNode 6 (heightSingleton 5) .nil) .nil)) (heightSingleton 9)
def deleteD3TieOutput : HTree := heightNode 4 (heightNode 3 (heightNode 2 (heightSingleton 1) .nil) .nil) (heightNode 8 (heightNode 7 (heightNode 6 (heightSingleton 5) .nil) .nil) .nil)
theorem delete_d3_tie :
    HeightBalance.delete AVL.heightAnnotation 3 9 deleteD3TieInput = deleteD3TieOutput ∧
      HeightBalance.ValidD AVL.heightAnnotation 3 deleteD3TieOutput ∧
      (deleteD3TieInput.height = deleteD3TieOutput.height ∨ deleteD3TieInput.height = deleteD3TieOutput.height + 1) ∧
      payloads deleteD3TieOutput = Search.OrderedList.delete 9 (payloads deleteD3TieInput) :=
  generic_delete_example AVL.heightAnnotation 3 9 deleteD3TieInput deleteD3TieOutput
    (by decide) (by decide) (by decide) (by decide)

/-- U23 supplemental: this fixture fixes the expected payload positions independently of the program. -/
def deleteD3StrictSingleInput : HTree := heightNode 6 (heightNode 4 (heightNode 3 (heightNode 2 (heightSingleton 1) .nil) .nil) (heightSingleton 5)) (heightSingleton 7)
def deleteD3StrictSingleOutput : HTree := heightNode 4 (heightNode 3 (heightNode 2 (heightSingleton 1) .nil) .nil) (heightNode 6 (heightSingleton 5) .nil)
theorem delete_d3_strict_single :
    HeightBalance.delete AVL.heightAnnotation 3 7 deleteD3StrictSingleInput = deleteD3StrictSingleOutput ∧
      HeightBalance.ValidD AVL.heightAnnotation 3 deleteD3StrictSingleOutput ∧
      (deleteD3StrictSingleInput.height = deleteD3StrictSingleOutput.height ∨ deleteD3StrictSingleInput.height = deleteD3StrictSingleOutput.height + 1) ∧
      payloads deleteD3StrictSingleOutput = Search.OrderedList.delete 7 (payloads deleteD3StrictSingleInput) :=
  generic_delete_example AVL.heightAnnotation 3 7 deleteD3StrictSingleInput deleteD3StrictSingleOutput
    (by decide) (by decide) (by decide) (by decide)

/-! U17–U22: exact predecessor deletion and both height alternatives. -/

/-- U17. -/
def deleteEmptyInput : HTree := .nil
def deleteEmptyOutput : HTree := .nil
theorem delete_empty :
    AVL.delete 8 deleteEmptyInput = deleteEmptyOutput ∧ AVL.Valid deleteEmptyOutput ∧
      (deleteEmptyInput.height = deleteEmptyOutput.height ∨ deleteEmptyInput.height = deleteEmptyOutput.height + 1) ∧
      payloads deleteEmptyOutput = Search.OrderedList.delete 8 (payloads deleteEmptyInput) :=
  ordinary_delete_example 8 deleteEmptyInput deleteEmptyOutput (by decide) (by decide) (by decide)

/-- U17. -/
def deleteSingletonInput : HTree := heightSingleton 5
def deleteSingletonOutput : HTree := .nil
theorem delete_singleton :
    AVL.delete 5 deleteSingletonInput = deleteSingletonOutput ∧ AVL.Valid deleteSingletonOutput ∧
      (deleteSingletonInput.height = deleteSingletonOutput.height ∨ deleteSingletonInput.height = deleteSingletonOutput.height + 1) ∧
      payloads deleteSingletonOutput = Search.OrderedList.delete 5 (payloads deleteSingletonInput) :=
  ordinary_delete_example 5 deleteSingletonInput deleteSingletonOutput (by decide) (by decide) (by decide)

/-- U18. -/
def deleteEmptyLeftInput : HTree := heightNode 2 .nil (heightSingleton 3)
def deleteEmptyLeftOutput : HTree := heightSingleton 3
theorem delete_empty_left :
    AVL.delete 2 deleteEmptyLeftInput = deleteEmptyLeftOutput ∧ AVL.Valid deleteEmptyLeftOutput ∧
      (deleteEmptyLeftInput.height = deleteEmptyLeftOutput.height ∨ deleteEmptyLeftInput.height = deleteEmptyLeftOutput.height + 1) ∧
      payloads deleteEmptyLeftOutput = Search.OrderedList.delete 2 (payloads deleteEmptyLeftInput) :=
  ordinary_delete_example 2 deleteEmptyLeftInput deleteEmptyLeftOutput (by decide) (by decide) (by decide)

/-- U19. -/
def deletePredecessorInput : HTree := perfectSeven
def deletePredecessorOutput : HTree := heightNode 3 (heightNode 2 (heightSingleton 1) .nil) (heightNode 6 (heightSingleton 5) (heightSingleton 7))
theorem delete_predecessor :
    AVL.delete 4 deletePredecessorInput = deletePredecessorOutput ∧ AVL.Valid deletePredecessorOutput ∧
      (deletePredecessorInput.height = deletePredecessorOutput.height ∨ deletePredecessorInput.height = deletePredecessorOutput.height + 1) ∧
      payloads deletePredecessorOutput = Search.OrderedList.delete 4 (payloads deletePredecessorInput) :=
  ordinary_delete_example 4 deletePredecessorInput deletePredecessorOutput (by decide) (by decide) (by decide)

/-- U20. -/
def deleteLeftTieInput : HTree := heightNode 4 (heightNode 2 (heightSingleton 1) (heightSingleton 3)) (heightSingleton 5)
def deleteLeftTieOutput : HTree := heightNode 2 (heightSingleton 1) (heightNode 4 (heightSingleton 3) .nil)
theorem delete_left_tie :
    AVL.delete 5 deleteLeftTieInput = deleteLeftTieOutput ∧ AVL.Valid deleteLeftTieOutput ∧
      (deleteLeftTieInput.height = deleteLeftTieOutput.height ∨ deleteLeftTieInput.height = deleteLeftTieOutput.height + 1) ∧
      payloads deleteLeftTieOutput = Search.OrderedList.delete 5 (payloads deleteLeftTieInput) :=
  ordinary_delete_example 5 deleteLeftTieInput deleteLeftTieOutput (by decide) (by decide) (by decide)

/-- U20. -/
def deleteRightTieInput : HTree := heightNode 2 (heightSingleton 1) (heightNode 4 (heightSingleton 3) (heightSingleton 5))
def deleteRightTieOutput : HTree := heightNode 4 (heightNode 2 .nil (heightSingleton 3)) (heightSingleton 5)
theorem delete_right_tie :
    AVL.delete 1 deleteRightTieInput = deleteRightTieOutput ∧ AVL.Valid deleteRightTieOutput ∧
      (deleteRightTieInput.height = deleteRightTieOutput.height ∨ deleteRightTieInput.height = deleteRightTieOutput.height + 1) ∧
      payloads deleteRightTieOutput = Search.OrderedList.delete 1 (payloads deleteRightTieInput) :=
  ordinary_delete_example 1 deleteRightTieInput deleteRightTieOutput (by decide) (by decide) (by decide)

/-- U21. -/
def deleteStrictSingleInput : HTree := heightNode 4 (heightNode 2 (heightSingleton 1) .nil) (heightSingleton 5)
def deleteStrictSingleOutput : HTree := heightNode 2 (heightSingleton 1) (heightSingleton 4)
theorem delete_strict_single :
    AVL.delete 5 deleteStrictSingleInput = deleteStrictSingleOutput ∧ AVL.Valid deleteStrictSingleOutput ∧
      (deleteStrictSingleInput.height = deleteStrictSingleOutput.height ∨ deleteStrictSingleInput.height = deleteStrictSingleOutput.height + 1) ∧
      payloads deleteStrictSingleOutput = Search.OrderedList.delete 5 (payloads deleteStrictSingleInput) :=
  ordinary_delete_example 5 deleteStrictSingleInput deleteStrictSingleOutput (by decide) (by decide) (by decide)

/-- U22. -/
def deleteMiddleLeftInput : HTree := heightNode 5 (heightNode 2 (heightSingleton 1) (heightNode 4 (heightSingleton 3) .nil)) (heightNode 7 (heightSingleton 6) .nil)
def deleteMiddleLeftOutput : HTree := heightNode 4 (heightNode 2 (heightSingleton 1) (heightSingleton 3)) (heightNode 5 .nil (heightSingleton 6))
theorem delete_middle_left :
    AVL.delete 7 deleteMiddleLeftInput = deleteMiddleLeftOutput ∧ AVL.Valid deleteMiddleLeftOutput ∧
      (deleteMiddleLeftInput.height = deleteMiddleLeftOutput.height ∨ deleteMiddleLeftInput.height = deleteMiddleLeftOutput.height + 1) ∧
      payloads deleteMiddleLeftOutput = Search.OrderedList.delete 7 (payloads deleteMiddleLeftInput) :=
  ordinary_delete_example 7 deleteMiddleLeftInput deleteMiddleLeftOutput (by decide) (by decide) (by decide)

/-- U22. -/
def deleteMiddleRightInput : HTree := heightNode 5 (heightNode 2 (heightSingleton 1) (heightNode 3 .nil (heightSingleton 4))) (heightNode 7 (heightSingleton 6) .nil)
def deleteMiddleRightOutput : HTree := heightNode 3 (heightNode 2 (heightSingleton 1) .nil) (heightNode 5 (heightSingleton 4) (heightSingleton 6))
theorem delete_middle_right :
    AVL.delete 7 deleteMiddleRightInput = deleteMiddleRightOutput ∧ AVL.Valid deleteMiddleRightOutput ∧
      (deleteMiddleRightInput.height = deleteMiddleRightOutput.height ∨ deleteMiddleRightInput.height = deleteMiddleRightOutput.height + 1) ∧
      payloads deleteMiddleRightOutput = Search.OrderedList.delete 7 (payloads deleteMiddleRightInput) :=
  ordinary_delete_example 7 deleteMiddleRightInput deleteMiddleRightOutput (by decide) (by decide) (by decide)

/-! U12/U27: zero tolerance keeps cache and list laws, but not balance. -/
theorem zero_insert_shape :
    HeightBalance.insert AVL.heightAnnotation 0 1 (heightSingleton 2) = heightNode 1 .nil (heightSingleton 2) := by decide
theorem zero_insert_separator :
    HeightBalance.ValidD AVL.heightAnnotation 0 (heightSingleton 2) ∧
      HeightBalance.CacheValid AVL.heightAnnotation
        (HeightBalance.insert AVL.heightAnnotation 0 1 (heightSingleton 2)) ∧
      payloads (HeightBalance.insert AVL.heightAnnotation 0 1 (heightSingleton 2)) =
        Search.OrderedList.insert 1 (payloads (heightSingleton 2)) ∧
      ¬ HeightBalance.ValidD AVL.heightAnnotation 0
        (HeightBalance.insert AVL.heightAnnotation 0 1 (heightSingleton 2)) :=
  ⟨by decide, HeightBalance.cacheValid_insert _ 0 1 (heightSingleton 2) (by decide),
    HeightBalance.inorder_insert _ 0 1 (heightSingleton 2) (by decide), by decide⟩

theorem zero_delete_shape :
    HeightBalance.delete AVL.heightAnnotation 0 3 three = heightNode 1 .nil (heightSingleton 2) := by decide
theorem zero_delete_separator :
    HeightBalance.ValidD AVL.heightAnnotation 0 three ∧
      HeightBalance.CacheValid AVL.heightAnnotation
        (HeightBalance.delete AVL.heightAnnotation 0 3 three) ∧
      payloads (HeightBalance.delete AVL.heightAnnotation 0 3 three) =
        Search.OrderedList.delete 3 (payloads three) ∧
      ¬ HeightBalance.ValidD AVL.heightAnnotation 0
        (HeightBalance.delete AVL.heightAnnotation 0 3 three) :=
  ⟨by decide, HeightBalance.cacheValid_delete _ 0 3 three (by decide),
    HeightBalance.inorder_delete _ 0 3 three (by decide), by decide⟩

/-! U13: extraction is defined without a payload witness or comparison instance. -/
theorem empty_word_extraction (d : Nat) :
    HeightBalance.splitMaxOption (wordAnnotation PEmpty.{u + 1}) d
      (.nil : BinaryTree (PEmpty.{u + 1} × (Nat × List PEmpty.{u + 1}))) = none :=
  HeightBalance.splitMaxOption_nil _ d

theorem empty_independent_annotation_extraction
    (ann : HeightBalance.HeightAnnotation PEmpty.{u + 1} σ) (d : Nat) :
    HeightBalance.splitMaxOption ann d .nil = none :=
  (HeightBalance.splitMaxOption_eq_none_iff ann d .nil).mpr rfl

theorem nonempty_extraction_domain (ann : HeightBalance.HeightAnnotation α σ)
    (d : Nat) (t : BinaryTree (α × σ)) (hn : t ≠ .nil) :
    ∃ t' m, HeightBalance.splitMaxOption ann d t = some (t', m) :=
  HeightBalance.splitMaxOption_exists_of_ne_nil ann d t hn

theorem successful_extraction_domain (ann : HeightBalance.HeightAnnotation α σ)
    (d : Nat) (t t' : BinaryTree (α × σ)) (m : α)
    (hs : HeightBalance.splitMaxOption ann d t = some (t', m)) : t ≠ .nil := by
  intro hn
  have hnone := (HeightBalance.splitMaxOption_eq_none_iff ann d t).mpr hn
  rw [hs] at hnone
  cases hnone

/-! U14–U16: right-empty retention, zero shrink and rightmost versus greatest. -/
theorem extraction_retains_left :
    AVL.splitMaxOption (heightNode 7 (heightSingleton 6) .nil) = some (heightSingleton 6, 7) ∧ AVL.Valid (heightSingleton 6) ∧
      ((heightNode 7 (heightSingleton 6) .nil).height = (heightSingleton 6).height ∨
        (heightNode 7 (heightSingleton 6) .nil).height = (heightSingleton 6).height + 1) ∧
      payloads (heightSingleton 6) ++ [7] = payloads (heightNode 7 (heightSingleton 6) .nil) :=
  ordinary_split_example _ _ 7 (AVL.splitMaxOption_node_nil 7 2 (heightSingleton 6)) (by decide)

def withoutSeven : HTree := heightNode 4 (heightNode 2 (heightSingleton 1) (heightSingleton 3)) (heightNode 6 (heightSingleton 5) .nil)
theorem extraction_keeps_height :
    AVL.splitMaxOption perfectSeven = some (withoutSeven, 7) ∧ AVL.Valid withoutSeven ∧
      (perfectSeven.height = withoutSeven.height ∨
        perfectSeven.height = withoutSeven.height + 1) ∧
      payloads withoutSeven ++ [7] = payloads perfectSeven :=
  ordinary_split_example perfectSeven withoutSeven 7 (by decide) (by decide)

theorem extracted_remainder_strict :
    Search.OrderedList.Strict (payloads withoutSeven) ∧
      ∀ x ∈ payloads withoutSeven, x < 7 :=
  AVL.strict_inorder_splitMaxOption perfectSeven withoutSeven 7
    extraction_keeps_height.1 (by decide)

theorem extracted_key_is_maximum_under_order :
    7 ∈ payloads perfectSeven ∧ ∀ x ∈ payloads perfectSeven, x ≤ 7 :=
  AVL.maximal_splitMaxOption perfectSeven withoutSeven 7
    extraction_keeps_height.1 (by decide)

theorem extraction_base_and_zero_shrink_observations :
    (heightNode 7 (heightSingleton 6) .nil).height = 2 ∧ (heightSingleton 6).height = 1 ∧
      perfectSeven.height = 3 ∧ withoutSeven.height = 3 ∧
      payloads withoutSeven = [1, 2, 3, 4, 5, 6] := by decide

def unorderedSplit : HTree := heightNode 5 (heightSingleton 9) (heightSingleton 2)
def unorderedRemainder : HTree := heightNode 5 (heightSingleton 9) .nil
theorem rightmost_extraction :
    AVL.splitMaxOption unorderedSplit = some (unorderedRemainder, 2) ∧
      AVL.Valid unorderedRemainder ∧
      (unorderedSplit.height = unorderedRemainder.height ∨
        unorderedSplit.height = unorderedRemainder.height + 1) ∧
      payloads unorderedRemainder ++ [2] = payloads unorderedSplit :=
  ordinary_split_example unorderedSplit unorderedRemainder 2 (by decide) (by decide)

theorem rightmost_is_not_unconditional_maximum :
    payloads unorderedSplit = [9, 5, 2] ∧
      ¬ (∀ x ∈ payloads unorderedSplit, x ≤ 2) ∧
      ¬ Search.OrderedList.Strict (payloads unorderedSplit) := by decide

def maximumUnordered : MTree := Cached.annotate maximumAnnotation.empty maximumAnnotation.combine
  (Cached.erase unorderedSplit)
def maximumUnorderedRemainder : MTree :=
  Cached.annotate maximumAnnotation.empty maximumAnnotation.combine (Cached.erase unorderedRemainder)

theorem unordered_maximum_extraction :
    HeightBalance.splitMaxOption maximumAnnotation 1 maximumUnordered =
      some (maximumUnorderedRemainder, 2) := by decide

theorem remainder_retains_greater_maximum :
    HeightBalance.CacheValid maximumAnnotation maximumUnorderedRemainder ∧
      Cached.read maximumAnnotation.empty maximumUnorderedRemainder = (2, some 9) ∧
      9 ∈ setTree (Cached.erase maximumUnorderedRemainder) ∧
      ∀ x ∈ setTree (Cached.erase maximumUnorderedRemainder), x ≤ 9 := by
  have hc := HeightBalance.cacheValid_splitMaxOption maximumAnnotation 1
    maximumUnordered maximumUnorderedRemainder 2 unordered_maximum_extraction (by decide)
  have hm := (HeightRebalance.maximum_reader_greatest maximumUnorderedRemainder hc 9).mp
    (by decide)
  exact ⟨hc, by decide, hm.1, hm.2⟩

/-! U20/U21: extraction realizes the same tie and strict-single alternatives. -/
theorem extraction_tie :
    AVL.splitMaxOption deleteLeftTieInput = some (deleteLeftTieOutput, 5) ∧
      AVL.Valid deleteLeftTieOutput ∧
      (deleteLeftTieInput.height = deleteLeftTieOutput.height ∨
        deleteLeftTieInput.height = deleteLeftTieOutput.height + 1) ∧
      payloads deleteLeftTieOutput ++ [5] = payloads deleteLeftTieInput :=
  ordinary_split_example deleteLeftTieInput deleteLeftTieOutput 5 (by decide) (by decide)

theorem extraction_strict_single :
    AVL.splitMaxOption deleteStrictSingleInput = some (deleteStrictSingleOutput, 5) ∧
      AVL.Valid deleteStrictSingleOutput ∧
      (deleteStrictSingleInput.height = deleteStrictSingleOutput.height ∨
        deleteStrictSingleInput.height = deleteStrictSingleOutput.height + 1) ∧
      payloads deleteStrictSingleOutput ++ [5] = payloads deleteStrictSingleInput :=
  ordinary_split_example deleteStrictSingleInput deleteStrictSingleOutput 5 (by decide) (by decide)

theorem ordinary_deletion_height_alternatives :
    deleteLeftTieInput.height = 3 ∧ deleteLeftTieOutput.height = 3 ∧
      deleteRightTieInput.height = 3 ∧ deleteRightTieOutput.height = 3 ∧
      deleteStrictSingleInput.height = 3 ∧ deleteStrictSingleOutput.height = 2 ∧
      deleteMiddleLeftInput.height = 4 ∧ deleteMiddleLeftOutput.height = 3 ∧
      deleteMiddleRightInput.height = 4 ∧ deleteMiddleRightOutput.height = 3 ∧
      payloads deletePredecessorOutput = [1, 2, 3, 5, 6, 7] := by decide

theorem larger_tolerance_height_alternatives :
    insertD2SingleLeftInput.height = 3 ∧ insertD2SingleLeftOutput.height = 3 ∧
      insertD3SingleLeftInput.height = 4 ∧ insertD3SingleLeftOutput.height = 4 ∧
      insertD3MiddleLeftOutput.height = 4 ∧ insertD3MiddleRightOutput.height = 4 ∧
      deleteD2TieInput.height = 4 ∧ deleteD2TieOutput.height = 4 ∧
      deleteD2StrictSingleInput.height = 4 ∧ deleteD2StrictSingleOutput.height = 3 ∧
      deleteD3TieInput.height = 5 ∧ deleteD3TieOutput.height = 5 ∧
      deleteD3StrictSingleInput.height = 5 ∧ deleteD3StrictSingleOutput.height = 4 ∧
      deleteD3MiddleLeftInput.height = 5 ∧ deleteD3MiddleLeftOutput.height = 4 ∧
      deleteD3MiddleRightInput.height = 5 ∧ deleteD3MiddleRightOutput.height = 4 := by decide

theorem generalized_is_not_ordinary :
    ¬ AVL.Valid insertD3MiddleLeftOutput ∧ ¬ AVL.Valid insertD3MiddleRightOutput ∧
      HeightRebalance.childHeights insertD3MiddleLeftOutput = (3, 1) ∧
      HeightRebalance.childHeights insertD3MiddleRightOutput = (1, 3) := by decide

/-! U25: deletion changes both summaries while preserving both relevant heights. -/
theorem same_height_maximum_delete :
    HeightBalance.delete maximumAnnotation 1 7 maximumWithSeven = maximumBase ∧
      HeightBalance.ValidD maximumAnnotation 1 maximumBase ∧
      (maximumWithSeven.height = maximumBase.height ∨
        maximumWithSeven.height = maximumBase.height + 1) ∧
      payloads maximumBase = Search.OrderedList.delete 7 (payloads maximumWithSeven) :=
  generic_delete_example maximumAnnotation 1 7 maximumWithSeven maximumBase
    (by decide) (by decide) (by decide) (by decide)

theorem same_height_word_delete :
    HeightBalance.delete (wordAnnotation Nat) 1 7 wordWithSeven = wordBase ∧
      HeightBalance.ValidD (wordAnnotation Nat) 1 wordBase ∧
      (wordWithSeven.height = wordBase.height ∨ wordWithSeven.height = wordBase.height + 1) ∧
      payloads wordBase = Search.OrderedList.delete 7 (payloads wordWithSeven) :=
  generic_delete_example (wordAnnotation Nat) 1 7 wordWithSeven wordBase
    (by decide) (by decide) (by decide) (by decide)

theorem deleted_maximum_semantics :
    (Cached.read maximumAnnotation.empty
      (HeightBalance.delete maximumAnnotation 1 7 maximumWithSeven)).2 =
      (payloads (HeightBalance.delete maximumAnnotation 1 7 maximumWithSeven)).max? :=
  HeightRebalance.maximum_reader_eq_list_maximum _
    (HeightBalance.cacheValid_delete maximumAnnotation 1 7 maximumWithSeven (by decide))

theorem deleted_word_semantics :
    (Cached.read (wordAnnotation Nat).empty
      (HeightBalance.delete (wordAnnotation Nat) 1 7 wordWithSeven)).2 =
      payloads (HeightBalance.delete (wordAnnotation Nat) 1 7 wordWithSeven) :=
  HeightRebalance.word_reader_eq_inorder _
    (HeightBalance.cacheValid_delete (wordAnnotation Nat) 1 7 wordWithSeven (by decide))

def staleMaximumAfterDelete : MTree := .node (4, (3, some 7))
  (HeightRebalance.maximumLeaf 2)
  (HeightBalance.node maximumAnnotation (HeightRebalance.maximumLeaf 5) 6 .nil)
def staleWordAfterDelete : WTree := .node (4, (3, [2, 4, 5, 6, 7]))
  (HeightRebalance.wordLeaf 2)
  (HeightBalance.node (wordAnnotation Nat) (HeightRebalance.wordLeaf 5) 6 .nil)
def staleMaximumAfterInsert : MTree := .node (4, (3, some 6))
  (HeightRebalance.maximumLeaf 2)
  (HeightBalance.node maximumAnnotation (HeightRebalance.maximumLeaf 5) 6
    (HeightRebalance.maximumLeaf 7))
def staleWordAfterInsert : WTree := .node (4, (3, [2, 4, 5, 6]))
  (HeightRebalance.wordLeaf 2)
  (HeightBalance.node (wordAnnotation Nat) (HeightRebalance.wordLeaf 5) 6
    (HeightRebalance.wordLeaf 7))

theorem stale_update_shapes_and_heights :
    Cached.erase staleMaximumAfterDelete = Cached.erase maximumBase ∧
      Cached.erase staleWordAfterDelete = Cached.erase wordBase ∧
      Cached.erase staleMaximumAfterInsert = Cached.erase maximumWithSeven ∧
      Cached.erase staleWordAfterInsert = Cached.erase wordWithSeven ∧
      HeightBalance.ht maximumAnnotation staleMaximumAfterDelete = staleMaximumAfterDelete.height ∧
      HeightBalance.ht (wordAnnotation Nat) staleWordAfterDelete = staleWordAfterDelete.height ∧
      HeightBalance.ht maximumAnnotation staleMaximumAfterInsert = staleMaximumAfterInsert.height ∧
      HeightBalance.ht (wordAnnotation Nat) staleWordAfterInsert = staleWordAfterInsert.height := by decide

theorem stale_maximum_delete_rejected : ¬ HeightBalance.CacheValid maximumAnnotation staleMaximumAfterDelete := by
  intro h
  have he := ((HeightBalance.cacheValid_node maximumAnnotation 4 (3, some 7)
    (HeightRebalance.maximumLeaf 2)
    (HeightBalance.node maximumAnnotation (HeightRebalance.maximumLeaf 5) 6 .nil)).mp h).2.2
  change (3, some 7) = (3, some 6) at he
  exact (by decide : (3, some 7) ≠ (3, some 6)) he

theorem stale_word_delete_rejected : ¬ HeightBalance.CacheValid (wordAnnotation Nat) staleWordAfterDelete := by
  intro h
  have he := ((HeightBalance.cacheValid_node (wordAnnotation Nat) 4 (3, [2, 4, 5, 6, 7])
    (HeightRebalance.wordLeaf 2)
    (HeightBalance.node (wordAnnotation Nat) (HeightRebalance.wordLeaf 5) 6 .nil)).mp h).2.2
  change (3, [2, 4, 5, 6, 7]) = (3, [2, 4, 5, 6]) at he
  exact (by decide : (3, [2, 4, 5, 6, 7]) ≠ (3, [2, 4, 5, 6])) he

theorem stale_maximum_insert_rejected : ¬ HeightBalance.CacheValid maximumAnnotation staleMaximumAfterInsert := by
  intro h
  have he := ((HeightBalance.cacheValid_node maximumAnnotation 4 (3, some 6)
    (HeightRebalance.maximumLeaf 2)
    (HeightBalance.node maximumAnnotation (HeightRebalance.maximumLeaf 5) 6
      (HeightRebalance.maximumLeaf 7))).mp h).2.2
  change (3, some 6) = (3, some 7) at he
  exact (by decide : (3, some 6) ≠ (3, some 7)) he

theorem stale_word_insert_rejected : ¬ HeightBalance.CacheValid (wordAnnotation Nat) staleWordAfterInsert := by
  intro h
  have he := ((HeightBalance.cacheValid_node (wordAnnotation Nat) 4 (3, [2, 4, 5, 6])
    (HeightRebalance.wordLeaf 2)
    (HeightBalance.node (wordAnnotation Nat) (HeightRebalance.wordLeaf 5) 6
      (HeightRebalance.wordLeaf 7))).mp h).2.2
  change (3, [2, 4, 5, 6]) = (3, [2, 4, 5, 6, 7]) at he
  exact (by decide : (3, [2, 4, 5, 6]) ≠ (3, [2, 4, 5, 6, 7])) he


/-! U26: complete noncommutative summaries use both direct repair orientations. -/
def wordOf (t : HTree) : WTree :=
  Cached.annotate (wordAnnotation Nat).empty (wordAnnotation Nat).combine (Cached.erase t)

theorem word_insert_reader [LT α] [DecidableLT α] (d : Nat) (x : α)
    (t : BinaryTree (α × (Nat × List α)))
    (hc : HeightBalance.CacheValid (wordAnnotation α) t) :
    (Cached.read (wordAnnotation α).empty (HeightBalance.insert (wordAnnotation α) d x t)).2 =
      payloads (HeightBalance.insert (wordAnnotation α) d x t) :=
  HeightRebalance.word_reader_eq_inorder _
    (HeightBalance.cacheValid_insert (wordAnnotation α) d x t hc)

theorem word_delete_reader [LT α] [DecidableLT α] (d : Nat) (x : α)
    (t : BinaryTree (α × (Nat × List α)))
    (hc : HeightBalance.CacheValid (wordAnnotation α) t) :
    (Cached.read (wordAnnotation α).empty (HeightBalance.delete (wordAnnotation α) d x t)).2 =
      payloads (HeightBalance.delete (wordAnnotation α) d x t) :=
  HeightRebalance.word_reader_eq_inorder _
    (HeightBalance.cacheValid_delete (wordAnnotation α) d x t hc)

theorem word_insert_left_single :
    HeightBalance.insert (wordAnnotation Nat) 1 1 (wordOf (heightNode 3 (heightSingleton 2) .nil)) = (wordOf (three)) ∧
      HeightBalance.ValidD (wordAnnotation Nat) 1 (wordOf (three)) ∧
      ((wordOf (three)).height = (wordOf (heightNode 3 (heightSingleton 2) .nil)).height ∨ (wordOf (three)).height = (wordOf (heightNode 3 (heightSingleton 2) .nil)).height + 1) ∧
      payloads (wordOf (three)) = Search.OrderedList.insert 1 (payloads (wordOf (heightNode 3 (heightSingleton 2) .nil))) :=
  generic_insert_example (wordAnnotation Nat) 1 1 (wordOf (heightNode 3 (heightSingleton 2) .nil)) (wordOf (three))
    (by decide) (by decide) (by decide) (by decide)

theorem word_insert_right_single :
    HeightBalance.insert (wordAnnotation Nat) 1 3 (wordOf (heightNode 1 .nil (heightSingleton 2))) = (wordOf (three)) ∧
      HeightBalance.ValidD (wordAnnotation Nat) 1 (wordOf (three)) ∧
      ((wordOf (three)).height = (wordOf (heightNode 1 .nil (heightSingleton 2))).height ∨ (wordOf (three)).height = (wordOf (heightNode 1 .nil (heightSingleton 2))).height + 1) ∧
      payloads (wordOf (three)) = Search.OrderedList.insert 3 (payloads (wordOf (heightNode 1 .nil (heightSingleton 2)))) :=
  generic_insert_example (wordAnnotation Nat) 1 3 (wordOf (heightNode 1 .nil (heightSingleton 2))) (wordOf (three))
    (by decide) (by decide) (by decide) (by decide)

theorem word_insert_left_double :
    HeightBalance.insert (wordAnnotation Nat) 1 2 (wordOf (heightNode 3 (heightSingleton 1) .nil)) = (wordOf (three)) ∧
      HeightBalance.ValidD (wordAnnotation Nat) 1 (wordOf (three)) ∧
      ((wordOf (three)).height = (wordOf (heightNode 3 (heightSingleton 1) .nil)).height ∨ (wordOf (three)).height = (wordOf (heightNode 3 (heightSingleton 1) .nil)).height + 1) ∧
      payloads (wordOf (three)) = Search.OrderedList.insert 2 (payloads (wordOf (heightNode 3 (heightSingleton 1) .nil))) :=
  generic_insert_example (wordAnnotation Nat) 1 2 (wordOf (heightNode 3 (heightSingleton 1) .nil)) (wordOf (three))
    (by decide) (by decide) (by decide) (by decide)

theorem word_insert_right_double :
    HeightBalance.insert (wordAnnotation Nat) 1 2 (wordOf (heightNode 1 .nil (heightSingleton 3))) = (wordOf (three)) ∧
      HeightBalance.ValidD (wordAnnotation Nat) 1 (wordOf (three)) ∧
      ((wordOf (three)).height = (wordOf (heightNode 1 .nil (heightSingleton 3))).height ∨ (wordOf (three)).height = (wordOf (heightNode 1 .nil (heightSingleton 3))).height + 1) ∧
      payloads (wordOf (three)) = Search.OrderedList.insert 2 (payloads (wordOf (heightNode 1 .nil (heightSingleton 3)))) :=
  generic_insert_example (wordAnnotation Nat) 1 2 (wordOf (heightNode 1 .nil (heightSingleton 3))) (wordOf (three))
    (by decide) (by decide) (by decide) (by decide)

theorem word_delete_right_tie :
    HeightBalance.delete (wordAnnotation Nat) 1 1 (wordOf (deleteRightTieInput)) = (wordOf (deleteRightTieOutput)) ∧
      HeightBalance.ValidD (wordAnnotation Nat) 1 (wordOf (deleteRightTieOutput)) ∧
      ((wordOf (deleteRightTieInput)).height = (wordOf (deleteRightTieOutput)).height ∨ (wordOf (deleteRightTieInput)).height = (wordOf (deleteRightTieOutput)).height + 1) ∧
      payloads (wordOf (deleteRightTieOutput)) = Search.OrderedList.delete 1 (payloads (wordOf (deleteRightTieInput))) :=
  generic_delete_example (wordAnnotation Nat) 1 1 (wordOf (deleteRightTieInput)) (wordOf (deleteRightTieOutput))
    (by decide) (by decide) (by decide) (by decide)

theorem word_delete_predecessor :
    HeightBalance.delete (wordAnnotation Nat) 1 4 (wordOf (perfectSeven)) = (wordOf (deletePredecessorOutput)) ∧
      HeightBalance.ValidD (wordAnnotation Nat) 1 (wordOf (deletePredecessorOutput)) ∧
      ((wordOf (perfectSeven)).height = (wordOf (deletePredecessorOutput)).height ∨ (wordOf (perfectSeven)).height = (wordOf (deletePredecessorOutput)).height + 1) ∧
      payloads (wordOf (deletePredecessorOutput)) = Search.OrderedList.delete 4 (payloads (wordOf (perfectSeven))) :=
  generic_delete_example (wordAnnotation Nat) 1 4 (wordOf (perfectSeven)) (wordOf (deletePredecessorOutput))
    (by decide) (by decide) (by decide) (by decide)

theorem direct_word_update_readers :
    (Cached.read (wordAnnotation Nat).empty
      (HeightBalance.insert (wordAnnotation Nat) 1 1 (wordOf (heightNode 3 (heightSingleton 2) .nil)))).2 = [1, 2, 3] ∧
    (Cached.read (wordAnnotation Nat).empty
      (HeightBalance.insert (wordAnnotation Nat) 1 3 (wordOf (heightNode 1 .nil (heightSingleton 2))))).2 = [1, 2, 3] ∧
    (Cached.read (wordAnnotation Nat).empty
      (HeightBalance.insert (wordAnnotation Nat) 1 2 (wordOf (heightNode 3 (heightSingleton 1) .nil)))).2 = [1, 2, 3] ∧
    (Cached.read (wordAnnotation Nat).empty
      (HeightBalance.insert (wordAnnotation Nat) 1 2 (wordOf (heightNode 1 .nil (heightSingleton 3))))).2 = [1, 2, 3] ∧
    (Cached.read (wordAnnotation Nat).empty
      (HeightBalance.delete (wordAnnotation Nat) 1 1 (wordOf deleteRightTieInput))).2 = [2, 3, 4, 5] ∧
    (Cached.read (wordAnnotation Nat).empty
      (HeightBalance.delete (wordAnnotation Nat) 1 4 (wordOf perfectSeven))).2 = [1, 2, 3, 5, 6, 7] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | rw [word_insert_reader _ _ _ (by decide)]
    | rw [word_delete_reader _ _ _ (by decide)]
  all_goals decide

def stalePredecessorWord : WTree := .node (3, (3, [1, 2, 3, 4, 5, 6, 7]))
  (wordOf (heightNode 2 (heightSingleton 1) .nil)) (wordOf (heightNode 6 (heightSingleton 5) (heightSingleton 7)))

theorem predecessor_word_replacement_is_needed :
    Cached.erase stalePredecessorWord = Cached.erase (wordOf deletePredecessorOutput) ∧
      HeightBalance.ht (wordAnnotation Nat) stalePredecessorWord = stalePredecessorWord.height ∧
      ¬ HeightBalance.CacheValid (wordAnnotation Nat) stalePredecessorWord := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  have he := ((HeightBalance.cacheValid_node (wordAnnotation Nat) 3 (3, [1, 2, 3, 4, 5, 6, 7])
    (wordOf (heightNode 2 (heightSingleton 1) .nil)) (wordOf (heightNode 6 (heightSingleton 5) (heightSingleton 7)))).mp h).2.2
  change (3, [1, 2, 3, 4, 5, 6, 7]) = (3, [1, 2, 3, 5, 6, 7]) at he
  exact (by decide : (3, [1, 2, 3, 4, 5, 6, 7]) ≠ (3, [1, 2, 3, 5, 6, 7])) he

theorem same_height_child_readers :
    Cached.read maximumAnnotation.empty
      (HeightBalance.node maximumAnnotation (HeightRebalance.maximumLeaf 5) 6 .nil) = (2, some 6) ∧
    Cached.read maximumAnnotation.empty
      (HeightBalance.node maximumAnnotation (HeightRebalance.maximumLeaf 5) 6
        (HeightRebalance.maximumLeaf 7)) = (2, some 7) ∧
    Cached.read (wordAnnotation Nat).empty
      (HeightBalance.node (wordAnnotation Nat) (HeightRebalance.wordLeaf 5) 6 .nil) = (2, [5, 6]) ∧
    Cached.read (wordAnnotation Nat).empty
      (HeightBalance.node (wordAnnotation Nat) (HeightRebalance.wordLeaf 5) 6
        (HeightRebalance.wordLeaf 7)) = (2, [5, 6, 7]) := by decide

/-! U28: fixed positive integer tolerances use the checked natural representative. -/
theorem positive_integer_update_contracts [LT α] [DecidableLT α]
    (ann : HeightBalance.HeightAnnotation α σ) (D : Int) (hD : 1 ≤ D)
    (x : α) (t : BinaryTree (α × σ)) (hv : HeightBalance.ValidD ann D.toNat t) :
    (D.toNat : Int) = D ∧
      (HeightBalance.ValidD ann D.toNat (HeightBalance.insert ann D.toNat x t) ∧
        ((HeightBalance.insert ann D.toNat x t).height = t.height ∨
          (HeightBalance.insert ann D.toNat x t).height = t.height + 1)) ∧
      (HeightBalance.ValidD ann D.toNat (HeightBalance.delete ann D.toNat x t) ∧
        (t.height = (HeightBalance.delete ann D.toNat x t).height ∨
          t.height = (HeightBalance.delete ann D.toNat x t).height + 1)) :=
  ⟨(HeightBalance.int_tolerance_toNat D hD).2,
    HeightBalance.validD_insert ann D.toNat x t (HeightBalance.int_tolerance_toNat D hD).1 hv,
    HeightBalance.validD_delete ann D.toNat x t (HeightBalance.int_tolerance_toNat D hD).1 hv⟩

theorem integer_one_two_three :
    HeightBalance.ValidD AVL.heightAnnotation (1 : Int).toNat
      (HeightBalance.insert AVL.heightAnnotation (1 : Int).toNat 1 (heightNode 3 (heightSingleton 2) .nil)) ∧
    HeightBalance.ValidD AVL.heightAnnotation (2 : Int).toNat
      (HeightBalance.insert AVL.heightAnnotation (2 : Int).toNat 1 insertD2SingleLeftInput) ∧
    HeightBalance.ValidD AVL.heightAnnotation (3 : Int).toNat
      (HeightBalance.delete AVL.heightAnnotation (3 : Int).toNat 8 deleteD3MiddleRightInput) :=
  ⟨(positive_integer_update_contracts AVL.heightAnnotation 1 (by decide) 1
      (heightNode 3 (heightSingleton 2) .nil) (by decide)).2.1.1,
    (positive_integer_update_contracts AVL.heightAnnotation 2 (by decide) 1
      insertD2SingleLeftInput (by decide)).2.1.1,
    (positive_integer_update_contracts AVL.heightAnnotation 3 (by decide) 8
      deleteD3MiddleRightInput (by decide)).2.2.1⟩

theorem negative_integer_is_not_a_natural_invariant :
    ¬ |(0 : Int) - (0 : Int)| ≤ (-1 : Int) ∧
      (-1 : Int).toNat = 0 ∧ (0 : Nat) ≤ 0 + (-1 : Int).toNat ∧
      (0 : Nat) ≤ 0 + (-1 : Int).toNat :=
  HeightRebalance.negative_tolerance_separator

theorem signed_subtraction_boundary :
    ¬ |(0 : Int) - (3 : Int)| ≤ 1 ∧ |((0 - 3 : Nat) : Int)| ≤ 1 ∧
      |((3 - 0 : Nat) : Int)| = |(3 : Int) - (0 : Int)| :=
  HeightRebalance.cast_before_subtraction_matters

/-! U09: arbitrary positive tolerances, beyond the finite d=2/d=3 instances. -/
def leftChain (b : Nat) : Nat → HTree
  | 0 => .nil
  | n + 1 => heightNode (b + n) (leftChain b n) .nil

def rightChain (b : Nat) : Nat → HTree
  | 0 => .nil
  | n + 1 => heightNode b .nil (rightChain (b + 1) n)

@[simp] theorem height_leftChain (b n : Nat) : (leftChain b n).height = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [leftChain, heightNode, AVL.height_node, BinaryTree.height, Nat.max_zero, ih]

@[simp] theorem height_rightChain (b n : Nat) : (rightChain b n).height = n := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => simp only [rightChain, heightNode, AVL.height_node, BinaryTree.height, Nat.zero_max, ih]

theorem cache_leftChain (b n : Nat) : AVL.CacheValid (leftChain b n) := by
  induction n with
  | zero => exact AVL.cacheValid_nil
  | succ n ih => exact (AVL.node_cacheValid_iff _ _ _).mpr ⟨ih, AVL.cacheValid_nil⟩

theorem cache_rightChain (b n : Nat) : AVL.CacheValid (rightChain b n) := by
  induction n generalizing b with
  | zero => exact AVL.cacheValid_nil
  | succ n ih => exact (AVL.node_cacheValid_iff _ _ _).mpr ⟨AVL.cacheValid_nil, ih (b + 1)⟩

@[simp] theorem ht_leftChain (b n : Nat) : AVL.ht (leftChain b n) = n :=
  (AVL.ht_eq_height_of_cacheValid _ (cache_leftChain b n)).trans (height_leftChain b n)

@[simp] theorem ht_rightChain (b n : Nat) : AVL.ht (rightChain b n) = n :=
  (AVL.ht_eq_height_of_cacheValid _ (cache_rightChain b n)).trans (height_rightChain b n)

theorem valid_leftChain (d b n : Nat) (hn : n ≤ d + 1) :
    HeightBalance.ValidD AVL.heightAnnotation d (leftChain b n) := by
  revert hn
  induction n with
  | zero => intro _; exact HeightBalance.validD_nil _ d
  | succ n ih =>
      intro hn
      apply (HeightBalance.node_validD_iff AVL.heightAnnotation d _ (b + n) .nil).mpr
      refine ⟨ih (by omega), HeightBalance.validD_nil _ d,
        (HeightBalance.height_balance_iff d _ _).mpr ?_⟩
      simp only [height_leftChain, BinaryTree.height]
      constructor <;> omega

theorem valid_rightChain (d b n : Nat) (hn : n ≤ d + 1) :
    HeightBalance.ValidD AVL.heightAnnotation d (rightChain b n) := by
  revert hn
  induction n generalizing b with
  | zero => intro _; exact HeightBalance.validD_nil _ d
  | succ n ih =>
      intro hn
      apply (HeightBalance.node_validD_iff AVL.heightAnnotation d .nil b _).mpr
      refine ⟨HeightBalance.validD_nil _ d, ih (b + 1) (by omega),
        (HeightBalance.height_balance_iff d _ _).mpr ?_⟩
      simp only [height_rightChain, BinaryTree.height]
      constructor <;> omega

private theorem insert_leftChain_below (d n : Nat) (hn : n ≤ d) :
    HeightBalance.insert AVL.heightAnnotation d 1 (leftChain 2 n) = leftChain 1 (n + 1) := by
  revert hn
  induction n generalizing d with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      rw [leftChain, heightNode, AVL.node_eq,
        HeightBalance.insert_of_lt _ _ _ _ _ _ _ (by omega), ih d (by omega)]
      rw [HeightBalance.balL_of_ne _ _ _ _ _ (by
        simp only [AVL.ht_heightAnnotation, ht_leftChain, AVL.ht_nil]
        omega)]
      simp only [leftChain, heightNode, AVL.node_heightAnnotation]
      congr 1; omega

private theorem insert_rightChain_below (d b n : Nat) (hn : n ≤ d) :
    HeightBalance.insert AVL.heightAnnotation d (b + n) (rightChain b n) =
      rightChain b (n + 1) := by
  revert hn
  induction n generalizing d b with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      rw [rightChain, heightNode, AVL.node_eq,
        HeightBalance.insert_of_gt _ _ _ _ _ _ _ (by omega) (by omega)]
      have hquery : b + (n + 1) = (b + 1) + n := by omega
      rw [hquery, ih d (b + 1) (by omega)]
      rw [HeightBalance.balR_of_ne _ _ _ _ _ (by
        simp only [AVL.ht_heightAnnotation, ht_rightChain, AVL.ht_nil]
        omega)]
      rfl

theorem uniform_left_single (d : Nat) :
    HeightBalance.insert AVL.heightAnnotation d 1 (leftChain 2 (d + 1)) =
      heightNode (d + 1) (leftChain 1 d) (heightSingleton (d + 2)) := by
  rw [leftChain, heightNode, AVL.node_eq,
    HeightBalance.insert_of_lt _ _ _ _ _ _ _ (by omega),
    insert_leftChain_below d d (Nat.le_refl _)]
  have h := HeightBalance.balL_single AVL.heightAnnotation d (leftChain 1 d)
    (1 + d) (d + 1) .nil (2 + d) .nil
    (by simp [AVL.heightAnnotation])
    (by simp only [AVL.ht_heightAnnotation, AVL.ht_nil, ht_leftChain, Nat.zero_le])
  simpa only [leftChain, heightNode, heightSingleton, AVL.node_eq, ht_leftChain, AVL.ht_nil, Nat.max_zero,
    AVL.node_heightAnnotation, Nat.add_comm] using h

theorem uniform_right_single (d : Nat) :
    HeightBalance.insert AVL.heightAnnotation d (d + 2) (rightChain 1 (d + 1)) =
      heightNode 2 (heightSingleton 1) (rightChain 3 d) := by
  rw [rightChain, heightNode, AVL.node_eq,
    HeightBalance.insert_of_gt _ _ _ _ _ _ _ (by omega) (by omega)]
  have hquery : d + 2 = 2 + d := by omega
  rw [hquery, insert_rightChain_below d 2 d (Nat.le_refl _)]
  have h := HeightBalance.balR_single AVL.heightAnnotation d .nil 1 .nil 2 (d + 1)
    (rightChain 3 d) (by simp [AVL.heightAnnotation])
    (by simp only [AVL.ht_heightAnnotation, AVL.ht_nil, ht_rightChain, Nat.zero_le])
  simpa only [rightChain, heightNode, heightSingleton, AVL.node_eq, ht_rightChain, AVL.ht_nil, Nat.zero_max,
    AVL.node_heightAnnotation] using h

theorem uniform_single_validity_and_height (d : Nat) (hd : 1 ≤ d) :
    HeightBalance.ValidD AVL.heightAnnotation d (heightNode (d + 1) (leftChain 1 d) (heightSingleton (d + 2))) ∧
      HeightBalance.ValidD AVL.heightAnnotation d (heightNode 2 (heightSingleton 1) (rightChain 3 d)) ∧
      (heightNode (d + 1) (leftChain 1 d) (heightSingleton (d + 2))).height = d + 1 ∧
      (heightNode 2 (heightSingleton 1) (rightChain 3 d)).height = d + 1 := by
  have hl := (HeightBalance.validD_insert AVL.heightAnnotation d 1 (leftChain 2 (d + 1))
    hd (valid_leftChain d 2 (d + 1) (Nat.le_refl _))).1
  have hr := (HeightBalance.validD_insert AVL.heightAnnotation d (d + 2) (rightChain 1 (d + 1))
    hd (valid_rightChain d 1 (d + 1) (Nat.le_refl _))).1
  rw [uniform_left_single d] at hl
  rw [uniform_right_single d] at hr
  refine ⟨hl, hr, ?_, ?_⟩
  · simp only [heightNode, heightSingleton, AVL.height_node, height_leftChain, BinaryTree.height]
    omega
  · simp only [heightNode, heightSingleton, AVL.height_node, height_rightChain, BinaryTree.height]
    omega

theorem payloads_leftChain (b n : Nat) : payloads (leftChain b n) = List.range' b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change inorder (Cached.erase (AVL.node (leftChain b n) (b + n) .nil)) = _
      rw [AVL.inorder_node]
      change payloads (leftChain b n) ++ [b + n] = _
      rw [ih]
      exact List.range'_1_concat.symm

theorem payloads_rightChain (b n : Nat) : payloads (rightChain b n) = List.range' b n := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
      change inorder (Cached.erase (AVL.node .nil b (rightChain (b + 1) n))) = _
      rw [AVL.inorder_node]
      change b :: payloads (rightChain (b + 1) n) = _
      rw [ih]
      rfl

theorem strict_leftChain (b n : Nat) : Search.OrderedList.Strict (payloads (leftChain b n)) := by
  rw [payloads_leftChain]
  exact List.pairwise_lt_range' (s := b) (n := n) 1 (by decide)

theorem strict_rightChain (b n : Nat) : Search.OrderedList.Strict (payloads (rightChain b n)) := by
  rw [payloads_rightChain]
  exact List.pairwise_lt_range' (s := b) (n := n) 1 (by decide)

theorem uniform_single_inorders (d : Nat) :
    payloads (HeightBalance.insert AVL.heightAnnotation d 1 (leftChain 2 (d + 1))) =
      List.range' 1 (d + 2) ∧
    payloads (HeightBalance.insert AVL.heightAnnotation d (d + 2) (rightChain 1 (d + 1))) =
      List.range' 1 (d + 2) := by
  constructor
  · change inorder (Cached.erase
      (HeightBalance.insert AVL.heightAnnotation d 1 (leftChain 2 (d + 1)))) = _
    rw [HeightBalance.inorder_insert _ _ _ _ (strict_leftChain 2 (d + 1))]
    change Search.OrderedList.insert 1 (payloads (leftChain 2 (d + 1))) = _
    rw [payloads_leftChain]
    rfl
  · rw [uniform_right_single]
    change inorder (Cached.erase (AVL.node (heightSingleton 1) 2 (rightChain 3 d))) = _
    rw [AVL.inorder_node]
    change [1, 2] ++ payloads (rightChain 3 d) = _
    rw [payloads_rightChain]
    rfl

theorem uniform_right_ordered_connection (d : Nat) :
    payloads (HeightBalance.insert AVL.heightAnnotation d (d + 2) (rightChain 1 (d + 1))) =
      Search.OrderedList.insert (d + 2) (payloads (rightChain 1 (d + 1))) :=
  HeightBalance.inorder_insert _ _ _ _ (strict_rightChain 1 (d + 1))

end Examples.HeightUpdates
