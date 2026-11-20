import Applications.Trees.AVL.Rebalance
import Applications.Trees.MaximumCacheObservations

/-! Connected local-rebalancing clients, including malformed caches, complete
augmentations, signed tolerances and exact payload placement. The independently
prepared expectations R01–R35/A01/A02/E01 are attributed in
`docs/research/fdsa-height-rebalance.md`; this module supplies their checked
connections to public results, not a new claim of independent derivation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.HeightRebalance
open Trees
universe u v
variable {α : Type u} {σ : Type v}

/- Finite example decisions remain local. The generic algebra needs neither
payload equality nor a default element. -/
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

abbrev HTree := BinaryTree (Nat × Nat)
def leaf (a : Nat) : HTree := AVL.node .nil a .nil
def leftStrict : HTree := AVL.node (leaf 1) 2 .nil
def leftTie : HTree := AVL.node (leaf 1) 2 (leaf 3)
def rightStrict : HTree := AVL.node .nil 2 (leaf 3)
def rightTie : HTree := AVL.node (leaf 2) 3 (leaf 4)
def leftDouble (p q : HTree) : HTree := AVL.node (leaf 1) 2 (AVL.node p 4 q)
def rightDouble (p q : HTree) : HTree := AVL.node (AVL.node p 4 q) 6 (leaf 7)
def doubleResult (p q : HTree) : HTree :=
  AVL.node (AVL.node (leaf 1) 2 p) 4 (AVL.node q 6 (leaf 7))

/-! R01–R09: exact ordinary branches, tagged payload positions and validity. -/
theorem ordinary_empty_left : AVL.balL (.nil : HTree) 2 .nil = leaf 2 :=
  AVL.balL_of_ne .nil 2 .nil (by decide)

theorem ordinary_empty_right : AVL.balR (.nil : HTree) 2 .nil = leaf 2 :=
  AVL.balR_of_ne .nil 2 .nil (by decide)

theorem ordinary_empty_valid : AVL.Valid (AVL.balL (.nil : HTree) 2 .nil) :=
  AVL.valid_balL .nil 2 .nil AVL.valid_nil AVL.valid_nil (by decide) (by decide)

theorem ordinary_empty_observations :
    (AVL.balL (.nil : HTree) 2 .nil).height = 1 ∧
    inorder (Cached.erase (AVL.balL (.nil : HTree) 2 .nil)) = [2] ∧
    (AVL.balR (.nil : HTree) 2 .nil).height = 1 ∧
    inorder (Cached.erase (AVL.balR (.nil : HTree) 2 .nil)) = [2] :=
  ⟨AVL.height_balL_of_ne .nil 2 .nil AVL.cacheValid_nil AVL.cacheValid_nil (by decide),
    (AVL.inorder_balL .nil 2 .nil).trans rfl,
    AVL.height_balR_of_ne .nil 2 .nil AVL.cacheValid_nil AVL.cacheValid_nil (by decide),
    (AVL.inorder_balR .nil 2 .nil).trans rfl⟩

theorem ordinary_left_strict : AVL.balL leftStrict 3 .nil = AVL.node (leaf 1) 2 (leaf 3) :=
  AVL.balL_single (leaf 1) 2 2 .nil 3 .nil (by decide) (by decide)

theorem ordinary_left_tie :
    AVL.balL leftTie 4 .nil = AVL.node (leaf 1) 2 (AVL.node (leaf 3) 4 .nil) :=
  AVL.balL_single (leaf 1) 2 2 (leaf 3) 4 .nil (by decide) (by decide)

theorem ordinary_right_strict : AVL.balR .nil 1 rightStrict = AVL.node (leaf 1) 2 (leaf 3) :=
  AVL.balR_single .nil 1 .nil 2 2 (leaf 3) (by decide) (by decide)

theorem ordinary_right_tie :
    AVL.balR .nil 1 rightTie = AVL.node (AVL.node .nil 1 (leaf 2)) 3 (leaf 4) :=
  AVL.balR_single .nil 1 (leaf 2) 3 2 (leaf 4) (by decide) (by decide)

theorem ordinary_single_heights :
    (AVL.balL leftStrict 3 .nil).height = 2 ∧
    (AVL.balL leftTie 4 .nil).height = 3 ∧
    (AVL.balR .nil 1 rightStrict).height = 2 ∧
    (AVL.balR .nil 1 rightTie).height = 3 := by
  rw [ordinary_left_strict, ordinary_left_tie, ordinary_right_strict, ordinary_right_tie]
  decide

theorem ordinary_single_validity :
    AVL.Valid (AVL.balL leftStrict 3 .nil) ∧ AVL.Valid (AVL.balL leftTie 4 .nil) ∧
    AVL.Valid (AVL.balR .nil 1 rightStrict) ∧ AVL.Valid (AVL.balR .nil 1 rightTie) :=
  ⟨AVL.valid_balL _ _ _ (by decide) (by decide) (by decide) (by decide),
    AVL.valid_balL _ _ _ (by decide) (by decide) (by decide) (by decide),
    AVL.valid_balR _ _ _ (by decide) (by decide) (by decide) (by decide),
    AVL.valid_balR _ _ _ (by decide) (by decide) (by decide) (by decide)⟩

theorem ordinary_single_inorders :
    inorder (Cached.erase (AVL.balL leftStrict 3 .nil)) = [1, 2, 3] ∧
    inorder (Cached.erase (AVL.balL leftTie 4 .nil)) = [1, 2, 3, 4] ∧
    inorder (Cached.erase (AVL.balR .nil 1 rightStrict)) = [1, 2, 3] ∧
    inorder (Cached.erase (AVL.balR .nil 1 rightTie)) = [1, 2, 3, 4] :=
  ⟨(AVL.inorder_balL _ _ _).trans rfl, (AVL.inorder_balL _ _ _).trans rfl,
    (AVL.inorder_balR _ _ _).trans rfl, (AVL.inorder_balR _ _ _).trans rfl⟩

theorem ordinary_double_left_left :
    AVL.balL (leftDouble (leaf 3) .nil) 6 (leaf 7) = doubleResult (leaf 3) .nil :=
  AVL.balL_double (leaf 1) 2 3 (leaf 3) 4 2 .nil 6 (leaf 7) (by decide) (by decide)

theorem ordinary_double_left_right :
    AVL.balL (leftDouble .nil (leaf 5)) 6 (leaf 7) = doubleResult .nil (leaf 5) :=
  AVL.balL_double (leaf 1) 2 3 .nil 4 2 (leaf 5) 6 (leaf 7) (by decide) (by decide)

theorem ordinary_double_left_both :
    AVL.balL (leftDouble (leaf 3) (leaf 5)) 6 (leaf 7) = doubleResult (leaf 3) (leaf 5) :=
  AVL.balL_double (leaf 1) 2 3 (leaf 3) 4 2 (leaf 5) 6 (leaf 7) (by decide) (by decide)

theorem ordinary_double_right_left :
    AVL.balR (leaf 1) 2 (rightDouble (leaf 3) .nil) = doubleResult (leaf 3) .nil :=
  AVL.balR_double (leaf 1) 2 (leaf 3) 4 2 .nil 6 3 (leaf 7) (by decide) (by decide)

theorem ordinary_double_right_right :
    AVL.balR (leaf 1) 2 (rightDouble .nil (leaf 5)) = doubleResult .nil (leaf 5) :=
  AVL.balR_double (leaf 1) 2 .nil 4 2 (leaf 5) 6 3 (leaf 7) (by decide) (by decide)

theorem ordinary_double_right_both :
    AVL.balR (leaf 1) 2 (rightDouble (leaf 3) (leaf 5)) = doubleResult (leaf 3) (leaf 5) :=
  AVL.balR_double (leaf 1) 2 (leaf 3) 4 2 (leaf 5) 6 3 (leaf 7) (by decide) (by decide)

theorem tagged_left_double_inorders :
    inorder (Cached.erase (AVL.balL (leftDouble (leaf 3) .nil) 6 (leaf 7))) =
      [1, 2, 3, 4, 6, 7] ∧
    inorder (Cached.erase (AVL.balL (leftDouble .nil (leaf 5)) 6 (leaf 7))) =
      [1, 2, 4, 5, 6, 7] ∧
    inorder (Cached.erase (AVL.balL (leftDouble (leaf 3) (leaf 5)) 6 (leaf 7))) =
      [1, 2, 3, 4, 5, 6, 7] :=
  ⟨(AVL.inorder_balL _ _ _).trans rfl, (AVL.inorder_balL _ _ _).trans rfl,
    (AVL.inorder_balL _ _ _).trans rfl⟩

theorem tagged_right_double_inorders :
    inorder (Cached.erase (AVL.balR (leaf 1) 2 (rightDouble (leaf 3) .nil))) =
      [1, 2, 3, 4, 6, 7] ∧
    inorder (Cached.erase (AVL.balR (leaf 1) 2 (rightDouble .nil (leaf 5)))) =
      [1, 2, 4, 5, 6, 7] ∧
    inorder (Cached.erase (AVL.balR (leaf 1) 2 (rightDouble (leaf 3) (leaf 5)))) =
      [1, 2, 3, 4, 5, 6, 7] :=
  ⟨(AVL.inorder_balR _ _ _).trans rfl, (AVL.inorder_balR _ _ _).trans rfl,
    (AVL.inorder_balR _ _ _).trans rfl⟩

theorem ordinary_double_heights :
    (AVL.balL (leftDouble (leaf 3) .nil) 6 (leaf 7)).height = 3 ∧
    (AVL.balL (leftDouble .nil (leaf 5)) 6 (leaf 7)).height = 3 ∧
    (AVL.balL (leftDouble (leaf 3) (leaf 5)) 6 (leaf 7)).height = 3 ∧
    (AVL.balR (leaf 1) 2 (rightDouble (leaf 3) .nil)).height = 3 ∧
    (AVL.balR (leaf 1) 2 (rightDouble .nil (leaf 5))).height = 3 ∧
    (AVL.balR (leaf 1) 2 (rightDouble (leaf 3) (leaf 5))).height = 3 :=
  ⟨AVL.height_balL_double (leaf 1) 2 3 (AVL.node (leaf 3) 4 .nil) 6 (leaf 7)
      (by decide) (by decide) (by decide) (by decide),
    AVL.height_balL_double (leaf 1) 2 3 (AVL.node .nil 4 (leaf 5)) 6 (leaf 7)
      (by decide) (by decide) (by decide) (by decide),
    AVL.height_balL_double (leaf 1) 2 3 (AVL.node (leaf 3) 4 (leaf 5)) 6 (leaf 7)
      (by decide) (by decide) (by decide) (by decide),
    AVL.height_balR_double (leaf 1) 2 (AVL.node (leaf 3) 4 .nil) 6 3 (leaf 7)
      (by decide) (by decide) (by decide) (by decide),
    AVL.height_balR_double (leaf 1) 2 (AVL.node .nil 4 (leaf 5)) 6 3 (leaf 7)
      (by decide) (by decide) (by decide) (by decide),
    AVL.height_balR_double (leaf 1) 2 (AVL.node (leaf 3) 4 (leaf 5)) 6 3 (leaf 7)
      (by decide) (by decide) (by decide) (by decide)⟩

theorem ordinary_double_validity :
    AVL.Valid (AVL.balL (leftDouble (leaf 3) .nil) 6 (leaf 7)) ∧
    AVL.Valid (AVL.balL (leftDouble .nil (leaf 5)) 6 (leaf 7)) ∧
    AVL.Valid (AVL.balL (leftDouble (leaf 3) (leaf 5)) 6 (leaf 7)) ∧
    AVL.Valid (AVL.balR (leaf 1) 2 (rightDouble (leaf 3) .nil)) ∧
    AVL.Valid (AVL.balR (leaf 1) 2 (rightDouble .nil (leaf 5))) ∧
    AVL.Valid (AVL.balR (leaf 1) 2 (rightDouble (leaf 3) (leaf 5))) :=
  ⟨AVL.valid_balL _ _ _ (by decide) (by decide) (by decide) (by decide),
    AVL.valid_balL _ _ _ (by decide) (by decide) (by decide) (by decide),
    AVL.valid_balL _ _ _ (by decide) (by decide) (by decide) (by decide),
    AVL.valid_balR _ _ _ (by decide) (by decide) (by decide) (by decide),
    AVL.valid_balR _ _ _ (by decide) (by decide) (by decide) (by decide),
    AVL.valid_balR _ _ _ (by decide) (by decide) (by decide) (by decide)⟩

theorem left_middle_diagram :
    (leaf 1).height = (leaf 7).height ∧
    max (BinaryTree.nil : HTree).height (leaf 5).height = (leaf 7).height ∧
    ((BinaryTree.nil : HTree).height = (leaf 7).height ∨ (leaf 5).height = (leaf 7).height) :=
  AVL.double_middle_heights_left (leaf 1) 2 3 .nil 4 2 (leaf 5) (leaf 7)
    (by decide) (by decide) (by decide)

theorem right_middle_diagram :
    (leaf 7).height = (leaf 1).height ∧
    max (leaf 3).height (BinaryTree.nil : HTree).height = (leaf 1).height ∧
    ((leaf 3).height = (leaf 1).height ∨ (BinaryTree.nil : HTree).height = (leaf 1).height) :=
  AVL.double_middle_heights_right (leaf 1) (leaf 3) 4 2 .nil 6 3 (leaf 7)
    (by decide) (by decide) (by decide)

theorem neither_middle_position_is_required :
    (BinaryTree.nil : HTree).height ≠ (leaf 7).height ∧
      (leaf 3).height = (leaf 7).height ∧ (leaf 5).height = (leaf 7).height := by decide

/-! R10–R11: no validity, inhabitance or positive-tolerance premise. -/
theorem empty_heavy_left_impossible (ann : HeightBalance.HeightAnnotation α σ)
    (d : Nat) (r : BinaryTree (α × σ)) :
    HeightBalance.ht ann .nil ≠ HeightBalance.ht ann r + d + 1 := by
  intro h
  exact HeightBalance.left_ne_nil_of_trigger ann d .nil r h rfl

theorem empty_heavy_right_impossible (ann : HeightBalance.HeightAnnotation α σ)
    (d : Nat) (l : BinaryTree (α × σ)) :
    HeightBalance.ht ann .nil ≠ HeightBalance.ht ann l + d + 1 := by
  intro h
  exact HeightBalance.right_ne_nil_of_trigger ann d l .nil h rfl

theorem empty_middle_impossible (ann : HeightBalance.HeightAnnotation α σ)
    (outer : BinaryTree (α × σ)) :
    ¬ HeightBalance.ht ann outer < HeightBalance.ht ann .nil := by
  intro h
  exact HeightBalance.ne_nil_of_ht_lt ann outer .nil h rfl

/-! R12–R18: raw stored tests, exact triggers and retained bad descendants. -/
def forgedTwo : HTree := .node (1, 2) .nil .nil
def forgedThree : HTree := .node (1, 3) .nil .nil
def zeroLeaf : HTree := .node (2, 0) .nil .nil
def rawTie : HTree := .node (1, 2) .nil zeroLeaf
def hiddenTrigger : HTree := .node (2, 0) (leaf 1) .nil
def badDescendant : HTree := .node (1, 0) .nil .nil
def correctRoot : HTree := .node (2, 2) badDescendant (leaf 3)

theorem forged_two_branch : AVL.balL forgedTwo 2 .nil = AVL.node .nil 1 (leaf 2) :=
  AVL.balL_single .nil 1 2 .nil 2 .nil (by decide) (by decide)

theorem forged_three_fallback :
    AVL.balL forgedThree 2 .nil = AVL.node forgedThree 2 .nil :=
  AVL.balL_of_ne _ _ _ (by decide)

theorem forged_trigger_separator :
    AVL.ht forgedTwo = 2 ∧ forgedTwo.height = 1 ∧
    AVL.CacheValid (AVL.balL forgedTwo 2 .nil) ∧
    AVL.ht (AVL.balL forgedThree 2 .nil) = 4 ∧
    (AVL.balL forgedThree 2 .nil).height = 2 ∧
    ¬ AVL.CacheValid (AVL.balL forgedThree 2 .nil) := by
  rw [forged_two_branch, forged_three_fallback]
  decide

theorem raw_cached_tie_branch :
    AVL.balL rawTie 3 .nil = AVL.node .nil 1 (AVL.node zeroLeaf 3 .nil) :=
  AVL.balL_single .nil 1 2 zeroLeaf 3 .nil (by decide) (by decide)

theorem raw_cached_tie_separator :
    AVL.ht zeroLeaf = 0 ∧ zeroLeaf.height = 1 ∧
    (AVL.balL rawTie 3 .nil).height = 3 ∧
    ¬ AVL.CacheValid (AVL.balL rawTie 3 .nil) ∧
    ¬ AVL.Balanced (Cached.erase (AVL.balL rawTie 3 .nil)) := by
  rw [raw_cached_tie_branch]
  decide

theorem hidden_actual_trigger_fallback :
    AVL.balL hiddenTrigger 3 .nil = AVL.node hiddenTrigger 3 .nil :=
  AVL.balL_of_ne _ _ _ (by decide)

theorem hidden_actual_trigger_separator :
    hiddenTrigger.height = 2 ∧ AVL.ht hiddenTrigger = 0 ∧
    (AVL.balL hiddenTrigger 3 .nil).height = 3 ∧
    AVL.ht (AVL.balL hiddenTrigger 3 .nil) = 1 := by
  rw [hidden_actual_trigger_fallback]
  decide

theorem correct_root_is_insufficient :
    AVL.ht correctRoot = correctRoot.height ∧
    AVL.ht correctRoot = max (AVL.ht badDescendant) (AVL.ht (leaf 3)) + 1 ∧
    ¬ AVL.CacheValid correctRoot := by decide

theorem retained_bad_descendant_branch :
    AVL.balL correctRoot 4 .nil = AVL.node (AVL.node badDescendant 2 .nil) 3 (leaf 4) :=
  AVL.balL_double badDescendant 2 2 .nil 3 1 .nil 4 .nil (by decide) (by decide)

theorem retained_bad_descendant_separator :
    (AVL.balL correctRoot 4 .nil).height = 3 ∧
    AVL.ht (AVL.balL correctRoot 4 .nil) = 2 ∧
    ¬ AVL.CacheValid (AVL.balL correctRoot 4 .nil) := by
  rw [retained_bad_descendant_branch]
  decide

theorem malformed_inorders :
    inorder (Cached.erase (AVL.balL forgedTwo 2 .nil)) = [1, 2] ∧
    inorder (Cached.erase (AVL.balL forgedThree 2 .nil)) = [1, 2] ∧
    inorder (Cached.erase (AVL.balL rawTie 3 .nil)) = [1, 2, 3] ∧
    inorder (Cached.erase (AVL.balL hiddenTrigger 3 .nil)) = [1, 2, 3] ∧
    inorder (Cached.erase (AVL.balL correctRoot 4 .nil)) = [1, 2, 3, 4] :=
  ⟨(AVL.inorder_balL _ _ _).trans rfl, (AVL.inorder_balL _ _ _).trans rfl,
    (AVL.inorder_balL _ _ _).trans rfl, (AVL.inorder_balL _ _ _).trans rfl,
    (AVL.inorder_balL _ _ _).trans rfl⟩

theorem duplicate_unordered_inorder :
    inorder (Cached.erase (AVL.balL (AVL.node (leaf 9) 9 .nil) 2 .nil)) = [9, 9, 2] :=
  (AVL.inorder_balL _ _ _).trans rfl

/-! R19–R29: all positive tolerances and explicit d=2/d=3 instances. -/
def perfect : Nat → HTree
  | 0 => .nil
  | n + 1 => AVL.node (perfect n) 0 (perfect n)

@[simp] theorem height_perfect (n : Nat) : (perfect n).height = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [perfect, AVL.height_node, ih]

theorem perfect_valid (d n : Nat) : HeightBalance.ValidD AVL.heightAnnotation d (perfect n) := by
  induction n with
  | zero => exact HeightBalance.validD_nil _ d
  | succ n ih =>
      apply (HeightBalance.node_validD_iff AVL.heightAnnotation d (perfect n) 0 (perfect n)).mpr
      refine ⟨ih, ih, (HeightBalance.height_balance_iff d _ _).mpr ?_⟩
      constructor <;> omega

theorem perfect_cache (n : Nat) : AVL.CacheValid (perfect n) := (perfect_valid 0 n).2

@[simp] theorem ht_perfect (n : Nat) : AVL.ht (perfect n) = n :=
  (AVL.ht_eq_height_of_cacheValid _ (perfect_cache n)).trans (height_perfect n)

theorem full_left_range (d hl hr : Nat) (hd : 1 ≤ d)
    (hlo : hr - d ≤ hl) (hhi : hl ≤ hr + d + 1) :
    HeightBalance.ValidD AVL.heightAnnotation d
      (HeightBalance.balL AVL.heightAnnotation d (perfect hl) 0 (perfect hr)) :=
  HeightBalance.validD_balL _ d _ 0 _ hd (perfect_valid d hl) (perfect_valid d hr)
    (by simpa only [height_perfect] using hlo) (by simpa only [height_perfect] using hhi)

theorem full_right_range (d hl hr : Nat) (hd : 1 ≤ d)
    (hlo : hl - d ≤ hr) (hhi : hr ≤ hl + d + 1) :
    HeightBalance.ValidD AVL.heightAnnotation d
      (HeightBalance.balR AVL.heightAnnotation d (perfect hl) 0 (perfect hr)) :=
  HeightBalance.validD_balR _ d _ 0 _ hd (perfect_valid d hl) (perfect_valid d hr)
    (by simpa only [height_perfect] using hlo) (by simpa only [height_perfect] using hhi)

theorem full_range_boundary_witnesses (d : Nat) (hd : 1 ≤ d) :
    HeightBalance.ValidD AVL.heightAnnotation d
      (HeightBalance.balL AVL.heightAnnotation d (perfect 0) 0 (perfect d)) ∧
    HeightBalance.ValidD AVL.heightAnnotation d
      (HeightBalance.balL AVL.heightAnnotation d (perfect d) 0 (perfect 0)) ∧
    HeightBalance.ValidD AVL.heightAnnotation d
      (HeightBalance.balL AVL.heightAnnotation d (perfect 0) 0 (perfect 0)) ∧
    HeightBalance.ValidD AVL.heightAnnotation d
      (HeightBalance.balL AVL.heightAnnotation d (perfect (d + 1)) 0 (perfect 0)) ∧
    HeightBalance.ValidD AVL.heightAnnotation d
      (HeightBalance.balR AVL.heightAnnotation d (perfect d) 0 (perfect 0)) ∧
    HeightBalance.ValidD AVL.heightAnnotation d
      (HeightBalance.balR AVL.heightAnnotation d (perfect 0) 0 (perfect d)) ∧
    HeightBalance.ValidD AVL.heightAnnotation d
      (HeightBalance.balR AVL.heightAnnotation d (perfect 0) 0 (perfect 0)) ∧
    HeightBalance.ValidD AVL.heightAnnotation d
      (HeightBalance.balR AVL.heightAnnotation d (perfect 0) 0 (perfect (d + 1))) :=
  ⟨full_left_range d 0 d hd (by omega) (by omega),
    full_left_range d d 0 hd (by omega) (by omega),
    full_left_range d 0 0 hd (by omega) (by omega),
    full_left_range d (d + 1) 0 hd (by omega) (by omega),
    full_right_range d d 0 hd (by omega) (by omega),
    full_right_range d 0 d hd (by omega) (by omega),
    full_right_range d 0 0 hd (by omega) (by omega),
    full_right_range d 0 (d + 1) hd (by omega) (by omega)⟩

theorem lower_boundary_heights (d : Nat) :
    (HeightBalance.balL AVL.heightAnnotation d (perfect 0) 0 (perfect d)).height = d + 1 ∧
    (HeightBalance.balR AVL.heightAnnotation d (perfect d) 0 (perfect 0)).height = d + 1 := by
  constructor
  · have h := HeightBalance.height_balL_of_ne AVL.heightAnnotation d (perfect 0) 0
      (perfect d) (perfect_cache 0) (perfect_cache d)
      (by simp only [height_perfect]; omega)
    simpa only [height_perfect, Nat.zero_max] using h
  · have h := HeightBalance.height_balR_of_ne AVL.heightAnnotation d (perfect d) 0
      (perfect 0) (perfect_cache d) (perfect_cache 0)
      (by simp only [height_perfect]; omega)
    simpa only [height_perfect, Nat.max_zero] using h

theorem ordinary_outside_trigger_height :
    (AVL.balL (perfect 3) 1 .nil).height = 4 ∧
    (AVL.balR .nil 1 (perfect 3)).height = 4 :=
  ⟨AVL.height_balL_of_ne _ _ _ (perfect_cache 3) AVL.cacheValid_nil (by decide),
    AVL.height_balR_of_ne _ _ _ AVL.cacheValid_nil (perfect_cache 3) (by decide)⟩

theorem outside_trigger_cache_without_balance :
    AVL.CacheValid (AVL.balL (perfect 3) 1 .nil) ∧
    AVL.CacheValid (AVL.balR .nil 1 (perfect 3)) ∧
    ¬ AVL.Valid (AVL.balL (perfect 3) 1 .nil) ∧
    ¬ AVL.Valid (AVL.balR .nil 1 (perfect 3)) :=
  ⟨AVL.cacheValid_balL _ _ _ (perfect_cache 3) AVL.cacheValid_nil,
    AVL.cacheValid_balR _ _ _ AVL.cacheValid_nil (perfect_cache 3), by decide, by decide⟩

theorem cache_only_trigger_heights :
    (AVL.balL (AVL.node (perfect 3) 1 .nil) 2 (perfect 2)).height = 4 ∧
    (AVL.balR (perfect 2) 1 (AVL.node .nil 2 (perfect 3))).height = 4 :=
  ⟨AVL.height_balL_single (perfect 3) 1 4 .nil 2 (perfect 2)
      (by decide) (perfect_cache 2) (by decide) (by decide),
    AVL.height_balR_single (perfect 2) 1 .nil 2 4 (perfect 3)
      (perfect_cache 2) (by decide) (by decide) (by decide)⟩

theorem cache_only_trigger_is_not_repair :
    ¬ AVL.Valid (AVL.balL (AVL.node (perfect 3) 1 .nil) 2 (perfect 2)) ∧
    ¬ AVL.Valid (AVL.balR (perfect 2) 1 (AVL.node .nil 2 (perfect 3))) := by decide

theorem too_tall_left_node_invalid (d : Nat) :
    ¬ HeightBalance.ValidD AVL.heightAnnotation d (AVL.node (perfect (d + 1)) 1 .nil) := by
  intro h
  have gap := ((HeightBalance.node_validD_iff AVL.heightAnnotation d _ 1 .nil).mp h).2.2
  have bound := ((HeightBalance.height_balance_iff d _ _).mp gap).1
  simp only [height_perfect, BinaryTree.height] at bound
  omega

theorem too_tall_right_node_invalid (d a : Nat) :
    ¬ HeightBalance.ValidD AVL.heightAnnotation d (AVL.node .nil a (perfect (d + 1))) := by
  intro h
  have gap := ((HeightBalance.node_validD_iff AVL.heightAnnotation d .nil a _).mp h).2.2
  have bound := ((HeightBalance.height_balance_iff d _ _).mp gap).2
  simp only [height_perfect, BinaryTree.height] at bound
  omega

theorem omitted_lower_bound_fails (d : Nat) :
    ¬ HeightBalance.ValidD AVL.heightAnnotation d
      (HeightBalance.balL AVL.heightAnnotation d .nil 1 (perfect (d + 1))) ∧
    ¬ HeightBalance.ValidD AVL.heightAnnotation d
      (HeightBalance.balR AVL.heightAnnotation d (perfect (d + 1)) 1 .nil) := by
  constructor
  · rw [HeightBalance.balL_of_ne _ _ _ _ _ (by
      simp only [HeightBalance.ht_nil, AVL.ht_heightAnnotation, ht_perfect]; omega)]
    exact too_tall_right_node_invalid d 1
  · rw [HeightBalance.balR_of_ne _ _ _ _ _ (by
      simp only [HeightBalance.ht_nil, AVL.ht_heightAnnotation, ht_perfect]; omega)]
    exact too_tall_left_node_invalid d

def singleLeft (d s : Nat) : HTree := .node (2, d + 1) (perfect d) (perfect s)
def singleRight (d s : Nat) : HTree := .node (2, d + 1) (perfect s) (perfect d)

theorem single_left_input_valid (d s : Nat) (hs : s ≤ d) :
    HeightBalance.ValidD AVL.heightAnnotation d (singleLeft d s) := by
  apply (AVL.validD_node_actual_iff d 2 (d + 1) (perfect d) (perfect s)).mpr
  refine ⟨perfect_valid d d, perfect_valid d s, ?_, ?_⟩
  · apply (HeightBalance.height_balance_iff d _ _).mpr
    simp only [height_perfect]
    constructor <;> omega
  · simp only [height_perfect, max_eq_left hs]

theorem single_right_input_valid (d s : Nat) (hs : s ≤ d) :
    HeightBalance.ValidD AVL.heightAnnotation d (singleRight d s) := by
  apply (AVL.validD_node_actual_iff d 2 (d + 1) (perfect s) (perfect d)).mpr
  refine ⟨perfect_valid d s, perfect_valid d d, ?_, ?_⟩
  · apply (HeightBalance.height_balance_iff d _ _).mpr
    simp only [height_perfect]
    constructor <;> omega
  · simp only [height_perfect, max_eq_right hs]

theorem single_outputs_valid (d s : Nat) (hd : 1 ≤ d) (hs : s ≤ d) :
    HeightBalance.ValidD AVL.heightAnnotation d
      (HeightBalance.balL AVL.heightAnnotation d (singleLeft d s) 3 .nil) ∧
    HeightBalance.ValidD AVL.heightAnnotation d
      (HeightBalance.balR AVL.heightAnnotation d .nil 1 (singleRight d s)) := by
  constructor
  · apply HeightBalance.validD_balL _ d _ 3 .nil hd (single_left_input_valid d s hs)
      (HeightBalance.validD_nil _ d)
    · simp only [BinaryTree.height, Nat.zero_sub, Nat.zero_le]
    · simp only [singleLeft, BinaryTree.height, height_perfect, max_eq_left hs, Nat.zero_add]
      exact Nat.le_refl _
  · apply HeightBalance.validD_balR _ d .nil 1 _ hd (HeightBalance.validD_nil _ d)
      (single_right_input_valid d s hs)
    · simp only [BinaryTree.height, Nat.zero_sub, Nat.zero_le]
    · simp only [singleRight, BinaryTree.height, height_perfect, max_eq_right hs, Nat.zero_add]
      exact Nat.le_refl _

theorem single_left_branch (d s : Nat) (hs : s ≤ d) :
    HeightBalance.balL AVL.heightAnnotation d (singleLeft d s) 3 .nil =
      AVL.node (perfect d) 2 (AVL.node (perfect s) 3 .nil) :=
  HeightBalance.balL_single AVL.heightAnnotation d _ 2 (d + 1) _ 3 .nil
    (by simp [AVL.heightAnnotation])
    (by simpa only [AVL.ht_heightAnnotation, ht_perfect] using hs)

theorem single_right_branch (d s : Nat) (hs : s ≤ d) :
    HeightBalance.balR AVL.heightAnnotation d .nil 1 (singleRight d s) =
      AVL.node (AVL.node .nil 1 (perfect s)) 2 (perfect d) :=
  HeightBalance.balR_single AVL.heightAnnotation d .nil 1 _ 2 (d + 1) _
    (by simp [AVL.heightAnnotation])
    (by simpa only [AVL.ht_heightAnnotation, ht_perfect] using hs)

theorem single_left_height (d s : Nat) (hd : 1 ≤ d) (hs : s ≤ d) :
    (HeightBalance.balL AVL.heightAnnotation d (singleLeft d s) 3 .nil).height =
      if s = d then d + 2 else d + 1 := by
  simpa only [singleLeft, height_perfect, BinaryTree.height, Nat.zero_add] using
    HeightBalance.height_balL_single AVL.heightAnnotation d (perfect d) 2 (d + 1)
      (perfect s) 3 .nil hd (single_left_input_valid d s hs).2
      (HeightBalance.cacheValid_nil _) (by simp [max_eq_left hs])
      (by simpa only [AVL.ht_heightAnnotation, ht_perfect] using hs)

theorem single_right_height (d s : Nat) (hd : 1 ≤ d) (hs : s ≤ d) :
    (HeightBalance.balR AVL.heightAnnotation d .nil 1 (singleRight d s)).height =
      if s = d then d + 2 else d + 1 := by
  simpa only [singleRight, height_perfect, BinaryTree.height, Nat.zero_add] using
    HeightBalance.height_balR_single AVL.heightAnnotation d .nil 1 (perfect s) 2 (d + 1)
      (perfect d) hd (HeightBalance.cacheValid_nil _) (single_right_input_valid d s hs).2
      (by simp [max_eq_right hs])
      (by simpa only [AVL.ht_heightAnnotation, ht_perfect] using hs)

def childHeights : HTree → Nat × Nat
  | .nil => (0, 0)
  | .node _ l r => (l.height, r.height)

theorem single_child_heights (d s : Nat) (hs : s ≤ d) :
    childHeights (HeightBalance.balL AVL.heightAnnotation d (singleLeft d s) 3 .nil) =
      (d, s + 1) ∧
    childHeights (HeightBalance.balR AVL.heightAnnotation d .nil 1 (singleRight d s)) =
      (s + 1, d) := by
  rw [single_left_branch d s hs, single_right_branch d s hs]
  change ((perfect d).height, (AVL.node (perfect s) 3 .nil).height) = (d, s + 1) ∧
    ((AVL.node .nil 1 (perfect s)).height, (perfect d).height) = (s + 1, d)
  simp

theorem single_heights_two_three :
    [(HeightBalance.balL AVL.heightAnnotation 2 (singleLeft 2 0) 3 .nil).height,
      (HeightBalance.balL AVL.heightAnnotation 2 (singleLeft 2 1) 3 .nil).height,
      (HeightBalance.balL AVL.heightAnnotation 2 (singleLeft 2 2) 3 .nil).height,
      (HeightBalance.balL AVL.heightAnnotation 3 (singleLeft 3 0) 3 .nil).height,
      (HeightBalance.balL AVL.heightAnnotation 3 (singleLeft 3 1) 3 .nil).height,
      (HeightBalance.balL AVL.heightAnnotation 3 (singleLeft 3 2) 3 .nil).height,
      (HeightBalance.balL AVL.heightAnnotation 3 (singleLeft 3 3) 3 .nil).height] =
      [3, 3, 4, 4, 4, 4, 5] ∧
    [(HeightBalance.balR AVL.heightAnnotation 2 .nil 1 (singleRight 2 0)).height,
      (HeightBalance.balR AVL.heightAnnotation 2 .nil 1 (singleRight 2 1)).height,
      (HeightBalance.balR AVL.heightAnnotation 2 .nil 1 (singleRight 2 2)).height,
      (HeightBalance.balR AVL.heightAnnotation 3 .nil 1 (singleRight 3 0)).height,
      (HeightBalance.balR AVL.heightAnnotation 3 .nil 1 (singleRight 3 1)).height,
      (HeightBalance.balR AVL.heightAnnotation 3 .nil 1 (singleRight 3 2)).height,
      (HeightBalance.balR AVL.heightAnnotation 3 .nil 1 (singleRight 3 3)).height] =
      [3, 3, 4, 4, 4, 4, 5] := by
  rw [single_left_height 2 0 (by decide) (by decide),
    single_left_height 2 1 (by decide) (by decide), single_left_height 2 2 (by decide) (by decide),
    single_left_height 3 0 (by decide) (by decide), single_left_height 3 1 (by decide) (by decide),
    single_left_height 3 2 (by decide) (by decide), single_left_height 3 3 (by decide) (by decide),
    single_right_height 2 0 (by decide) (by decide),
    single_right_height 2 1 (by decide) (by decide), single_right_height 2 2 (by decide) (by decide),
    single_right_height 3 0 (by decide) (by decide), single_right_height 3 1 (by decide) (by decide),
    single_right_height 3 2 (by decide) (by decide), single_right_height 3 3 (by decide) (by decide)]
  decide

def tieInnerLeft (d : Nat) : HTree := AVL.node .nil 2 (perfect d)
def tieInnerRight (d : Nat) : HTree := AVL.node (perfect d) 2 .nil
def tieHeavyLeft (d : Nat) : HTree := AVL.node (perfect (d + 1)) 1 (tieInnerLeft d)
def tieHeavyRight (d : Nat) : HTree := AVL.node (tieInnerRight d) 3 (perfect (d + 1))

theorem generalized_tie_guards (d : Nat) :
    AVL.ht (tieInnerLeft d) = AVL.ht (perfect (d + 1)) ∧
    AVL.ht (tieHeavyLeft d) = AVL.ht (perfect 1) + d + 1 ∧
    AVL.ht (tieInnerRight d) = AVL.ht (perfect (d + 1)) ∧
    AVL.ht (tieHeavyRight d) = AVL.ht (perfect 1) + d + 1 := by
  simp [tieInnerLeft, tieInnerRight, tieHeavyLeft, tieHeavyRight,
    Nat.add_comm, Nat.add_left_comm]

theorem tie_heavy_valid (d : Nat) :
    HeightBalance.ValidD AVL.heightAnnotation d (tieHeavyLeft d) ∧
    HeightBalance.ValidD AVL.heightAnnotation d (tieHeavyRight d) := by
  have innerL : HeightBalance.ValidD AVL.heightAnnotation d (tieInnerLeft d) := by
    apply (HeightBalance.node_validD_iff _ d .nil 2 (perfect d)).mpr
    refine ⟨HeightBalance.validD_nil _ d, perfect_valid d d, ?_⟩
    apply (HeightBalance.height_balance_iff d _ _).mpr
    simp only [height_perfect, BinaryTree.height]
    constructor <;> omega
  have innerR : HeightBalance.ValidD AVL.heightAnnotation d (tieInnerRight d) := by
    apply (HeightBalance.node_validD_iff _ d (perfect d) 2 .nil).mpr
    refine ⟨perfect_valid d d, HeightBalance.validD_nil _ d, ?_⟩
    apply (HeightBalance.height_balance_iff d _ _).mpr
    simp only [height_perfect, BinaryTree.height]
    constructor <;> omega
  constructor
  · apply (HeightBalance.node_validD_iff _ d (perfect (d + 1)) 1 (tieInnerLeft d)).mpr
    refine ⟨perfect_valid d (d + 1), innerL, (HeightBalance.height_balance_iff d _ _).mpr ?_⟩
    simp only [tieInnerLeft, AVL.height_node, height_perfect, BinaryTree.height, Nat.zero_max]
    constructor <;> omega
  · apply (HeightBalance.node_validD_iff _ d (tieInnerRight d) 3 (perfect (d + 1))).mpr
    refine ⟨innerR, perfect_valid d (d + 1), (HeightBalance.height_balance_iff d _ _).mpr ?_⟩
    simp only [tieInnerRight, AVL.height_node, height_perfect, BinaryTree.height, Nat.max_zero]
    constructor <;> omega

theorem tie_repair_valid (d : Nat) (hd : 1 ≤ d) :
    HeightBalance.ValidD AVL.heightAnnotation d
      (HeightBalance.balL AVL.heightAnnotation d (tieHeavyLeft d) 3 (perfect 1)) ∧
    HeightBalance.ValidD AVL.heightAnnotation d
      (HeightBalance.balR AVL.heightAnnotation d (perfect 1) 1 (tieHeavyRight d)) := by
  constructor
  · apply HeightBalance.validD_balL _ d _ 3 _ hd (tie_heavy_valid d).1 (perfect_valid d 1)
    all_goals simp [tieHeavyLeft, tieInnerLeft]; omega
  · apply HeightBalance.validD_balR _ d _ 1 _ hd (perfect_valid d 1) (tie_heavy_valid d).2
    all_goals simp [tieHeavyRight, tieInnerRight]; omega

theorem forced_double_on_tie_fails (d : Nat) :
    ¬ HeightBalance.ValidD AVL.heightAnnotation d
      (AVL.node (AVL.node (perfect (d + 1)) 1 .nil) 2 (AVL.node (perfect d) 3 (perfect 1))) ∧
    ¬ HeightBalance.ValidD AVL.heightAnnotation d
      (AVL.node (AVL.node (perfect 1) 1 (perfect d)) 2 (AVL.node .nil 3 (perfect (d + 1)))) := by
  constructor
  · intro h
    exact too_tall_left_node_invalid d ((HeightBalance.node_validD_iff _ d _ 2 _).mp h).1
  · intro h
    exact too_tall_right_node_invalid d 3 ((HeightBalance.node_validD_iff _ d _ 2 _).mp h).2.1

def doubleLeftInput (x p q : Nat) : HTree :=
  AVL.node (perfect x) 1 (AVL.node (perfect p) 2 (perfect q))
def doubleRightInput (x p q : Nat) : HTree :=
  AVL.node (AVL.node (perfect p) 2 (perfect q)) 3 (perfect x)

theorem generalized_left_double_branch (d x p q k : Nat)
    (h : max x (max p q + 1) + 1 = k + d + 1) (hs : x < max p q + 1) :
    HeightBalance.balL AVL.heightAnnotation d (doubleLeftInput x p q) 3 (perfect k) =
      AVL.node (AVL.node (perfect x) 1 (perfect p)) 2 (AVL.node (perfect q) 3 (perfect k)) := by
  apply HeightBalance.balL_double
  · change max (AVL.ht (perfect x)) (AVL.ht (AVL.node (perfect p) 2 (perfect q))) + 1 =
      AVL.ht (perfect k) + d + 1
    simpa only [AVL.ht_node_smart, ht_perfect] using h
  · change AVL.ht (perfect x) < AVL.ht (AVL.node (perfect p) 2 (perfect q))
    simpa only [AVL.ht_node_smart, ht_perfect] using hs

theorem generalized_right_double_branch (d x p q k : Nat)
    (h : max (max p q + 1) x + 1 = k + d + 1) (hs : x < max p q + 1) :
    HeightBalance.balR AVL.heightAnnotation d (perfect k) 1 (doubleRightInput x p q) =
      AVL.node (AVL.node (perfect k) 1 (perfect p)) 2 (AVL.node (perfect q) 3 (perfect x)) := by
  apply HeightBalance.balR_double
  · change max (AVL.ht (AVL.node (perfect p) 2 (perfect q))) (AVL.ht (perfect x)) + 1 =
      AVL.ht (perfect k) + d + 1
    simpa only [AVL.ht_node_smart, ht_perfect] using h
  · change AVL.ht (perfect x) < AVL.ht (AVL.node (perfect p) 2 (perfect q))
    simpa only [AVL.ht_node_smart, ht_perfect] using hs

theorem generalized_left_double_children (d x p q k : Nat)
    (h : max x (max p q + 1) + 1 = k + d + 1) (hs : x < max p q + 1) :
    childHeights (HeightBalance.balL AVL.heightAnnotation d
      (doubleLeftInput x p q) 3 (perfect k)) = (max x p + 1, max q k + 1) := by
  rw [generalized_left_double_branch d x p q k h hs]
  change ((AVL.node (perfect x) 1 (perfect p)).height,
    (AVL.node (perfect q) 3 (perfect k)).height) = _
  simp

theorem generalized_right_double_children (d x p q k : Nat)
    (h : max (max p q + 1) x + 1 = k + d + 1) (hs : x < max p q + 1) :
    childHeights (HeightBalance.balR AVL.heightAnnotation d
      (perfect k) 1 (doubleRightInput x p q)) = (max k p + 1, max q x + 1) := by
  rw [generalized_right_double_branch d x p q k h hs]
  change ((AVL.node (perfect k) 1 (perfect p)).height,
    (AVL.node (perfect q) 3 (perfect x)).height) = _
  simp

theorem generalized_double_positions :
    childHeights (HeightBalance.balL AVL.heightAnnotation 2 (doubleLeftInput 0 1 0) 3 .nil) = (2, 1) ∧
    childHeights (HeightBalance.balL AVL.heightAnnotation 2 (doubleLeftInput 0 0 1) 3 .nil) = (1, 2) ∧
    childHeights (HeightBalance.balL AVL.heightAnnotation 2 (doubleLeftInput 0 1 1) 3 .nil) = (2, 2) ∧
    childHeights (HeightBalance.balL AVL.heightAnnotation 3 (doubleLeftInput 0 2 0) 3 .nil) = (3, 1) ∧
    childHeights (HeightBalance.balL AVL.heightAnnotation 3 (doubleLeftInput 0 0 2) 3 .nil) = (1, 3) ∧
    childHeights (HeightBalance.balL AVL.heightAnnotation 3 (doubleLeftInput 0 2 2) 3 .nil) = (3, 3) :=
  ⟨generalized_left_double_children 2 0 1 0 0 (by decide) (by decide),
    generalized_left_double_children 2 0 0 1 0 (by decide) (by decide),
    generalized_left_double_children 2 0 1 1 0 (by decide) (by decide),
    generalized_left_double_children 3 0 2 0 0 (by decide) (by decide),
    generalized_left_double_children 3 0 0 2 0 (by decide) (by decide),
    generalized_left_double_children 3 0 2 2 0 (by decide) (by decide)⟩

theorem generalized_right_double_positions :
    childHeights (HeightBalance.balR AVL.heightAnnotation 2 .nil 1 (doubleRightInput 0 1 0)) = (2, 1) ∧
    childHeights (HeightBalance.balR AVL.heightAnnotation 2 .nil 1 (doubleRightInput 0 0 1)) = (1, 2) ∧
    childHeights (HeightBalance.balR AVL.heightAnnotation 2 .nil 1 (doubleRightInput 0 1 1)) = (2, 2) ∧
    childHeights (HeightBalance.balR AVL.heightAnnotation 3 .nil 1 (doubleRightInput 0 2 0)) = (3, 1) ∧
    childHeights (HeightBalance.balR AVL.heightAnnotation 3 .nil 1 (doubleRightInput 0 0 2)) = (1, 3) ∧
    childHeights (HeightBalance.balR AVL.heightAnnotation 3 .nil 1 (doubleRightInput 0 2 2)) = (3, 3) ∧
    childHeights (HeightBalance.balR AVL.heightAnnotation 3 .nil 1 (doubleRightInput 1 0 2)) = (1, 3) :=
  ⟨generalized_right_double_children 2 0 1 0 0 (by decide) (by decide),
    generalized_right_double_children 2 0 0 1 0 (by decide) (by decide),
    generalized_right_double_children 2 0 1 1 0 (by decide) (by decide),
    generalized_right_double_children 3 0 2 0 0 (by decide) (by decide),
    generalized_right_double_children 3 0 0 2 0 (by decide) (by decide),
    generalized_right_double_children 3 0 2 2 0 (by decide) (by decide),
    generalized_right_double_children 3 1 0 2 0 (by decide) (by decide)⟩

theorem positive_short_double_height :
    (HeightBalance.balL AVL.heightAnnotation 2 (doubleLeftInput 2 1 3) 3 (perfect 2)).height = 5 :=
  HeightBalance.height_balL_double _ 2 (perfect 2) 1 5
    (AVL.node (perfect 1) 2 (perfect 3)) 3 (perfect 2)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem positive_short_double_children :
    childHeights (HeightBalance.balL AVL.heightAnnotation 2
      (doubleLeftInput 2 1 3) 3 (perfect 2)) = (3, 4) :=
  generalized_left_double_children 2 2 1 3 2 (by decide) (by decide)

theorem right_oriented_double_height :
    (HeightBalance.balR AVL.heightAnnotation 3 .nil 1 (doubleRightInput 1 0 2)).height = 4 :=
  HeightBalance.height_balR_double _ 3 .nil 1 (AVL.node .nil 2 (perfect 2)) 3 4 (perfect 1)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem positive_short_double_valid :
    HeightBalance.ValidD AVL.heightAnnotation 2
      (HeightBalance.balL AVL.heightAnnotation 2 (doubleLeftInput 2 1 3) 3 (perfect 2)) :=
  HeightBalance.validD_balL _ 2 _ 3 _ (by decide) (by decide) (by decide) (by decide) (by decide)

theorem right_oriented_double_valid :
    HeightBalance.ValidD AVL.heightAnnotation 3
      (HeightBalance.balR AVL.heightAnnotation 3 .nil 1 (doubleRightInput 1 0 2)) :=
  HeightBalance.validD_balR _ 3 _ 1 _ (by decide) (by decide) (by decide) (by decide) (by decide)

theorem middle_balance_is_needed :
    max (max 3 0 + 1) (max 3 2 + 1) = 4 ∧
    ¬ HeightBalance.ValidD AVL.heightAnnotation 2 (doubleLeftInput 3 0 3) ∧
    ¬ HeightBalance.ValidD AVL.heightAnnotation 2
      (HeightBalance.balL AVL.heightAnnotation 2 (doubleLeftInput 3 0 3) 3 (perfect 2)) := by
  rcases HeightBalance.double_rotation_height_bounds 2 3 0 3 2
      (by decide) (by decide) (by decide) (by decide) with ⟨_, _, _, _, _, _, _, hmax, _, _⟩
  exact ⟨hmax, by decide, by decide⟩

theorem bad_middle_still_has_height_law :
    (HeightBalance.balL AVL.heightAnnotation 2 (doubleLeftInput 3 0 3) 3 (perfect 2)).height = 5 :=
  HeightBalance.height_balL_double _ 2 (perfect 3) 1 5
    (AVL.node .nil 2 (perfect 3)) 3 (perfect 2)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem bad_middle_double_children :
    childHeights (HeightBalance.balL AVL.heightAnnotation 2
      (doubleLeftInput 3 0 3) 3 (perfect 2)) = (4, 4) :=
  generalized_left_double_children 2 3 0 3 2 (by decide) (by decide)

/-! R30–R35: cast order, negative tolerances, zero tolerance and raw fallback. -/
theorem full_natural_lower_bound (d hl hr : Nat) : hr - d ≤ hl ↔ hr ≤ hl + d :=
  HeightBalance.height_lower_bound_iff d hl hr

theorem truncated_lower_boundary : (0 : Nat) - 3 ≤ 0 ∧ (0 : Nat) ≤ 0 + 3 :=
  ⟨by decide, (HeightBalance.height_lower_bound_iff 3 0 0).mp (by decide)⟩

theorem cast_before_subtraction_matters :
    ¬ |(0 : Int) - (3 : Int)| ≤ 1 ∧
    |((0 - 3 : Nat) : Int)| ≤ 1 ∧
    |((3 - 0 : Nat) : Int)| = |(3 : Int) - (0 : Int)| := by decide

theorem signed_balance_transport (d hl hr : Nat) :
    |(hl : Int) - (hr : Int)| ≤ (d : Int) ↔ hl ≤ hr + d ∧ hr ≤ hl + d :=
  HeightBalance.height_balance_iff d hl hr

theorem positive_integer_tolerance_transport (D : Int) (hD : 1 ≤ D) (hl hr : Nat) :
    1 ≤ D.toNat ∧ (D.toNat : Int) = D ∧
      (|(hl : Int) - (hr : Int)| ≤ D ↔ hl ≤ hr + D.toNat ∧ hr ≤ hl + D.toNat) :=
  ⟨(HeightBalance.int_tolerance_toNat D hD).1,
    (HeightBalance.int_tolerance_toNat D hD).2,
    HeightBalance.height_balance_int_iff D hD hl hr⟩

theorem negative_tolerance_separator :
    ¬ |(0 : Int) - (0 : Int)| ≤ (-1 : Int) ∧
    (-1 : Int).toNat = 0 ∧ (0 : Nat) ≤ 0 + (-1 : Int).toNat ∧
    (0 : Nat) ≤ 0 + (-1 : Int).toNat := by decide

theorem zero_tolerance_branch :
    HeightBalance.balL AVL.heightAnnotation 0 (leaf 1) 2 .nil = AVL.node .nil 1 (leaf 2) :=
  HeightBalance.balL_single _ 0 .nil 1 1 .nil 2 .nil (by decide) (by decide)

theorem zero_tolerance_is_not_repair :
    HeightBalance.ValidD AVL.heightAnnotation 0 (leaf 1) ∧
    HeightBalance.ValidD AVL.heightAnnotation 0 (.nil : HTree) ∧
    HeightBalance.CacheValid AVL.heightAnnotation
      (HeightBalance.balL AVL.heightAnnotation 0 (leaf 1) 2 .nil) ∧
    ¬ HeightBalance.ValidD AVL.heightAnnotation 0
      (HeightBalance.balL AVL.heightAnnotation 0 (leaf 1) 2 .nil) :=
  ⟨by decide, HeightBalance.validD_nil _ 0,
    HeightBalance.cacheValid_balL _ 0 _ 2 .nil (by decide) (by decide), by decide⟩

theorem zero_tolerance_inorder :
    inorder (Cached.erase (HeightBalance.balL AVL.heightAnnotation 0 (leaf 1) 2 .nil)) = [1, 2] :=
  (HeightBalance.inorder_balL _ 0 _ 2 .nil).trans rfl

def falseActualFallback : HTree := .node (1, 2) (perfect 2) .nil

theorem actual_nontrigger_requires_cache :
    falseActualFallback.height ≠ (BinaryTree.nil : HTree).height + 2 ∧
    AVL.balL falseActualFallback 2 .nil = AVL.node (perfect 2) 1 (leaf 2) ∧
    (AVL.balL falseActualFallback 2 .nil).height = 3 ∧
    max falseActualFallback.height (BinaryTree.nil : HTree).height + 1 = 4 :=
  ⟨by decide, AVL.balL_single (perfect 2) 1 2 .nil 2 .nil (by decide) (by decide),
    by decide, by decide⟩

/-! A01: height and the actual optional-maximum algebra are recomputed together. -/
def maximumAnnotation : HeightBalance.HeightAnnotation Nat (Nat × Option Nat) where
  empty := (0, none)
  combine := fun l a r => (max l.1 r.1 + 1, MaximumCache.combine l.2 a r.2)
  height := Prod.fst
  height_empty := rfl
  height_combine := by intros; rfl

abbrev MTree := BinaryTree (Nat × (Nat × Option Nat))
def maximumLeaf (a : Nat) : MTree := HeightBalance.node maximumAnnotation .nil a .nil
def maximumLeft : MTree := HeightBalance.node maximumAnnotation (maximumLeaf 1) 2 .nil
def maximumRight : MTree := HeightBalance.node maximumAnnotation .nil 2 (maximumLeaf 9)
def maximumResult : MTree :=
  HeightBalance.node maximumAnnotation (maximumLeaf 1) 2 (maximumLeaf 9)
def staleMaximum : MTree := .node (2, (2, some 2)) (maximumLeaf 1) (maximumLeaf 9)

theorem maximum_left_branch :
    HeightBalance.balL maximumAnnotation 1 maximumLeft 9 .nil = maximumResult :=
  HeightBalance.balL_single _ 1 (maximumLeaf 1) 2 (2, some 2) .nil 9 .nil
    (by decide) (by decide)

theorem maximum_right_branch :
    HeightBalance.balR maximumAnnotation 1 .nil 1 maximumRight = maximumResult :=
  HeightBalance.balR_single _ 1 .nil 1 .nil 2 (2, some 9) (maximumLeaf 9)
    (by decide) (by decide)

theorem maximum_left_cache :
    HeightBalance.CacheValid maximumAnnotation
      (HeightBalance.balL maximumAnnotation 1 maximumLeft 9 .nil) :=
  HeightBalance.cacheValid_balL _ 1 _ 9 .nil (by decide) (by decide)

theorem maximum_right_cache :
    HeightBalance.CacheValid maximumAnnotation
      (HeightBalance.balR maximumAnnotation 1 .nil 1 maximumRight) :=
  HeightBalance.cacheValid_balR _ 1 .nil 1 _ (by decide) (by decide)

theorem maximum_both_valid :
    HeightBalance.ValidD maximumAnnotation 1
      (HeightBalance.balL maximumAnnotation 1 maximumLeft 9 .nil) ∧
    HeightBalance.ValidD maximumAnnotation 1
      (HeightBalance.balR maximumAnnotation 1 .nil 1 maximumRight) :=
  ⟨HeightBalance.validD_balL _ 1 _ 9 .nil
      (by decide) (by decide) (by decide) (by decide) (by decide),
    HeightBalance.validD_balR _ 1 .nil 1 _
      (by decide) (by decide) (by decide) (by decide) (by decide)⟩

theorem maximum_readers :
    Cached.read maximumAnnotation.empty
      (HeightBalance.balL maximumAnnotation 1 maximumLeft 9 .nil) = (2, some 9) ∧
    Cached.read maximumAnnotation.empty
      (HeightBalance.balR maximumAnnotation 1 .nil 1 maximumRight) = (2, some 9) := by
  rw [maximum_left_branch, maximum_right_branch]
  decide

theorem maximum_inorders :
    inorder (Cached.erase (HeightBalance.balL maximumAnnotation 1 maximumLeft 9 .nil)) = [1, 2, 9] ∧
    inorder (Cached.erase (HeightBalance.balR maximumAnnotation 1 .nil 1 maximumRight)) = [1, 2, 9] :=
  ⟨(HeightBalance.inorder_balL _ 1 _ 9 .nil).trans rfl,
    (HeightBalance.inorder_balR _ 1 .nil 1 _).trans rfl⟩

/-- This is an actual projection of the complete fold into the existing maximum fold. -/
theorem maximum_fold_fusion (t : BinaryTree Nat) :
    (Trees.fold maximumAnnotation.empty maximumAnnotation.combine t).2 = MaximumCache.summary t :=
  Trees.fold_fusion maximumAnnotation.empty maximumAnnotation.combine
    (none : Option Nat) MaximumCache.combine Prod.snd rfl (fun _ _ _ => rfl) t

theorem maximum_reader_eq_summary (t : MTree) (hc : HeightBalance.CacheValid maximumAnnotation t) :
    (Cached.read maximumAnnotation.empty t).2 = MaximumCache.summary (Cached.erase t) :=
  (congrArg Prod.snd (Cached.read_eq_fold maximumAnnotation.empty maximumAnnotation.combine t hc)).trans
    (maximum_fold_fusion (Cached.erase t))

theorem maximum_reader_eq_list_maximum (t : MTree)
    (hc : HeightBalance.CacheValid maximumAnnotation t) :
    (Cached.read maximumAnnotation.empty t).2 = (inorder (Cached.erase t)).max? :=
  (maximum_reader_eq_summary t hc).trans (MaximumCache.summary_eq_max?_inorder (Cached.erase t))

theorem maximum_reader_greatest (t : MTree) (hc : HeightBalance.CacheValid maximumAnnotation t)
    (m : Nat) :
    (Cached.read maximumAnnotation.empty t).2 = some m ↔
      m ∈ setTree (Cached.erase t) ∧ ∀ x ∈ setTree (Cached.erase t), x ≤ m := by
  rw [maximum_reader_eq_summary t hc, MaximumCache.summary_eq_some_iff]

theorem maximum_left_greatest :
    9 ∈ setTree (Cached.erase (HeightBalance.balL maximumAnnotation 1 maximumLeft 9 .nil)) ∧
    ∀ x ∈ setTree (Cached.erase (HeightBalance.balL maximumAnnotation 1 maximumLeft 9 .nil)), x ≤ 9 :=
  (maximum_reader_greatest _ maximum_left_cache 9).mp (congrArg Prod.snd maximum_readers.1)

theorem maximum_right_list_maximum :
    (inorder (Cached.erase (HeightBalance.balR maximumAnnotation 1 .nil 1 maximumRight))).max? = some 9 :=
  (maximum_reader_eq_list_maximum _ maximum_right_cache).symm.trans
    (congrArg Prod.snd maximum_readers.2)

theorem maximum_projected_height :
    HeightBalance.ht maximumAnnotation
      (HeightBalance.balR maximumAnnotation 1 .nil 1 maximumRight) =
      (HeightBalance.balR maximumAnnotation 1 .nil 1 maximumRight).height :=
  HeightBalance.ht_eq_height_of_cacheValid _ _ maximum_right_cache

theorem stale_maximum_height_tests_pass :
    Cached.erase staleMaximum = Cached.erase maximumResult ∧
    staleMaximum.height = 2 ∧ HeightBalance.ht maximumAnnotation staleMaximum = 2 ∧
    HeightBalance.ht maximumAnnotation staleMaximum = HeightBalance.ht maximumAnnotation maximumResult ∧
    inorder (Cached.erase staleMaximum) = [1, 2, 9] ∧
    HeightBalance.BalancedD 1 (Cached.erase staleMaximum) := by decide

theorem stale_maximum_cache_rejected : ¬ HeightBalance.CacheValid maximumAnnotation staleMaximum := by
  intro h
  have full := ((HeightBalance.cacheValid_node maximumAnnotation 2 (2, some 2)
    (maximumLeaf 1) (maximumLeaf 9)).mp h).2.2
  exact (by decide : (2, some 2) ≠ maximumAnnotation.combine
    (Cached.read maximumAnnotation.empty (maximumLeaf 1)) 2
    (Cached.read maximumAnnotation.empty (maximumLeaf 9))) full

theorem stale_maximum_full_validity_rejected : ¬ HeightBalance.ValidD maximumAnnotation 1 staleMaximum := by
  intro h
  have full := ((HeightBalance.validD_node_iff maximumAnnotation 1 2 (2, some 2)
    (maximumLeaf 1) (maximumLeaf 9)).mp h).2.2.2
  exact (by decide : (2, some 2) ≠ maximumAnnotation.combine
    (Cached.read maximumAnnotation.empty (maximumLeaf 1)) 2
    (Cached.read maximumAnnotation.empty (maximumLeaf 9))) full

/-! A02: the ordered word is not invariant under a plain annotation-preserving mirror. -/
def wordAnnotation (α : Type u) : HeightBalance.HeightAnnotation α (Nat × List α) where
  empty := (0, [])
  combine := fun l a r => (max l.1 r.1 + 1, l.2 ++ (a :: r.2))
  height := Prod.fst
  height_empty := rfl
  height_combine := by intros; rfl

abbrev WTree := BinaryTree (Nat × (Nat × List Nat))
def wordLeaf (a : Nat) : WTree := HeightBalance.node (wordAnnotation Nat) .nil a .nil
def wordLeft : WTree := HeightBalance.node (wordAnnotation Nat) (wordLeaf 1) 2 .nil
def wordRight : WTree := HeightBalance.node (wordAnnotation Nat) .nil 2 (wordLeaf 3)
def wordResult : WTree := HeightBalance.node (wordAnnotation Nat) (wordLeaf 1) 2 (wordLeaf 3)

theorem word_left_branch :
    HeightBalance.balL (wordAnnotation Nat) 1 wordLeft 3 .nil = wordResult :=
  HeightBalance.balL_single _ 1 (wordLeaf 1) 2 (2, [1, 2]) .nil 3 .nil (by decide) (by decide)

theorem word_right_branch :
    HeightBalance.balR (wordAnnotation Nat) 1 .nil 1 wordRight = wordResult :=
  HeightBalance.balR_single _ 1 .nil 1 .nil 2 (2, [2, 3]) (wordLeaf 3) (by decide) (by decide)

theorem word_right_cache :
    HeightBalance.CacheValid (wordAnnotation Nat)
      (HeightBalance.balR (wordAnnotation Nat) 1 .nil 1 wordRight) :=
  HeightBalance.cacheValid_balR _ 1 .nil 1 _ (by decide) (by decide)

theorem word_right_valid :
    HeightBalance.ValidD (wordAnnotation Nat) 1
      (HeightBalance.balR (wordAnnotation Nat) 1 .nil 1 wordRight) :=
  HeightBalance.validD_balR _ 1 .nil 1 _ (by decide) (by decide) (by decide) (by decide) (by decide)

theorem word_right_inorder :
    inorder (Cached.erase (HeightBalance.balR (wordAnnotation Nat) 1 .nil 1 wordRight)) = [1, 2, 3] :=
  (HeightBalance.inorder_balR _ 1 .nil 1 _).trans rfl

theorem word_right_reader :
    Cached.read (wordAnnotation Nat).empty
      (HeightBalance.balR (wordAnnotation Nat) 1 .nil 1 wordRight) = (2, [1, 2, 3]) := by
  rw [word_right_branch]
  decide

theorem word_fold_fusion (t : BinaryTree α) :
    (Trees.fold (wordAnnotation α).empty (wordAnnotation α).combine t).2 = inorder t :=
  Trees.fold_fusion (wordAnnotation α).empty (wordAnnotation α).combine
    ([] : List α) (fun l a r => l ++ (a :: r)) Prod.snd rfl (fun _ _ _ => rfl) t

theorem word_reader_eq_inorder (t : BinaryTree (α × (Nat × List α)))
    (hc : HeightBalance.CacheValid (wordAnnotation α) t) :
    (Cached.read (wordAnnotation α).empty t).2 = inorder (Cached.erase t) :=
  (congrArg Prod.snd (Cached.read_eq_fold (wordAnnotation α).empty
    (wordAnnotation α).combine t hc)).trans (word_fold_fusion (Cached.erase t))

theorem word_right_semantic_bridge :
    (Cached.read (wordAnnotation Nat).empty
      (HeightBalance.balR (wordAnnotation Nat) 1 .nil 1 wordRight)).2 =
      inorder (Cached.erase (HeightBalance.balR (wordAnnotation Nat) 1 .nil 1 wordRight)) :=
  word_reader_eq_inorder _ word_right_cache

/-- Exchange children while retaining each label, including its entire old cache. -/
def plainMirror : BinaryTree α → BinaryTree α
  | .nil => .nil
  | .node a l r => .node a (plainMirror r) (plainMirror l)

def recomputedWordMirror : WTree := Cached.annotate (wordAnnotation Nat).empty
  (wordAnnotation Nat).combine (plainMirror (Cached.erase wordResult))

theorem plain_mirror_keeps_the_wrong_word :
    Cached.read (wordAnnotation Nat).empty (plainMirror wordResult) = (2, [1, 2, 3]) ∧
    inorder (Cached.erase (plainMirror wordResult)) = [3, 2, 1] ∧
    HeightBalance.ht (wordAnnotation Nat) (plainMirror wordResult) = (plainMirror wordResult).height ∧
    HeightBalance.BalancedD 1 (Cached.erase (plainMirror wordResult)) ∧
    ¬ HeightBalance.CacheValid (wordAnnotation Nat) (plainMirror wordResult) := by decide

theorem recomputed_mirror_cache :
    HeightBalance.CacheValid (wordAnnotation Nat) recomputedWordMirror :=
  Cached.annotate_valid (wordAnnotation Nat).empty (wordAnnotation Nat).combine _

theorem recomputed_mirror_observations :
    Cached.erase recomputedWordMirror = Cached.erase (plainMirror wordResult) ∧
    Cached.read (wordAnnotation Nat).empty recomputedWordMirror = (2, [3, 2, 1]) ∧
    recomputedWordMirror ≠ plainMirror wordResult := by
  refine ⟨?_, by decide, by decide⟩
  exact Cached.erase_annotate (wordAnnotation Nat).empty (wordAnnotation Nat).combine _

def mirroredLeftAsRight : WTree :=
  plainMirror (HeightBalance.balL (wordAnnotation Nat) 1 (plainMirror wordRight) 1 .nil)

theorem mirror_derived_right_is_wrong :
    Cached.erase mirroredLeftAsRight =
      Cached.erase (HeightBalance.balR (wordAnnotation Nat) 1 .nil 1 wordRight) ∧
    Cached.read (wordAnnotation Nat).empty mirroredLeftAsRight = (2, [3, 2, 1]) ∧
    ¬ HeightBalance.CacheValid (wordAnnotation Nat) mirroredLeftAsRight ∧
    mirroredLeftAsRight ≠ HeightBalance.balR (wordAnnotation Nat) 1 .nil 1 wordRight := by
  rw [word_right_branch]
  decide

/-! E01: an empty payload type has an empty cached tree, without a pivot or default. -/
theorem empty_payload_word_laws (d : Nat) :
    Cached.read (wordAnnotation PEmpty.{u + 1}).empty
      (.nil : BinaryTree (PEmpty.{u + 1} × (Nat × List PEmpty.{u + 1}))) = (0, []) ∧
    HeightBalance.CacheValid (wordAnnotation PEmpty.{u + 1}) .nil ∧
    HeightBalance.ValidD (wordAnnotation PEmpty.{u + 1}) d .nil :=
  ⟨rfl, HeightBalance.cacheValid_nil _, HeightBalance.validD_nil _ d⟩

theorem empty_payload_independent_universes
    (ann : HeightBalance.HeightAnnotation PEmpty.{u + 1} σ) (d : Nat) :
    HeightBalance.ht ann .nil = 0 ∧ HeightBalance.ValidD ann d .nil :=
  ⟨HeightBalance.ht_nil ann, HeightBalance.validD_nil ann d⟩

end Examples.HeightRebalance
