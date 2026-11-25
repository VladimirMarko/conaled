import Applications.Search.OrderedMap.DecodedKeysModels
import Applications.Search.RedBlack.Models
import Applications.Search.RedBlack.Depth

/-!
# A shared chronological tree history

The same writes retain a negative key, a repeated key, and the latest payload.
The ordinary source tree provides the comparison state for the balanced source
tree. These are mathematical observations of the actual operations.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RedBlackHistory

open Search.OrderedMap
open Representations.SignedComparison

universe u v w z

/-- The accepted model contract carries one history across different valid carriers. -/
theorem model_histories_agree {κ : Type u} {ν : Type v} {T : Type w} {U : Type z}
    [DecidableEq κ]
    {a : Search.TotalTable.Ops κ ν T} {b : Search.TotalTable.Ops κ ν U}
    {oa : EnumeratedTable.Observations κ ν T} {ob : EnumeratedTable.Observations κ ν U}
    {da db : ν} {P : T → Prop} {Q : U → Prop}
    {ma : T → Meaning κ ν} {mb : U → Meaning κ ν}
    (ha : EnumeratedTable.ModelLaws a oa da P ma)
    (hb : EnumeratedTable.ModelLaws b ob db Q mb)
    (bindings : List (κ × ν)) {t : T} {s : U} (ht : P t) (hs : Q s)
    (same : ma t = mb s) :
    ma (Search.TotalTable.setAll a bindings t) =
      mb (Search.TotalTable.setAll b bindings s) := by
  rw [ha.setAll bindings ht, hb.setAll bindings hs, same]

def writes : List (Int × Nat) := [(3, 303), (1, 101), (3, 333), (-2, 202)]

def ordinary : BinaryTree (Int × Nat) :=
  bindAll (DecodedKeys.ops intLtb) writes .nil

theorem ordinary_shape :
    ordinary = .node (3, 333) (.node (1, 101) (.node (-2, 202) .nil .nil) .nil) .nil := rfl

theorem ordinary_height : ordinary.height = 3 := rfl

theorem ordinary_size : ordinary.numNodes = 3 := rfl

theorem ordinary_queries :
    ([-2, 1, 2, 3] : List Int).map (fun q => DecodedKeys.lookup? intLtb q ordinary) =
      [some 202, some 101, none, some 333] := rfl

/-- The existing chronological client preserves validity for any signed history. -/
theorem ordinary_history_valid {ν : Type u} (default : ν) (bindings : List (Int × ν)) :
    DecodedKeys.BST id (bindAll (DecodedKeys.ops intLtb) bindings .nil) := by
  let _ : LinearOrder Int := linearOrderOfStrict id intLtb int_decode_injective intLtb_true_iff
  let _ : DecidableEq Int :=
    (linearOrderOfStrict id intLtb int_decode_injective intLtb_true_iff).toDecidableEq
  have law := DecodedKeys.model_enum_laws id intLtb int_decode_injective intLtb_true_iff default
  have valid := law.totalTable_laws.setAll_valid bindings law.empty_valid
  change DecodedKeys.BST id
    (Search.TotalTable.setAll (Search.TotalTable.ofPartial (DecodedKeys.ops intLtb) default)
      bindings .nil) at valid
  rw [Search.TotalTable.setAll_ofPartial] at valid
  exact valid

theorem ordinary_valid : DecodedKeys.BST id ordinary :=
  ordinary_history_valid 0 writes

/-- Chronological source insertion preserves ordering without a color premise. -/
theorem balanced_history_valid {κ : Type u} {ν : Type v}
    (decode : κ → Int) (ltb : κ → κ → Bool)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
    (bindings : List (κ × ν)) {t : Search.RedBlack.Tree κ ν}
    (valid : Search.RedBlack.BST decode t) :
    Search.RedBlack.BST decode (bindAll (Search.RedBlack.ops ltb) bindings t) := by
  induction bindings generalizing t with
  | nil => exact valid
  | cons binding rest ih =>
      exact ih (Search.RedBlack.insert_bst decode ltb hlt valid binding.1 binding.2)

/-- The same executor preserves a black-root shape for arbitrary Boolean tests. -/
theorem balanced_history_shape {κ : Type u} {ν : Type v} (ltb : κ → κ → Bool)
    (bindings : List (κ × ν)) {t : Search.RedBlack.Tree κ ν}
    (shape : ∃ n, Search.RedBlack.RB t .red n) :
    ∃ n, Search.RedBlack.RB (bindAll (Search.RedBlack.ops ltb) bindings t) .red n := by
  induction bindings generalizing t with
  | nil => exact shape
  | cons binding rest ih =>
      obtain ⟨n, shape⟩ := shape
      exact ih (Search.RedBlack.insert_RB ltb binding.1 binding.2 shape)

/-- Both actual realizations implement the same arbitrary chronological history. -/
theorem histories_meaning_agree {κ : Type u} {ν : Type v}
    (decode : κ → Int) (ltb : κ → κ → Bool) (hinj : Function.Injective decode)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
    (default : ν) (bindings : List (κ × ν)) :
    Search.RedBlack.enumAbs decode ltb hinj hlt
        (bindAll (Search.RedBlack.ops ltb) bindings .nil) =
      DecodedKeys.enumAbs decode ltb hinj hlt
        (bindAll (DecodedKeys.ops ltb) bindings .nil) := by
  let _ : LinearOrder κ := linearOrderOfStrict decode ltb hinj hlt
  let _ : DecidableEq κ := (linearOrderOfStrict decode ltb hinj hlt).toDecidableEq
  have colored := Search.RedBlack.model_enum_laws decode ltb hinj hlt default
  have uncolored := DecodedKeys.model_enum_laws decode ltb hinj hlt default
  have same := model_histories_agree colored uncolored bindings
    colored.empty_valid uncolored.empty_valid (by rfl)
  change Search.RedBlack.enumAbs decode ltb hinj hlt
      (Search.TotalTable.setAll (Search.TotalTable.ofPartial (Search.RedBlack.ops ltb) default)
        bindings .nil) =
    DecodedKeys.enumAbs decode ltb hinj hlt
      (Search.TotalTable.setAll (Search.TotalTable.ofPartial (DecodedKeys.ops ltb) default)
        bindings .nil) at same
  simpa only [Search.TotalTable.setAll_ofPartial] using same

/-- Optional observations agree for every signed history, including missing queries. -/
theorem signed_histories_lookup_agree {ν : Type u} (default : ν)
    (bindings : List (Int × ν)) (query : Int) :
    Search.RedBlack.lookup? intLtb query
        (bindAll (Search.RedBlack.ops intLtb) bindings .nil) =
      DecodedKeys.lookup? intLtb query
        (bindAll (DecodedKeys.ops intLtb) bindings .nil) := by
  have same := congrFun
    (histories_meaning_agree id intLtb int_decode_injective intLtb_true_iff default bindings) query
  rw [Search.RedBlack.enumAbs_lookup id intLtb int_decode_injective intLtb_true_iff
      (balanced_history_valid id intLtb intLtb_true_iff bindings (Search.RedBlack.bst_nil id)),
    DecodedKeys.enumAbs_lookup id intLtb int_decode_injective intLtb_true_iff
      (ordinary_history_valid default bindings)] at same
  exact same

/-- The existing client executes the exact source operations on the same writes. -/
def balanced : Search.RedBlack.Tree Int Nat :=
  bindAll (Search.RedBlack.ops intLtb) writes .nil

theorem balanced_valid : Search.RedBlack.BST id balanced :=
  balanced_history_valid id intLtb intLtb_true_iff writes (Search.RedBlack.bst_nil id)

theorem history_meaning_agrees :
    Search.RedBlack.enumAbs id intLtb int_decode_injective intLtb_true_iff balanced =
      DecodedKeys.enumAbs id intLtb int_decode_injective intLtb_true_iff ordinary :=
  histories_meaning_agree id intLtb int_decode_injective intLtb_true_iff 0 writes

theorem balanced_shape :
    balanced = .node .black (.node .black .nil (-2, 202) .nil) (1, 101)
      (.node .black .nil (3, 333) .nil) := rfl

theorem balanced_height : balanced.depth = 2 := rfl

theorem balanced_size : balanced.size = 3 := rfl

theorem balanced_queries :
    ([-2, 1, 2, 3] : List Int).map (fun q => Search.RedBlack.lookup? intLtb q balanced) =
      [some 202, some 101, none, some 333] := rfl

theorem balanced_elements :
    Search.RedBlack.elements balanced = [(-2, 202), (1, 101), (3, 333)] := rfl

theorem history_elements_agree : Search.RedBlack.elements balanced = DecodedKeys.elements ordinary := rfl

/-- Rotation preserves bindings but changes the represented tree. -/
theorem history_shapes_differ : Search.RedBlack.eraseColors balanced ≠ ordinary := by
  intro same
  have sameHeight := congrArg BinaryTree.height same
  change 2 = 3 at sameHeight
  cases sameHeight

/-- This concrete history consumes the exact parent-color constructor laws. -/
theorem balanced_rb : Search.RedBlack.RB balanced .red 2 := by
  rw [balanced_shape]
  exact Search.RedBlack.RB.black .red 1 101
    (Search.RedBlack.RB.black .black (-2) 202
      (Search.RedBlack.RB.nil .black) (Search.RedBlack.RB.nil .black))
    (Search.RedBlack.RB.black .black 3 333
      (Search.RedBlack.RB.nil .black) (Search.RedBlack.RB.nil .black))

theorem balanced_mindepth : Search.RedBlack.mindepth balanced = 2 := rfl

theorem balanced_source_bound :
    Search.RedBlack.height balanced ≤ 2 * Search.RedBlack.mindepth balanced + 1 :=
  Search.RedBlack.redblack_balanced balanced_rb

theorem balanced_log_bound :
    Search.RedBlack.height balanced ≤ 2 * (balanced.size + 1).log2 :=
  balanced_rb.height_log_bound

theorem history_height_advantage : Search.RedBlack.height balanced < ordinary.height := by
  change 2 < 3
  decide

def storesDefault : Search.RedBlack.Tree Int Nat :=
  Search.RedBlack.insert intLtb 3 0 balanced

/-- Default-valued answers agree while the optional observations distinguish presence. -/
theorem stored_default_and_absence :
    Search.RedBlack.lookup? intLtb 3 storesDefault = some 0 ∧
      Search.RedBlack.lookup? intLtb 2 storesDefault = none ∧
      Search.RedBlack.lookup intLtb 0 3 storesDefault = 0 ∧
      Search.RedBlack.lookup intLtb 0 2 storesDefault = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

end Examples.RedBlackHistory
