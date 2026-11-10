import Examples.FiniteListInterfaces
import Applications.Sequences.SuffixTrim
import Applications.Sequences.RunCompression
import Applications.Resources.TreeFlattening.Core
import Applications.Resources.GuardedBuild

/-! Function-level finite-list derivations feed an actual forest traversal and
independently specified run compression. Suffix trimming supplies a second
sequence consumer. These connections preserve values and order. The measured
guarded-compression stage counts its predicate tests and inserted cons cells;
forest traversal, filtering, mapping and certificate checking are outside that
stage's work count. No physical allocation or runtime claim is made.
See `docs/research/adwh-finite-lists.md`. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.ListPipelines

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

theorem filter_concat (p : α → Bool) :
    List.filter p ∘ List.flatten = List.flatten ∘ List.map (List.filter p) := by
  funext blocks
  exact List.filter_flatten

theorem map_concat (f : α → β) :
    List.map f ∘ List.flatten = List.flatten ∘ List.map (List.map f) := by
  funext blocks
  exact List.map_flatten

theorem map_fusion (f : β → γ) (g : α → β) :
    List.map f ∘ List.map g = List.map (f ∘ g) := by
  funext xs
  exact List.map_map

theorem concatMap_definition (f : α → List β) :
    List.flatten ∘ List.map f = List.flatMap f := rfl

/-- Preserve the intermediate equalities of the source point-free calculation. -/
theorem map_filter_concat_derivation (f : α → β) (p : α → Bool) :
    List.map f ∘ (List.filter p ∘ List.flatten) =
      List.flatMap (List.map f ∘ List.filter p) := by
  calc
    List.map f ∘ (List.filter p ∘ List.flatten) =
        List.map f ∘ (List.flatten ∘ List.map (List.filter p)) := by
          rw [filter_concat]
    _ = List.flatten ∘ (List.map (List.map f) ∘ List.map (List.filter p)) := by
          exact congrArg (fun k => k ∘ List.map (List.filter p)) (map_concat f)
    _ = List.flatten ∘ List.map (List.map f ∘ List.filter p) := by
          rw [map_fusion]
    _ = List.flatMap (List.map f ∘ List.filter p) := concatMap_definition _

/-- Derive nested folding through the existing master fusion rule. The step
need not be associative, and its accumulator type can differ from the element. -/
theorem foldr_concat_from_master (f : α → β → β) (e : β) :
    List.foldr f e ∘ List.flatten =
      List.foldr (fun xs y => xs.foldr f y) e := by
  funext blocks
  have fusion := SquareKit.ListFusion.foldr_reachable
    (fun xs ys : List α => xs ++ ys) (fun xs y => xs.foldr f y)
    (List.foldr f e) (fun _ => True) [] trivial (fun _ _ _ => trivial)
    (fun _ _ _ => List.foldr_append) blocks
  have append_fold : blocks.foldr (fun xs ys : List α => xs ++ ys) [] = blocks.flatten := by
    simpa only [id_eq, List.map_id, List.append_nil] using
      (List.foldr_append_eq_append (l := blocks) (f := id) (l' := []))
  simpa only [Function.comp_apply, append_fold, List.foldr_nil] using fusion

/-- Distribute the actual ordered forest output into per-tree transformations. -/
theorem forest_distribution (p : α → Bool) (f : α → β)
    (trees : List (Bracketing.Tree α)) :
    ((Resources.TreeFlattening.fromTs trees).filter p).map f =
      trees.flatMap (fun t => ((Bracketing.fringeSpec t).filter p).map f) := by
  rw [Resources.TreeFlattening.fromTs_refinement]
  have derivation := congrFun (map_filter_concat_derivation f p)
    (trees.map Bracketing.fringeSpec)
  simpa only [Function.comp_def, List.flatMap_def, List.map_map] using derivation

/-- A certificate for the distributed sequence reaches the source-style
equality build after the actual forest producer. -/
theorem compressed_forest [BEq β] [LawfulBEq β]
    (p : α → Bool) (f : α → β) (trees : List (Bracketing.Tree α)) (out : List β)
    (certificate : Applications.Sequences.RunCompression.Spec
      (trees.flatMap (fun t => ((Bracketing.fringeSpec t).filter p).map f)) out) :
    Applications.Sequences.RunCompression.build
      (((Resources.TreeFlattening.fromTs trees).filter p).map f) = out := by
  rw [forest_distribution]
  exact (Applications.Sequences.RunCompression.build_equality_iff _ _).mpr certificate

private def forest : List (Bracketing.Tree Nat) :=
  [.fork (.leaf 1) (.leaf 0), .leaf 1, .fork (.leaf 2) (.leaf 1)]

private def nonzero (n : Nat) : Bool := n != 0

theorem forest_intermediate :
    ((Resources.TreeFlattening.fromTs forest).filter nonzero).map Nat.succ =
      [2, 2, 3, 2] := by
  rw [forest_distribution]
  rfl

theorem forest_certificate :
    Applications.Sequences.RunCompression.Spec ([2, 2, 3, 2] : List Nat) [2, 3, 2] :=
  .repeated (.boundary (by decide) (.boundary (by decide) (.single 2)))

theorem forest_result :
    Applications.Sequences.RunCompression.build
      (((Resources.TreeFlattening.fromTs forest).filter nonzero).map Nat.succ) =
      [2, 3, 2] := by
  apply compressed_forest
  exact forest_certificate

theorem empty_forest_result :
    Applications.Sequences.RunCompression.build
      (List.map Nat.succ
        ((Resources.TreeFlattening.fromTs ([] : List (Bracketing.Tree Nat))).filter nonzero)) = [] :=
  compressed_forest nonzero Nat.succ [] [] .nil

/-- The accumulator is an ordered word, not a commutative numeric summary. -/
theorem nested_word_fold :
    List.foldr (· :: ·) ["tail"]
      (([["red", "blue"], [], ["red"]] : List (List String)).flatten) =
      ["red", "blue", "red", "tail"] := by
  have standard := congrFun (foldr_concat_from_master (fun x ys => x :: ys) ["tail"])
    ([["red", "blue"], [], ["red"]] : List (List String))
  exact standard.trans rfl

/-- Retain the source scan fixture through the existing suffix-values law. -/
theorem source_suffix_sums :
    ([1, 2, 3] : List Nat).scanr (· + ·) 0 = [6, 5, 3, 0] := by
  rw [SquareKit.ListFusion.scanr_suffix_values]
  rfl

open Applications.Sequences.SuffixTrim

theorem even_suffix :
    trim (fun n : Nat => n % 2 == 0) [1, 4, 3, 6, 2, 4] = [1, 4, 3] := by
  rw [trim_eq_reverse_dropWhile]
  rfl

theorem even_suffix_spec :
    Spec (fun n : Nat => n % 2 == 0) [1, 4, 3, 6, 2, 4] [1, 4, 3] :=
  (trim_iff _ _ _).mp even_suffix

theorem trim_boundaries :
    trim (fun _ : Nat => true) [] = [] ∧
      trim (fun _ : Nat => true) [2, 4] = [] ∧
      trim (fun _ : Nat => false) [1, 2] = [1, 2] := by
  simp only [trim_eq_reverse_dropWhile]
  decide

/-- Removing an all-matching padding suffix before compression does not change
the consumer's result. The input may still contain matching internal entries. -/
theorem trim_compress_padding [BEq α] (p : α → Bool) (xs padding : List α)
    (all : ∀ x ∈ padding, p x = true) :
    Applications.Sequences.RunCompression.build (trim p (xs ++ padding)) =
      Applications.Sequences.RunCompression.build (trim p xs) := by
  rw [trim_append_all p xs padding all]

theorem padded_runs :
    Applications.Sequences.RunCompression.build
      (trim (fun n : Nat => n == 0) ([1, 1, 2, 1] ++ [0, 0, 0])) = [1, 2, 1] := by
  rw [trim_compress_padding _ _ _ (by simp)]
  have retained : trim (fun n : Nat => n == 0) [1, 1, 2, 1] = [1, 1, 2, 1] := by
    rw [trim_eq_reverse_dropWhile]
    rfl
  rw [retained]
  exact (Applications.Sequences.RunCompression.build_equality_iff _ _).mpr
    (.repeated (.boundary (by decide) (.boundary (by decide) (.single 1))))

universe uGuardedForest vGuardedForest

/-- A certificate for the distributed output determines the measured equality
builder's value after the actual ordered forest producer. -/
theorem measured_compressed_forest
    {α : Type uGuardedForest} {β : Type vGuardedForest} [BEq β] [LawfulBEq β]
    (p : α → Bool) (f : α → β) (trees : List (Bracketing.Tree α)) (out : List β)
    (certificate : Applications.Sequences.RunCompression.Spec
      (trees.flatMap (fun t => ((Bracketing.fringeSpec t).filter p).map f)) out) :
    (Resources.GuardedBuild.buildRun (· == ·)
      (((Resources.TreeFlattening.fromTs trees).filter p).map f)).1 = out := by
  rw [forest_distribution]
  exact Resources.GuardedBuild.buildRun_equality_of_spec certificate

/-- Only compression predicate tests and inserted cons cells are counted.
Traversal, filter, map and certificate checking are outside this stage's model.
This work bound does not require that Boolean equality be lawful. -/
theorem measured_forest_work_le
    {α : Type uGuardedForest} {β : Type vGuardedForest} [BEq β]
    (p : α → Bool) (f : α → β) (trees : List (Bracketing.Tree α)) :
    (Resources.GuardedBuild.buildRun (· == ·)
      (((Resources.TreeFlattening.fromTs trees).filter p).map f)).2 ≤
      3 * (((Resources.TreeFlattening.fromTs trees).filter p).map f).length :=
  Resources.GuardedBuild.buildRun_work_le (· == ·) _

theorem measured_forest_value :
    (Resources.GuardedBuild.buildRun (fun x y : Nat => x == y)
      (((Resources.TreeFlattening.fromTs forest).filter nonzero).map Nat.succ)).1 =
      [2, 3, 2] := by
  apply measured_compressed_forest
  rw [← forest_distribution nonzero Nat.succ forest, forest_intermediate]
  exact forest_certificate

/-- Specialize the universal bound to the actual four-entry producer output. -/
theorem measured_forest_work_le_twelve :
    (Resources.GuardedBuild.buildRun (fun x y : Nat => x == y)
      (((Resources.TreeFlattening.fromTs forest).filter nonzero).map Nat.succ)).2 ≤
      12 := by
  calc
    (Resources.GuardedBuild.buildRun (fun x y : Nat => x == y)
      (((Resources.TreeFlattening.fromTs forest).filter nonzero).map Nat.succ)).2 ≤
        3 * (((Resources.TreeFlattening.fromTs forest).filter nonzero).map Nat.succ).length :=
      measured_forest_work_le nonzero Nat.succ forest
    _ = 12 := by
      rw [forest_intermediate]
      decide

/-- Suffix-first insertion charges are 1,2,2,3. The first projection uses the
independent existing certificate; the second is the actual shared run's work. -/
theorem measured_forest_pair :
    Resources.GuardedBuild.buildRun (fun x y : Nat => x == y)
      (((Resources.TreeFlattening.fromTs forest).filter nonzero).map Nat.succ) =
      ([2, 3, 2], 8) := by
  apply Prod.ext
  · exact measured_forest_value
  · calc
      (Resources.GuardedBuild.buildRun (fun x y : Nat => x == y)
        (((Resources.TreeFlattening.fromTs forest).filter nonzero).map Nat.succ)).2 =
          (Resources.GuardedBuild.buildRun (fun x y : Nat => x == y)
            [2, 2, 3, 2]).2 := by rw [forest_intermediate]
      _ = (Resources.run (Resources.GuardedBuild.insertRun (fun x y : Nat => x == y))
          [2, 3, 2, 2] []).2 :=
        congrArg Prod.snd
          (Resources.GuardedBuild.buildRun_eq_run_reverse
            (fun x y : Nat => x == y) [2, 2, 3, 2])
      _ = 8 := rfl

end Examples.ListPipelines
