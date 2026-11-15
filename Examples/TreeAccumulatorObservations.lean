import Examples.TreeAccumulator

/-! Two entry tariffs on one invocation and a right-before-left ordered
diagnostic, using existing projection homs and the existing FreeMonoid decoder.
Source and statement assessment:
`docs/research/fdsa-tree-accumulator-invocation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace TreeAccumulatorObservationExamples
open Resources Resources.TreeAccumulator
open TreeFoldObservationExamples (Trace words)
universe u
variable {α : Type u}

/-- Both components observe the same invocation; they are not separate phases. -/
theorem invoke_pair (entry₁ entry₂ : Nat) (t : BinaryTree α) (suffix : List α) :
    (invoke (entry₁, entry₂) t suffix).2 =
      (entry₁ * (2 * t.numNodes + 1), entry₂ * (2 * t.numNodes + 1)) := by
  apply Prod.ext
  · calc
      (invoke (entry₁, entry₂) t suffix).2.1 = (invoke entry₁ t suffix).2 :=
        congrArg Prod.snd
          (reweight_invoke (AddMonoidHom.fst Nat Nat) (entry₁, entry₂) t suffix)
      _ = entry₁ * (2 * t.numNodes + 1) := invoke_cost entry₁ t suffix
  · calc
      (invoke (entry₁, entry₂) t suffix).2.2 = (invoke entry₂ t suffix).2 :=
        congrArg Prod.snd
          (reweight_invoke (AddMonoidHom.snd Nat Nat) (entry₁, entry₂) t suffix)
      _ = entry₂ * (2 * t.numNodes + 1) := invoke_cost entry₂ t suffix

theorem pair_sample :
    invoke ((1, 2) : Nat × Nat) TreeCacheExamples.sample [9, 8] =
      ([0, 1, 2, 3, 9, 8], (9, 18)) := by
  apply Prod.ext
  · rw [invoke_value, TreeCacheExamples.sample_inorder]
    rfl
  · rw [invoke_pair, TreeCacheExamples.sample_size]

/-- The same invocation algebra records a post-body node token; nil is silent.
The ordinary fold returns measured functions, not a separate trace evaluator. -/
def traceInvoke (t : BinaryTree Nat) : List Nat → Measured (List Nat) Trace :=
  Trees.fold (fun suffix => (suffix, 0))
    (fun left a right => nodeRun (Additive.ofMul (FreeMonoid.of a)) left a right) t

theorem trace_nil (suffix : List Nat) : traceInvoke .nil suffix = (suffix, 0) := rfl

theorem trace_node (a : Nat) (l r : BinaryTree Nat) (suffix : List Nat) :
    traceInvoke (.node a l r) suffix =
      nodeRun (Additive.ofMul (FreeMonoid.of a))
        (traceInvoke l) a (traceInvoke r) suffix := rfl

theorem trace_value (t : BinaryTree Nat) (suffix : List Nat) :
    (traceInvoke t suffix).1 = Trees.inorder t ++ suffix := by
  induction t generalizing suffix with
  | nil => simp only [trace_nil, Trees.inorder_nil, List.nil_append]
  | node a l r ihl ihr =>
      rw [trace_node, nodeRun_value, ihr, ihl, Trees.inorder_node]
      simp only [List.append_assoc, List.cons_append]

/-- All suffixes produce the same post-body node-event word on this tree. -/
theorem trace_sample_word (suffix : List Nat) :
    words (traceInvoke TreeCacheExamples.sample suffix).2 = [2, 3, 0, 1] := by
  simp only [TreeCacheExamples.sample, trace_node, nodeRun_cost, trace_nil,
    words, toMul_add, toMul_ofMul, toMul_zero,
    FreeMonoid.toList_mul, FreeMonoid.toList_of, FreeMonoid.toList_one,
    List.nil_append, List.append_nil, List.cons_append]

theorem trace_sample (suffix : List Nat) :
    (traceInvoke TreeCacheExamples.sample suffix).1 = [0, 1, 2, 3] ++ suffix ∧
      words (traceInvoke TreeCacheExamples.sample suffix).2 = [2, 3, 0, 1] := by
  constructor
  · rw [trace_value, TreeCacheExamples.sample_inorder]
  · exact trace_sample_word suffix

/-- This comparison concerns words. The earlier callback returns a size
summary, while this invocation returns the inorder list with its suffix. -/
theorem invocation_order_differs (suffix : List Nat) :
    words (traceInvoke TreeCacheExamples.sample suffix).2 ≠
      words (TreeFold.run (0 : Trace) 0 TreeFoldObservationExamples.traceStep
        TreeCacheExamples.sample).2 := by
  rw [trace_sample_word, TreeFoldObservationExamples.trace_sample.2]
  decide

end TreeAccumulatorObservationExamples
