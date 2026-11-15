# Reconstruction source statement assessment

Candidate `d02419738a9e16963727b25acf2e18f374dd16de`. Both modules are UNCOMPILED. This author assessment is inside the existing whole-Chapter4 implementation/review loop; it is neither an independent review outcome nor compiler evidence. Complete authored inventory: 10 core declarations and 22 example declarations, pinned in `reconstruction-public-headers.json`.

## Algorithms, assumptions and failure semantics

`reconstruct?` consumes ordinary `List α` traversals and returns `Option (BinaryTree α)`. The only typeclass assumption is executable label comparison, `[DecidableEq α]`; no label default or order is used. Its empty/empty and empty/nonempty branches are explicit. `reconstruct?_cons` preserves the frozen first-occurrence `idxOf` split and propagates either child failure. The membership guard supplies the stated absent-root failure equation `reconstruct?_cons_of_not_mem`. Both recursive preorder slices are at most the parent tail length; the supplied length proof is intended to establish termination on arbitrary inputs, not only well-formed traversals.

`reconstruct` takes `getD .nil`, so malformed cases have a total explicit fallback without `Inhabited α`. `reconstruct_nil_nil` and `reconstruct_of_none` connect the wrapper to the Option behavior. These branches do not assert that every duplicate-label interpretation will be searched or that rejection characterizes malformed inputs in full generality. No unproved runtime or successful-parse soundness claim is made.

## Correctness statements and proof structure

`reconstruct?_traversals` universally quantifies over finite `BinaryTree α` with exactly the source hypothesis `(preorder t).Nodup`; its conclusion returns `some t`, rather than merely a matching size, shape class or multiset. The proof extracts child-preorder Nodup and absence of the root from the preorder tail. The inherited independent set-membership bridges transfer that absence to the left inorder. Thus the first inorder root index is the LEFT subtree's inorder length. Inorder/preorder length laws then justify the preorder split. The two induction hypotheses apply to the actual left and right trees; the proof does not posit correct parsing as an extra premise.

`reconstruct_traversals` exposes the book's exact tree equality at the public total function, using the Option theorem. The premise is satisfiable, and the examples establish it explicitly. It is deliberately retained: duplicate-label ambiguity is shown separately, not hidden in an extra structural hypothesis.

## Cases and public-law connections

The sample has independently fixed preorder `[9,3,5,7,6]` and inorder `[3,5,9,6,7]`, with asymmetric left/right subtrees. `sample_preorder_nodup` proves the required condition; `sample_reconstruct?` and `sample_reconstruct` consume their general laws using these observations. The generic singleton consumes the same all-tree theorem. Empty lists over `Empty` demonstrate absence of a default-label requirement.

Empty-mismatch and missing-root cases use public base/failure equations; the fallback consumes `reconstruct_of_none`. Surplus preorder and surplus inorder examples exercise failure propagation through recursive children. The same-multiset example rejects `[1,2,3]`/`[3,1,2]`. The additive application `same_labels_not_joint_traversals` uses that failure together with distinctness and the general correctness theorem to prove that NO tree has both traversals, rather than relying on rejection alone.

Generic `leftRepeated a` and `rightRepeated a` are exactly the two-node opposite-orientation counterexample. Their four exact traversal equations, inequality by left projection, and failure of preorder Nodup require no decidable equality. Under decidable equality, `repeated_parser_choice` computes the specified right-child choice. `repeated_left_not_recovered` exhibits failure to recover the other tree outside the theorem's hypothesis. These cases explain the source precondition without weakening it.

## Findings and qualification

No mathematical weakening was found in this source assessment: the algorithm is total on every pair of lists, the expected malformed/duplicate behavior is explicit, the universal theorem uses the exact distinct-preorder condition and reconstructs the exact tree, and every requested counterexample/use remains. Actual Lean elaboration, termination checking, typeclass inference and proof checking remain UNVERIFIED until root runs the qualified compiler. Root must inspect actual elaborated types and resolve any source/API diagnostics. All original 76 Chapter4 obligations, entrypoint/correspondence integration, full immutable check/audit, independent Standards and Spec reviews and immediate verification remain open at the chapter level.
