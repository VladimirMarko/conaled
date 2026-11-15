# C03-MINIMUM-ELAB-002: finish the concrete invalid-rank guard

Original candidate: `b150953544438985ce979cc30b9a2f9237091fe8`.
Successor: `d0479dd03371f1c1f0b41dff5f1882a36206f40a`.
Tree: `4f7cc77eb1a7d270117ea33065727084c552a630`.

The entire closed attempt2 log, result, terminal and reconciliation were read in
`cb90a2`. Owned session 6299 is CLOSED with actual exit 1, terminal `2f30c7`.
The outer log is 5115 bytes, SHA-256
`d3ccba1b17f60768073ae7e394f3d50c4727c5c891b107fae3eb7e35b95d4340`.
It reports that both `Applications.Resources.SelectionPolicy` and
`Applications.Resources.MinimumPivot` built successfully. The sole remaining
error is in `Examples.MinimumPivot.invalid_value`: after the public value
theorem and sorted-length correspondence, the remaining goal is
`input.length ≤ 4`.

The explicit input is `[3,1,4,2]`. The successor adds only `decide` after the
existing length rewrite, discharging that closed natural-number inequality by
kernel reduction. The statement still claims that zero-based rank 4 of this
four-element list returns `none`. The proof still consumes `run_value` and
`ordered_perm`; it does not replace the public-result connection with an
unrelated calculation. No assumption, expected result or cost changes.

The exact diff adds one proof line. All 52 new raw statement headers and lexical
contexts are unchanged; all other 51 declaration blocks are identical. The
other 17 owned source files are byte-identical, including both cores that
actually built and the prior C03-MINIMUM-ELAB-001 correction. All 402 cumulative
public declarations and seven existing named private helpers remain in scope.

The complete original statement/case assessment is retained at
`minimum-pivot-review-note.md`, SHA-256
`36eeb7d69656230ede4bb47739dfe98e9df38bb9d08940a5b9259177dedb24dd`.
Its full mathematical scope is unchanged: actual measured pivot construction
and three-way branch erasure; duplicate-aware optional values; distinct valid
rank exact trace, `k+1` active invocations and `k` edges; exact scan and separately
charged source tariff; largest-rank quadratic and fixed-rank linear bounds;
and all 23 consumers, including the invalid-rank case, singleton, rank-zero and
duplicate counterexamples, and the universal growing range family. This proof
correction changes none of their quantifier order, domains or conclusions.

The rebound inventory retains all headers and records successor source hashes.
`MinimumPivotStatements-candidate3.lean` retains the same 52 explicit-`@` checks,
import and supported printing options; only the candidate comment changes.
Every earlier input, inventory, correction and actual failure is preserved.
There has been no actual type execution by the author and no execution is
relabeled as belonging to this successor.

The successor is uncompiled. Root must run the same three focused targets at
the exact new commit. The prior core successes do not turn the failed examples
run into a successful complete check. No author Lean/Lake/cache/runtime action
occurred, and no full Chapter 3 check, exhaustive audit, independent review,
immediate verification or acceptance credit is claimed.

Root now explicitly owns C03-055. This author's next assigned work is C03-080,
only after the minimum slice passes all three targets and root explicitly
releases it. The complete 83-obligation Chapter 3 scope remains with the existing
coordinator and review loop.
