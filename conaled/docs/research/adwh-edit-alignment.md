# Edit alignments and cached rows (#167)

`Applications.EditAlignment` reconstructs the fixed-price Chapter 13 edit
solvers as ordinary Lean functions. `Semantics` defines ordered alignment
independently of any solver. `Recursive` proves global optimality and the
exchange argument for copying equal heads. `Rows` and `Cached` refine actual
row folds at every suffix position. `Observation` connects both realizations
to the existing optimization and relational observation interfaces.

An operation copies a symbol, replaces a source symbol by a target symbol,
deletes a source symbol or inserts a target symbol. `Aligns` relates the ordered
operation list to its complete input and output. `aligns_iff_reconstruct`
connects this relation to an executable fold. Equal-symbol replacements are
admissible: the feasible set is every aligning script, not just scripts the
executors generate. `MinimumEdit` minimizes over that entire feasible set and
`minimumEdit_iff_minimizer` identifies it with `Optimization.minimizers`.

Prices are fixed: copy 0, replace 3, delete 2 and insert 2. The recursive `mce`
considers diagonal, deletion and insertion candidates in that order. Its binary
`best` invokes the existing `Optimization.Thinning.argmin`, so ties retain the
first candidate. `best_firstMinimum` exposes the independent positional tie
contract. Optimality follows by induction on an arbitrary aligning script.
The equal-head exchange proof removes matching input/output heads without
increasing cost; this justifies the row executors' copy shortcut. These results
do not claim that the shortcut is valid for arbitrary prices.

## Rows and cached representation

`firstrow` uses standard `List.tails` on the deletion script. `nextrow` zips the
source with the old row and its tail using standard nested `List.zip`, then
folds right. Its boundary reads standard `List.getLastD`. The full table is an
outer right fold over target symbols. Source utility implementations for tails,
three-way zip and last are not copied. The local last-element lemma only states
a law of the standard operation.

`modelRow` and `modelRow3` specialize standard `xs.tails.map evaluate`.
`Applications.DynamicProgramming.SuffixRow` shares the nonempty, length, head,
last and optional-entry laws for arbitrary evaluators and result types. Length
and indexed entries reuse `List.length_tails` and `List.getElem_tails`; neither
client repeats an induction on source suffixes. Their evaluators retain the
uncached and cached tie policies. The public model-row names and source-shaped
statements remain available as thin specializations.

`editTable_entry` proves that position `i ≤ xs.length` is exactly
`mce (xs.drop i) ys`. The row length is `xs.length + 1`; the last column is the
insertion-only solution from empty source. Initialization, next-row refinement
and the entire outer fold are proved, including empty source or target.
`mce2_eq_mce` derives final witness agreement from this all-entry invariant.

The cached representation is a pair of score and script. `CacheValid` states
that the score equals the independently folded script cost. `cachedCons` adds
an operation's price to the stored score; `cachedBest` invokes existing `argmin`
on stored scores. Neither operation rescans the script to obtain its cost.
The cached initial row and next rows are actual folds of these operations.
`editTable3_entry` identifies every entry with a valid cached solution of its
suffix problem, and `editTable3_cache_valid` states validity for all entries.
The `cache` encoding appears in specifications and proofs, rather than
replacing the cached executor with a solver followed by cost recomputation.

Cached unequal-head choices use insert, replace, delete order. `mceIRD` records
that policy; `mce3_eq_mceIRD` proves exact witness equality to it. The uncached
and cached witnesses need not be equal. `mce3_cost_eq_mce2` proves equal optimum
cost while retaining their different tie policies. All minimum claims remain
global over independent alignments.

## Shared consumers and checked boundaries

`witnessSquare` uses `Optimization.selectionSquare`; its uncached and cached
instances expose the same optimum-witness specification. `costSquare` composes
this with the shared `Optimization.observationSquare costE` from #164.
`cachedCostSquare` uses that composed specification and proof while its
executable observation reads `mce3Result.fst`. Cache correctness justifies this
replacement. Thus the scalar client observes the maintained score directly.
The public attainment results give an independently optimal witness at the
observed cost, and `observed_cost_agreement` uses uniqueness of optimum values.
These are direct functions, proofs and square composition; no edit-specific
language or representation framework is introduced.

`Examples.EditAlignment` retains empty, deletion-only, insertion-only, identical
repeated-symbol and singleton replacement cases. The replacement costs 3 and
delete/insert costs 4. An equal-symbol replacement is explicitly admissible but
more expensive than copy. For `abca → bac`, the uncached solver selects
`delete a, copy b, delete c, copy a, insert c`; the cached solver selects
`insert b, copy a, delete b, copy c, delete a`. Both are proved globally optimal,
reconstruct the same input/output and have observed cost 6. Their witnesses
are unequal. A shared first-minimum specialization checks the tie convention.

A suffix-length evaluator also consumes the shared optional-entry law without
edit-specific assumptions. All three row entries for `[0,1] → [1]` are checked through the entry theorems,
including the terminal insertion column, with cached scores 2, 0 and 2. The
length theorem rejects the next position. A deliberately invalid cache assigns
score 0 to delete/insert; comparison then selects its true cost-4 script over
a valid cost-3 replacement. Both scripts are proved to align the same inputs.
This explains the cache-validity premise. Valid cached choice is separately
checked through `cachedBest_valid`.

## Statement review and provenance

The initial mathematical obligation was to connect actual row computations to
independent global alignment optimality, including the two source tie orders.
The source's displayed tie example fixed the expected witnesses before the
new public consumers were checked. The final cases use the row, optimum,
representation and observation results, rather than treating reduced output
alone as a correctness proof.

Statement review covered every definition and theorem family: ordered source
and target indices in each alignment constructor; equality-replacement
admissibility; all-script quantification in optimum claims; fixed prices and
exchange bounds; first-tie behavior; source suffix indexing and terminal row
length; old-row versus newly constructed neighbor dependencies; initialization
and the whole outer fold; validity of every cached entry; exact I/R/D reference
agreement versus cost-only cross-solver agreement; and the problem index and
attained witness retained by scalar observations. Source types are generalized
to arbitrary symbol universes in the algorithm modules. Observation clients
use `Type` symbols to fit the existing single-universe relational interface.
No stronger equality, complexity, demand or runtime claim is asserted.

The [declaration ledger](adwh-edit-alignment-provenance.tsv) records inspected
source declarations, immutable member hashes and retained/deferred scope.
Hashes were recomputed from the repository ZIP and matched against its manifest
and the inspected extraction. Selected proof arguments are adapted from the
preserved source; their surrounding imported closure is not copied.
`EditDistance` through `mce2_spec` and `EditDistanceCached` through `mce3_spec`
are reconstructed, with standard operations replacing utility implementations
and shared optimization selection replacing standalone binary minima.
Selected `EditExamples` declarations supply the tie case. `EditWeighted` was
inspected to establish the fixed-price boundary and remains deferred.

Operation counters, raw costs, all-minima enumeration, parameterized prices,
metric composition, LCS connections and their larger example sets remain
separate. The original material stays intact in
[checkpoint-233](../history/algorithm-design-haskell/README.md).

Targeted validation: `direnv exec . lake build Examples.EditAlignment`.
The public entrypoint imports these examples, bringing the slice into normal
build and proof audit. The coordinating session owns fresh full integration
validation, independent Standards/Spec reviews and supervising intent review.
