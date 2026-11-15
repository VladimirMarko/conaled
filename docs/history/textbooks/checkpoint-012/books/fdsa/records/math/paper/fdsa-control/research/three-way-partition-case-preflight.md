# Shared three-way partition: independent case preflight

Prepared 2026-11-02 for possible shared groundwork used by Chapter 2's
three-way quicksort and Chapter 3's selection. This is source preparation,
not source implementation, a frozen new requirement, chapter activation,
compiled evidence or either final review axis. Root owns the sole Chapter 1
validation run at `07e480f6ec9958d4975bb90151005b84f2907614`.

The compact proposed scope is an extraction of the existing value interface
plus one actual recursively measured realization of the source partition.
The existing chapter plans remain unchanged. No new measured binary-partition
or two-pass executor, comparison framework, keyed abstraction, or test campaign
is needed for these cases.

## Evidence and inspected interfaces

I read the governing `../REQUEST.md`, conaled's `AGENTS.md`, architectural and
domain guidance, glossary, ADRs 0001/0010, and the complete example-driven skill
and worked example. Relevant retained plans are
`chapter02-reuse-plan.md` and `selection-proof-plan.md`, especially the latter's
section 2. The current inventories retain C02-102, C03-011/013/031 and the
corresponding Appendix B.2 obligations; none is closed by this note.

The primary book is the July 27, 2026 edition of
[FDSA](https://fdsa-book.net/functional_data_structures_algorithms.pdf), PDF
SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
I read the retained passages in Exercise 2.3, printed p.28; selection's
arbitrary-pivot/termination discussion, pp.34–35; its time-function context,
p.40; and Appendix B.2, p.348. The latter gives the empty entry cost one,
one additional entry for each cons, and the exact `length+1` result.

The pinned companion
[Selection.thy](https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Selection.thy)
at revision `f86f290225eebcc52c1ae7dba2e098f405f51c21` supplies the three-filter
specification, `partition3_code` and `T_partition3`. The code equation calls
the tail partition once, then tests head less than pivot, then pivot equal to
head, and prepends the head to exactly one returned bucket. The companion
revision is a separately pinned reference, not claimed to have generated
the manuscript.

| Inspected file | Bytes | SHA-256 |
| --- | ---: | --- |
| `book-source/Selection.thy` | 47,922 | `c2e5970bcdc9430ef802a6612381fdd3820a02bc796d20f4a202060f3f00b4e8` |
| `Applications/Selection/ThreeWay.lean` | 10,489 | `bd72ca5f11d028cde9420ae42f9a9f1f84d6cfc00bf02bd528a61fd00f586d52` |
| `Applications/Resources/Measured.lean` | 2,906 | `feb5f2f3096b327d8cf636343f33fcc7be08d1324f3dc7ff6f168bf68a203f46` |
| `Applications/Resources/CallCount.lean` | 2,447 | `5bb2d9e1e43dde11fdcee3c492c44662351c72e9a27af385b79de53e8e76b2a8` |
| `Examples/RankSelection.lean` | 5,085 | `641a752cdee9b2ab30e66bb2f7feda2548cffebfe6733460b52ff5f7e119520e` |

All four inspected project files are byte-identical between the main checkout
and the repaired Chapter 1 validation checkout. These are ordinary input
identities, not project artifact-integrity or validation results.

`Applications.Selection.partition3` currently performs two standard
`List.partition` operations. Its public `partition3_eq_filters` describes the
exact ordered lists, and `partition3_perm`, the three membership equivalences,
`partition_lengths` and `partition_strict_sizes` provide existing semantic
consequences. The latter requires `p ∈ xs`. The downstream `sorted_partition`,
`dispatch_value` and selector/consumer results have additional selection roles;
their existing cases must survive any extraction.

The proposed measured name `partitionRun` is schematic in this note. Its
separate public contracts should identify the actual returned triple with the
existing partition value and establish actual cost `xs.length+1`. Ordinary
`Resources.bind` passes a result's first projection to its continuation and
adds observations. `CallCount.tick` adds one after evaluating the body.
Comparisons, projections, tuple construction and cons have no additional charge
in this particular source observation.

## Compact cases and independent expected results

The proposed cases below are enough to distinguish the consequential domains,
value order and resource boundaries. They are not a quota for each declaration.
Use the eventual public value/cost/equation laws to connect them; evaluating
closed lists without those connections leaves the intended application missing.

### 1. Empty input and a generic equal-block family

For any supplied `p : α` with the existing `[LinearOrder α]` assumption,
the empty input has triple `([], [], [])` and cost one. The source counts the
empty recursive invocation, so a zero result would implement another tariff.
No `Inhabited α` is needed because the pivot is an explicit argument.

For all natural `n`, `replicate n p` has triple
`([], replicate n p, [])` and cost `n+1`. This family is polymorphic and includes
the singleton cost two. Every equal occurrence is retained; no `Nodup` premise
belongs here. For `n>0`, establish pivot membership and specialize the existing
strict-side theorem to obtain zero-length strict sides smaller than `n`.
For `n=0`, keep the correct value/cost result without asserting `0<0`.

Connect the triple through `partitionRun_value` and the shared
`partition3_eq_filters` or its source cons equations. Connect cost through
`partitionRun_cost`. This family also prevents an accidental all-input bound
`cost ≤ C*length` for any fixed natural `C`: its empty case has positive cost.
No new asymptotic theorem is required for this observation.

An operation requiring a pivot cannot be invoked on `Empty` without such a
value. The relevant zero-size case is the empty list with an explicitly supplied
pivot. Do not manufacture an Empty pivot, a default element or a new domain
wrapper merely to add an empty-type example.

### 2. Mixed buckets with duplicates and visible internal order

Take pivot two and the eight-element input

```text
[4, 1, 2, 0, 3, 2, 1, 4].
```

The independently expected triple is

```text
([1, 0, 1], [2, 2], [4, 3, 4]),
```

and the work is nine. Reading the input from left to right puts the first four
in the upper bucket, the first one in the lower bucket, both twos in the equal
bucket, and so on. The lower and upper buckets both retain nonsorted order;
partitioning does not sort them. Their lengths are three, two and three, summing
to eight. The flattened result is a permutation of the original list and need
not equal that list. In particular, set membership alone would lose the repeated
ones, twos and fours and is not the required observation.

Use the new value bridge followed by the shared filter law for the exact lists,
the existing permutation/length laws for the occurrence and size consequences,
and the new actual cost theorem for nine. Establish `2 ∈ xs` before using
`partition_strict_sizes`; both strict sides then have length three, strictly
less than eight. This one fixture exercises all three source cons branches
without inventing a separate test for every helper theorem.

### 3. Absent pivots distinguish semantics and shrinking

| Pivot / input | Expected triple | Work | Shrinking observation |
| --- | --- | ---: | --- |
| `4`, `[3,1,3]` | `([3,1,3], [], [])` | 4 | The lower side is the complete input, so its length is not strictly smaller. |
| `2`, `[3,1,3,1]` | `([1,1], [], [3,3])` | 5 | Both strict sides have length two, less than four, despite the absent pivot. |

Both rows must retain the unconditional value, permutation, membership and
total-length contracts. The first refutes an unconditional strict-side claim
and shows why selection's recursive progress requires its own premise. The
second shows that `p ∈ xs` is sufficient, not necessary, for both sides to
shrink. Do not change the existing implication into an equivalence.

Neither row has an inhabited equal bucket. A semantic selection recurrence may
use an arbitrary pivot, but a reached equal branch needs its index bounds;
the partition interface alone cannot conclude that `es` is nonempty or return
an element of it. The selector's middle-index helper and full recurrence can
remain in the owning chapter; these cases do not require implementing them now.

### 4. A continuation consumes the first returned bucket

Use the same eight-element fixture and bind its measured partition at pivot
two directly to a second invocation of the same proposed executor, at pivot
one on the returned lower bucket:

```text
Resources.bind (partitionRun 2 xs)
  (fun triple => partitionRun 1 triple.1).
```

The first actual lower list is `[1,0,1]`. Its second partition is
`([0], [1,1], [])`, with work four. The combined expected value is this latter
triple and the combined expected work is `9+4=13`.

This can be an example expression rather than a new public executor. Establish
the first actual value through its public bridge before rewriting the second
input. Then use `Resources.bind_value`/`CallCount.let_rule` and the two public
cost results. The example detects accidentally passing the original list,
passing the whole measured pair instead of the triple, or adding an undeclared
outer entry charge. The continuation's argument is the plain triple; its first
field is the lower list. The top-level measured result has a separate first
projection for that entire triple.

This composition uses only the same proposed single-pass operation and the
existing measured sequencing interface. It introduces no separately measured
two-pass implementation and assigns no source algorithm an unproved cost.

### 5. Preserve the existing selector clients

Extraction should retain the existing `Applications.Selection` public names,
statements and assumptions. The complete existing
`Examples.RankSelection` already checks empty/invalid ranks, repeated selected
values, both head/last pivot policies, administrative fuel and the lower-median
consumer. Its named `duplicate_selection` selects the third one-based occurrence
of `[1,2,2,3]` and returns two through the current semantic interface.

Retaining those clients in the unchanged public import/audit closure supplies
compatibility coverage when the eventual full candidate is built. Do not
duplicate that entire selector case suite or claim its current fuel-based
algorithm already executes `partitionRun`. The new measured value theorem
should meet the preserved partition interface directly, so later sorting and
selection clients can reuse the same semantic laws.

## Calculation method and limits

The literal expectations above were fixed from the bucket specification and
the count of input cells plus the final empty entry. A small ordinary Python
read-only calculation checked the fixed literal triples with the three
predicates and verified lengths and the `9+4=13` addition. It wrote no data or
project source, invoked no Lean or checker and supplies no formal validation.

The generic replicate calculation follows by induction on `n`: the tail returns
only copies of `p` in the middle, the head satisfies equality, and one cons entry
is added. These independent expectations should remain fixed when proofs are
written. A script, theorem or closed reduction of the future implementation
cannot be its only source of expected values.

## Statement and API risks to keep explicit

1. **Complete values and component order.** The result is the ordered triple
   lower/equal/upper with occurrence multiplicities. Set equality, a reordered
   pair nesting, equality of only flattened multisets or a sorted result is
   weaker or different. Right-associated products use `.1`, `.2.1`, `.2.2`.
2. **Pivot domain.** Value, coverage and exact work need no membership premise.
   The existing strict-size implication requires membership and is useful for
   termination. An absent interior pivot can still shrink; empty input cannot
   witness strict shrinkage.
3. **Source execution.** Define an actual single tail recursion and classify
   its returned triple. A synthetic pair consisting of the old two-pass value
   and a separately attached `length+1` annotation would not establish the
   source execution requirement.
4. **Resource boundaries.** Count one per invocation including nil, with
   comparisons and constructors zero in this declared model. The old two-pass
   `List.partition` value implementation has no `n+1` resource theorem merely
   because it returns the same triple. Exercise 2.3's three-filter value
   expression and Exercise 2.4's separately charged two-filter quicksort retain
   their own observations. No new exact old-executor count is proposed here.
5. **No incidental generalized domain.** Existing `[LinearOrder α]` domains
   support the source. Keep universe-polymorphic payloads and avoid adding
   `Nodup`, `Inhabited`, boundedness or finiteness. This unit has no demonstrated
   need for a new keyed comparator or preservation typeclass.
6. **Equal keys versus equal payloads.** The current equal bucket means
   literal `x=p` in the supplied linear order. Distinct records with the same
   external key need a separately stated keyed interface; assigning a
   lexicographic order to records does not make all equal-key records equal.
   Do not silently claim that stronger interface from the existing definition.
   A new tagged-record case or keyed API is not required for this bounded scope.
7. **Monotone relabeling does not preserve buckets.** Existing selector value
   theorems permit noninjective monotone maps, but the partition triples do
   not. For `p=2`, `xs=[1,3]`, a constant map to natural zero sends the old
   triple to `([0],[],[0])`; partitioning the mapped list around mapped pivot
   instead yields `([],[0,0],[])`. Both maps are monotone. This is a boundary
   against inventing an invalid transport claim, not a new required map theorem.
8. **Validation and placement.** The public library must not import Examples.
   The new value owner, actual measured module and compact connected cases
   need normal public import coverage, focused compilation, the applicable
   complete candidate build/audit, both retained final review axes and immediate
   candidate verification when prerequisites and compiler exclusivity permit.
   This preflight supplies none of those results.

No source, ref, worktree, cache, compiler, project hash helper, checkpoint or
remote operation was changed by this assignment. The only authored file is
this report. Full quicksort3, the selector's middle-index bridge, actual
median-of-medians or randomized executions, their termination and total costs,
and all original chapter obligations remain with their existing owners.
