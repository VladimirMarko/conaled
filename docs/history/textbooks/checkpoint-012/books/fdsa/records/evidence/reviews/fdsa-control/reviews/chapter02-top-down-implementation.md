# Floor-left top-down value implementation

Root implementation within active FDSA-002, 3 November 2026. This is a source
draft, not accepted coverage or a completed Lean validation. Full chapter scope
and all comparison-count obligations remain. The isolated worktree starts at
accepted Chapter1 R=07e480f6ec9958d4975bb90151005b84f2907614; no unaccepted shared
code is a dependency of these two value files.

## Source and required cases

The actual pinned Chapter2 text, printed pp17–19, defines the split point n div2
and returns lists of length≤1 unchanged. Root read its displayed value, cost,
multiset, sortedness, length and power-of-two comparison claims, and the full
prepared mergesort-proof-plan. The new value recurrence uses the same contiguous
floor-left split and canonical left-tie List.merge. Existing standard sortBy
uses ceil-left and is retained unchanged. No equality of observations follows
from the later proved value equality.

Applications/Sorting/TopDown.lean adds the exact value algorithm and one-step
base/recursive equations; its recursive calls use strict child-length decreases.
Permutation, length and membership are comparator-generic. The input-local
sortedness theorem uses only Std.IsPreorder on keys and the two branch-compatibility
implications for members actually present in the input. The ordinary keyed
specialization uses decidable key order and Std.IsLinearPreorder. Stable
occurrence observations additionally use decidable key equality, with no order,
equality decision, injective key map or inhabitance assumption on payloads.
Agreement with the existing standard sorter is derived from two independent
StableSort witnesses, under key antisymmetry (Std.IsLinearOrder).

## Statement review and connected uses

- The split is xs.take (xs.length/2) followed by the complementary drop, without
  reversing or alternating either half. The nonrecursive guard prevents a
  length-one right half from recursing unchanged. The proof of permutation
  composes actual child permutations, List.merge_perm_append and the exact
  ordered take/append/drop identity.
- Input-local compatibility is used on original members recovered from child
  permutations and take/drop membership. No arbitrary whole-type comparator
  law is smuggled into comparator-generic erasure or size facts.
- Stable sorting is proved recursively by mergeBy_filter on the actual sorted
  children, their equal-key filter identities and ordered split reconstruction.
  Both permutation and full-record equal-key order are retained. This is
  stronger than sorted keys plus support equality.
- Examples/TopDownSorting.lean applies the public step law to the independently
  expected split [2] and [1,0] at length3. Its sorted value uses public agreement
  with the independently specified existing sorter. A multiset client retains
  both occurrences of2 for an arbitrary comparator, and a false comparator
  still satisfies permutation/length (not an unsupported sortedness claim).
- The keyed client has keys [1,0,1] with arbitrary first/middle/last payloads;
  the expected output is middle,first,last. The equal-key filter case derives
  first,last from the new StableSort contract across the split. Empty payload
  and singleton cases consume the public base equations.

The actual compiler must still establish that the proposed proof scripts
elaborate. No focused result, full audit or review approval is claimed here.
The next necessary work includes XM01's actual measured merge after its own
acceptance, measured recursion on returned sorted children, explicit source
comparison-only recurrences, natural logarithmic bound and real power-of-two
corollary. Those are not replaced by these value statements.

Draft commit: 66cd1cca539cb667a7bae17d91d51c0ffeb718dc. Two new files, 195 lines; clean working tree. Root finished full source readback and statement review; actual Lean elaboration remains pending.

## Focused compilation and proof corrections

Root combined the stopped insertion draft95cfce3 and top-down draft66cd1cc by
history-preserving merge89455c in the isolated top-down worktree, now branch
work/fdsa-ch02-values. It has independently copied private pinned dependency
caches, all nine HEADs clean/exact, and no shared writable project outputs.
Evidence: provenance/chapter02-values-private-environment/private-cache.json.
The foundation candidate/checker remains untouched in its separate checkout.

Focused attempt1 compiled both insertion modules unchanged. The only TopDown
errors were dependent conditional rewrite proofs; correction5a61c28 uses exact
branch splitting and preserves every definition/statement. Attempt2 compiled
TopDown core, with two example reduction failures. Correction7d9d54b proves
those same expected outputs through independent observations: Nat sorted
permutation uniqueness, and an explicit expected StableSort contract for arbitrary
payloads with two equal keys. No expectation, hypothesis or algorithm changed.
The full logs and actual outcomes of each attempt remain in provenance/
chapter02-values-focused-attempt{1,2,3}/. These are focused development results,
not a complete Chapter2 candidate record, audit, independent review or acceptance.

Focused attempt3 required exposing the canonical Nat order in the independent
sorted-permutation example; c3f7b1b corrected only that proof and attempt4 passed
all four modules. Successor b167717 adds two useful connected clients: the
existing nonnegative-domain comparator exercises the new input-local sortedness
law, and the existing signed-record expected output exercises the value-agreement
theorem. It also corrects the source section header to §2.4. Focused attempt5
passed all four modules on exact clean b167717 (actual kit exit0,11.014s).
No source algorithm, required hypothesis or expected value changed. The current
summary is provenance/chapter02-values-focused-summary.json. These results do
not close the broader chapter, its missing costs, audit or independent review.
