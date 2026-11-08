# Elegant memoization: primary-source findings

Inspected talk repository at commit `470b6d828b92a30cb061d47587b6c790423f0aa8` and MemoTrie at `dd3f6a2290d00872178ed304be3e061a1a5a8183` (Cabal version **0.6.11**). The user-supplied reconstruction was read only as a lead; it is neither a transcript nor primary evidence. No Haskell build or benchmark was run.

## Preserved talk and unfinished scope

The [pinned slide source](https://github.com/conal/talk-2014-elegant-memoization/blob/470b6d828b92a30cb061d47587b6c790423f0aa8/elegant-memoization.lhs) and outline survive. The README dates the talk to April 3, 2014. Source line 201 qualifies the inverse law by undefined values; the closing frames “An almost beautiful story” and “Some memoization challenges” explicitly identify non-strict, higher-order, polymorphic and deep memoization. These are the documented open challenges, not evidence that ordinary MemoTrie was left unimplemented. The correctness appendix contains calculations for elementary domains. Its “Memoization via higher-order types” frame gives functor combinators and Exp/Log equations; this should not be confused with solved memoization of arbitrary function-valued arguments. Source inspection establishes surviving slides, not the absence of every possible recording.

## Hinze original recovered

The broken CiteSeer link can be replaced by [Hinze's Oxford publication entry P11](https://www.cs.ox.ac.uk/ralf.hinze/publications/) and its [updated original PostScript](https://www.cs.ox.ac.uk/ralf.hinze/publications/WGP00b.ps.gz): *Memo functions, polytypically!*, WGP 2000, proceedings pp.17–32. The author explicitly says this version supersedes the proceedings. Download succeeded; local conversion yielded `WGP00b.pdf` and text. Locators below use its own page numbers.

§3 pp.5–6 requires lazy evaluation for potentially infinite tables and full laziness to share a table across queries. §3.1 derives representation shapes from exponential laws. §3.3 pp.9–11 derives tabulation as a right inverse of lookup, then warns that the Haskell equation only holds for hyper-strict functions, which completely evaluate their arguments. The proposed mathematical setting uses pointed cpos and **strict continuous maps**, coalesced sums, and smash products; it is not ordinary arbitrary continuous-map semantics. The converse uses fixed-point induction for recursive types. §4 pp.14–15 derives functor/naturality laws within those assumptions. These results justify extensional representations under a stated semantics, not a universal Haskell contextual equivalence or an implementation-independent cache bound.

## Actual Haskell implementation and caveats

[Pinned Data.MemoTrie source](https://github.com/conal/MemoTrie/blob/dd3f6a2290d00872178ed304be3e061a1a5a8183/src/Data/MemoTrie.hs) defines `HasTrie` with associated data family, `trie`, `untrie`, and enumeration (lines90ff); `memo = untrie . trie` (156–157); and `memoFix h = fix (memo . h)` (174–175). Recursive calls must use the supplied recursive argument: wrapping an already closed recursive function does not redirect its internal calls through the memo table. This fixed point supplies no general termination or productivity guarantee.

The unit-instance proof commentary at lines273–279 explicitly acknowledges its non-strictness bug and says the proofs require hyper-strict functions. A concrete derived counterexample follows from the Bool code: `f = const 1` gives `f undefined = 1`, while `untrie (trie f) undefined` must inspect the Boolean and diverges. Thus “memo is identity” must identify its observation domain. Total finite constructor keys support the intended pointwise statement; arbitrary partial or infinite keys do not follow.

Lines139–153 discuss rewrite rules: eliminating `untrie . trie` would defeat memoization even though that is the intended denotational equation. This directly separates semantic correctness from runtime sharing. A shared lazy trie can retain computed entries; extensionally equivalent implementations may recompute, allocate different amounts, or retain excessive memory. The source does not establish a generic time/space theorem. Enumeration and equality also should not be assumed terminating for infinite key domains.

## Bounded integration proposal (our deduction)

Start with empty/unit/Bool/sum/product total domains and two explicit contracts: tabulate/lookup round trips, and preservation of selected observations under composition. Prove result-side naturality only under the selected total interpretation. Add one structurally recursive key example through bounded observations, without claiming finite total storage for an infinite domain. A simple extension law should show how a new domain equivalence transports the representation and its proof.

Keep an operational deliverable separate: a persistent memo-table state machine or explicitly shared delayed representation with a cost observation. Test repeated queries to the same retained table and prove the corresponding hit/miss or evaluation-count property if claiming memoization, rather than calling extensional trie correctness a cache theorem. A bounded well-founded recursive example can compare ordinary evaluation against memoized recursion with the same result and an explicit reuse measure. General fixed points, Haskell bottom equivalence, arbitrary higher-order keys and polymorphic/deep memoization remain separate research obligations. This is sufficient motivation for an integration issue, without porting all of MemoTrie or claiming to resolve the talk's challenges.

## Fit with this repository

The [user-supplied reconstruction](../history/elegant-memoization/README.md)
is archived verbatim with provenance. It supplied leads, not evidence for the
claims above. The preserved slides and implementation establish a working core
alongside explicitly unfinished challenges.

`SquareKit/WordCoalgebra.lean` and `Applications/Languages/WitnessTrie.lean`
(#255) provide bounded observations and exact selected parsing decisions.
They do not provide a retained cache or a sharing theorem. The language trie
indexes observations by words; a MemoTrie represents a function by the shape of
its key type. These uses can share observation laws without assuming they are
the same representation.

`Applications/EditAlignment/Cached.lean` stores scores and scripts;
`Applications/Resources/TreeFlattening/Cached.lean` supplies a measured cached
tree traversal. Neither is a generic function memoization interface. Their
semantic erasure and cost separation are useful precedents. The historical
`docs/history/compiling-with-squares-possibilities.md` already suggests memo
tries, but that suggestion is not an implemented contract.

The integration should use the shared representation/interpretation vocabulary
and coordinate with #174 (data structures), #193 (resource semantics), and #255
(language observations). New key representations must satisfy the stated
round-trip laws; new operations must prove compatibility with lookup. An
extension must reuse an existing client theorem under those assumptions.
Cost claims additionally require an explicit retained state and workload.
This keeps the extension discipline visible without importing Haskell's
partiality or sharing assumptions into Lean's total function semantics.

Implementation is tracked in [#263](https://github.com/VladimirMarko/conaled/issues/263).

## Bounded implementation

The total constructors, bounded word tables, domain-equivalence transport and
retained well-founded recursive client are implemented in
`Applications/Memoization/`. The [implementation report](compositional-memoization.md)
records checked contracts, actual operation counts, source boundaries and the
remaining dependent-parser adapter obligation. This completes the bounded
implementation proposed above; it does not settle the talk's broader challenges.
