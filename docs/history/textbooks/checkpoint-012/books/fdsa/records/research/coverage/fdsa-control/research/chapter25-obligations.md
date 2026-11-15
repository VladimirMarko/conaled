# Chapter 25: Fast String Search by Knuth–Morris–Pratt

Research date: 2026-11-02. Local ticket: `FDSA-025`.

**State: queued; source preparation only.** This original inventory changes
no Lean implementation, build, ticket, acceptance state or remote content.
Every row is a future implementation/proof/reuse obligation. Chapter order
and acceptance remain controlled by the parent task.

## Sources and inspected identities

| Source | Inspected identity |
|---|---|
| Book | Lawrence C. Paulson, Chapter25, printed pp.293–304, PDF pages299–310, July27,2026 version. Official PDF <https://fdsa-book.net/functional_data_structures_algorithms.pdf>, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. |
| Formal companion | *Knuth–Morris–Pratt String Search*, Lawrence C. Paulson, AFP November27,2023, <https://isa-afp.org/entries/KnuthMorrisPratt.html>. Inspected archive <https://isa-afp.org/release/afp-KnuthMorrisPratt-2026-10-26.tar.gz>, 7,929 bytes, SHA-256 `cf032135553f0c0589aa14a6b55077fd419b6a5c83ce1e4f882a9eef1f27b2cb`. |
| Main theory | `KnuthMorrisPratt/KnuthMorrisPratt.thy`, 32,537 bytes, SHA-256 `4b98a497476dbffa0eb29390d32d7a8f9b722e41d12edf5d31cea824bd732f0e`. It imports `Collections.Diff_Array` and Isabelle's `While_Combinator`. No `sorry`, `oops` or `axiomatization` marker was found in this file; no Isabelle build was run. |
| Array dependency | <https://isa-afp.org/entries/Collections.html>, dated archive <https://isa-afp.org/release/afp-Collections-2026-10-26.tar.gz>, 293,987 bytes, SHA-256 `e6c36de1d66963ad3520a4709e4b372014c3ea60cc1a7acc74b1ddb36d06fc41`. Inspected `Collections/Lib/Diff_Array.thy`, 39,477 bytes, SHA-256 `a47955986305fb310c16fd5c227f22024064574facb0c644fcddc5e82926f149`. |
| AFP license | Entries advertise BSD; shared <https://isa-afp.org/LICENSE>, SHA-256 `9ac784670a1624c9b0f83f61c2c68163985cfd50f5c2fbe9699623311a5ce4bd`. Retain attribution/notices when adapting code/proofs. |
| Lean/project pins | conaled baseline `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`, inspected HEAD `1aabd512284fe86254278ac631eda061d311050b`; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`; Lean4.35.0 source `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Inspected dependency files use Apache-2.0. Local candidate inspection is not acceptance. |

The AFP source revision postdates the book. Archive identity and hash pin
what was inspected; they do not claim that it generated the July PDF.
Reading copies are in `book-source/`. The inventory/provenance, rather than
the manuscript, is the deliverable. There are **no numbered exercises** in
this chapter. All nine numbered lemmas/corollaries, Equation25.1, and the
introductory average/worst-case mathematical assertions remain in scope.
References to Boyer–Moore, Why3 and the original KMP paper do not require
porting every algorithm or theorem in those works.

## Carrier, indexing, partiality and cost conventions

Let `m=p.size`, `n=a.size`, where both pattern and text are arrays over an
arbitrary equality type. A Lean implementation needs `DecidableEq α`, or
`BEq α` with an explicit law equating its answers to equality. No order,
finite alphabet or byte encoding is required for deterministic KMP
correctness. A finite alphabet and a probability law enter only the
introductory **average-case naive-search** discussion.

The book's next table is shifted relative to the usual prefix function:
`nxt[j]` is the longest proper border of the prefix of length **`j`**.
For `0<j<m`, it stores a number below `j`. Entry0 is initialized to0 but
is never used as a positive fallback. The full-pattern border is not
computed. The builder starts at `(i,j)=(1,0)` and continues only while
`i+1<m`; for `m=2`, it performs no loop-body step.

`matches a i b j k` includes both bounds `i+k≤a.size`, `j+k≤b.size`,
even for `k=0`. Equality of clamped empty extracts is not enough. Generic
array reads must be guarded by derived bounds rather than an arbitrary
payload default. Update and read bounds for every executed branch are
proof obligations, separate from the abstraction of an array as a list.

There is one extra HOL-domain detail in the printed builder invariant:
it permits `i=m`, but its table clause then observes `nxt[m]`. Source
`array_get` is list indexing and is underspecified there. Actual initial
and reachable builder states satisfy **`i<m`** whenever the loop is used.
A safe source adapter can strengthen the reachable-state invariant to
`i<m`, and/or bound the table clause explicitly by `k<m`. The latter
weakening follows from the printed invariant and is sufficient for its
terminal correctness theorem, since that theorem asks only `k<m`.
Document this domain adaptation; do not silently identify arbitrary
out-of-range HOL reads with Lean's default values.

Both outer recursions are partial on arbitrary malformed arguments. The
AFP `partial_function (tailrec)` equations are not unrestricted
termination theorems. In Lean, use valid-state well-founded recursion or
an evaluation/partial-run relation with proved termination on the stated
domain. A finite budget exhausted on an invalid table is not a proof that
the pattern is absent.

The chapter's explicit `Tbuildtab` counts **executed loop bodies**. Its
base branch returns the accumulator unchanged. It therefore differs
from a charge at every recursive function entry. Each body performs one
element equality test, possibly one table read or update. Lookup, update,
size, index arithmetic and equality are assumed constant-time in the
chapter's abstract unit-cost model; initializing the whole table is
linear in `m`. These assumptions do not certify Lean runtime allocation,
sharing or bit complexity.

## Existing KMP implementations and exact reuse limits

There are two substantive implementations to evaluate before creating a
new one. Their algorithms are related to the book, but their table
representation, state transitions, return observations and costs differ.

| Existing component | Actual useful support and boundary |
|---|---|
| Batteries `Data/Array/Match.lean`: `Array.PrefixTable`, `PrefixTable.step`, `PrefixTable.extend`, `Array.mkPrefixTable`, `Array.Matcher.ofArray` | Generic alphabet implementation. `PrefixTable.valid` only proves each fallback entry is at most its index; it does **not** assert maximal-border correctness. `step` is total by decreasing fallback index. The table stores `(character,borderLength)` through each position, including the full pattern. |
| Batteries `Array.Matcher.next?`, `mkPrefixTableOfStream` | These are `partial` definitions. `next?` consumes one stream element, then performs several fallback comparisons inside `step`. The book counts each fallback as a separate loop body at unchanged text index. Semantic comments are not proved matching/cost contracts. |
| Batteries `Data/List/Matcher.lean`: `List.Matcher.find?` | Returns optional `(start,end)` and explicitly returns `some (0,0)` for an empty pattern. A potential external result adapter, but it loses the book's residual terminal `j` on failure. |
| Batteries `Data/String/Matcher.lean`: `String.Matcher.find?` | No equivalent empty-pattern correction: empty pattern/empty text gives `none`; with nonempty text, the empty match is returned after the first consumed character. This is not the source's unrestricted first-occurrence behavior. |
| Core `Init/Data/String/Pattern/String.lean`, namespace `String.Slice.Pattern.ForwardSliceSearcher` | Actual total KMP implementation: `buildTable`, `buildTable.go`, `buildTable.computeDistance`, `getElem_buildTable_le`, finite search iterator. It uses UTF-8 bytes and slice positions, an ordinary full-prefix table, extra remaining-capacity rejection and code-point-boundary jumps. |
| Core `Init/Data/String/Lemmas/Pattern/String/ForwardSearcher.lean`, namespace `String.Slice.Pattern.Model.ForwardSliceSearcher` | `PartialMatch`, `PartialMatch.partialMatch_iff`, `prefixFunction_eq_iff`, `prefixFunction_sub_one_lt`, `prefixFunctionRecurrence_eq_prefixFunction`, `IsTable`, `isTable_buildTable`, `getElem_buildTable`, `Invariants.not_matchesAt_of_prefixFunction_eq` supply real border/maximality/skipped-range proofs. Many implementation lemmas are not public and use `import all`; assess the dependency/export boundary before reuse. |
| Core `lawfulToForwardSearcherModel`; `Pattern.Model.find?_eq_some_iff`, `find?_eq_none_iff` | Correctness and earliest-match/absence specifications under their strict pattern, lawful searcher/model and finite iterator premises. The slice theorem is for nonempty patterns; top-level string facts handle empty strings separately. |
| Core `String.contains_string_iff` | Character-list infix semantics for the public string operation. A byte/character-index transport is still necessary for this chapter's generic array positions. |
| Core Array laws | `Array.replicate`, `size_replicate`, `getElem_replicate`, `set`, `size_set`, `getElem_set_self`, `getElem_set_ne`, `getElem_set`, `extract_extract`, `toList_extract`, `getElem_toList` support exact guarded value semantics. They do not establish difference-array runtime costs. |
| conaled `Applications/Dijkstra/Store.lean`: `lookup`, `write`, `lookup_write` | Existing fixed-size Vector/store interface pattern. KMP border invariants and recurrence are absent. |
| conaled `Resources.Measured`, `Resources.Potential`, `Resources.DijkstraStore` | Value erasure, measured observations and decreasing-budget proof scaffolding. Store copy/read/write models are explicit abstract observations, not proofs of physical Lean Array mutation. No verified difference-array implementation was found in the bounded repository/library search. |

| Inspected dependency file | SHA-256 |
|---|---|
| Batteries `Data/Array/Match.lean` | `b2879e275b13fe8384c94ed43b8b824ad21214c3eb1b1f0545df673ea3d519af` |
| Batteries `Data/List/Matcher.lean` | `3e790291f8d8190dfb7b3e970f6532319eb406c7df07240be9691e3a1b550896` |
| Batteries `Data/String/Matcher.lean` | `26581d6d4de65e09eae6d8fc57ae27bbd4d60edf8cd8696ef6d2e43c34ffa605` |
| Core `String/Pattern/String.lean` | `89a148830f8d4570850076c0abd04dbf8c9cf5f55f8384b7e9fda4c6898418db` |
| Core `String/Lemmas/Pattern/String/ForwardSearcher.lean` | `eedd874499ff97c6c91bded31fc6688b0ed5cb6eef6a5afa34b407f9dfe647c2` |
| Core `String/Lemmas/Pattern/Find/Basic.lean` | `ee1993598318690b228047e929f914ab48e14f64cd1b1aeff6a4b35c3ee92066` |
| Core `String/Lemmas/Pattern/Find/String.lean` | `3c9c2fe02778f0b4638cb023ceead7f51818407c9c685f68014db0faadb952a8` |

For a usual prefix table `t`, the source relation is
`nxt[j] = t[j−1]` for `0<j<m`, with appropriate projection from
Batteries' pair entries. Pattern `"aa"` separates the recurrences:
source table `[0,0]` needs zero builder bodies, whereas the usual table
has `[0,1]` and compares the second character. A shifted-value equality
is therefore insufficient as a measured implementation bridge.

Core search rejects `p="ab"`, `a="b"` immediately because the pattern
cannot fit; the source executes one mismatch comparison. Even ASCII
does not remove this recurrence mismatch. For `p="a"`, `a="éa"`, a
UTF-8 byte offset2 differs from the source `Array Char` element index1.
The core iterator also resets after a success, whereas the book returns
the first terminal pair. Reuse these proofs and implementations through
explicit specializations/refinements, not an unchecked name match.

## Exhaustive coverage checklist

`isNext p j k` refers to the source's shifted proper-border predicate.
All array reads mentioned in executable rows require bounds; mathematical
source statements with underspecified reads receive the explicit domain
adaptation above. Bounds involving subtraction use natural subtraction
only after the invariant gives the necessary inequalities.

### Introductory claims, arrays and matches

| ID | Required object or checked statement | Source, premises and reuse/gap |
|---|---|---|
| C25-001 | Specify a faithful naive left-to-right alignment search, its earliest occurrence result, and the element comparisons made before advancing one alignment. | p.293 comparison algorithm. Its recurrence must be stated before assigning average/worst-case counts; no need to introduce Boyer–Moore. |
| C25-002 | Under a fixed pattern and independent uniform text symbols from a finite alphabet of size `q≥2`, a `k`-symbol prefix matches at one valid alignment with probability `q^(−k)`. | p.293 random-text/geometric-series assertion. State independence, fixed-pattern and distribution assumptions; alphabet cardinality alone does not specify a probability law. |
| C25-003 | Expected matched-prefix length is bounded by a geometric sum; expected comparisons at an alignment are at most `Σ(k<m) q^(−k) ≤ q/(q−1) ≤ 2`. | p.293 mathematical reasoning. Distinguish matching successes from the extra failing comparison. Truncation near boundaries can only reduce this bound. |
| C25-004 | Obtain an expected `O(n)` comparison upper bound for naive search by summing over at most `n` alignments; early success only lowers it. | p.293 “linear time” claim. Independence between overlapping alignments is unnecessary for linearity of expectation. Extend to a specified nonuniform iid law only with a maximum symbol probability strictly below1. No universal random-input claim is available without these premises. |
| C25-005 | Naive worst-case comparison upper bound is `O(mn)`; for distinct `x,y`, pattern `x^(m−1)y` and text `x^(n−1)y`, `1≤m≤n`, a full-fit-alignment implementation uses `m(n−m+1)` comparisons. | p.293 pathological example. This yields a quadratic family when `m` is proportional to `n`; the final alignment succeeds. Specify bounds/termination for `m=0`, `m>n` separately. |
| C25-006 | Preserve the KMP total `O(m+n)` claim and its worst-case `Θ(m+n)` reading for nonempty patterns over an alphabet with at least two symbols, under unit-cost array/equality primitives and linear initialization. | pp.293–294,304. It is not a pointwise lower bound for every input: first-occurrence search can stop early, and an empty pattern performs no text scan. Connect to actual loop counts below. |
| C25-007 | Array abstraction provides zero-based read, length, update and length-`m` constant initialization with exact list/Array correspondence. | §25.1 p.294; `Diff_Array` lines8–22,79–97. Standard Lean Array/Vector laws are value-level reuse. |
| C25-008 | Prove length preservation of updates, same-index/other-index lookup laws on valid indices, and initialization's length/value laws. | §25.1 and builder proof. Preserve optional/guarded invalid reads; no blanket `Inhabited α` assumption. |
| C25-009 | Model the single-threaded update discipline: only the newest table version is used after each update, and search performs no updates. | p.294. Retain a trace/property justifying the source's conditional efficient-array interpretation; arbitrary persistent access to old versions is not covered. |
| C25-010 | Separate the assumed constant-cost read/update/size primitive model from linear initialization and from any proved concrete backend realization. | p.294; difference-array archive has code-generator mappings, not Lean hardware cost proofs. State equality/index arithmetic costs as well. |
| C25-011 | `matches a i b j k` means `i+k≤a.size`, `j+k≤b.size`, and equality at every aligned offset below `k`. | §25.2 p.294; source `matches`, lines20–22. Bounds remain part of the relation, not external optional hypotheses. |
| C25-012 | Empty match iff both starting positions are at most their array lengths. | p.295; `matches_empty`, lines24–25. An out-of-range pair of empty extracts must not satisfy this predicate. |
| C25-013 | Prefix weakening: a length-`k` match yields every shorter match at the same starts. | p.295; `matches_right_weakening`, lines44–46. |
| C25-014 | Suffix weakening: a match of length `k` yields the length-`k−r` match at starts shifted by `r`, for `r≤k`; also derive the source subtraction-based variant with its arithmetic premises. | p.295; `matches_left_weakening_add`, `matches_left_weakening`, lines48–59. |
| C25-015 | Matches are symmetric between arrays and transitive through the same middle segment. | Lemma25.1/25.4 proofs pp.296,299; `matches_sym`, `matches_trans`, lines61–66. |
| C25-016 | A match extends by one when both successor positions are in bounds and the next symbols agree. | pp.298,302; `matches_right_extension`, lines27–33. |
| C25-017 | A symbol disagreement at any compared offset refutes a longer full match; include the first-offset special case. | pp.298–299,302–303; `matches_contradiction_at_first`, `matches_contradiction_at_i`, lines35–42. |

### Proper borders and the next table

| ID | Required object or checked statement | Source, premises and reuse/gap |
|---|---|---|
| C25-018 | `isNext p j k` is `k<j`, a length-`k` prefix/suffix self-match ending at boundary `j`, and absence of any longer proper border below `j`. | p.296; `is_next`, lines70–73. “Ending at `j`” means the half-open prefix boundary, not the character index included. |
| C25-019 | Proper-border existence/uniqueness for `0<j≤m`, strict fallback decrease `k<j`, and `isNext p 1 0 ↔ 1≤m`. | Definition and table construction; source `next_1_0`, lines115–116. Existence/uniqueness can reuse a proved prefix-function characterization. |
| C25-020 | Reconstruct the Figure25.1 pattern `xyzxyzxzxy` and shifted table `[0,0,0,0,1,2,3,4,0,1]`. | p.295; source `Knuth_pattern` example. A checked finite example should distinguish this layout from the usual unshifted full-prefix table. |
| C25-021 | **Lemma25.1:** from `matches a (i−j) p 0 j`, `isNext p j k` and `j≤i`, derive `matches a (i−k) p 0 k`. | p.296; `next_iteration`, lines75–84. Proof uses suffix weakening and transitivity, preserving truncated-subtraction conditions. |
| C25-022 | Prove the intermediate maximality statement: for `k<r<j`, the same text prefix cannot have an `r`-symbol match ending at `i`. | Lemma25.2 proof; `next_is_maximal`, lines86–96. |
| C25-023 | **Lemma25.2:** no full match starts at `s` satisfying `i−j<s<i−k` under Lemma25.1's premises. | p.296; `next_is_maximal'`, lines99–113. Formal `matches a s ...` uses a **start**, despite preceding prose saying “ending at” that position. |
| C25-024 | Establish a checked relation from the shifted source table to a conventional prefix-function table, and state the unused zero/full-border differences. | p.295 source layout versus existing KMP libraries. This is required if those implementations/proofs are used; equality of a final found index is not a table or step proof. |

### Table-building state, recurrence and invariant

| ID | Required object or checked statement | Source, premises and reuse/gap |
|---|---|---|
| C25-025 | Exact equality branch: write `j+1` at index `i+1`, increment both `i,j`, and return the updated table/state. | p.297; `buildtab_step`, lines120–124. One symbol comparison, one write. |
| C25-026 | Exact mismatch-at-zero branch: write0 at `i+1`, increment `i`, retain `j=0`. | p.297; same definition. Do not omit the zero write from a claimed exact operation count merely because initialization already placed0 there. |
| C25-027 | Exact positive-mismatch branch: retain table and `i`, replace `j` by `nxt[j]`. | p.297; same definition. This is a separate loop body with no text/pattern advancement. |
| C25-028 | Under builder invariant and `i+1<m`, all pattern/table reads and the possible write are in bounds. | pp.297–298. Pattern reads need `j<i<m`; table fallback needs `j<m`; write needs `i+1<m` and table length `m`. |
| C25-029 | First builder invariant conjunct: table length equals pattern length. | p.297; `buildtab_invariant`, lines127–133. |
| C25-030 | Index conjuncts: `i≤m`, `j<i`; record the stronger reachable-state fact `i<m` and the out-of-range final table-clause adaptation explicitly. | pp.297–298 and domain discussion above. Do not assign an unmentioned default to `nxt[m]`. |
| C25-031 | Partial-border match conjunct: `matches p (i−j) p 0 j`. | p.297; table-building invariant. |
| C25-032 | Completed table entries satisfy `isNext p k nxt[k]` for positive `k≤i`, with the source/Lean domain convention made explicit. | p.297; completed-prefix invariant. Actual executed states have `k<m`. |
| C25-033 | No candidate border longer than `j+1` and shorter than `i+1` matches the pattern prefix ending at `i+1`. | p.297; final invariant conjunct `∀k, j+1<k<i+1 → ¬matches p (i+1−k) p 0 k`. This is needed to justify maximality after a successful comparison. |
| C25-034 | For `m≥2`, zero table of length `m`, `i=1,j=0` satisfies the full builder invariant and the stronger safe index bound. | pp.300–301; `buildtab_invariant_init`, lines137–138. `m=0,1` are handled outside the loop. |
| C25-035 | A body preserves table length in all branches. | p.297; `length_invariant`, lines144–146. |
| C25-036 | Under the loop guard, a body preserves the upper bound for `i`, including safe strict `i<m` for reachable executions. | pp.297–298; `i_invariant`, lines148–151. |
| C25-037 | A body preserves `j<i`; fallback uses `nxt[j]<j`. | p.298; `ji_invariant`, lines153–163. Correct entries, not just a nonnegative table, justify decrease. |
| C25-038 | A body preserves the partial-border match conjunct in equality, zero-mismatch and positive-fallback branches. | p.298; `matches_invariant`, lines165–168; fallback uses Lemma25.1. |
| C25-039 | **Lemma25.3:** under invariant and loop guard, every positive table index at most new `i` satisfies `isNext` in the new table. | p.298; `is_next_invariant`, lines170–199. Equal branch proves the newly written positive border is maximal; zero-mismatch proves0 is maximal; fallback leaves prior entries intact. |
| C25-040 | **Lemma25.4:** under invariant, `m≥2`, loop guard and `j′+1<k<i′+1`, there is no length-`k` self-match ending at `i′+1`. | pp.298–299; `non_matches_invariant`, lines206–266. Preserve its three-branch proof and the corrected fallback bound, not the erroneous widened bound in the prose. |
| C25-041 | Recover the fallback proof's three subcases: `k>j+1` uses old exclusion; `k=j+1` uses the current mismatch; `k≤j` uses a shorter hypothetical match plus `isNext` maximality to contradict transitivity. | p.299; source lines238–261. Source correctly requires `k<i+1` when `i′=i`. |
| C25-042 | **Corollary25.5:** the complete builder invariant is preserved by each guarded body. | p.299; theorem `buildtab_invariant`, lines269–276. Combine the six conjunct proofs; `m≥2` follows from the valid-state/guard assumptions here. |
| C25-043 | Exact outer recursion calls one body and recurs when `i+1<m`, otherwise returns `nxt` unchanged. | §25.5 p.299; `partial_function buildtab`, lines286–292. The returned result is a table, not the final index pair. |
| C25-044 | Define the valid-state evaluation/termination relation and derive computation induction usable from the builder invariant. | pp.299–301; source `rel_buildtab m` is lexicographic `(m−i,j)` on the tuple's index fields, with `wf_rel_buildtab`. A partial recursive equation alone does not supply this induction. |
| C25-045 | In a recursive body either `i` increases by1 and `j` is unchanged/increases by1, or `i` is unchanged and `j` strictly decreases. | p.300; guard and table invariant supply the three cases. This is a statement about actual execution, not an invented cost sequence. |
| C25-046 | The nonnegative measure `2m−2i+j` strictly decreases on every guarded body; alternatively prove the source lexicographic decrease and relate the integer/Nat potential. | p.300; under `i≤m`, the natural expression agrees with the stated nonnegative integer quantity. |
| C25-047 | **Lemma25.6:** from the builder invariant, each positive `k<m` in its final table satisfies `isNext p k`. | pp.299–300; `buildtab_correct`, lines306–335. Termination/domain and safe index interpretation are explicit. |
| C25-048 | The builder preserves table length globally, so all final-table queries used by search are within bounds. | Supporting executable obligation, following `length_invariant` and C24-style finite-run induction. Source's displayed correctness only states border values; Lean dependent reads additionally need this length fact. |
| C25-049 | `table p` builds from zero initialization at `(1,0)` when `m>1`, otherwise returns a zero-filled array of length `m`. | p.300; `table`, lines338–342. Include exact `m=0,1,2` outputs and zero body count for `m≤2`. |
| C25-050 | **Equation25.1:** for `0<j<m`, `isNext p j (table p)[j]`; also retain table length `m` and fallback strictness. | p.300; `is_next_table`, lines344–348. No claim is made for the absent full-prefix entry at `j=m`. |
| C25-051 | Provide the invalid-state self-loop demonstrating builder nontermination, with corrected condition `nxt[j]=j`. | p.300; example below. Formalize it as a loop-state relation/counterexample, not by requiring a total executable function to diverge in Lean's kernel. |
| C25-052 | Preserve the logic explanation with its domain: Nat-valued `f(x)=f(x+1)` has constant solutions, whereas `f(x)=f(x+1)+1` has no Nat-valued solution on all natural `x`. | pp.300–301. This contrasts partial tail recursion with a non-tail accumulated time equation. It is false without a suitable well-founded output order, e.g. an Int-valued negative-linear function can satisfy the latter equation. |

### Builder time, single-threaded execution and backend boundary

| ID | Required object or checked statement | Source, premises and reuse/gap |
|---|---|---|
| C25-053 | Exact accumulated time recursion: guarded body updates state and increases accumulator by1; terminal branch returns that accumulator. | p.301; `T_buildtab`, lines353–358. It counts loop bodies/element equality tests, not function entries, all primitive operations, or physical allocations. |
| C25-054 | Measured builder erases to the same table/state evaluation, and final count is initial accumulator plus the number of executed bodies. | p.301 meaning of the cost function; derive from actual evaluations. An arbitrary tail-recursive solution on a looping invalid state is not a finite runtime. |
| C25-055 | Prove the accumulated-potential bound using guarded invariant preservation and decrease. | Source `T_buildtab_correct`, lines360–390. The resource proof must refer to the same branch decisions and table states. |
| C25-056 | **Lemma25.7:** invariant implies `Tbuildtab p nxt i j t ≤ 2m−2i+j+t`. | p.301; exact source inequality. Natural/integer casts need `i≤m`; do not charge an extra terminal entry. |
| C25-057 | For `m≥2`, initialized builder body count is at most `2(m−1)`; `m=0,1` bypass it. | p.301; `T_buildtab_linear`, lines392–395. This is a valid loose bound, not a claim of exact attainment. |
| C25-058 | Initialization plus bounded per-body primitive costs yields `O(m)` preprocessing; explicitly include `m` writes/initialization work and any equality tariff. | pp.294,300–301. A constant-time primitive model is a stated premise, not a theorem about an arbitrary persistent Array implementation. |
| C25-059 | Prove the table-use trace is single-threaded: every write consumes the current version for subsequent operations, and no old table version is queried later. | p.294 explanatory mathematical property. Source update models keep old-version undo information; reuse of old versions can make costs depend on chain length or copying. |
| C25-060 | If realizing difference arrays, give a checked logical-array representation and persistence/current-version access correspondence sufficient for C25-059; state the primitive-cost contract for the physical backing store. | §25.1; `Diff_Array.thy` uses list semantics plus target code mappings. No source proof certifies those target mappings' hardware costs. A standard Array adapter is a value realization, not automatically this data structure or cost theorem. |

### Search state, recurrence, invariants and correctness

| ID | Required object or checked statement | Source, premises and reuse/gap |
|---|---|---|
| C25-061 | Exact equality search body maps `(i,j)` to `(i+1,j+1)` after comparing `a[i]` with `p[j]`. | p.302; `KMP_step`, lines400–403. Table, text and pattern are unchanged. |
| C25-062 | Exact zero-prefix mismatch maps `(i,0)` to `(i+1,0)`. | p.302; same definition. No fallback read at table index0. |
| C25-063 | Exact positive-prefix mismatch maps `(i,j)` to `(i,nxt[j])`. | p.302. Repeats comparison at the same text position in the next body; it does not reread the whole already matched text prefix. |
| C25-064 | Search invariant index bounds: `j≤m`, `j≤i`, `i≤n`. | p.302; `KMP_invariant`, lines406–410. The body guard strengthens the required text/pattern read bounds. |
| C25-065 | Search invariant includes a prefix match `matches a (i−j) p 0 j`. | p.302. The candidate start is `i−j`; subtraction is exact because `j≤i`. |
| C25-066 | Search invariant excludes every full occurrence starting before `i−j`. | p.302; same definition. This is an earliest-match invariant, not merely existence of a current partial match. |
| C25-067 | Initial `(0,0)` satisfies all search invariant conjuncts for arbitrary text/pattern lengths, including empty ones. | p.303; `KMP_invariant_init`, lines414–415. |
| C25-068 | The body is memory-safe under invariant, `j<m`, `i<n` and the actual correct table's size/value laws. | p.302. A generalized arbitrary-table version needs both length and proper-border assumptions, not just numeric fallback bounds. |
| C25-069 | Equality and zero-prefix mismatch preserve index bounds, current match and earlier-start exclusion. | pp.302–303; source `KMP_invariant`, lines419–455. On zero mismatch, the failed current start is excluded explicitly. |
| C25-070 | Positive mismatch preserves the partial match by Lemma25.1 and excludes all skipped candidate starts by Lemma25.2 plus the current mismatching start. | pp.302–303; same source proof. Include the strict skipped interval endpoints. |
| C25-071 | Package complete search-invariant preservation for `KMP_step p (table p) a i j` under both loop guards. | pp.302–303; source `KMP_invariant`. No need to demand a symbol order. |
| C25-072 | Exact `search m n nxt p a i j`: while `j<m ∧ i<n`, execute one KMP body and recurse; otherwise return `(i,j)`. | p.303; partial source `search`, lines459–463. Cached `m,n,nxt` are not recomputed in the loop. Their equality to actual lengths/correct table is a correctness premise. |
| C25-073 | Prove termination for `m=p.size`, `n=a.size`, `nxt=table p` from the search invariant using either `(n−i,j)` lexicographic decrease or potential `2n−2i+j`. | pp.303–304; `rel_KMP`, `wf_rel_KMP`, `searchW_halts`. Arbitrary incorrect tables can loop. |
| C25-074 | `KMP_search p a` returns `search m n (table p) p a 0 0` as the terminal pair, including residual `j` on failure. | p.303; `KMP_search`, lines514–516. An optional index-only library result is a projection, not the same full observation. |
| C25-075 | Whole-run invariant plus terminal condition gives `j′=m ∨ i′=n`, all index bounds, and no further active body. | pp.303–304; needed for result decoding and absence correctness. Both equalities can hold simultaneously at a match ending at the text boundary. |
| C25-076 | Preserve the printed `first_occur p a r`: `r<n` implies a full match at `r`, and no smaller start is a full match. | p.303; `first_occur`, lines472–473. It lacks `r≤n` and is weaker than a complete optional-result specification; do not silently strengthen its definition. |
| C25-077 | Define exact numeric decoder `if j′=m then i′−m else i′`, and prove it lies in `[0,n]` for actual returned states. | pp.302–304. A failed search has `i′=n`; a successful empty pattern returns0. |
| C25-078 | **Lemma25.8:** starting from any search invariant state with the actual table/lengths, decoded terminal result satisfies printed `first_occur`. | p.304; `KMP_correct`, lines475–512. Termination and arithmetic bounds justify its computation induction. |
| C25-079 | **Corollary25.9:** decoded `KMP_search p a` satisfies `first_occur`. | p.304; source lemma `KMP_search`, lines519–523. Handles all finite lengths, not only nonempty patterns. |
| C25-080 | Supply the complete result bridge: `j′=m` iff a full occurrence exists; successful start is the least one; otherwise no occurrence exists. | pp.302–304 semantic intent. Derive from terminal invariant/range, not merely `first_occur` alone. |
| C25-081 | An explicit optional decoder returns `some (i′−m)` exactly on success and `none` on genuine absence; empty pattern returns `some 0` even on empty text. | Cross-cutting failure-interface adaptation of pp.302–304. Retain source terminal pair as a reconstruction observation. |
| C25-082 | Preserve the domain and counterexamples for the numeric failure sentinel and weak `first_occur` predicate. | p.303; examples below. For nonempty patterns, `r=n` represents failure; for empty pattern/empty text it coincides with success. |
| C25-083 | Prove literal state/step correspondence before using Batteries or core KMP to claim source execution; a final earliest-index theorem alone gives only an extensional adapter. | Library reuse section. Pattern/text byte encodings, shifted tables, extra preprocessing and early-rejection branches must be identified. |

### Search complexity, examples and formal-source alternatives

| ID | Required object or checked statement | Source, premises and reuse/gap |
|---|---|---|
| C25-084 | Instrument search by one unit per executed `KMP_step`, with terminal count0 or unchanged accumulator; erasure is the exact source terminal pair. | p.304 linearity assertion. Main AFP theory has builder time functions but no corresponding `T_search`; this mathematical obligation remains to be formalized. |
| C25-085 | Under the search invariant and correct table, potential `2n−2i+j` is nonnegative and drops by at least1 per body. | p.304. Equality drops1, zero mismatch drops2, and positive fallback drops `j−nxt[j]≥1`. |
| C25-086 | From `(0,0)`, at most `2n` search bodies/equality comparisons execute. | p.304 stated bound. Link the inequality to the measured/evaluation recurrence C25-084 and include `n=0`. |
| C25-087 | Correct the printed claim of exact `2n` attainment: for `n>0`, the actual first-occurrence loop uses at most `2n−1`; pattern `xy` against `x^n`, `x≠y`, attains this stronger bound. | p.304 tightness assertion. Formalize the corrected upper bound and witness as a visible source disposition, while retaining the valid weaker printed bound. |
| C25-088 | Combine source table initialization, builder and search counts into a total linear upper bound with named primitive tariffs; state worst-case lower witnesses needed for `Θ(m+n)`. | pp.293–294,304. Early success invalidates an unqualified per-input lower bound in `n`; empty-pattern behavior is separate. |
| C25-089 | Preserve the source's pathological-prefix example and show the algorithm advances the candidate start without rescanning the already established prefix. | pp.293–295. Do not interpret this as never comparing the current mismatching text element against multiple pattern positions. |
| C25-090 | Checked executable examples cover empty/trivial patterns, immediate and boundary matches, absence, overlaps, proper-border fallback chains and the Figure25.1 table. | Chapter examples and source `Knuth_pattern`, `CLR_pattern`, `bad_list`. Small parameterized regressions suffice; reproducing the source's multi-million-symbol evaluation literals is not a chapter proof requirement. |
| C25-091 | The source's optional while-loop builder/search versions may serve as partiality adapters only after proving their valid-domain correspondence with the tail-recursive definitions and measured counts. | Companion `buildtabW`, `buildtabW_halts/correct`, `T_buildtabW_*`, `searchW`, `searchW_halts`, `KMP_correctW`, `KMP_searchW`. These are alternative formal-source support, not separate book algorithms required in addition to a checked equivalent realization. |
| C25-092 | Preserve deterministic correctness independently of alphabet size/randomness; probability assumptions belong only to C25-002–004. | Entire chapter. A fixed finite byte specialization does not alone cover arbitrary equality arrays. |
| C25-093 | Record target-code boundary: source logical difference arrays are wrapped lists; SML/Scala realize current/undo versions, while inspected Haskell mapping uses ordinary functional arrays. | `Diff_Array.thy` lines8–22,545–591,595–795,799–1091. The filename is not proof that every backend meets constant-time update assumptions. |
| C25-094 | Keep historical/implementation discussion as identified analysis, while preserving mathematical assertions, explicit source defects and conditional runtime statements as checked obligations. | Chapter Notes p.304 and cross-cutting decisions. No external paper is imported wholesale, and no unfinished conjecture is reclassified as a promised proof. |

## Explicit source corrections and counterexamples

1. **Start versus end, p.296.** Lemma25.2 excludes a full occurrence
   whose **starting** index lies in the skipped interval. The preceding
   prose calls it an ending position, but `matches a k p 0 m` starts at
   `k`. Preserve the formal lemma and correct the explanatory sentence.

2. **Fallback-case upper bound, p.299.** In the positive-mismatch case
   of Lemma25.4, `i′=i`. The required bound remains `k<i+1`; the proof
   text incorrectly widens it to `k<i+2`. This is a false intermediate
   assertion, not a harmless extra case. For example, let
   `p=[0,1,0,2,3]`, `nxt=[0,0,0,1,0]`, `i=3`, `j=1`. The builder
   invariant and loop guard hold; the mismatch falls back to `j′=0`.
   The erroneous range admits `k=4`, but
   `matches p (i+1−k) p 0 k = matches p 0 p 0 4` is true.
   The source proof correctly assumes `k < Suc i` at its fallback
   subcase. Retain the corrected bound and check this counterexample.

3. **Nontermination example, p.300.** The unchanged fallback needs
   `nxt[j]=j`; the book instead writes `p[j]=j`, which is not even
   type-general for arbitrary alphabet values. With Nat pattern `[0,1]`,
   `i=0`, `j=1`, the table `[0,1]` makes the guarded state repeat.
   For the same pattern/indices and table `[0,0]`, the printed pattern
   condition still holds but the state changes and the run terminates.
   Thus the printed premises alone do not imply the claimed loop.

4. **Builder invariant's out-of-range terminal clause, p.297.** The
   permitted case `i=m` asks for `nxt[m]` in a length-`m` table. This
   does not occur in the actual initialized run, whose `i` remains below
   `m`, but it matters when translating the invariant as a general
   predicate. Bound the clause or strengthen the reachable-state domain
   and prove the source-facing implication explicitly. A default0 read
   is one possible separate totalization, not the source's specified
   behavior outside valid indices.

5. **Failure sentinel and weak specification, pp.303–304.** Empty
   pattern and empty text yield terminal `(0,0)`, so `j=m` and the
   source decoder returns0. It is a successful empty match even though
   `r=n`. Conversely, for absent nonempty `p=[1]`, `a=[0]`, the
   printed `first_occur p a 2` holds although2 exceeds text length1.
   Actual search returns1; range and complete success/failure facts
   must accompany the printed theorem. Use an optional result adapter
   to avoid ambiguous sentinels without changing source reconstruction.

6. **The `2n` tightness claim, p.304.** The upper bound is correct;
   positive-length exact attainment is not. If a nonzero run ends with
   `j≥1`, terminal potential is at least1. If it ends at `j=0`, its
   final consuming step is a zero-prefix mismatch and drops potential
   by2. In either case, for `n>0`, count is at most `2n−1`.
   Pattern `xy` and text `x^n`, with distinct symbols, attain
   `1+2(n−1)=2n−1`: the first `x` matches, and each later `x`
   causes one fallback mismatch followed by one match. This is the
   corrected exact worst-case witness; the bound and witness need Lean
   proofs, not just this reasoning.

7. **Meaning of the total `Θ` claim, p.294.** If the pattern matches
   immediately at the text's start, this first-occurrence implementation
   inspects only the initial pattern-length segment. For empty pattern,
   it inspects no text at all. Thus `Θ(m+n)` is valid as a suitable
   nonempty-pattern worst-case running-time statement over an alphabet
   with two distinct symbols under the source's primitive assumptions,
   not a lower bound for every run. Keep the
   universal upper bound and the separately quantified worst-case lower
   family. This preserves the mathematical claim with its necessary
   execution domain rather than imposing unnecessary scanning.

The stated finite examples and resource reasoning are source-audit
evidence, not completed Lean results. Any genuine false statement should
receive a checked small counterexample alongside its corrected theorem.
Printed syntax/terminology corrections should retain their locations and
the exact source declaration used for reconstruction.

## Difference arrays and runtime interpretation

The inspected array theory's logical carrier is `Array (List α)` with
list indexing/update. The generated SML realization uses a current mutable
array plus undo cells for old versions; reading an old version may follow
undo links, and updating it can realize a copy. The Scala mapping is
similar. The Haskell section explicitly uses ordinary functional arrays
instead of its older difference-array mapping. These are implementation
facts at the pinned revision, not a proof that any target has the same
runtime as the abstract chapter model.

For this chapter, the table builder's single current-version chain and
the search's read-only use are the relevant properties to formalize.
A concrete alternative with proved value semantics can satisfy the
algorithmic contract. A source-facing constant-time update theorem must
also identify the single-threaded use condition and primitive-store cost
model; an equality of arrays does not establish a copying or allocation
bound. No global runtime axiom should be introduced to conceal this
boundary.

## Completion boundary

Chapter25 acceptance requires the exact source builder/search behavior
or checked recurrence refinements, proper-border and skipped-range
proofs, valid-domain termination, table size and read safety, earliest
occurrence and absence specifications including empty inputs, both loop
count proofs, precise average/worst-case claims, and visible source-error
dispositions. Existing byte-string or generic KMP code can reduce work,
but only the proved matching interfaces count as reuse. The inventory
does not change validation or independent-review requirements.
