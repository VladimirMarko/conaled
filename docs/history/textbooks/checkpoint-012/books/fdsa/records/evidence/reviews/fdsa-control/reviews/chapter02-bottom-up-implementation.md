# Bottom-up and tail-pass value implementation

Worker handoff within the existing active Chapter 2 implementation loop,
4 November 2026. The two value files passed focused compilation and their 87
public declarations passed the recorded statement inspection at cumulative
development candidate `98696d86162bd93c1cba46719eeb65bf6cabe65a`. The later
sections retain every failed attempt, correction and exact evidence identity.
The separately authorized comparison layer is committed as the uncompiled draft
`7f17c441eba102bbb93c3193f6f1d800ff39f578`, described below. This author
report is not an independent Standards or Spec approval, a complete candidate
check, or accepted coverage.

Worktree: `conaled-ch02-bottom-up`, branch `work/fdsa-ch02-bottom-up`.
Accepted starting base: `07e480f6ec9958d4975bb90151005b84f2907614`.
The original value draft uses only existing accepted sorting modules and pinned
standard dependencies. Its source does not import other Chapter 2 drafts or
the unaccepted shared-foundation candidate. Root subsequently authorized the
explicit development-only dependency fast-forward recorded below and two new
comparison files. Ownership now covers `Applications/Sorting/BottomUp.lean`,
`Examples/BottomUpSorting.lean`, `Applications/Resources/BottomUpSorting.lean`,
`Examples/BottomUpCosts.lean` and this handoff. Public root imports, chapter
coverage and acceptance remain with root.

## Source and implementation decisions

The worker read the actual pinned PDF's extracted Chapter 2, section 2.5
(printed pp.19–21) and Exercise 2.6 (printed p.29), together with the 112-item
obligation inventory, requirements, mergesort proof/reuse plans and scope
reconciliation. The recovered PDF hash was checked as
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The external source is at `research-source/functional_data_structures_algorithms.pdf`
beside the restored workspace; no extra copy is introduced into the repository.

The worker read `AGENTS.md`, the implementation and review-loop instructions,
the example-driven-development skill including its worked example, architectural
quality/domain guidance, `GLOSSARY.md`, the ADR index and applicable module/audit
ADRs. This is continuation of the assigned implementation subset, with no new
shared unit or enclosing review workflow.

`mergePairsBy` is the literal three-case adjacent-pass recurrence. It keeps
an unpaired final run and combines pairs with canonical `List.merge`.
`mergeAllBy` returns the empty list or sole run at its two base cases and
otherwise recurses on that actual adjacent pass. Its decreasing measure is
the outer run count. `sortBottomUpBy` passes the singleton-run initialization
to `mergeAllBy`.

`mergePairsRevBy` is the permitted append-free tail recurrence. Its empty case
returns the arbitrary accumulator; its singleton case conses that last run;
its two-run case tail-calls itself with the completed merge consed onto the
accumulator. The operation itself contains no append or reverse. Its exact
proposed invariant is:

```
mergePairsRevBy cmp acc xss = (mergePairsBy cmp xss).reverse ++ acc
```

This reverses the outer list of completed runs, not the elements of individual
runs. `mergeAllRevBy` repeatedly calls the tail pass with an empty accumulator;
`sortBottomUpRevBy` initializes it with singleton runs. Their separate value
recurrences are retained. No equality between either pair of whole algorithms
is asserted for arbitrary payloads.

## Proposed source-obligation coverage

These are proposed theorem connections, all still awaiting focused compilation
and the later full chapter gates; they are not tracker closure claims.

| Source obligations | Draft connection |
| --- | --- |
| C02-040–043 | Literal ordinary pass, repeated-pass and singleton-run definitions; public base/step equations; exact ceil-half run count and strict decrease for at least two runs. |
| C02-044 | `multiset_flatten_eq_sum` connects the standard multiset of flattened runs to the standard list sum of inner multisets. No new multiset carrier or accounting foundation. |
| C02-045–047 | Comparator-generic flattened permutation, multiset and length laws for pass, repeated pass and initialized sorter. |
| C02-048–050 | Each-run sortedness preserved by the pass; sorted result from sorted input runs; sorted singleton-initialized result, all with input-local comparator compatibility. |
| C02-054 | `mergePairsBy_uniform_length` retains `Even xss.length` and uniform input length `m`, concluding output lengths `2*m`. Empty runs and `m=0` are allowed. |
| C02-074 | Flattened total length preserved; `mergePairsBy_sum_lengths` also exposes the equal sum of run lengths. |
| C02-105 value/termination part | Actual tail pass/repeated pass/sorter, arbitrary accumulator value law, strict run-count decrease, permutation/multiset and sortedness. The comparison-complexity part remains pending. |
| C02-106 value/support part | Exact arbitrary-accumulator run count, additive flattened multiset and flattened total length; repeated tail pass multiset. Its resource comparison remains pending. |

## Static statement review

The permutation, multiset, run-count and total-length theorems take an arbitrary
Boolean comparator and no order, payload equality decision, injective key map
or inhabitance hypotheses. They compose the actual `List.merge_perm_append`
law through adjacent recursion and repeated passes. The standard multiset
observation retains all occurrence multiplicities.

The pass sortedness theorem observes keys through `[LE κ]` and
`[Std.IsPreorder κ]`, assumes every original run is sorted, and requires the
two comparator branch implications only on members of the original flattened
input. For a recursive pass those membership hypotheses are recovered from
the actual permutation. No global comparator law is added implicitly. The
ordinary keyed specializations require decidable key comparison and
`Std.IsLinearPreorder` on keys. They package sortedness and permutation;
neither is mislabeled as a stable-sort contract.

The arbitrary accumulator value/permutation/multiset equations require no
sortedness at all. The tail-pass each-run sortedness statement separately
requires sorted accumulator runs because they are retained unchanged; it
does not impose cross-run ordering or comparator assumptions on accumulator
members that are never compared by this pass.

The run-count proof counts empty inner lists as runs, preserving the source
termination measure. The uniform-length proof retains the evenness premise.
A single unsorted run remains unchanged by the repeated-pass base case, so
the each-run sortedness premise cannot be removed. No comparison-count,
allocation, stack-space or asymptotic fact follows from these value and length
statements.

## Connected cases and counterexamples

The examples use the public recurrences and laws, with independent expected
data or observations:

- A five-run ragged input includes an empty run, unequal run lengths, two
  occurrences of 2 and an unpaired final run. Its expected adjacent-pass value
  is `[[1,2,3],[0,4],[2,5]]`; law clients separately observe three output runs,
  seven flattened elements and multiplicity two for 2.
- Four equally sized runs exercise the evenness-dependent doubling law.
  Three singleton runs refute the version without evenness. Four empty
  runs have two output runs and zero elements, distinguishing the measures.
- The single unsorted run `[2,1]` refutes sortedness without the source premise.
  The five-element duplicate sorter cases use independent expected sorted
  lists plus permutation uniqueness, for both ordinary and tail variants.
- The accepted nonnegative-domain comparator and its existing local evidence
  exercise both new input-local sortedness laws. Existing signed-key records
  exercise the tail sort correctness contract. Arbitrary payload and constant
  false-comparator clients retain permutation and length without order laws.
- A nonempty accumulator `[[99],[],[42,43]]` checks its exact final position
  after reversed merged runs, six outer runs and ten total elements. An
  unsorted accumulator `[[9,0],[],[7]]` uses the unconditional multiset law.
- Arbitrary payloads at equal key 0 give ordinary output `first,middle,last`
  and tail output `last,first,middle`, by the actual recurrence equations.
  Distinct string payloads then refute stability of the tail sorter using
  the complete equal-key filter observation. A separate three-run example
  refutes equality of the ordinary pass and empty-accumulator tail pass.
- Empty payload type and arbitrary singleton payload clients show that no
  default value, payload order or payload equality decision is required.

## Validation and outstanding work

No Lean compiler or builder has been invoked by this worker. Root has qualified
the pinned native environment and has retained the build hold. The full source
was read back and the statements checked against the pinned obligations. Static
search found no admissions, axioms, unsafe declarations, external implementations
or native decision procedures in the two files. Elaboration, dependency/import
closure and the complete candidate audit are still unestablished.

The first draft remained uncommitted through checkpoint0083 and the assigned
independent foundation/XM01 source reviews. Root then released implementation
preparation and an owned-file draft commit, while retaining the build hold.
The unchanged first two-file draft was committed as
`101aaa6f94f75af35d339746bff44305840373fe` on `work/fdsa-ch02-bottom-up`,
directly after the accepted starting base. The commit contains exactly the two
owned Lean files, 629 added lines. Their identities remain:

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| `Applications/Sorting/BottomUp.lean` | 19,658 | `ae9c015b9391907737db661f55fa585a75c33aa6e76c23d3773dfc057e71ee1b` |
| `Examples/BottomUpSorting.lean` | 8,400 | `994b870e6f446d9eae5153c3e1511581b683e80e5473d2c5f99665ff04c56637` |

The tracked working tree and index are clean. The unrelated pre-existing
`docs/history/algorithm-design-haskell/.checkpoint-233.zip.EA8xCS` remains
untracked and untouched: 23,068,672 bytes, SHA-256
`c6795852cc57d6210e2fbe7d509a10c4e3caf5cfe3fce4d9c32983ba45193711`.
Its presence means this checkout is **not** clean for a candidate recorder or
acceptance check. It was neither staged, removed nor ignored. An isolated clean
candidate or an explicitly recorded authorized preservation move is needed
before those checks. No acceptance exclusion has been silently introduced.

The first commit command stopped because the recovered repository had no Git
author identity configured. No commit was created by that failed command. The
second command used only per-command `user.name=ChatGPT` and
`user.email=chatgpt@localhost`, matching the existing worker draft identity;
it did not modify global or repository Git configuration.

The following remain explicit: C02-051–053 and C02-055–057 comparison formulas
and bounds; the comparison-equivalence/additive formula and same-complexity
part of Exercise 2.6/C02-105–106; integration with the actual measured merge
after that shared dependency passes; subsequent natural-run composition and
its separately required operational claims; complete chapter validation,
independent Standards and Spec reviews, immediate immutable-candidate
verification, and accepted-branch integration. No stability theorem for either
new sorter is claimed from value agreement. The selected C02-107 top-down
stability work is a separate component.

## Comparison-layer preparation after the draft commit

This is a bounded implementation design, not new compiled declarations or a
relaxation of the outstanding resource obligations. The worker reread the
entire frozen Chapter2 requirements, all 112 current obligations and the scope
reconciliation, then read exact XM01 candidate
`72a0951aee406f7db67998d2a3bf8810f4e1bccc`'s `Resources.ListMerge` and unchanged
`Resources.Measured` APIs through Git objects. Its focused checks and independent
source assessment do not make XM01 an accepted dependency. **At this preparation
stage the bottom-up branch had no XM01 or top-down-cost dependency incorporated.**

The natural next module is `Applications/Resources/BottomUpSorting.lean`, with
connected clients in `Examples/BottomUpCosts.lean`. It should retain `Measured`
and `bind` and project `ListMerge.run` through `reweight Prod.fst` to count only
the required head comparisons. Empty/singleton pass and repeated-pass cases use
zero comparison cost. No function-entry, singleton-map, outer-list traversal,
cons, reversal, append or allocation charge is inserted into this printed
counter.

The proposed actual adjacent-pass execution first binds the measured merge of
the first two runs, then the measured pass on the remaining runs, and constructs
the output from both returned values. The tail execution binds that same measured
merge and tail-calls itself on the actual returned run consed onto the arbitrary
accumulator. Its recursive definition contains neither append nor reverse.
The scalar equations must be derived from these executions, not used as an
unconnected second algorithm. The tail pass's cost is independent of the old
accumulator and equals the ordinary pass cost; its value is the reversed list
of completed runs followed by that accumulator.

Each repeated-pass execution must recur on the actual measured pass's returned
run list. A local binding of that measured pair exposes its first projection
for the decreasing-measure proof, using the value erasure theorem and existing
strict run-count decrease. The callback must not introduce an unconstrained
arbitrary next run list or substitute a differently ordered pure pass. A shared
local binding also avoids executing the measured pass twice merely to recover
its value and cost.

The reusable bound route is one comparison bound per pass by flattened total
length, exact preservation of that length, exact ceil-half run count, and the
pinned `Nat.clog_of_two_le` recurrence. This yields for each repeated-pass
variant `comparisons ≤ xss.flatten.length * Nat.clog 2 xss.length`, including
zero/singleton outer lists and any number of empty inner lists. Uniform run
length then gives C02-055 without evenness; the power-of-two specializations
give C02-056/057 with `m=0` and `k=0` retained. The separately required uniform
output-length doubling theorem continues to require evenness. The natural-run
composition can consume the same general bound for C02-073–076. The existing
Growth extension being compiled by root supplies the intended ceiling/real-log
correspondence; it must be incorporated by exact identity before use, rather
than independently copied or assumed to be accepted.

Retain these independent cost cases alongside the previously recorded value
cases: the ragged five-run pass costs exactly 2 comparisons; a long sole run
costs zero; multiple empty runs cost zero despite outer traversal; and three
equal singleton runs have the same first-pass cost 1 but complete ordinary/tail
costs **3 and 2**. A nonempty accumulator must retain the same first-pass cost
as the empty accumulator. The three-equal case prevents an unjustified transfer
of exact total counts from per-pass equality, while both total algorithms can
satisfy the same logarithmic bound. These remain proposed Lean expectations;
the current draft commit contains no comparison theorem or empirical count
claim.

Root must explicitly incorporate the recorded XM01 prerequisite and any shared
Growth extension into the development branch before authoring/importing this
layer as an integrated module. That development composition will remain
unaccepted until the existing full Chapter2 gates pass. The immediate next
compiler task is the two-file value draft, once root releases the one private
cache. No compiler or cache was touched during this preparation, and the frozen
foundation/XM01 review candidates and historical reports are unchanged.

## Focused attempt1 and proof-only correction

Root ran the first two-target focused build in its exclusive compiler checkout
at exact value candidate `101aaa6f94f75af35d339746bff44305840373fe`. The preserved
`provenance/chapter02-bottom-up-focused-20261104-attempt1/result.json` records
actual **exit 1**, 22.135 seconds, completed at
`2026-11-04T04:48:33.515837+00:00`. The complete closed 4,463-byte log has SHA-256
`380e22d418718907ed7fde6d8d7b1a7bcef707a09815cf3d4ca79ba0fba0087a`.
The author read both complete records. No success or audit is inferred from
that failed build.

The resource-free core failed at the two `mergePairsBy_length` base proofs and
the induction step of `multiset_flatten_eq_sum`. The base `rfl` proofs did not
elaborate without the public pass equations. The multiset step attempted a
syntactic `List.map_cons` rewrite while elaboration had exposed a list-do/map
form for the coercions. No changed mathematical expectation was indicated.

The proof-only correction is committed at
`0f4ca66e85e510987393ae9a5066e4b45ef8422f`, parent `101aaa6`, with exactly one
changed owned file and 9 added / 3 removed lines. The base cases now rewrite
`mergePairsBy_nil` / `mergePairsBy_singleton` and list lengths, then prove the
closed natural arithmetic by ordinary `decide`. The multiset induction step
uses `change` to expose the definitionally corresponding append/coercion and
cons/sum shape before rewriting its original induction hypothesis. No
definition, theorem statement, premise, expected example, import or option was
changed. These correction scripts still require the next actual compiler run.

Current core source: 19,878 bytes, SHA-256
`18cd276d8a99c16cd5f24568a92d7effa2e2ef762acb051ce28b70af56f4b711`.
Examples remain exactly 8,400 bytes, SHA-256
`994b870e6f446d9eae5153c3e1511581b683e80e5473d2c5f99665ff04c56637`.
The entire small diff was read back and `git diff --check` passed before the
commit. The author checkout's tracked tree/index are clean and the unrelated
partial ZIP retains its recorded identity. No compiler or cache was used here.

The failed attempt's result also records four untracked insertion/top-down
value files in root's compiler checkout. They are not bottom-up source changes
and do not establish a clean-candidate check. Root will preserve them as tracked
inputs in a newly recorded cumulative Chapter2 development merge combining
`7fb7c3e` and this correction. That future exact source identity and its
diagnostics must be recorded separately; the original accepted full-review
base remains `07e480f`, and all original attempt evidence remains retained.

## Focused attempt2 and redundant-tactic correction

The next root-owned combined focused command used cumulative development
candidate `8cc255095e41288bf3093285ebd8ae3b506fc6dc` and targeted both bottom-up
and alternating modules/examples. Its actual result was **exit 1**, 48.184
seconds, completed `2026-11-04T04:54:00.380907+00:00`; final HEAD matched and
the final compiler-checkout status was clean. Its full 6,609-byte log has
SHA-256 `2fabaa95aa8fbf1810597c41e5a5806b887cf89a50b7ede0319ca58aa122d8a7`
and is retained with its result under
`provenance/chapter02-bottom-up-focused-20261104-attempt2/`.

The multiset correction elaborated. The only bottom-up diagnostics were
`No goals to be solved` at the two following `decide` lines: each preceding
`simp only` already discharged the base equation and arithmetic. Separate
alternating proof failures belong to root's assigned correction and were not
edited by this worker. This combined command remains a failed focused check,
without any full audit or candidate verification record.

Author commit `9918e4b4e0b909f239e7a0796cb98e316e4b7056`, parent `0f4ca66`,
removes exactly those two redundant `decide` lines and changes nothing else.
The core is now 19,856 bytes, SHA-256
`4df83022174bc4e5becfb441617624d57695158d69dc7241209ca077dc2c7791`.
The example file remains byte-identical to the original draft. The two-line
diff was read back and passed `git diff --check`; no local compiler/cache work
occurred. The unrelated partial ZIP remains untouched, and this correction
awaits root's next recorded cumulative-candidate build.

## Focused attempt3 and example recurrence correction

Root's next combined command ran at cumulative candidate
`b5516e43fcc43b26f92f7220002b4eff4d7ba59e`. Its actual result was **exit 1**,
16.346 seconds, completed `2026-11-04T04:57:35.004563+00:00`, with matching
final HEAD and clean final source status. The complete 7,585-byte log has
SHA-256 `b57bd2c42036b8ce3613469766df9687047db04f27778ed5830da8fe25421f3c`
under `provenance/chapter02-bottom-up-focused-20261104-attempt3/`.

**`Applications.Sorting.BottomUp` built successfully in that exact focused
run.** The combined command still failed: four remaining bottom-up example
proofs could not reduce the logical `List.merge` definition through direct
`rfl`, `change` or `decide`, and a separate alternating permutation proof
remained with root. This establishes focused elaboration of the value core,
not successful examples, full validation, audit or acceptance.

Author commit `0ec00a7f4a014bcafa362ba0ae3d1a97119178a1`, parent `9918e4b`,
changes only six proof lines in `Examples/BottomUpSorting.lean`. The ragged
pass value, generic ordinary/tail equal-key values, and pass-inequality proofs
now use `List.cons_merge_cons` plus the public empty-side simp equations after
their existing pass/repeated-pass recurrence steps. The worker inspected the
pinned public equations before this correction. Every declaration, premise,
expected output and the complete tail-stability counterexample is unchanged.

Examples now have 8,440 bytes, SHA-256
`45abc8fd198b9a8cae0ebce144326981f23cbc0aa79969ece82bc031739e9d4c`.
The successfully elaborated core remains byte-identical at 19,856 bytes /
`4df83022174bc4e5becfb441617624d57695158d69dc7241209ca077dc2c7791`.
The small proof diff was read back and passed `git diff --check`. No local
compiler/cache operation occurred and the unrelated partial ZIP was untouched.
The example correction awaits root's next recorded focused result.

## Focused attempt4 and the same example proof correction

The cumulative candidate for attempt4 was
`d404e2ad3164efe30d61504e71fd62bdff5b8929`. The combined focused command
returned actual **exit 1**, 21.904 seconds, completed
`2026-11-04T05:02:44.294055+00:00`, again with matching final HEAD and clean
final source status. Its closed 7,351-byte log has SHA-256
`46a4ced742ffcc57b9176038a2784fd4e984b927c733bb5576bc232cdd86285a`
under `provenance/chapter02-bottom-up-focused-20261104-attempt4/`.

Both algorithm libraries had built, but the command still failed. The only
remaining bottom-up example diagnostics were six unused-simp-argument errors:
the available public merge simp laws already discharged the branches, so the
explicit `List.cons_merge_cons` arguments were unnecessary. Root separately
owns the two alternating example lint diagnostics. These are continuations of
the same example elaboration/correction loop, not new independent reviews.

Author commit `1b705afef4601d955d3ed55b09e6abbec576905b`, parent `0ec00a7`,
removes exactly those six explicit arguments, preserving `natCompare` in its
two concrete cases. No definitions, statements, premises, expected outputs,
imports or lint options changed. Examples are now 8,304 bytes, SHA-256
`1d4a312363af87926c085f790ca7279273df050f40234c449e0e0fa9e5b5592b`.
The core's successful focused identity remains unchanged. The proof diff was
read back and passed `git diff --check`; no local builds/cache operations or
changes to the unrelated partial ZIP occurred. The next root-owned command
must establish the actual result for the newly recorded cumulative candidate.

## Focused attempt5 and complete bottom-up statement readback

The unchanged cumulative development candidate
`98696d86162bd93c1cba46719eeb65bf6cabe65a` passed root's four-target command
in **17.481 seconds, actual exit 0**, completed
`2026-11-04T05:04:48.989699+00:00`. Final HEAD matched and final source status
was clean. The complete closed 1,401-byte log has SHA-256
`cab1074b263d717c9f70b2cdfba694fddd43f282b853f74bfcbb83ebc7e63983`, under
`provenance/chapter02-bottom-up-focused-20261104-attempt5/`. Both bottom-up
targets passed; the two alternating targets passed in the same command. The
635 jobs include existing dependencies, not 635 new book results. Existing
module-import advisories remain visible. No linter or source policy was disabled.

Root's 126-declaration statement inspection on the same candidate subsequently
returned **actual exit 0**, 38.091 seconds, completed
`2026-11-04T05:07:47.990828+00:00`, with matching clean final source. Its full
41,284-byte log SHA-256 is
`3296e4ba5330af5a1e1d6897ea7acb9898452def68510df2e9c343e70c1180b8`, under
`provenance/chapter02-bottom-up-alternating-types-20261104/`. The inspection
source has SHA-256
`9ef7e05799ff059a262fc1cab1ffaae1ed269b1076931c44a6913bd6e2dda471`;
`provenance/chapter02-bottom-up-alternating-statement-source-20261104/identity.json`
retains all names and exact source hashes.

The author read back **all 87 bottom-up public declarations** in that log:
59 library interfaces and 28 example declarations, together with both complete
source files from the exact Git candidate and the inspection source. The
private singleton-run flatten helper was also read in the source; this public
type inspection is not an exhaustive declaration/axiom audit. No contract
issue was found. In particular:

- Raw algorithms, permutations, multiset/length/run-count laws and arbitrary
  accumulator equalities have no hidden order, equality-decision, inhabitance
  or payload-instance requirement and retain universe-polymorphic payloads.
- Sortedness interfaces retain independently universe-polymorphic keys,
  `Std.IsPreorder` with input-local comparator compatibility, and each-run
  sortedness. The concrete key comparator needs `Std.IsLinearPreorder` and
  decidable key comparison, without payload antisymmetry or equality.
- Uniform length doubling retains evenness, whereas occurrence and total-length
  preservation do not. Empty inner runs remain counted by the termination
  measure. The multiset sum elaboration has the intended list coercion/map
  meaning and retains all occurrences.
- The tail invariant reverses only the produced outer run list, then appends
  the arbitrary accumulator in the theorem. The actual tail definition uses
  cons and recursion. Its sortedness premise concerns accumulator runs
  individually and does not demand comparator compatibility on untouched
  accumulator elements.
- The independent ragged, duplicate, unsorted-single-run, empty-payload and
  arbitrary-payload examples retain their expected data. Equal-key output
  order differs exactly as specified, and the tail stability counterexample
  is a negation of the full retained equal-key filtering contract.

These are author statement-review observations. They do not replace either
independent review axis. Neither successful focused command produced a full
verification record or an exhaustive audit. Full C02 scope, source/public
coverage, integrated checking, both independent final reviews, immediate
verification and accepted-branch integration remain pending.

## Authorized development dependency incorporation

After the preceding readback root authorized a **development-only fast-forward**
of `work/fdsa-ch02-bottom-up` from
`1b705afef4601d955d3ed55b09e6abbec576905b` to exact
`98696d86162bd93c1cba46719eeb65bf6cabe65a` for the next comparison slice.
`git merge --ff-only` succeeded. Read-only ancestry checks confirmed that the
original accepted base `07e480f`, original XM01 candidate `72a0951`, and prior
author tip `1b705af` are ancestors. No conflict resolution or source edit was
part of this fast-forward; the two bottom-up value files retained their checked
hashes. The tracked working tree/index were clean afterward. The unrelated
23,068,672-byte partial ZIP remained untouched at its same recorded SHA-256;
the author worktree therefore remains unsuitable for a clean-candidate recorder.

The explicitly incorporated dependencies include exact `ListMerge.lean`
SHA-256 `df38ab6fd95baca45be4c5f7e6cd86f4e168fbff0ab21899783c8b52a41d1975`,
the shared `Growth.lean` extension SHA-256
`99be17f2d45ac30de1e912c2181460dac046c8b98e40ea3209abfec342107786`, and the
top-down resource module SHA-256
`26531f25e57c0d198fc90d0a10652051ac6159098f493629af3283b54ab687bc`.
Their development inclusion does not claim foundation/XM01/Chapter2 acceptance.
The accepted full-chapter review base remains `07e480f`; root owns future
immutable candidate checks. No local compiler or dependency cache was used.

## Actual comparison implementation draft after checkpoint0085

Root saved/exposed checkpoint0085, then explicitly released the two-file
comparison implementation. Author commit
`7f17c441eba102bbb93c3193f6f1d800ff39f578` is a direct child of development
parent `98696d86162bd93c1cba46719eeb65bf6cabe65a`. It adds exactly:

| File | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `Applications/Resources/BottomUpSorting.lean` | 503 | 23,066 | `730bf51f45a8c492e9c3c9da4dd0ea7fcd43ac81c787d87241984680c02846a6` |
| `Examples/BottomUpCosts.lean` | 241 | 11,905 | `a242d7219d9221b0c085ff2107a40f9532d995bc5326de5a1c7cdcfaa4263aa1` |

The 76 public resource declarations, its one private length helper and the 29
public example declarations are source inventory counts, not checked/audited
declaration counts. All 105 public names and exact file identities are retained
in `provenance/chapter02-bottom-up-costs-author-draft-20261104.json`, SHA-256
`44b6264da7c728e918ea49f747974557aaa98a88ab069733a51fa838a543d2e2`.
No compiler or cache was used by the author; these new proof scripts remain
**uncompiled**. Root owns the next immutable cumulative focused command.

### Executed observations and source correspondence

The worker reread the actual pinned book's §2.5, printed pp.19–21, and
Exercise2.6, printed p.29; the source-counter/readiness records and all 112
Chapter2 obligations remain the requirements. The general arbitrary-run bound
and integer-ceiling correspondence retain the separately recorded §2.6 / AFP
provenance. The inspected standard APIs include exact `Nat.clog_of_two_le`,
`Nat.clog_pow`, `Real.ceil_logb_natCast` and `Int.clog_natCast`. This draft
reuses the explicitly incorporated XM01 measured merge and shared Growth
extension rather than defining another merge, logarithm or resource framework.

`pairsRun` binds `reweight Prod.fst (ListMerge.run cmp xs ys)` for the first
actual pair, then the measured pass on the remaining runs, and conses the two
returned results. Its `pairsComparisons` projection has zero empty/singleton
cost and the exact source additive recurrence. `pairsRun_value` separately
identifies the previously checked value pass. The bound by flattened total
length uses the actual merge bound and needs no sortedness, comparator law,
evenness or uniform run sizes.

`allRun` captures one measured pass result with a local `let`, contributes its
cost once, and recurses on that same pair's first projection. The decreasing
measure uses value erasure and the checked ceil-half run count. Its public
step theorem expresses the corresponding `bind (pairsRun ...) (allRun cmp)`
equation. No unrelated or reordered value is substituted for the returned
input, and no second scalar sorter manufactures the count. The mathematical
measured model does not claim compiler-level sharing or runtime behavior.

`run` supplies singleton initialization. Public scalar recurrences and value
erasures remain separate. Each new raw execution/bound is universe-polymorphic
in the payload and requires no payload order, equality decision or inhabitant.
Only head comparisons are charged: dispatch, outer-list traversal, construction,
singleton initialization, accumulator cons, the comparator's implementation,
allocation and other machine costs remain outside this declared tariff.

For Exercise2.6, `pairsRevRun` executes the same actual pair merge and conses
its returned list onto the arbitrary accumulator before its recursive call.
The definition contains neither append nor reverse. Its exact whole-pair
correspondence is

```
pairsRevRun cmp acc xss =
  ((pairsRun cmp xss).1.reverse ++ acc, (pairsRun cmp xss).2)
```

The scalar equality is proved from the actual selected comparisons, for every
accumulator; it is not inferred from a value theorem. `allRevRun` repeatedly
uses an empty accumulator and its actual reversed output run list. Its cost
recurrence and total bound are separate from ordinary `allRun`. No theorem
asserts equality of their complete counts or transfers stable payload order.

### Proposed requirement destinations and statement review

Every row below describes source in the uncompiled draft, not accepted coverage.

| Obligations | Proposed public destination / retained premise |
| --- | --- |
| C02-051 | `pairsRun`, `pairsRun_value`, zero and `pairsComparisons_step` laws; actual first-pair comparison projection. |
| C02-052 | `allRun`, erasure and `allComparisons_step`; next argument is the actual pass result. |
| C02-053 | `run`, `run_value`, `comparisons_eq_all`; singleton initialization contributes no comparisons. |
| C02-055 / C02-073 | `pairsComparisons_le` and `_le_uniform`; uniform bound needs only the specified run lengths, not evenness. |
| C02-056 | `allComparisons_le_uniform_pow`; both uniform length `m` and run count `2^k`, allowing `m=0`, `k=0`. |
| C02-057 | `comparisons_le_of_length_pow`, derived from the general bound; exact source power-of-two premise retained. |
| C02-075 | `clog_two_ceil_half`, `clog_two_source_half`, `int_ceil_logb_two_nat`, `int_ceil_logb_two_source_half`; source recurrence has `2≤n`, convention bridge includes zero and one. |
| C02-076 | `allComparisons_le_clog` and `_le_int_ceil`; arbitrary inner lengths and outer count, with totalized zero/singleton cases. |
| C02-105/106 comparison part | `pairsRevComparisons_eq`, whole-pair `pairsRevRun_eq`, exact tail recurrences and separate `allRevComparisons_le_clog` / `_le_uniform_pow` / initialized sorter bounds. |

The previously checked C02-054 evenness-dependent length-doubling theorem and
C02-074 total-length preservation are reused unchanged. Both actual merge trees
have the general `N * Nat.clog 2 r` bound, where `N` is the flattened length and
`r` the outer run count. This statement allows arbitrarily many empty runs.
Uniform and power-of-two bounds are consequences of that common proof shape,
not a claim that the two trees have equal work.

The integer-ceiling theorem is a direct checked-library correspondence target,
with integer-cast counts and total length. There is no hidden positive-run-count
premise. The unrounded real-log sorter corollaries retain the power-of-two
premise. The asymptotic theorems use the existing Growth bridge for actual
families whose `n`th input has length `n`; a descending Nat range family is the
concrete nonvacuous client. No asymptotic statement concerns compiled runtime.

Static statement review found no intended mathematical gap or false strengthened
claim. Actual elaborated types still require root's compiler/type inspection.
The first compiler run must resolve any proof elaboration issues, particularly
the captured measured-result termination obligations, quotient/coercion/log-cast
rewrites, and simplifier/lint details. Corrections must preserve all current
statements and independently expected observations unless a mathematical reason
is documented. No source policy or linter was disabled in this draft.

### Connected expectations

The new clients consume the execution/value/counter/bound interfaces, including:

- A long arbitrary sole run returns unchanged with zero comparisons; concrete
  `[2,1]` demonstrates that this says nothing about sortedness without the
  original run invariant.
- The ragged five-run pass returns `[[1,2,3],[0,4],[2,5]]` with cost **2**. A
  nonempty, unsorted accumulator is retained in the exact expected final
  position with the same cost. A universal two-accumulator client uses the
  public pass-count equality.
- Three equal singleton runs produce different run orders at equal first-pass
  cost **1**. Actual three-input sequencing gives complete ordinary cost **3**
  and reversed-pass cost **2**. Equal unlabelled results do not identify those
  counts. Arbitrary tagged payloads retain the expected `first,middle,last`
  versus `last,first,middle` outputs with those exact costs, and measured erasure
  preserves the existing concrete stability counterexample.
- A uniform odd pass has its cost budget while its leftover refutes unconditional
  doubling. Four empty runs specialize `m=0` to zero comparisons; an arbitrary
  long single run specializes `k=0`; four length-two runs obtain the printed
  budget **16**. The five ragged runs obtain the nonuniform budget **21**.
- The integer-ceiling bridge is used at zero and one; the source half recurrence
  is used at five; initialized singletons use the exponent-zero bound. Empty
  payload and arbitrary-comparator clients avoid hidden typeclass premises.
- Existing input-local comparator evidence supplies sorted returned values;
  raw occurrence and budget clients remain independent of those order laws.

### Current hold and remaining gates

Both new files were read back completely. Static inspection found no forbidden
proof form or trailing whitespace, and the staged `git diff --check` passed.
The commit contains only the two new files. Both previously checked value files,
all dependency/tooling files and the unrelated partial ZIP retain their prior
identities. The author tracked tree/index are clean after the commit; the
preserved unrelated file remains explicitly untracked. Source is now held for
root's actual diagnostic loop; no author builder is running.

The complete natural scanner/merger composition, its independent operational
builder model, all other Chapter2 cost/probability/source obligations, public
root/coverage integration, independent Standards and Spec assessment, full
candidate checks and exhaustive audit, immediate verification and accepted-tip
integration remain pending. The source and validation scope was not reduced.

## Bottom-up comparison focused attempt 1 and proof correction — 2026-11-04

Root's first comparison build closed on the immutable cumulative development
candidate `ccaee94222b78ac57e9a8ea23c6e86c056a19a23`. Its two bottom-up comparison
files match the original author draft
`7f17c441eba102bbb93c3193f6f1d800ff39f578`. The qualified native command used one
Lean thread and requested the two bottom-up comparison targets together with
six partition/selection targets. The complete record remains at
`provenance/chapter02-bottom-up-partition-focused-20261104-attempt1/`.

The actual result is **exit 1**, started `2026-11-04T05:34:29.997243+00:00` and
completed `2026-11-04T05:35:27.532811+00:00`, with recorded elapsed time
**57.535265859 seconds**. The final compiler-worktree HEAD equals the recorded
candidate and its final status is clean. The closed log is **10,268 bytes**,
SHA-256 `0377de6e8d754f38d17a8d283a826916af12f21158762407813835b68f795807`.
There is no candidate-verification record. These are focused development
diagnostics, not a successful full check, audit or acceptance.

All eight actual diagnostics in `Applications.Resources.BottomUpSorting` were
read. They concern proof elaboration only:

| Original location | Actual diagnostic | Bounded correction |
| --- | --- | --- |
| `int_ceil_logb_two_nat`, line 118 | Direct rewriting did not match the library's explicitly cast natural base `↑2` against the real numeral `2`. | Use the same library theorem with `simpa only [Nat.cast_ofNat, Int.clog_natCast]`, normalizing the numeral cast and integer ceiling-log cast. |
| `int_ceil_logb_two_source_half`, line 123 | The simplifier distributed a natural-number cast inside the right logarithm before the source correspondence could match. | Explicitly rewrite each complete ceiling expression using its precise natural input, then apply the source recurrence and the integer-cast addition equations. |
| `allRun_nil` / `allRun_singleton`, lines 144/148 | Rewriting the actual execution left `pure [] = ([], 0)` or `pure xs = (xs, 0)`. | Finish the residual definitional equality with `rfl`. |
| `allRun_step`, line 153 | Rewriting left the captured-pass-result continuation versus the public bind continuation. | Finish with `rfl`, reducing the actual `Resources.bind`; both continuations use precisely the same actual first projection. |
| `allRevRun_nil` / `allRevRun_singleton`, lines 371/375 | The reversed execution had the same residual `pure` equalities. | Finish with `rfl`. |
| `allRevRun_step`, line 380 | The reversed execution had the same residual captured-result/public-bind equality. | Finish with `rfl`; no reversed-pass definition or argument changed. |

The log also contains independent XQ01 partition diagnostics. Root owns their
correction; no partition/selection source was edited here. The resource module
failed before its new examples could be checked, so no success is claimed for
`Examples.BottomUpCosts` or for the remaining dependency-blocked targets.

The correction is the local commit
**`1e4b34bbb12d83a48678132c79243eefc5a9f4f2`**, directly after the original
`7f17c441eba102bbb93c3193f6f1d800ff39f578` draft. It changes only
`Applications/Resources/BottomUpSorting.lean`: 14 inserted and five removed
lines across eight proof scripts. The revised file is **23,175 bytes**, SHA-256
`74cc812fb1f1706621daeb1c51512a9ddb3d85dc57a36589aafe96e8514a6826`.
Every definition, theorem statement, premise and independently expected value
or comparison total remains unchanged. In particular the actual measured pass
still supplies the next recursive argument, the arbitrary-accumulator pass
count equality remains separate from the complete-sort bounds, and the
ordinary/reversed complete three-equal-key totals remain **3** and **2**.

The examples file remains **11,905 bytes**, SHA-256
`a242d7219d9221b0c085ff2107a40f9532d995bc5326de5a1c7cdcfaa4263aa1`.
The correction diff was read back in full and `git diff --check` passed before
the scoped commit. This is an uncompiled author correction awaiting root's
next immutable-candidate check, not evidence that the diagnostics are resolved.
No author compiler or dependency-cache operation was performed.

After the commit the tracked author tree/index are clean. The unrelated partial
ZIP remains explicitly untracked and unchanged: **23,068,672 bytes**, SHA-256
`c6795852cc57d6210e2fbe7d509a10c4e3caf5cfe3fce4d9c32983ba45193711`, at
`docs/history/algorithm-design-haskell/.checkpoint-233.zip.EA8xCS`. It was not
removed, staged, ignored or used as acceptance evidence. Original draft and
failed-attempt records remain intact. Source/ref writes are held for root's
next diagnostic or checkpoint instruction; the complete Chapter 2 scope and
all independent-review, full-check, exhaustive-audit, immediate-verification
and accepted-tip integration gates remain pending.

## Extended focused attempt 1: resource success and example correction — 2026-11-04

The next qualified, one-thread development check closed at the immutable central
candidate **`5d7a479549f5acd64a9e5adb418ab48780c238ef`**, with records at
`provenance/chapter02-extended-sorting-focused-20261104-attempt1/`. Its 12 named
targets combine the two bottom-up cost targets with partition/selection,
three-way quicksort and random-pivot targets. Both bottom-up cost source files
at this central candidate were compared byte-for-byte through `git show` with
author commit `1e4b34bbb12d83a48678132c79243eefc5a9f4f2`; both match exactly.

The enclosing result is **exit 1**, not a successful combined check. It started
at `2026-11-04T05:48:37.530289+00:00` and completed at
`2026-11-04T05:53:27.581996+00:00`, with recorded elapsed time
**290.051303003 seconds**. Its final HEAD matches the candidate and its final
status is clean. The complete closed log is **17,330 bytes**, SHA-256
`6ff459c43eade60da3fc4a15edd26da81c71ae5767be9b1a73253f0a29faad76`.
There is no candidate-verification record.

Within that failed enclosing attempt, the log explicitly records
**`Built Applications.Resources.BottomUpSorting (87s)`**. Thus the eight prior
resource proof diagnostics were resolved for that exact source/candidate under
the qualified environment. The module-system import advisory remains disclosed;
no linter, proof restriction or validation gate was disabled. This individual
module success does not establish the example target, combined target set,
complete candidate check, exhaustive audit or acceptance.

The complete `Examples.BottomUpCosts` diagnostics were four proof-elaboration
errors in two existing connected cases:

| Original location | Actual diagnostic | Minimal successor proof change |
| --- | --- | --- |
| `four_empty_runs_zero`, line 173 | `decide` rejected the free type variable in the length premise `[[], [], [], []].length = 2 ^ 2` for the ordinary uniform-power bound. | Replace only that length witness with `by rfl`. |
| `four_empty_runs_zero`, line 174 | The same free-variable diagnostic for the reversed uniform-power bound. | Replace only that length witness with `by rfl`. |
| `single_run_power_zero`, line 182 | The broad `simpa` was unnecessary because its simp set could close the singleton goal directly. | Restrict it to `simpa only [Nat.mul_zero, Nat.zero_mul] using` the ordinary public uniform-power theorem. |
| `single_run_power_zero`, line 183 | The same unnecessary-`simpa` diagnostic for the reversed singleton. | Use the same two-rule restricted simplification of the reversed public uniform-power theorem. |

The corrected zero-bound clients retain their intended public-theorem
connections. The `m=0` case still obtains both bounds for four empty runs and
then derives zero actual comparisons. The `k=0` case still specializes both
uniform-power bounds to an arbitrarily long single run. No generic payload,
comparator, run-count or uniform-length premise was removed or strengthened.
No expected list, cost, bound, algorithm or theorem statement was changed.
Other independent target failures remain the responsibility of their assigned
authors; none of those sources was edited here.

The minimal successor commit is
**`6e0f7f41540299b12ce09c91db408f83d20f9948`**, directly after
`1e4b34bbb12d83a48678132c79243eefc5a9f4f2`. Its full diff changes only
`Examples/BottomUpCosts.lean`, with **six inserted and four removed lines**.
The diff was read back in full and `git diff --check` passed before committing
with the existing per-command Git identity. The new examples file is
**11,979 bytes**, SHA-256
`221702bf831eb0c3d71a43030928b4b9a5a12d79177d9328c0242cddc654d1b2`.
The successfully built resource source remains **23,175 bytes**, SHA-256
`74cc812fb1f1706621daeb1c51512a9ddb3d85dc57a36589aafe96e8514a6826`.

No compiler or dependency-cache work was performed in the author worktree, and
there is no compiler result yet for this successor. The tracked author tree and
index are clean. The sole unrelated untracked partial ZIP remains unchanged at
**23,068,672 bytes**, SHA-256
`c6795852cc57d6210e2fbe7d509a10c4e3caf5cfe3fce4d9c32983ba45193711`.
The original draft, both failed enclosing records and the successful individual
resource-module evidence are retained without rewriting history. All author
source/ref/control writes are held after this handoff. The full Chapter 2 scope,
independent review axes, whole-candidate validation and exhaustive audit,
immediate verification and accepted-tip integration remain pending.

## Root continuation: singleton generic length witnesses — 4 November 2026

The closed focused attempt3 at d19a22d8654dde54b7a781b455ab3e3f37bf8589 returned exit1 in28.317976846s, clean unchanged source. Complete5338-byte log SHA2564ef07061c0ff20c58adf95b51146d4a54619b7196edc0120c18e5b7f6315080b and native record are secured. The only two remaining diagnostics are generic `[xs].length=2^0` witnesses using `decide`, exposed after retaining the public uniform-power applications. Root changed precisely those two proofs to `rfl` in the held author checkout; no algorithms/statements/cases or resource bytes changed. Successor a6f950d7d5dc4aef521445250f9bfbd59166291d was merged into clean development candidate 6d91b822d0f3cf1aeeda333a9e1d47ebb26e709b. Exact diff and identities: provenance/chapter02-bottom-up-costs-correction3-20261104/. Focused compilation and all later gates remain pending.

## Complete comparison source/type author assessment — 2026-11-04

After checkpoint 0087, the author completed the requested full readback of the
two comparison files and all **105** elaborated public statements: **76** in
the resource module and **29** in its connected examples. The complete
512-line resource source, including its private uniform-flatten-length helper,
and complete 243-line example source/proofs were assessed against the frozen
Chapter 2 requirements, applicable current source obligations, recorded scope
reconciliation and actual pinned book passages. The complete 462-line resource
type output and 450-line example type output were read, not sampled.

**Author source/statement findings: zero.** The dedicated assessment is
`provenance/chapter02-bottom-up-costs-types-20261104/author-readback.md`,
**29,643 bytes**, SHA-256
`63ee3063c90b5656738dd948597d9fcb70cf1462ea87cec633ae1e656ed5faa6`.
It contains a separate assessment row for every one of the 76 resource and
29 example declarations, exact source/output identities, requirement mapping,
execution/premise/boundary assessment, all actual failure history and explicit
remaining gates. The ordered table names were checked against the exact
inspection manifest; both inventories match completely.

### Successful focused and type evidence

Both new successful records use immutable central candidate
**`6d91b822d0f3cf1aeeda333a9e1d47ebb26e709b`**, with clean unchanged final source.
Their actual commands ran through the qualified native kit with one Lean thread;
both saved native records report exit 0, no timeout and no recorder error.

| Record | Actual terminal result | Complete closed log |
| --- | --- | --- |
| `chapter02-bottom-up-costs-focused-20261104-attempt4` | Exit **0**, **142.193826109 s**; both named cost targets pass. | **2,968 bytes**, SHA-256 `44df874a8351b38a24f564fe4a7ebfe0b3ff9289fdf393b367a8e654fc76a6a2`. |
| `chapter02-bottom-up-costs-types-20261104` | Exit **0**, **111.586157087 s**; all 105 explicit-universe/public type checks pass. | **69,695 bytes**, SHA-256 `b77970fe06b930f34286bcdb0e9a9ce1bdfbffceb2cdaf7f213cdf501137493d`. |

The successful focused log replays the earlier checked resource module and
builds the corrected examples in 126 seconds. Its 2,087 Lake jobs include
dependencies and are not a count of new formalization modules. Replayed
module-system import advisories remain disclosed. The exact full type-log
digest above was recomputed from disk and matches `result.json`; the report
records a harmless task-message digest transcription correction.

The held author tip remains
**`a6f950d7d5dc4aef521445250f9bfbd59166291d`**. Both assessed source files match
their checked central versions byte-for-byte:

- Resource source: **23,175 bytes**, SHA-256
  `74cc812fb1f1706621daeb1c51512a9ddb3d85dc57a36589aafe96e8514a6826`.
- Example source: **11,973 bytes**, SHA-256
  `12572e3395c681b18f266374732eb63b059a13eb0f76aef25400aefa8d54a136`.

The reused value files, `ListMerge`, `Measured` and `Growth` also agree between
the author and checked central commits. The 76/29 source public-name lists,
inspection manifest and full elaborated-output headings agree in order, and
both split outputs occur contiguously in the closed full type log. No Lean,
compiler, checker or dependency-cache operation was run for this readback.

### Contract conclusions and continued hold

Every generic payload interface retains its arbitrary universe and plain
Boolean comparator without a payload order, equality decision, default or
finiteness premise. Actual measured pair results supply subsequent values and
recursive run lists. The count recurrences remain projections of those
executions. General bounds use flattened payload length and outer run count
separately; uniform bounds keep exactly the uniformity/power premises and
include `m=0` and `k=0`. Integer-ceiling agreement includes zero and one; the
halving recurrence retains `2≤n`; real-log pointwise bounds retain the printed
power-of-two premise. Actual length-indexed families connect to the existing
Growth asymptotic bridge.

The append-free accumulator pass retains arbitrary-accumulator value and
comparison laws. Its count equality is proved independently of value erasure,
and complete reversed sorting has its own bound rather than false total-count
equality. The independently expected ordinary/reversed totals **3 versus 2**,
tagged payload orders and concrete instability witness are all present in the
elaborated types and source proofs. Ragged/empty/odd runs, a long unsorted sole
run, arbitrary and empty payload types, local comparator evidence and the
zero-bound public-theorem clients remain consequential connected cases.

Earlier failed aggregate records, the resource module's earlier individual
success, the final two generic-witness errors and root's precise `rfl` repair
are retained as history. No failure is relabelled as a pass. This is an author
statement assessment, not either independent final review axis or acceptance.
No full candidate check/audit or immediate verification record is supplied by
these focused commands. Public exposure/coverage, all remaining Chapter 2
obligations, independent Standards and Spec reviews, complete candidate
validation, exhaustive audit and accepted-tip integration remain pending.
No terminal outcome is inferred for the separate foundation check.

Only the dedicated report and this handoff were written. Author HEAD/source
are unchanged, the tracked tree/index are clean, and the unrelated partial ZIP
remains explicitly untracked with its recorded 23,068,672-byte identity and
SHA-256 `c6795852cc57d6210e2fbe7d509a10c4e3caf5cfe3fce4d9c32983ba45193711`.
All author source/ref/control writes are now **HELD** for root's next instruction.
