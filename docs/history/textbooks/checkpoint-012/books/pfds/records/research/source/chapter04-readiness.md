# Chapter 4 readiness after the suspension foundations

Prepared 2026-11-03. This is source/readiness preparation, not Chapter 4
implementation, acceptance or a new review loop. Chapter 2 remains the earliest
unaccepted chapter, and Chapter 3 implementation has not begun. No Lean source,
ticket, coverage row, Git reference or compiler state was changed here.

## Inspected scope and existing evidence

This note supplements `suspension-foundation-inventory.md`; it does not replace
that complete syntax, static-semantics and Appendix A inventory. I re-read the
complete published Chapter 4, printed pp. 31–38, and thesis Chapter 2, printed
pp. 7–12. I visually checked book pp. 35–37, including both exercises and Figure
4.1, and thesis pp. 8 and 11, including the deliberately premature `take` and
Figure 2.1. The existing complete visual inventory records book p. 38 as blank.
For both manuscripts, physical PDF page = printed page + 12. Thus the decisive
book pages are PDF 47–49 and thesis pages PDF 20 and 23. Exact manuscript hashes
and acquisition identities remain in `union-source-identities.json`.

The comparison uses the frozen candidates, not the current main branch:

| Foundation | Exact candidate | Available development result and boundary |
| --- | --- | --- |
| 10014 | `a3feaff319ad5fad912fb8bdc113f33fea4e2a60` | Source suspension extension, stateful forcing/matching, lazy sugar, finite execution, relocation and force observations. Stream algorithms and exercises are expressly outside its scope. |
| 10019 | `361f5f3f6bb3de1974510ce355883dac2bf25333` | Admitted pure-source correspondence and actual self-reentry precluding finite completion; value-cell persistence and later cache-hit behavior. This is not a stream-productivity theorem. |
| 10020 | `3dd930c3e3989f3e5530463f3ac937a629551335` | Successful cache writes per address are at most one for actual finite admitted source runs, at every observation budget. Exceptional body attempts can still repeat. |

These candidates have focused evidence and retained independent static review
records; their required own acceptance gates remain pending. Historical a3
documentation describing the later pure claim as unproved is not evidence that
the separate corrected 361 development is absent. Consult the current candidate
manifests and review records. No result is accepted merely by citing this note.

The actual APIs checked include `Core.ForceObservation.value_observed`,
`value_reflected`, `raised_observed`, `raised_reflected`; the `Derived` formation
and force-delay laws; `Pure.Simulation.source_reentry_not_terminates` and
`finite_body_entry_not_active`; and `source_cacheWrites_le_one` in
`Pure/CacheCounts.lean`. The shallow constructor example in
`Examples/SuspensionMachine.lean` already returns a delayed field without
forcing its raising body.

## Remaining source obligations

| Source | Remaining Chapter 4 connection |
| --- | --- |
| Book 31–33; thesis 7–8 | Account for the printed delayed computation and early-versus-delayed pattern examples through the existing public semantics. The expensive prime computation can remain a parameter; the point is its demand schedule. Preserve strict argument evaluation surrounding a lazy function. |
| Book 34, 36; thesis 8–11 | Realize `StreamCell` with an outer suspension and a separately suspended tail. Expose its constructor observation and connect it to finite list/prefix specifications. The element itself is not automatically delayed. A suspension of a strict list is a different computation. |
| Book 34–35; thesis 9 | Stream append: formation returns a suspension; demanding a nonempty left cell leaves the recursive append suspended. Empty-left demand forces the first right cell. Connect values and actual demand events, not just fully forced list concatenation. Contrast with monolithic suspended-list append. |
| Book 35–36; thesis 8, 11 | `take`: count zero must avoid input demand; other demanded output cells force one next input cell and leave the recursive output delayed. Retain the thesis's unannotated, premature-pattern implementation as a discriminating negative case. |
| Book 35–36, Exercise 4.1; thesis 9–11 | Define and relate both book `drop` forms and the thesis form. The book helper returns a Stream; the thesis helper returns a StreamCell. Demanding the result traverses skipped cells and demands the residual first cell, unless the input ends first. Extra suspension allocations and cache events need not agree. |
| Book 35–36; thesis 10–11 | `reverse`: first result demand traverses the entire finite input. The thesis accumulator is a StreamCell whose earlier cell is delayed; the book accumulator is a Stream whose newly constructed cell is delayed. Relate their observations without equating their heap graphs or allocation counts. |
| Book 35–36; thesis 10 | Trivial suspensions: establish the bounded-body work claim under the selected primitive-cost model. If pre-memoized creation is implemented, prove its observation refinement and separate cost effect; do not change the general Appendix A allocation rule silently. |
| Book 37, Exercise 4.2 | Implement lazy insertion sort and prove its demanded prefix agrees with a sorted permutation, then connect the actual source work to the stated prefix bound. The printed bound is **O(n·k)**; text extraction incorrectly renders the multiplication as subtraction. There are no lettered exercise subparts. |

Chapter notes, book p. 37 and thesis pp. 10–12, supply historical provenance and
representation commentary. They do not require independently formalizing every
cited theorem about optimal lazy reduction, dynamic programming or path
compression. Book Appendix A's contents on p. 185 list no separate stream
module or insertion-sort implementation; do not invent an omitted Haskell
Chapter 4 listing as an additional source program.

## Exercise 4.1: reuse the existing force law, retain its observation

The force-after-delay gap is narrower than the original inventory's prospective
description. The current `ForceObservation` theorems already transport arbitrary
finite normal and raised body executions, including bodies that allocate or
mutate. They relate results and reached stores using a relocation which fixes
old addresses and skips the private cell. Normal and raised runs retain their
respective extra transition counts. Initial bounded memory, fixed existing
cell contents/captures and primitive equivariance are explicit premises.

Remaining work is a compositional stream observation and the repeated use of
that law inside the two actual `drop` implementations. Returned tail handles,
their future observations, generated lazy binders and reachable captured
environments must be related. A theorem only about one isolated atom-valued
body is insufficient; literal equality of returned addresses, all closure
environments or full stores would also be the wrong target. `Bounded` memory
alone does not imply the required capture/content fixedness; discharge those
premises for the chosen stream representation.

The existing four laws concern finite normal/raised completions. They do not
themselves give arbitrary contextual equivalence for faults, fuel exhaustion
or divergence. A Chapter 4 theorem should specify its well-formed stream domain
and demanded-prefix observation and establish the necessary correspondence.
Pure/finite or productive-client restrictions are legitimate explicit domains,
not an excuse to treat all streams as already terminated lists.

## Integer counts and finite-prefix observations

Both printed signatures use `int`, and the programs branch on zero, then
otherwise decrement. They do not reject negative inputs. On a finite defined
stream, negative `take` keeps producing cells until the input ends; negative
`drop` keeps skipping until it ends. On an infinite productive input, negative
`take` can keep delivering finite prefixes while negative `drop` has no first
result cell. These are consequences of the printed code, not claims already
formalized here. For a natural-count first slice, state that restriction and
retain the signed behavior as remaining union scope. A negative-input clamp
would define a different operation.

`Progress.Producer`, `Delivers`, `Delivers.coherent` and `productive_of_next`
provide reusable finite-delivery machinery with explicit silent work. A source
adapter must retain the heap/cache in its state and distinguish a returned NIL
from an emitted element or an unfinished computation. `Productive` demands
arbitrarily many outputs, so it is not the general correctness condition for a
finite stream. Treating every raw thunk as a guarded one-output-per-step
coalgebra would assume away the monolithic work this chapter is explaining.

## Exercise 4.2: semantic and cost proof obligations

The existing `Applications.Sorting.StableSort`, `insertionOn_spec` and
`sortOn_eq_insertionOn` supply an independent finite sorting specification.
They can identify the finite value result and its prefixes. Their strict
list algorithms supply no stream demand schedule or prefix runtime bound.
If the new insertion comparison puts an element before an equal key, a stable
key-sorting contract is a useful compatible specialization; record the tie
policy instead of adding stability as an unexplained source requirement.

A candidate lazy insertion network must expose its actual stage/cell work.
A useful proof target is that demanding k results encounters only a bounded
number of cells per insertion stage, across n stages, with memoized repeated
demands sharing those same cells. A rectangular stage/prefix bound, together
with the operation-local work, can justify the printed O(n·k) claim. This is a
proposed argument, not a checked theorem or a synthetic cost definition.

Keep these premises and edge cases explicit:

- The source input is finite of length n, and each required input-cell demand,
  comparison and selected memory/constructor primitive has its stated cost.
  An arbitrary expensive or nonterminating thunk cannot receive a uniform
  bound from its output length alone.
- Separate constructing the sorter, demanding k cells and demanding the final
  NIL. State the valid-prefix range and account for n=0 and k=0 separately;
  an expression with nonzero setup cost cannot literally be bounded by C·n·k
  when either factor is zero. An explicit finite bound with setup/additive
  terms should precede the positive-domain asymptotic corollary.
- If a client permits k>n, specify whether it stops at NIL and prove that
  behavior. Do not claim k returned elements without the required length.
- The pure cache-write theorem needs an actual finite source evaluation and
  its represented domain/primitive premises. Establish these for stream code.
  It counts successful writes, not all body attempts: the existing handled
  retry with two attempts and zero writes remains a counterexample to that
  shortcut. A total successful stream computation must supply the additional
  body/work correspondence used by its bound.
- Mathematical-integer comparison, environment lookup and the Lean heap
  implementation are not automatically unit-time host operations. Count
  declared source events or carry explicit primitive-cost bounds.

If the implementation consumes 10020's general trace bound, make that actual
dependency explicit at Chapter 4 activation. The current ticket 10004 lists
10014 and 10019; this preparation does not alter the tracker.

## Useful future connected cases and sequencing

The first stream slice can pair one available Cons cell with a tail whose body
raises or recurs. Append/take formation and first-cell demand should return
without entering that tail, whereas a sufficiently large drop and reverse
must encounter it. This reuses the existing shallow-constructor and actual
body-event interfaces. Also retain empty-left append demanding its right
input, zero-take on an unforced failing input, zero-drop demanding the residual
cell only when its result is forced, and repeated output demand becoming a hit.

For sort, use empty/singleton inputs, duplicate keys with distinguishable
payloads, ascending and descending inputs, a first-element request versus a
complete request, and repeated observation of the same cached prefix. Prove
their connection to the general sorting and actual-work laws; value-only
examples do not exercise the complexity argument.

The existing TU.FORCE ledger row also mentions thesis §8.2 p. 107 (PDF 119).
That page deliberately retains immediate argument forcing in digit increment
to support one-level-ahead work. I inspected the page; it belongs to the later
implicit-recursive-slowdown algorithm. General Chapter 4 sugar/stream results
must not certify that later increment or its amortized theorem. Preserve the
forward algorithm obligation or an explicit owner handoff when the row is
reconciled; no coverage row is changed here.

Activate these formal stream obligations only when the chapter sequence and
prerequisite acceptance gates permit it. The complete source inventory,
candidate development evidence and this readiness note remain distinct from
Chapter 4's eventual exact-candidate build, exhaustive audit, independent
Standards/Spec outcomes and immediate final verification.
