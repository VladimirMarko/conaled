# PFDS mixed 1/2/3 numeral operations: unqualified preparation

TU.DIG123 is the lazy redundant base-two representation with digits 1,2,3, safe
digit 2, and a common amortized account for mixed increment/decrement histories.
It is a mandatory **thesis** variant under CTB-58, not a replacement for the
Cambridge book's different 0/1/2 representation or its unread exercise subparts.
This paper curates 19 November 2026 preparation by `/root/books_remaining` and
independent cases by `/root/books_remaining/chapter06_interval_cases`, preserved
by the former. Both remain partial, unqualified mathematical work. No Lean,
prototype, runtime test or new qualification is supplied here. Current requirements and receiving status are tracked in [CTB](../textbooks/CTB.json): CTB-78 integration acceptance precedes resumed book formalization. This paper is not a Lean dependency or a receiving validation receipt.

## Primary source and attribution

The original main author authenticated and read Okasaki's 1996 dissertation
[author-hosted PDF](https://www.cs.cmu.edu/~rwh/students/okasaki.pdf):628,877 bytes,
162pages, SHA256 `f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072`.
Printed 107–111 were read as text; printed 110–111/physical 122–123 were visually
inspected, including the displayed clauses and singleton pattern. The independent
case author reported reading the same supplied text and two rendered target
pages. Its attribution is distinct from the parent's reading; this curation
makes no new primary visual-reading claim.

The surviving canonical `thesis-chapter08-source-inventory-045.md`, §7
T8-DECREMENT, was also read for the partial zero domain, singleton demand,
ordinary-binary alternation, compatible-versus-maintained budgets, safe 2 account
and the value shift caused by renaming digits. Its whole-chapter historical
reading remains attributed to its original author. Source reuse was inspected
at donor `7c0ed589087945d3e6e9c44b3ff2845872deaa14`; current integration does not
turn those old observations into new validation receipts.

The preparation did not have the Cambridge 232-page book PDF (canonical
9,356,709 bytes, SHA256
`b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41`).
Its Chapters 9–11, exercise subparts and Haskell correspondence still need their
actual source inspection where not otherwise recorded. The thesis supplies
only its own supplement. Old scratch PDFs/renders/receipts are not assumed
available from their former paths; primary bodies are not copied into this repo.

## Exact canonical requirements

The authoritative chapter registry is `docs/history/textbooks/checkpoint-024/TICKETS.json`, record **CTB-58**, with `mathematical_scope.key = pfds-9`. It preserves the chapter's 19 exercise headings, its book pages 115–140, prerequisites, numerical representations, collections, and the distinct thesis supplements. Its slice explicitly separates book digits 0/1/2 from thesis digits 1/2/3 and requires mixed increment/decrement accounting. This selection does not change that parent scope or its prerequisite CTB-57.

The exact selected row occurs in both:

- `docs/history/textbooks/checkpoint-012/books/pfds/records/research/source/thesis-obligations.json`, `items[id=TU.DIG123]`.
- `docs/history/textbooks/checkpoint-012/books/pfds/records/research/coverage/coverage.json`, `items[id=TU.DIG123]`, historical owner ticket 10015, proof status unproved.

The row's contract requires implementation and analysis of the thesis lazy 1/2/3 representation, constant amortized mixed increment/decrement, the one-debit allowance after 2 and none after 1/3, and the ordinary binary alternating-operation counterexample. Its source sections are exactly `["8.3"]` and printed pages `[110,111]`. There is no numbered theorem attached to this particular source claim and no new canonical row has been invented here.

The [current CTB catalog](../textbooks/CTB.json) preserves the integration and persistence owners GitHub #558 and #174, historical references CTB-51/53/55, 77 later exercise headings, evaluator/work correspondence, and physical allocation/sharing. The donor coverage inventory records 83 book exercise headings,12 numbered book results,16 thesis forward cost contracts, and a bounded FIFO client whose completion does not discharge the union. **This preparation closes none of those counts.**

For a later bounded implementation, the selected row entails the following inseparable obligations. These are a decomposition of TU.DIG123, not replacement ledger IDs:

| Obligation | Required result |
|---|---|
| Representation | Independent base-two interpretation of finite 1/2/3 digit sequences, empty zero, positive nonempty values, and explicit nonuniqueness. |
| Operations | All four increment clauses and four decrement clauses, including the ordered singleton match and decrement's missing zero case. |
| Meaning | Increment adds 1; successful decrement subtracts 1 on exactly the intended positive domain; recursive borrow receives a positive tail. |
| Demand | Immediate outer-input forcing, suspended result construction, one-level-ahead recursive behavior, and the singleton test's forced tail. |
| Memoization/persistence | Retained handles, fresh allocation identities, correct cache reuse, and preserved meaning across valid heap evolution. |
| Accounting | One common debit discipline for mixed operations; explicit source work, boundary payment, and actual realized-cost correspondence. |
| Separation cases | Ordinary binary alternation, incompatible budget use, eager/shallow observation distinction, and distinct equal-valued allocations. |
| Source boundary | No identification with book 0/1/2 by constructor renaming; no claim to the book's unread subparts or other thesis variants. |

## Independent mathematical account

Everything in this section is paper reasoning, not a checked Lean declaration or candidate result. The independent case section below preserves a separately prepared set of discriminating cases, with distinct authorship and reading attribution.

### Value layer and domains

Use finite little-endian digit sequences as an independent mathematical observation:

`V([])=0`, and `V(d::ds)=digitValue(d)+2*V(ds)`, with digit values 1,2,3.

All such finite sequences are numerically admissible; do not import ordinary binary's highest-one canonicality predicate. A nonempty sequence is positive, and `V(ds)=0` iff `ds=[]`. For length k,

`2^k-1 ≤ V(ds) ≤ 3*(2^k-1)`.

Thus the finite length is logarithmically controlled by its value, but the decoder is not injective: `[3]` and `[1,1]` both denote 3. This is a redundant representation, so algebraic operations should expose numeric observations, not an unjustified state isomorphism.

The independent finite equations are:

| Input | Increment result | Decrement result |
|---|---|---|
| `[]` | `[1]` | undefined in the displayed source |
| `[1]` | `[2]` | `[]` |
| `1::ds`, nonempty ds | `2::ds` | `2::dec(ds)` |
| `2::ds` | `3::ds` | `1::ds` |
| `3::ds` | `2::inc(ds)` | `2::ds` |

For the carry branch, `2+2*(V(ds)+1)=(3+2*V(ds))+1`. For a nonterminal borrow, `V(ds)>0` justifies `2+2*(V(ds)-1)=(1+2*V(ds))-1`; the positivity proof prevents natural subtraction from concealing an invalid zero recursive call. `V(ds)=1` forces exactly `[1]`, so the singleton branch completely describes the positive-to-zero case.

The paper example `inc([3])=[2,1]`, followed by `dec([2,1])=[1,1]`, returns the original number 3 with a different representation. Do not state `dec(inc(ds))=ds` as list equality. A valid public statement is equality of numeric meanings, with the appropriate partial-domain handling.

The displayed thesis line `datatype Nat = Digit Stream` has the form of a type abbreviation despite its keyword. Its algorithms operate directly on stream cells; a semantic transcription should record that typographic issue and use the stream type without inventing an extra runtime wrapper constructor. No change to the mathematical algorithm follows from this syntactic disposition.

### The source demand contract

The source `inc` and `dec` match suspended inputs **before returning** an outer suspension. They are not the alternative fully delayed `inc'` on printed 107. A faithful core realization therefore uses ordinary function clauses with suspended patterns and delayed right sides. Applying the generic `lazyFunction` sugar around the whole match would move input forcing and needs a separate observation/cost comparison; it is not the baseline translation.

In a carry/borrow branch, the recursive call is inside the outer delayed result. When that result is forced, constructing its cell calls the recursive function; that call immediately inspects its input before returning the next suspended result. This is the one-level-ahead convention from §8.2. Do not describe the entire recursive call as a completely untouched tail expression after the outer cell has already been returned.

Decrement's first clause matches `One` and a suspended empty tail. On a One with nonempty tail, this first clause **forces and memoizes the tail**, discovers a nonempty cell, and then falls through to the next clause. The next clause sees the resulting memory. On Two or Three, the first clause's digit mismatch does not need that tail test. Preserve this asymmetric demand and any corresponding cache hit when a later clause retries an outer pattern.

Decrement on a represented empty stream has no displayed clause. The core source should expose the actual match failure/raised Match result under its established semantics. A total library facade may return `none` at zero, but it must be a proved adapter with a distinct contract. It must not silently redefine the source function to saturate at zero.

### A useful strict shadow, and why it is insufficient

For a strict finite-list reference program, let `danger(ds)` count digits 1 and 3 and charge one per changed digit, including the terminating branch. A paper induction gives, for each legal increment/decrement,

`writes + danger(after) ≤ danger(before) + 2`.

Each recursively propagated 3→2 or1→2 removes one dangerous digit; a terminal 2→3 or2→1 can add one; removing singleton 1 or changing1→2/3→2 reduces the potential. The empty increment adds one. The existing invariant-aware potential theorem can telescope this on a linear trajectory with its initial potential retained.

This shadow is useful for semantic checking and as a second explicit tariff, but it is **not the lazy persistent theorem**. Repeatedly applying strict carry to the same retained length-k all-Three value reuses the old potential in each branch. A linear telescoping proof cannot pay for those independent executions with one initial credit. Likewise, forcing every digit after each source operation introduces additional observer work that the operation-only constant bound does not promise.

### One common debit account

Use the source allowance as an upper bound: an outer boundary has no unpaid debt; a tail after Two may retain one unit; tails after One/Three may retain none. Fully paid configurations are allowed. Bookkeeping is attached to actual suspended work and logical histories, rather than to an abstract digit list alone.

At the paper skeleton level, the potentially expensive terminal transitions are Two→Three and Two→One: they eliminate a one-unit tail allowance and must pass that unit outward. A propagating Three→Two or nonterminal One→Two creates the safe allowance that can retain one unit from the recursively generated work. A local intrinsic-work debit plus at most one passed unit gives a constant outward obligation. The remaining transitions and empty/singleton cases are constant boundaries.

That explains the common mixed-operation invariant, but **does not yet establish a literal two-transition or two-allocation bound**. Source pattern matching, failed-clause continuation, Nil construction, cache hits, closure/application overhead, and primitive costs must be priced. One abstract debit can cover a proved bounded local block, or a bounded collection of work-unit identities. In particular, allocating the empty increment's outer result and its eventual Nil tail must not disappear from the account.

The intended quantitative conclusion is a proved bound of the form

`actualWork ≤ initialAccountedBoundary + K * numberOfOperations + fixedSetup`,

for the chosen finite operation-history domain and explicitly declared tariff. K is to be derived from the actual operation/block proofs. It is not chosen here from an executed candidate. Extra full-digit observations are separately charged. For a closed history constructed from zero, the appropriate setup/initial boundary can be discharged by that construction; for an imported state, it must remain explicit.

Persistence requires distinguishing a physical shared computation from per-history discharge multiplicity. A debit may be discharged along several logical futures; that does not mean its actual memoized work is executed several times. Conversely, two fresh suspensions containing equal code are distinct work identities. A single global boolean 'debt paid for this address' is not automatically the source's per-history account.

## Existing shared interfaces

The following declarations and their relevant bodies were read at the fixed source snapshot. This is a reuse inventory, not a claim that they already prove TU.DIG123. The owner table records the inspected contracts; the broad suspension implementation families were not fully reread, as qualified below.

| Owner | Actual public declarations | Role and limit |
|---|---|---|
| `Applications/Resources/BinaryCounter.lean` | `Resources.BinaryCounter.value`, `inc`, `value_inc`, `incWithCost_eq`, `flipCost_potential`, `counter_potential` | Existing independent numeral meaning and actual counted strict execution; useful style and an ordinary-binary comparator. Its carrier is0/1, not the requested representation or lazy algorithm. |
| `Applications/Resources/BinaryCounter/Decrement.lean` | `decBits`, `decBits_spec` | Existing partial decrement/domain proof for canonical ordinary binary. It proves no mixed lazy cost theorem. |
| `Applications/Resources/Measured.lean` | `Resources.Measured`, `bind`, `bind_erases`, `reweight_bind`, `erasureSquare` | Reuse value/ordered-observation composition; do not create a second resource executor. Value erasure does not equate costs. |
| `Applications/Resources/Potential.lean` | `run_potential_map_of_invariant`, `run_cost_le_map_of_invariant`, `run_constant_charge` | Telescope an actual lawful trajectory, with initial potential and closure hypotheses explicit. Suitable for the strict shadow or a separately justified state account, not automatic persistent-fork payment. |
| `Applications/Resources/Persistent/History.lean` | `Resources.Persistent.history`, `HistoryClosed`, `history_trans` | Logical operation histories retain loops, cycles, and parallel-use arrows; actual source incidence is still to be supplied. |
| `Applications/Resources/Persistent/Debits.lean` | `Fresh`, `Allocated`, `Paid`, `Discipline`, `realized_card_le`, `PaidWithBoundary`, `realized_card_le_boundary` | Compose the concrete debit proofs and retain open-scope initial payment. Allocation sets and discharge multisets are deliberately different. |
| `Applications/Resources/Persistent/Realization.lean` | `realizeStep`, `realize_run_identity`, `realize_run_cost`, `realize_run_cost_le_fresh` | Existing interpreter for unshared work plus newly realized identities. It still needs the algorithm-to-actual-work correspondence. `seen` is already realized work, not unpaid or prepaid debt. |
| `Applications/Suspensions/Syntax.lean` | `Suspensions.Core.Expr`, `Pattern`, `force`, `lazyFunction`, `Env.rec` | Ordinary functions, ordered suspended patterns, recursive bindings, and delayed bodies are already expressible. The baseline must not be replaced by the differently delayed `lazyFunction`. |
| `Applications/Suspensions/Machine.lean` | `transition`, `delay_transition`, `body_transition`, `hit_transition`, `memoize_before_match`, `failed_clause_retains_state`, `raised_skips_memoize` | Actual allocation/body/cache and ordered-failure behavior needed by the literal source clauses. Existing operational distinctions remain intact. |
| `Applications/Suspensions/Observation.lean` | `observe`, `completion_eq_search`, `completed_sound`, `workload_reweight` | Read exact ordered events from the existing machine; event-list length agrees with actual finite transition count. Reweight only after this trace exists. |
| `Applications/Suspensions/BodyRealization.lean` | `body_realization_cost`, `body_realization_cost_of_counts`, `body_realization_observe_cost` | Selected body-entry support and occurrence equality under explicit hypotheses. These results expressly do not count work inside a body. One-body-per-address is not the desired work theorem. |

Current suspension status notes describe extensive pure-execution/nonreentry work, but those large implementation families were not freshly reread in full. If a later proof uses their nonrepetition consequences, its exact current hypotheses and bodies must be inspected then. Pure normal return alone must not replace `NoMemoizeUnwind`; exceptional retries remain a different source behavior. For this finite digit client, a direct preservation/termination proof excluding such failures may be more economical than broad assumptions about every pure program.

A bounded search found the current ordinary-binary owners above, and the canonical selected row remains unproved. This preparation does not assert a repository-wide absence theorem for every possible redundant-numeral implementation.

## Concrete proof route and integration boundaries

The following is a proposed proof sequence after current receiving acceptance; it is not a completed implementation or new qualification.

1. **Finite semantic observation.** Add the 1/2/3 digit carrier, independent value fold, partial shadow operations, positivity/length bounds, and value laws. Expose observational rather than representational inverse laws. Preserve all source clauses and zero-domain decisions.
2. **Literal source expressions.** Define the small digit/stream tags and ordinary recursive function clauses using the existing suspension core. Retain nested suspension patterns and their order. Prove source clauses against the existing actual machine, including the nonterminal-One first-clause failure and retained cache effects.
3. **Represented finite streams.** Relate reachable stream handles and memory to independent finite digit meanings. Allow unforced and cached forms; show source allocation and justified cache changes preserve older represented handles. Do not turn decoding into a free runtime traversal or identify distinct addresses with equal meanings.
4. **Local execution blocks.** Derive actual event/count correspondence for each function clause and each forced result-body block, retaining caller continuations and recursive-call boundaries. Separate the constant intrinsic block from recursively realized work. Count the extra singleton-tail observation, Nil constructions, failed matches, hits, writes, and the declared primitive tariff.
5. **Mixed debit preservation.** Construct debit identities at the corresponding delayed-work creation, track obligations after safe/dangerous digits, and prove the same account is preserved by both operations. Establish `Fresh`, `Allocated`, and `Paid` from actual allocation/incidence and the demand-before-work discipline. The source's brief debit argument is the proof guide, not a premise containing the desired global complexity result.
6. **Actual-work composition.** Prove that the measured source trace is bounded by the selected unshared blocks plus newly realized work units. Only then invoke the existing debit/realization theorems. Supply a closed-history corollary from zero and a boundary-accounted theorem for imported roots/retained versions.
7. **Connected clients.** Connect the independent cases through those public results. Include a mixed linear history and a persistent fork using the same retained source handle; distinguish that from two equal-valued fresh handles. Retain the ordinary-binary counterfamily under a precise demand observer and the source-vs-shadow tariff distinction.

Likely ownership is a narrow numeral module for the independent meaning, a source-client module using `Applications/Suspensions`, and an algorithm-specific resource layer using `Applications/Resources`. Exact new file names are unchecked implementation choices. There is no reason here to replace `Resources.Measured`, add another generic evaluator, modify the unrestricted suspension transition, or collapse existing book/thesis variants.

The present row is more than a list arithmetic exercise. A semantic-only checkpoint may preserve useful progress, but full TU.DIG123 still requires the literal lazy realization and the persistent mixed resource theorem. Likewise, proving only an abstract debit cardinality theorem or one body entry per address would leave its decisive work connection open.

## Independent demand and persistence cases

The following separately derived cases preserve the original partial boundary:
the case author did not establish a general lazy ordinary-binary lower bound,
a complete heap-level debit/work theorem or an exact runtime constant. The main
paper above supplies the complementary proof route. Repeated equations here
make the independent expectations readable; they do not constitute a second
implementation or stronger acceptance claim.

### Independent case 1. Value laws and nonunique representations

For finite digit streams, use little-endian binary weights:

`V([])=0`, `V(d::ds)=d+2*V(ds)`, for digits 1,2,3.

Every finite nonempty representation has positive value; only empty represents zero. Source decrement is partial on empty.

Incrementing Three uses `2+2*(V(ds)+1)=3+2*V(ds)+1`. Decrementing a non-singleton One uses `2+2*(V(ds)-1)=1+2*V(ds)-1`, with the nonempty tail providing `V(ds)≥1`. The singleton One case must be separated before that subtraction identity.

| Operation | Fully observed digit result |
|---|---|
| `inc []` | `[1]` |
| `inc [1]` | `[2]` |
| `inc [2]` | `[3]` |
| `inc [3]` | `[2,1]` |
| `dec [1]` | `[]` |
| `dec [2]` | `[1]` |
| `dec [3]` | `[2]` |
| `dec [1,1]` | `[2]` |
| `dec [1,3]` | `[2,2]` |

Representation equality is too strong for round trips:

- `V([3])=V([1,1])=3`.
- `dec(inc([3]))=[1,1]`, which differs from `[3]`.
- `inc(dec([1,1]))=[3]`, which differs from `[1,1]`.

Heap identity equality is stronger still and must remain separate from numeric meaning.

### Independent case 2. Demand cases that must survive formalization

The result suspension delays its body, not the function's initial pattern match. Increment forces the input outer suspension immediately. A Three branch returns a fresh suspension whose body contains recursive increment; that recursive call occurs when the result is forced.

Decrement with a One head forces its tail while trying the first singleton pattern. It does so even when the tail is nonempty and the first clause fails. The second One clause then returns a new suspension containing the recursive decrement. Two/Three decrement does not need to force the tail merely to reject the One pattern.

#### Pending-tail separator

1. The input's outer node is already `Cons One T`.
2. T is unevaluated and returns `Cons Three U`.
3. Calling decrement must evaluate and memoize T before returning its new result suspension.
4. It has not yet performed recursive `dec T`.
5. Forcing the returned suspension calls `dec T`. That call sees cached Three, creates the next result suspension, and does not need to force U.

The failed first pattern therefore contributes observable demand; the later visit to T is a cache hit rather than a repeated body evaluation.

If T instead returns `Cons One U`, forcing the first result causes the recursive decrement's singleton test to force U. This distinguishes immediate lookahead from eager completion of an entire borrow cascade.

For `Cons One T` where T eventually returns Nil, increment need not force T but decrement must. If T carries expensive prepaid work, this also distinguishes an amortized guarantee from a worst-case bound on one operation.

### Independent case 3. Debit route and explicit unfinished conditions

The candidate account extends the preceding source proof:

- Public outer suspensions have no outstanding debit.
- A tail after Two may have at most one normalized debit.
- A tail after One or Three has no outstanding debit.
- Work identities come from actual suspension allocations and must be consistent across aliases.

The qualitative cases are:

| Change | Paper obligation |
|---|---|
| Two→One/Three | The tail loses its allowance; pass/discharge that obligation together with the bounded new-result obligation. |
| Three increment→Two with recursive increment | The recursive result tail may retain one unit; its excess passes outward. |
| Nonempty One decrement→Two with recursive decrement | The same safe-tail allowance absorbs one unit. The early singleton test forces an input tail that One already requires to be paid. |
| Singleton One decrement / empty increment | Account explicitly for boundary suspensions and any new Nil suspension; do not assume recursive-case constants already cover these. |

For a normalized one-unit production obligation, the recursive excess calculation is `1+max(K-1,0)≤K` for `K≥1`. The explicit `K≥1` qualification is added by the preserving parent to state the implicit constant premise. For a real event tariff, scale the safe-tail allowance to a proved bounded intrinsic production block and derive the actual constant.

**The child did not establish a complete heap-level accounting theorem or an exact numeric runtime constant.** A digit-write count is insufficient. Initial funding/heap terms and extra observation work must remain explicit. Arbitrarily traversing every branch's entire stream is not free under an operation-only bound.

The preserving parent also retains a scope distinction: actual work identities are physical, while discharge obligations/witnesses follow logical histories and may be counted repeatedly. Consistency across aliases must not silently become a single global paid/unpaid boolean replacing the source's history-indexed account.

### Independent case 4. Persistence and fresh identities

Two increment calls on the same retained Three-headed version create two fresh result suspensions. They may share the old tail, whose body is evaluated once. Forcing the two fresh results nevertheless creates distinct recursive-result suspensions: memoization does not globally memoize `inc tail` by argument value.

Likewise, several decrements of a shared One-headed version may share its initial tail evaluation, but their new result bodies remain separate computations.

An eager-list potential counting non-Two digits can explain a linear-history digit-rewrite bound. It cannot pay for persistent forks: repeatedly incrementing the same eager k-digit all-Three version rewrites k digits on each branch. The lazy source initially allocates each branch's outer result suspension. These execution models must remain separate.

### Independent case 5. Mixed binary counterexample: remaining demand proof

The source's ordinary binary cycle alternates `2^k-1` and `2^k`. Fully observed canonical digit transformations traverse the k-digit boundary in both directions. Their separate debit proofs need opposite safe digits.

The pointwise minimum of the allowance bounds is zero allowance everywhere. This is consistent, but removes the capacity used to absorb recursive excess. Thus a formal proof should not claim that the two allowance predicates are logically contradictory. The failure concerns a shared maintained budget for mixed operations.

For the actual lazy source, a proposed lower-bound route uses a version-by-digit demand grid: alternating operations allocate fresh carry/borrow suspensions; after the pipeline fills, forcing each preceding outer result propagates through fresh pending work at successive lower levels. The child reported only a small two-bit paper trace indicating this cascade. **A general heap trace and asymptotic lower bound were not completed.** Counting denotational changes or adding free full-stream traversals would not supply that missing proof.

A positive redundant example stabilizes differently:

`[3] --inc--> [2,1] --dec--> [1,1] --inc--> [2,1] --dec--> [1,1]`.

After the first carry, the later operations change only the leading digit and retain the tail. This is a discriminating example, not the general debit theorem.

## Remaining scope

This paper closes none of CTB-58's 19 exercise headings, Theorem 9.1/Lemma 9.2,
numerical collection contracts, TU.SEG, TU.SCHEDULE, later book chapters or
appendices. Its unresolved center is the concrete mixed debit/actual-work
correspondence, with explicit initial funding and observation charges. The
ordinary-binary demand-grid lower bound remains incomplete. A semantic-only
numeral layer, abstract debit theorem or one-body-per-address fact would be
useful progress but would not discharge TU.DIG123.
