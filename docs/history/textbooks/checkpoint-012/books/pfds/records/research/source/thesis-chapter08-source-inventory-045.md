# Thesis Chapter 8: complete source inventory (preparation only)

Prepared 2026-11-04 UTC by `/root/thesis_bootstrapping_inventory` during the
coordinator's recovery/validation work. The `045` suffix is the reserved
recovery-series label, not a claim that a particular validation run passed.
This is source accounting and proposed proof work. **Every formal obligation,
comparison, cost calculation and suggested specialization below is unproved.**
No implementation, compiler/test run, formal review, acceptance decision or
chapter-frontier advancement is supplied by this note.

## 1. Source identity, inspection extent and reconciliation

The inspected primary source is Chris Okasaki, *Purely Functional Data
Structures*, CMU-CS-96-177 (September 1996), the exact 162-page PDF at
`research-pfds/source-assets/okasaki-thesis-1996.pdf`, 628,877 bytes, SHA256
`f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072`.
The hash was checked again for this task. References `[T pN]` mean printed
Arabic page N of those bytes; its one-based physical PDF page is N+12.

Read **all of Chapter 8, printed 105–126 / PDF117–138**, in extracted text and
on the actual rendered pages. All 22 page images were inspected, including
all mathematical/code pages, all six figures and all four numbered theorems.
Printed126 contains only the running header. Also inspected the text and
render of printed53 / PDF65 to check the primitive DEQUE signature, and read
the relevant bibliography entries in the extracted thesis text. No cited
external research paper was fetched or read in this task.

Applied the PDF skill. Extraction used system `/usr/bin/pdftotext -layout`;
rendering used system `/usr/bin/pdftoppm -scale-to 1800 -png`. Reproducible
intermediates are under `research-pfds/thesis-chapter08-045/`: the complete
chapter text, individual `p105.txt` through `p126.txt`, `thesis-117.png` through
`thesis-138.png`, and supporting p53 text/image. They are outside `session`
and need not enter recovery checkpoints. This note preserves the source
identity, exact locations, inspected extent and mathematical obligations.

The book PDF is absent in this recovery environment. **This is not a fresh
inspection or completion claim for Book9, Book11, Book7 or Appendix A.**
Historical book comparisons below are explicitly attributed to the existing
records. Their primary book locations must be revisited when that source is
available; no historical Library file was accessed to obtain it.

Read the complete `book-thesis-union.md` and
`union-scope-reconciliation.md`; read the relevant `T1.05`, `T1.08`, `T1.10`,
`T1.11`, `TU.DIG123`, `TU.SCHEDULE`, `TU.FORCE`, `TU.TRACE` and `TU.MODULES`
records from `thesis-obligations.json`. Read the scheduled-binomial section
and related cost/readiness passages of `chapter07-union-readiness.md`, plus
the relevant navigation entries in `book-full-inventory.md`. The reports
named `chapter08-union-readiness.md` and `chapter08-exercise-readiness.md`
concern **Book8 / thesis Chapter5**, not the thesis chapter inspected here.

| Supporting record | SHA256 at this inspection |
| --- | --- |
| `book-thesis-union.md` | `fd307d2221335bb8412b797b2a750be6d2752c17b487fa81d31ef89d61645ffd` |
| `thesis-obligations.json` | `d98a57b4aa508b2d2e40719e4e689ec15a7e5f67685b9029455c2e83d8b984ad` |
| `union-scope-reconciliation.md` | `1f1e008b6d183af59b91545ebd5b612210ffc08c1b7dc1cf3730bb444a2ce780` |
| `chapter07-union-readiness.md` | `16e7b987cede2126befd55d63d46cb752aeefcf9b871a18c986b09d19ab38d68` |
| `union-source-identities.json` | `937977ba7efe6e527c1dffdca7d480e2cb9a39a3ad3b3914d18fd9b7c8a5e24a` |

The existing crosswalk places numerical material under Book9 /10009 and10015,
with a scheduling comparison to Book7 /10007; queues, deques and catenable
deques belong to Book11 /10011. Appendix correspondence remains integration
work under10012. This note does not create or change those assignments.
Local labels such as `T8-SCHEDULE` below are navigation labels for proposed
obligations, not new canonical coverage rows or independent review findings.

## 2. Complete page, figure and numbered-result accounting

Chapter8 has §§8.1–8.6, **Figures8.1–8.6**, and **Theorems8.1–8.4**. It has no
numbered exercise, lemma or definition heading. The unnumbered algorithms,
variants, invariants and performance claims remain obligations in addition to
the four theorem labels.

| Printed / PDF | Material inspected and retained |
| --- | --- |
| 105 /117 | Introduction; §8.1 explicit recursive slowdown; digits0/1/2, separated2 invariant, run grouping. |
| 106 /118 | `ones`, `simpleInc`, `fixup`, composed increment; green/yellow/red template. |
| 107 /119 | §8.2 lazy binary increment, separately delayed-argument `inc'`, Theorem8.1 statement. |
| 108 /120 | Complete Theorem8.1 proof; debit passing; green/yellow template and geometric-frequency intuition. |
| 109 /121 | Scheduled `lazyInc`, zero, schedule, `exec`, two-step increment, ranges and pending-work coverage. |
| 110 /122 | Theorem8.2 and all three carry cases; §8.3 addition/comparison cost discussion. |
| 111 /123 | Ordinary binary decrement and mixed-operation failure; redundant digits1/2/3 increment/decrement. |
| 112 /124 | §8.4 implicit queue carrier; snoc including two forcing placements; tail equations. |
| 113 /125 | Figure8.1 queue implementation; explicit-slowdown buffer comparison begins. |
| 114 /126 | Buffer comparison ends; queue debit invariant; complete Theorem8.3 proof; random-access remark begins. |
| 115 /127 | Random access, full and both restricted implicit deques; §8.5 simple catenable-deque introduction. |
| 116 /128 | Figure8.2 implicit deque, all digit helpers, displayed front operations and omitted symmetric operations. |
| 117 /129 | Figure8.3 CATENABLEDEQUE signature; simple carrier, cons and tail explanation. |
| 118 /130 | Simple tail equation, recursive append and sharper logarithmic bound; advanced five-segment/compound carrier. |
| 119 /131 | Figure8.4 simple catenable deque, including all append combinations and helper domains. |
| 120 /132 | Advanced deep/deep append, `share`, endpoint insertion, six deep-tail cases. |
| 121 /133 | Borrowing/replacement, `replaceHead`, primitive-operation claims, debit allowances, Theorem8.4 statement and proof start. |
| 122 /134 | Figure8.5 advanced carrier, helpers, all append combinations and exact thresholds. |
| 123 /135 | Figure8.6 advanced replacement and all six tail cases; symmetric functions left to the implementer. |
| 124 /136 | Theorem8.4 proof completion and §8.6 recursive-slowdown related work. |
| 125 /137 | Lazy/scheduled binomial-heap and catenable-deque historical comparisons. |
| 126 /138 | Running header only; no omitted mathematical content. |

| Named item | Primary location | Unproved obligation family |
| --- | --- | --- |
| Theorem8.1 | 107–108 /119–120 | Constant amortized lazy binary increment with the printed forcing placement. |
| Theorem8.2 | 110 /122, definitions109 | Completed-zero separation and the resulting constant worst-case scheduled increment. |
| Theorem8.3 | 114 /126, Figure8.1 at113 | Constant amortized implicit-queue snoc/tail; complete shallow and forcing cases. |
| Theorem8.4 | 121,124 /133,136, Figures8.5–8.6 | Constant amortized advanced append/tail/init; all cases, primitive premises and exact debit normalization. |

## 3. Common semantic and cost premises

All algorithm obligations require actual finite representations, well-founded
recursive calls or a justified finite demand semantics, and ordered sequence
or numeric denotations. A multiset equation is too weak for a queue/deque;
physical cell count is not the unfolded sequence length of a shared result.
Catenating a value with itself preserves two occurrences of every element.
Repeated references and retained versions must be covered without assuming
that independently constructed, extensionally equal suspensions share a cache.

These are pure algorithm instances of the source suspension semantics. Fresh
allocation, evaluation order, successful memoization, cache-hit cost and
payment before first force must be connected to actual executions. General
effectful/retrying suspensions are not automatically at-most-once; the earlier
`TU.FORCE` and `TU.TRACE` qualifications remain applicable. An endpoint-value
proof, a geometric series, or a single persistent-version path does not prove
the general history-sensitive debit claim.

Debit allowances are **upper bounds on unpaid obligations**, not assertions
that every allowed slot is occupied. Passing debits outward requires a proof
that every relevant demand pays them before the underlying computation runs.
The source's small debit constants use normalized work units; allocation,
matching, primitive deque calls, recursion inside a suspension and repeated
forces must all receive a consistent charge. Counting only fresh body entries
does not bound unbounded work inside one body. [T108,114,121,124]

State the unit-cost assumptions for cell access/allocation, fixed constructor
inspection, arithmetic on block lengths, and primitive deque operations.
They are not automatically Lean runtime or arbitrary-precision bit-cost
bounds. Logarithmic expressions require explicit small-input constants; use
an equivalent total bound such as `1 + log2(n+1)` where necessary. Numeric
digit-length bounds require canonical/reachable finite binary inputs, not
arbitrarily many high zero digits.

Nonuniform carriers recur at pairs, deques of elements, or compound elements.
Their actual construction and invariants must be supplied. An unconstrained
abstract type constructor together with operations/laws is not automatically
an admissible recursive datatype in the target formalization. A uniform
encoding needs level-aware shape predicates; a generic result also needs an
actual admissible primitive realization. This extends the earlier structural
decomposition concerns without closing `TU.MODULES` here.

## 4. T8-EXPLICIT: explicit recursive slowdown

The §8.1 numeral has little-endian digits0/1/2. `Ones k` compresses k adjacent
one digits; Zero and Two each occupy one position. The value is the usual
base-two weighted sum after expansion. Two denotes a temporary carry, not a
new radix. Require positive run lengths and no adjacent Ones blocks in the
normalized carrier. A suitable reachable/canonical restriction rules out
irrelevant high zero padding. [T105–106]

The global invariant places a zero before the first Two and between any two
Twos, with any number of intervening Ones. Consequently the first digit is
not Two, and the successor of a Two selected for repair is not Two. Preserve
these consequences separately: the first is needed by the public increment,
the second by the internal repair.

The complete displayed algorithm consists of four components:

- `ones` discards a zero-length run and merges with an immediately following
  Ones run. Prove denotation, normalization and fixed-node work on its domain.
- `simpleInc` maps empty to a singleton one run, changes a leading Zero to one,
  or changes the first One of a run into Two and retains the shortened run.
  Its domain excludes a leading Two; distinguish public valid states from the
  temporarily weakened intermediate state after this operation.
- `fixup` handles a leading Two or a Two immediately after the first Ones
  block. It changes that Two to Zero and applies `simpleInc` to the suffix.
  Other forms are unchanged. Prove that this preserves represented value,
  restores separation and does not invoke `simpleInc` outside its domain.
- Public increment is `fixup(simpleInc ds)`. The composition-operator version
  in the remark denotes the same composition; it is not a different carry
  schedule. Prove value+1, totality on valid inputs and a uniform worst-case
  bound in the source primitive-cost model.

No scan through all Ones or expansion of a run is part of the implementation.
The first non-One digit is at the first or second list cell. The constant-time
claim relies on that representation and the arithmetic cost premise for run
counts, including subtraction from a positive count. [T106]

The green/yellow/red abstraction maps these colors to0/1/2. An operation may
degrade green to yellow or yellow to red, but cannot jump green to red; repair
upgrades the first non-yellow red level to green while possibly degrading its
successor. Grouped yellow levels make repair accessible in bounded work.
A generic theorem needs these transition, representation and cost premises;
the color terminology alone is not a theorem for arbitrary structures.
Kaplan–Tarjan real-time deques/lists are cited examples, not supplied complete
implementations in this chapter. [T106–107]

## 5. T8-LAZY: binary streams and Theorem8.1

The ordinary lazy carrier is a finite stream of Zero/One digits. Increment
forces its argument immediately. Empty produces a singleton One; Zero becomes
One and stops; One becomes Zero and places the recursive increment in the
suspended output body. Value+1 and finite/canonical output must be proved
alongside the precise demand behavior. [T107]

The separately displayed `inc'` suspends the case analysis itself. It is a
retained source variant: full values may agree while argument-forcing times
differ. The thesis deliberately uses the earlier-forcing `inc` to inspect one
level ahead. Do not substitute `inc'` or book `fun lazy` notation into that
proof without a demand/cost correspondence. This directly refines the existing
`TU.FORCE` source obligation.

Theorem8.1 uses the following account: a tail after Zero may retain one debit;
a tail after One none; the outermost suspension none. Overflowing debits pass
to the enclosing suspension and are discharged at the outermost boundary.
The dependency order of earlier and later tails is essential to safe passing.
The two illustrated proof cases are:

- A terminating Zero-to-One step creates its new-suspension debit and loses
  the old tail's one-debit allowance, for an upper budget of two.
- A One-to-Zero step can force the old tail because its allowance is zero.
  It creates a debit and receives overflow from the recursive call; the new
  Zero tail keeps one of the recursive call's two-budget account. [T108]

The source says the cascade always has two debits. A formal statement should
distinguish a **budget of at most two** from exact occupancy. In particular,
the Nil/extension base case is present in code but omitted from the printed
induction, and an allowed debit need not exist. Cover Nil, an all-Ones carry,
already-memoized tails, sharing, and any terminal-cell work explicitly.

The implicit green/yellow template maps green to Zero and yellow to One.
Green operations stop and may become yellow; propagation from yellow is lazy
and first restores green locally. The frequency intuition suggests a geometric
sum over levels. The thesis itself notes persistence complicates this picture;
the debit-passing and logical-history proof must supply the actual result.
Implicit slowdown naturally yields amortized bounds, with scheduling a further
construction, not an automatic consequence of laziness. [T108–109]

The addition/comparison discussion claims logarithmic digit work and at most
logarithmically many pending debits in this finite numeral representation.
Retain the debt/length lemma and an observer for any such operation; the
chapter supplies no complete addition/comparison algorithms or corresponding
cost recurrences here. Do not convert this discussion into coverage of all
Book9 arithmetic operations. [T110]

## 6. T8-SCHEDULE: explicit work schedule and Theorem8.2

The scheduled numeral is a digit stream paired with a strict list of stream
jobs. Its zero has an empty digit stream and empty schedule. `lazyInc` is the
earlier-forcing `inc` under a new name. Each public increment creates its result,
puts that stream first on the schedule and applies `exec` twice. `exec` leaves
an empty schedule alone, removes a job when its first digit is One, and advances
its cursor after Zero. [T109]

Required representation and execution facts include:

1. Every scheduled job is nonempty and represents the remaining suffix of a
   carry, whose output consists of zero or more Zeros followed by a One.
   The missing Nil-job equation is safe only under this invariant.
2. A job's range is its **remaining** interval of digit positions through its
   terminating One. Consumed output positions are removed. Relate these indices
   and offsets to the current digit stream and to actual shared cells.
3. Every relevant unevaluated digit body is covered by a scheduled range;
   completed cells stay memoized. Treat the terminal Nil separately rather
   than pretending it is another digit or a valid carry job.
4. Separated ranges imply that the old input digit needed by a scheduled body
   is already forced. Account for construction-time inspection as well as
   the work performed by `exec`; two cursor steps need not mean exactly two
   physical force events.
5. `exec` changes readiness and schedule cursors, preserving the numeral value.
   Public increment preserves all invariants and adds one to that value.

Theorem8.2 strengthens nonoverlap: before the first pending range there are at
least two completed Zeros, and between consecutive ranges at least one. A
completed Zero is its memoized cell, not merely a Zero in the eventual value.
The zeros need not be adjacent to each other or the job. The assertion about a
first range is conditional when the schedule is empty. [T110]

Let m be the number of initial Zeros in the newly created carry output.
The source proof has the following cases, visually confirmed as **m >= 2** in
the third case:

| Case | Two-step progress to preserve |
| --- | --- |
| m=0 | First execution removes the new singleton-One job; the second advances or removes the old first job, or does nothing if none exists. |
| m=1 | Both new digits are completed and the new job is removed; the new Zero replaces the first old separator. |
| m>=2 | Two new leading Zeros are completed; the residual new job becomes first, and an old completed Zero separates it from the old first job when one exists. |

The written proof names two old jobs and their separators. Supply the absent
first-job and absent second-job cases, the initial zero and small numerals,
and carries extending beyond the old highest digit. These are boundary proof
obligations, not a claim that the separation theorem is false.

The constant worst-case theorem then needs bounded intrinsic work per scheduled
body, constant cache-hit/maintenance costs and the proved dependency readiness.
A list of nonoverlapping abstract intervals alone does not establish any of
those physical facts. Retained versions must preserve readiness under a cache
extension, without changing their numeral denotations.

This is `TU.SCHEDULE`'s **binary-number** realization. The existing Chapter7
readiness report records analogous residual-range and small-schedule issues
for the book's scheduled binomial heaps. A reusable scheduling theorem is
plausible, but needs distinct checked numeral and tree/heap instantiations.
The book theorem and Exercise7.3 have not been re-inspected here.

## 7. T8-DECREMENT: incompatible accounts and digits1/2/3

The displayed ordinary-binary decrement is partial on zero. It removes a
singleton One, changes a nonterminal One to Zero, or changes Zero to One and
recursively borrows. The singleton pattern itself forces the tail to test Nil;
retain that demand in the cost model. State a positive-value precondition or
an explicit checked adapter, rather than silently choosing behavior for Nil.
[T111]

The source's counterfamily alternates values `2^k-1` and `2^k`, traversing the
full logical carry/borrow length. Its conclusion is that the two separate
constant-amortized proofs cannot both be used for arbitrary mixed histories
of these functions. To formalize a lower bound, fix the demanded execution,
setup and fresh suspension identities, and count realized carry/borrow work;
the number of changed eventual digits is not by itself an immediate strict
cost trace. No source evaluator or counterexample test was run here.

Increment's account allows debt after Zero, while decrement's allows it after
One. Read the source's description of contradictory invariants as a conflict
in maintaining the accounts within the claimed budgets. The upper-bound
predicates themselves have an intersection: every tail fully paid satisfies
both. An argument that their conjunction is logically unsatisfiable would be
wrong. The failed inference is combining independently valid cost accounts
without proving compatibility and a shared budget. [T111]

The replacement representation uses base-two digits **1,2,3**, with Two safe
(green) and One/Three dangerous (yellow). Empty denotes zero; all nonempty
digits are positive, and representations need not be unique. The following
transition table paraphrases the complete displayed functions:

| Operation/input | Output action |
| --- | --- |
| inc empty | Produce a singleton One. |
| inc One / Two | Replace the leading digit by Two / Three, retaining its tail. |
| inc Three | Produce Two and recursively increment the tail lazily. |
| dec singleton One | Produce empty. |
| dec nonterminal One | Produce Two and recursively decrement the positive tail lazily. |
| dec Two / Three | Replace the leading digit by One / Two, retaining its tail. |

Prove numeric+1/−1, finite representation validity, positivity of a recursive
borrow argument, and empty/partial behavior. The common invariant allows one
debit after Two and none after One/Three, with an unpaid-free outer boundary.
Prove one account for arbitrary mixed inc/dec histories, including the
singleton match and all boundary cases. This is the existing `TU.DIG123`
obligation, still unproved; no numbered theorem is supplied for it. [T111]

The existing union records identify the book variant as digits0/1/2 with safe
One. A constructor rename is not a value-preserving comparison. For equal
length k, subtracting one from every thesis digit changes the weighted sum by
`2^k-1`; even the one-digit thesis One denotes1 while its renamed Zero denotes0.
That is a proposed elementary correspondence calculation, not a checked bridge
to the unavailable book implementation. Preserve both source variants and
their different empty/high-digit behavior.

## 8. T8-QUEUE: implicit queues and Theorem8.3

The queue is either shallow with zero/one element, or deep with a strict front
digit of size1/2, a suspended queue of ordered pairs, and a strict rear digit
of size0/1. Its denotation is front, followed by flattened middle pairs in FIFO
order, followed by rear. Pair order and the level-doubling interpretation must
be proved, not inferred merely from the type. A valid deep value is nonempty.
[T112–113, Figure8.1]

All five QUEUE operations remain obligations. `empty` is shallow zero;
`isEmpty` recognizes precisely that case; `head` selects the first strict
front element and raises the implementation's EMPTY on empty; `snoc` and
`tail` obey these exhaustive cases:

| Operation/case | Required transition |
| --- | --- |
| snoc shallow0 | Shallow singleton. |
| snoc shallow1 | Deep front containing old and new elements, empty suspended middle, rear0. |
| snoc deep rear0 | Place the new element in rear1. |
| snoc deep rear1 containing x | Append pair(x,new) to middle lazily and reset rear0. |
| tail shallow0 / shallow1 | EMPTY / shallow0. |
| tail deep front2(x,y) | Front1(y), unchanged middle/rear. |
| tail deep front1, middle empty | Collapse to the rear as a shallow queue. |
| tail deep front1, middle nonempty | Force/read its first pair(y,z), use front2(y,z), suspend middle tail. |

The main snoc clause forces the middle before creating its recursive snoc
suspension. The alternate p112 clause delays that force inside the suspension;
the thesis says this does not change the running-time bound. Retain both
realizations and prove the bound/correspondence with their distinct demand
traces. Tail must force the middle to decide emptiness and obtain the borrowed
pair, but may suspend its recursive tail. [T112–113]

For the debit account, front2 is green and front1 yellow; rear0 green and
rear1 yellow. The middle allowance equals the number of green endpoints:

| Front size / rear size | Allowed middle debits |
| --- | ---: |
| 2 /0 | 2 |
| 2 /1 or 1 /0 | 1 |
| 1 /1 | 0 |

Theorem8.3's proof treats tail. A terminating front2-to-front1 step loses one
allowance. An intermediate front1-to-front2 borrow with rear0 passes the old
middle's possible one debit before forcing it; the new suspended recursive
call receives its own unit plus recursive overflow, fitting the new allowance2.
With rear1, the old middle has zero allowance; the new allowance1 keeps one
of the two-unit recursive account and passes one. Thus the displayed argument
passes at most one debit per cascade to its outer boundary. Snoc has the
analogous endpoint/color analysis. [T114]

The proof explicitly omits shallow queues for exposition. Formalization must
include shallow transitions, collapse, empty middle, fresh empty suspensions,
nonexistent inherited debits, both snoc forcing placements and the exact
normalized body charge. This is not permission to omit those reachable states
or to claim an exact one-debit event on every operation. T1.05 remains open;
head/isEmpty's direct strict access additionally supports a proposed constant
worst-case bound under the primitive model.

The comparison with ordinary recursive slowdown allows explicit endpoint
sizes0–3: front0 red, front1 yellow, front2/3 green; rear3 red, rear2 yellow,
rear0/1 green. Repair may need a second carry/borrow to make the opposite
endpoint green, explaining the extra green digit. This is an explanatory
transition sketch, not a second complete deque implementation supplied here.
[T113–114]

The random-access remark is also an obligation, not merely motivation:
lookup/update of index i is claimed in O(log i) time via a logarithmic sequence
of complete binary leaf trees represented by repeated pairing. Specify an
index convention and small-index bound, for example O(1+log(i+1)); give an
actual search/update algorithm, out-of-range behavior, order preservation and
the demand/debit account. No such functions are listed here. Do not silently
replace this front-index claim by an external nearest-end bound, or label it
worst-case without the required operational proof. The claim of being slower
in practice is an empirical source remark, not a theorem or new benchmark.
[T114–115]

## 9. T8-DEQUE: full and restricted implicit deques

Figure8.2 uses shallow digits of size0–3 and deep front/rear digits of size1–3,
with a suspended deque of ordered pairs. Both endpoint digits are green at
size2 and yellow at sizes1/3. Prove the same ordered flattening law, recursive
validity and the two-endpoint debit account for mixed operations. [T115–116]

The figure lists six fixed-size helpers: insertion at either end, head/last,
and tail/init. Their exact sequence behavior is required; empty observations
and removals raise EMPTY. Digit insertion is only defined through size2;
the enclosing operation handles size3 before calling that helper. Prove those
domains so a missing helper clause is not reached on valid public input.

Displayed cons makes a shallow size3 plus new element into a deep value with
front(new,a), rear(b,c), and empty middle. At deep front3(a,b,c), it keeps
front(new,a) and lazily conses pair(b,c) onto the middle, forcing the old middle
inside that suspension. Otherwise it extends the front digit. Displayed tail
removes locally when the front is2/3; at front1 it forces the middle, collapses
to shallow rear if empty, or borrows the first pair and suspends middle tail.
Head reads the strict front. All shallow/empty transitions must be covered.

The figure leaves snoc/last/init to symmetry. Supply those functions and prove
the reversal relationship, preserving pair order and forcing placement; the
ellipsis is not already executable code. The snoc overflow moves the first
two elements of a size3 rear into the recursive rear and retains its last
element with the new element. The corresponding init borrow is from the
middle's last pair. T1.08's six operation bounds remain unproved.

Both restricted variants are explicitly in scope, distinct from the earlier
rebuilding-based restricted deques:

| Variant [T115] | Permitted updates | Deep front / rear sizes |
| --- | --- | --- |
| Output-restricted | cons, snoc, tail | 1/2/3 and 0/1 |
| Input-restricted | cons, tail, init | 1/2/3 and 1/2 |

Specify the shallow representation and transition rules for each, and prove
their own shape, semantics, forcing and resource contracts. A general
end-capability construction could provide checked specializations. Simply
restricting the public methods of the full deque does not by itself establish
the output-restricted rear0/1 representation. The existing reconciliation's
`UNION-VAR-002` already retains these smaller-buffer variants; no new book
Exercise11.2 comparison was performed here.

## 10. T8-SIMPLE-CAT: simple catenable deques

Figure8.3 specifies nine entries: empty, isEmpty, cons, head, tail, snoc, last,
init and append. Head/tail/last/init raise the catenable implementation's EMPTY
on empty. The ordinary primitive deque has its own interface and exception;
the displayed shallow guards translate emptiness to the wrapper's exception.
[T117, Figure8.3; T119]

The simple representation has a shallow arbitrary-sized primitive deque, or
a deep front and rear of at least two elements each plus a suspended catenable
deque of primitive deques, each of size at least two. Denotation is front,
flattened middle blocks, then rear. Recursive validity and the nonempty-block
lower bounds are essential. Shallow values are not bounded to one element;
only the short-append branch inputs have that restriction. [T115,117–119]

Cons/snoc extend the corresponding primitive endpoint; head/last inspect it.
Tail removes locally if the front size exceeds2. At size2, a nonempty middle
supplies a new front block, preceded by the surviving old front element;
the new block has size at least3 and the middle tail is suspended. The empty
middle branch contains the confirmed source error described below. Init needs
the corresponding ordered rear transition, including its collapse boundary.

All four append combinations in Figure8.4 are distinct obligations:

| Inputs | Printed algorithm to account for |
| --- | --- |
| Shallow/Shallow | If one side has size<2, append that zero/one-element side using its short helper; otherwise create Deep(left, empty middle, right). |
| Shallow/Deep | For size<2, prepend locally; otherwise install the shallow deque as front and suspend cons of the old front into the middle. |
| Deep/Shallow | Symmetric size<2 local append or rear replacement with suspended middle snoc. |
| Deep/Deep | Retain the first front and second rear; suspend append of middle1 with rear1 snoced onto it and middle2 with front2 consed onto it. |

The simple `shortAppendL/R` helpers handle only a zero/one-element short side.
They do not implement unrestricted primitive deque concatenation. Prove their
call-site preconditions and exact ordered result. [T119]

The source claims O(1) amortized endpoint operations and the sharper append
bound **O(min(log n1, log n2))**, since recursive append descends only while
both operands are deep. Each recursive level accounts for constant debit work
that must be paid to retain the deletion invariant. Prove the logarithmic
depth bound from positive blocks of size>=2 and the semantic, unfolded operand
sizes. Include an additive constant and empty-input cases. T1.10's O(log n)
summary must not erase this two-input bound. [T118]

Unlike the advanced representation, the simple discussion does not print a
fully explicit numeric debit invariant. A candidate suggested by the earlier
queue proof is a middle allowance equal to the number of endpoints with size
greater than2, but that is **proposed here**, not a quoted theorem or proved
invariant. Check append, collapse, primitive-deque work and all persistent
demands before adopting it.

### Confirmed semantic correction: surviving front element

Both p118 and Figure8.4 p119 literally return only `Shallow r` when tail sees
a front of size2 and empty middle. This is the existing `UNION-SRC-003`, now
independently rechecked on the thesis render. With a suitable primitive deque,
publicly catenate shallow `[a,b]` and `[c,d]`. The result is a valid deep value
with those endpoints and empty middle. Literal tail returns `[c,d]`; the list
specification requires `[b,c,d]`. The calculation is a paper source-semantic
discriminator, **not a Lean-checked refutation or executed test**.

The intended collapse must preserve the surviving front element, for example
as `Shallow(D.cons(D.last f,r))` under size(f)=2. Preserve the analogous init
obligation; a naive mirror that returns only the front drops the surviving
rear element. The existing reconciliation reports that the book's corrected
rule preserves the element, but the book and its Haskell listing were not
available for reinspection here. Do not claim literal correctness of this
thesis branch or silently call the corrected branch identical source code.

## 11. T8-ADVANCED-CAT: five segments and compound elements

The advanced carrier has shallow arbitrary-sized primitive deques and deep
values `(F,A,M,B,R)`. F and R have at least3 base elements; M at least2. A and
B are suspended catenable deques of compound elements. A compound is either
Simple(d), with at least2 elements, or a full CE(F',C',R'), whose endpoint
primitive deques each have at least2 elements and whose suspended C' is a
catenable deque of compounds. [T118,122]

Define mutually compatible ordered denotations: Simple flattens its deque;
CE flattens its front, recursively flattened middle compounds, then rear;
Deep flattens F, A's compounds, M, B's compounds, R in that order. Prove all
minimum sizes, recursive validity and finite denotation. The source calls the
compound middle **C** in prose/p118 but names its record field **A** in
Figures8.5–8.6. Normalize the field name consistently while keeping the
distinction between the outer antemedial A and a compound's middle C.

### Helpers and append

`share(f,r)` removes the last element from f and first from r and makes those
two elements, in that order, the new middle deque. Its returned fringes are
`init f` and `tail r`. In deep/deep append, input endpoints size>=3 leave
compound fringes size>=2. In shallow/shallow construction, input sizes>=4
leave deep endpoints size>=3. These different preconditions explain two of
the thresholds; prove them explicitly. [T120,122]

Advanced `shortAppendL` walks the short left input from its last element and
conses into the right; `shortAppendR` walks the short right input from its head
and snocs into the left. They preserve order but are linear in the short side
in general. Actual calls bound that side: at most3 in a shallow/shallow short
branch, at most2 in a printed shallow/deep short branch, and exactly2 when
combining the remainder of a size3 front during tail. [T122–123]

The printed append thresholds are exact:

| Inputs | Threshold/action |
| --- | --- |
| Shallow/Shallow | Test left size<4, then right size<4, for a bounded short append. If both are>=4, use share and create Deep with empty A/B. |
| Shallow/Deep | If shallow size<3, append locally into F. Otherwise set F to the shallow deque and suspend cons(Simple oldF) into A. |
| Deep/Shallow | If shallow size<3, append locally into R. Otherwise set R to the shallow deque and suspend snoc(Simple oldR) into B. |
| Deep/Deep | Use share(R1,F2), preserving F1 and R2 and constructing the two compound insertions below. |

For deep/deep append, the new A is suspended snoc onto A1 of
CE(M1,B1,init R1); the new M is `[last R1, head F2]`; the new B is suspended
cons of CE(tail F2,A2,M2) onto B2. All inherited pieces must occur once and in
their original sequence order. This append does not recursively call append:
it schedules only cons and snoc of compounds at the next level. Its suspended
operands' force positions are part of the source behavior. [T120,122]

The earlier reconciliation's `UNION-VAR-001` reports `<4` in the book's mixed
shallow/deep cases versus thesis `<3`; both use `<4` for shallow/shallow.
This task rechecks only the thesis. At shallow size3 the thesis creates a new
dangerous size3 endpoint and a suspended compound insertion. The historically
reported book branch merges those three elements into the old endpoint.
Keep both variants pending actual comparison; representation validity alone
does not equate their allocation, demand or debit behavior.

### Replacement and every tail case

`replaceHead(x,c)` replaces the first compound element by x using a primitive
tail followed by cons in the shallow deque or deep front. It requires c to be
nonempty, preserves its shape/size boundaries, and avoids the recursive
borrowing that a catenable-level `cons(x,tail c)` could cause. The p121
unoptimized expression is an explanatory intermediate form; the final figure
uses replacement. Prove value correspondence and the actual avoided demand,
rather than assuming equal values imply equal work. [T121,123]

| Deep tail guard | Required result in source sequence order |
| --- | --- |
| size(F)>3 | Replace F by primitive tail F; other fields unchanged. |
| size(F)=3, A begins with Simple(d) | New F=(tail F)++d; suspend tail A; retain M/B/R. |
| size(F)=3, A begins with CE(F',C',R') | New F=(tail F)++F'; new A suspends `force C' ++ replaceHead(Simple R',force A)`; retain M/B/R. |
| size(F)=3, A empty, B begins with Simple(d) | New F=(tail F)++M; A empty; new M=d; suspend tail B; retain R. |
| size(F)=3, A empty, B begins with CE(F',C',R') | New F=(tail F)++M; new A suspends cons(Simple F',force C'); new M=R'; suspend tail B; retain R. |
| size(F)=3, A and B empty | Append the two shallow deques containing `(tail F)++M` and R, using the shallow/shallow rules. |

Here the unqualified small `++` inside a new front denotes the bounded
primitive helper's ordered result; the operation in the A suspension is the
recursive catenable append. Distinguish these in any formal syntax. In every
borrowing case that retains Deep, the new F has at least4 elements; the next
front deletion can therefore be local. The final collapse/construction case
must also prove the size and threshold conditions of its append. [T120–123]

Include shallow/empty tail, all size4-to-size3 transitions, and both empty
tests before selecting a compound. The complete figures still omit snoc,
last, replaceLast and init as symmetric definitions. Supply them with ordered
reversal laws for endpoints, A/B and full compounds; the simple word
"symmetric" is not implementation or proof coverage.

### Theorem8.4: exact printed account and unresolved details

Let `gF` and `gR` indicate that the corresponding endpoint length exceeds3.
The printed capacities are

    cap(C) = 4,
    cap(A) = 4*gF + gR,
    cap(B) = gF + 4*gR.

All are unpaid-debit upper bounds, with C the compound-middle role regardless
of its record label. [T121]

The deep/deep append argument creates two debits for the suspended compound
snoc/cons and pays both. Transferring B1 or A2 to a C field can require one
additional payment each when its old capacity was5. Changing the opposite
endpoint of the inherited A1/B2 can instead lower its capacity by one. The
source explains the relevant mutually exclusive conditions, giving **at most
four** payments in the deep/deep case. Prove the indicator inequalities for
all four endpoint colors and connect transfers to actual debit identities.
[T121,124]

For tail/init, the printed target is **at most five** discharged debits.
The argument handles a cascade by passing obligations outward:

- A terminating front4-to-front3 step can lose4 units of A allowance and1 of
  B allowance; larger fronts lose neither. No new recursive body is created.
- At front3 with A nonempty, force A only after passing its possible old
  one-unit debt (present only when R is green).
- A Simple head gives a new A with allowance4 or5. The source assigns at most
  five units from recursive tail to that suspension and argues that at most
  one total unit passes outward after accounting for old A.
- A full head gives a new A with the printed total budget9: four from C', four
  from append and one for replaceHead. New allowance4 or5, together with the
  complementary old-A payment, gives the claimed outer budget5.
- Shallow tails and the A-empty/B-nonempty/A-and-B-empty cases require separate
  proofs. The prose calls the A-empty cases similar but does not show their
  payments, both forces, recursive-call distribution or shallow append cases.

There are two concrete gaps to resolve before treating these small constants
as a checked resource theorem:

**Mixed append threshold.** The proof's four-budget argument is explicitly
for deep/deep append, whereas the tail proof uses a four-budget append account
inside a full compound case. The printed `<3` mixed-case threshold needs its
own analysis. For example, take only the allowed numerical capacities of an
old deep value with size(F)>3 and size(R)=3. They permit four unpaid units on
A and one on B. Prepending a shallow size3 value takes the replacement branch:
new F has size3, so both new capacities are zero, and the new A wraps a suspended
cons. Under direct passing with one unit for that new body, the required
discharge is `4 + 1 + 1 = 6`. The symmetric boundary has the same issue.

This is an **unchecked allowance-level calculation**, not a construction of
a reachable saturated state, a lower bound on every possible accounting, or
a refutation of Theorem8.4's asymptotic O(1) statement. A stronger reachable
invariant, a different justified debit placement, or revised explicit constants
may address it. The printed local-capacity inequalities alone must not be
cited as an already established uniform four-budget proof for all append
branches. Any repair must retain the source threshold as a distinct variant.

**Charge normalization.** The Simple-head tail discussion does not explicitly
add the fresh suspended-call debit that the earlier Theorem8.3 discussion
counts. The full-head discussion separately names one for replaceHead.
Fix whether the recursive budget already includes its enclosing body's unit,
then count every actual body/primitive call exactly once. Prove the same
convention in the omitted A-empty cases. This is a proof-accounting obligation,
not a claim of a missing executable statement or a measured cost failure.
[T114 compared with T124]

The source additionally states that cons/snoc/head/last make no use of lazy
evaluation and take O(1) worst-case time. At the wrapper level they use a
bounded number of primitive deque calls, without forcing the catenable A/B/C
fields. A generic absolute worst-case theorem needs corresponding **primitive
D worst-case** bounds; DEQUE's type signature supplies none. With only
persistent-amortized primitive bounds, state and prove the appropriate
amortized composition instead. The earlier text permits ordinary deques from
Chapter5 or §8.4, so this premise cannot be hidden. T1.11 and Theorem8.4 remain
unproved in either interpretation. [T115,117,121–123]

## 12. Source corrections, interfaces and genuine ambiguities

All entries below were checked against rendered thesis pages. They have
different statuses and should not be collapsed into a single generic erratum.

| Location | Observation | Required disposition |
| --- | --- | --- |
| p111 redundant numeral declaration | Prints `datatype Nat = Digit Stream` although the intended carrier is the already declared stream type. | Record the alias declaration correction to `type`; do not pretend the literal line is a valid new datatype declaration. |
| p112 tail snippet and Figure8.1 p113 | Borrowing returns unprimed `Two(y,z)`, while the declared OneTwo constructor is `Two'`. | Use the declared constructor and document the name correction. The primed pattern constructors themselves are visible on the render; extraction corrupts some primes. |
| Figure8.2 p116 | The Two digit declaration literally contains `of of`. | Remove the duplicated keyword as a syntax correction. The carrier name Queue is consistent with the thesis DEQUE signature and is not an error. |
| p118 and Figure8.4 p119 | Empty-middle deep tail loses the front survivor. | Preserve the explicit four-element discriminator and the corrected semantic branch; this is substantive, not a formatting fix. |
| p118 versus pp120–123 | Compound middle is named C in the initial declaration/prose and A in the full figures. | Choose one consistent field name; preserve its distinct semantic/debit role. Figures8.5–8.6 agree with each other. |
| pp120–123, including cons/replaceHead clauses | Several record-construction expressions have an extra closing parenthesis. | Record the needed syntactic completion/correction; no new mathematical algorithm is implied. |
| Figure5.1 p53 versus Figures8.4–8.6 | The DEQUE signature exposes no `size`, but these functors call `D.size`. | Supply a stated sized-deque capability with semantic/cost laws, or a separately identified bounded-threshold observer. |
| Figure8.5 p122 | Mixed append uses `<3`; shallow/shallow uses `<4`. | Retain literal thesis thresholds and compare later with the historically recorded book variant. Recheck all debit constants at size3. |
| Theorems8.1–8.4 proofs | Some terminal/shallow/empty-schedule branches and exact debit-occupancy distinctions are omitted. | Complete the induction and physical-work account; do not label omitted cases already proved. |

For size tests, a complete traversal of D is not a constant-time primitive.
One valid prospective route is exact cached size with proved maintenance and
its chosen arithmetic model. Another is a bounded number of empty/tail
observations to decide thresholds2,3,4. The latter has different allocation
and demand behavior and needs primitive-operation bounds and safe domains;
it must be identified as a realization choice, not silently attributed to
the printed `D.size`. This refines existing `UNION-PREMISE-001` without
modifying any shared library API.

## 13. Related work, historical statements and unsupplied algorithms

The §8.6 attributions are source context, not new verified history or an
instruction to formalize every external paper. [T124–125]

- Recursive slowdown is attributed to Kaplan–Tarjan [KT95,KT96b], with links
  to regularity constraints [GMPR77] and Brodal's heap technique [Bro95].
- Lazy binomial heaps [Kin94,Oka96b] are described as implicit slowdown
  instances with constant amortized insertion and logarithmic other operations;
  scheduling in [Oka96b] is said to give worst-case bounds. These are related
  to existing book heap obligations, not a complete heap implementation supplied
  in Chapter8. [Oka96b] is *The role of lazy evaluation in amortized data
  structures*, as identified in the thesis bibliography.
- The Buchsbaum–Tarjan [BT95] catenable deque comparison gives log-star worst-case
  deletion and constant worst-case other operations. This chapter's claimed
  constant amortized result changes the cost mode; it is not a proof of a
  constant worst-case replacement. The independently developed [KT96a] work
  is listed in the bibliography as an August1996 draft revision of [KT95].
  Its complicated worst-case construction is not reproduced here.

The general slowdown templates, alternative forcing, numeral observers,
random access and restricted deque variants remain explicitly classified
source obligations even where only sketches or remarks are supplied. None
may disappear because it has no theorem number or complete printed functor.

## 14. Proposed independent cases and remaining integration work

The following are **specifications for future connected tests/proofs**, not
tests executed in this task. Expected values should be fixed independently
of the future implementation and then connected to source execution.

| Family | Discriminating cases to retain |
| --- | --- |
| Explicit slowdown | Empty; run length1 removal; Zero next to an Ones run; repair with/without a leading run; separated Twos; extension beyond the final digit. |
| Lazy inc / inc' | Same numeral value with different first argument-force timing; no-carry, carry, all-Ones and Nil; retained versions sharing a tail versus independently allocated equal tails. |
| Scheduled digits | First increments from zero; m=0,1,2; absent old jobs; a single old job; nonadjacent completed separators; two jobs; carry beyond the former highest digit. |
| Mixed binary and123 digits | Alternate `2^k-1`/`2^k` under an explicit demand observer; singleton decrement; One with nonempty tail; Three carry; alternating directions in the shared123 account. |
| Implicit queue | All four snoc cases; both front sizes and both rear sizes on tail; empty/nonempty middle borrow; pair ordering; both snoc force placements; empty exceptions. |
| Implicit deques | Shallow0–3; front/rear size3 insertion overflow; size1 borrow with empty/nonempty middle; simultaneous mixed-end operations; both restricted buffer specializations. |
| Simple catenable deque | Every shallow/deep append combination at sizes0,1,2; front/rear size2 collapse; the `[a,b] ++ [c,d]` survivor case; middle blocks of the minimum size; unequal depths. |
| Advanced append | Shallow sizes2,3,4 on both sides; all four endpoint-color combinations in deep/deep append; exact share order; retained and aliased operands. |
| Advanced tail/init | All six deep cases and their mirrors; full/degenerate compounds; minimal fringes; size4-to-size3 allowance loss; A-empty cases; final shallow collapse versus reconstructed Deep. |
| Generic primitive assumptions | Same ordered result for a sized realization and a bounded-threshold realization, with separately stated traces; distinguish wrapper work from the primitive deque's work. |

Before accepting an owning chapter, provide concrete definitions, validity
and ordered-value theorems, source-corrected equations where necessary, complete
exception/partial domains, suspension/forcing correspondence and measured
work recurrences for every retained variant. Prove the debit/history laws and
scheduled readiness before attaching the claimed amortized or worst-case
labels. Revisit full Book9/11 text, exercises and relevant Haskell listings
when the book is available; the thesis inspection cannot close them.

The only durable file authored by this task is this inventory. The frozen
Chapter7 inventory remains unchanged (SHA256
`9f584c9b5279afac58356c4806662e7621cf7a8868cba2266db2058ce113966a`).
All source, refs, dependencies, runtime/controller state, requirements and
trackers were left to the coordinator. No Lean/Lake/compiler/test or process
control action was performed. Durability inclusion is the coordinator's
checkpoint action. Every proposed formal obligation in this note remains
**unproved**.
