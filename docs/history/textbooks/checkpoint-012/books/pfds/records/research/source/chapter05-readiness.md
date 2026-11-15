# Chapter5 union scope and reuse readiness

Prepared2026-11-03. This is read-only source/mathematical preparation, not Chapter5
implementation, a new implementation/review loop, a checked theorem or acceptance.
Chapter2 remains earliest unaccepted; Chapter3 implementation has not begun.
No Lean source, candidate, compiler input or acceptance frontier changes here.

## Inspected sources and page fidelity

Read the complete published Chapter5, printed39–56, all Figures5.1–5.6,
Lemma5.1, Theorem5.2 and Exercises5.1–5.9 with their subparts. Also read thesis
printed13–22: traditional amortization and queue implementation, the repeated-
version failure, and the transition to logical histories/lazy debit accounting.
The graph/lazy-debit material at thesis19–22 is already assigned to10017/10021
and Chapter6; its presence does not turn Chapter5 into a claim that persistent
amortization has already been formalized.

Visually checked book40/41/44–51/53–55 and AppendixA186/198–200, plus thesis
14/15/18/19. The source images were rendered with system Poppler; an initial
runtime-wrapper invocation failed before rendering, then /usr/bin/pdftoppm
succeeded. Text/renders are research-pfds/chapter05 assets and excluded from
deliverables. Exact PDF identities remain union-source-identities.json; book
SHA b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41,
thesisSHA f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072.
For both, printed page+12=physical PDF page.

Important visual corrections: splay bigger/partition uses non-strict <=, not the
extracted <. Lemma5.1 assumes positive x,y,z and y+z<=x, with a strict conclusion
1+log2(y)+log2(z)<2log2(x). Theorem5.2 is non-strict. The insertion simplification
on p51 is printed as an approximation, not a valid exact <= simplification.
The exact expression must survive small-size formalization.

## Complete chapter obligations

| Source | Formal scope to retain |
| --- | --- |
|39–41; thesis13–15|Actual versus amortized charges along the same trajectory; prefix as well as whole-run savings; allocated-before-spent credit accounting; exact telescoping with both boundary potentials; conversion between located credits and aggregate potential under explicit domains.|
|42–44, Figs5.1/5.2; thesis16–18, Figs3.1/3.2|Five-operation FIFO interface, pair-of-lists abstraction, nonempty-front invariant, exact smart-constructor/snoc/head/tail equations and empty failures; worst-case constant snoc/head and linear tail; both constant amortized analyses.|
|44–45, E5.1a/b and Fig5.3|Eight-operation deque interface; both sides nonempty for size>=2; half-split/reverse rebalancing, singleton/empty behavior; amortized proof using the absolute length difference.|
|45–46, E5.2/5.3|Actual Chapter3 binomial insertion carries, tree-count potential, constant amortized insertion, independent located-credit analysis; multi-input potential for merge and retained logarithmic merge/deleteMin amortized bounds.|
|46–51, Figs5.4/5.5, E5.4/5.5/5.6|Duplicate-preserving splay heap; separate smaller/bigger and paired partition; exact rotations and partition observations; all heap operations/failures; real log-size potential, Lemma5.1, both zig-zig and zig-zag access cases, amortized insertion and deleteMin.|
|51–52, E5.7|Plain findMin is not independently logarithmic amortized; paired findMin/deleteMin accounting and generic ExplicitMin remedy; actual insertion-plus-inorder sort, sorted multiset semantics, linear work on ascending and descending inputs.|
|52–54, Fig5.6, E5.8a/b/c|Nonempty-child multiway pairing heaps; exact link/insert and two-pass delete; child/sibling binary conversion, root no-sibling invariant, binary operations and correspondence; splay-style real potential proof for merge/delete and resulting operation bounds.|
|54–55, E5.9; thesis19|Reachable retained-version sequences that defeat ephemeral queue/binomial/splay/pairing amortized claims; include construction cost and actual operation observations. Identify failure of linear consumption, not failure of functional correctness.|
|55–56 and practitioner remarks|Historical attributions, empirical rankings and conjectures are classified as such. No current performance ranking or resolution of a historical open question is inferred or asserted.|

There are nine numbered exercises;5.1 has(a,b),5.8 has(a,b,c). The proof exercise
5.5 and the sorted-input complexity exercise5.7 are substantive obligations, not
exposition. Splay merge is included for functional completeness and can cost
linear time; the chapter does not supply a general logarithmic meld guarantee
for that implementation. Its broad introductory phrase about every operation
must be read with the explicit later findMin/merge qualifications.

## Existing conaled capabilities and exact limits

Inspected main76d77a107deb37c30e0b061c30b03a3f8c6aa12c and frozen5e048f7.
The selected Potential, FIFOContracts, BinaryCounter, SymmetricCosts,
SymmetricWorkload, Symmetric.Core and AbstractFIFO files are unchanged between
these candidates. Existing code is reuse evidence, not new PFDS acceptance.

| Existing code | Reuse and remaining connection |
| --- | --- |
|Resources.Measured/Workload|One actual measured computation, monoidal observations, erasure, reweighting, run composition and invariant/value fusion. No new executor is needed.|
|Resources.Potential|budget follows the actual state; run_potential/run_potential_exact telescope with initial/final potential; run_zero_potential and constant-charge corollaries preserve assumptions. It is currently Nat-valued, not the real logarithmic splay theorem.|
|Resources.BinaryCounter|Actual increment/flip cost, ones potential and finite sequence bounds. Useful model/connection for binomial carry, but not itself a proof about link calls or heap occurrences.|
|Sequences.AbstractFIFO / Resources.FIFOContracts|Existing simulation/observation and implementation-specific accounting witnesses. Its delete is total and endpoint head uncharged; source empty exceptions and charged queries need explicit adapters/observations.|
|Sequences.Symmetric.Core|List-pair carrier, Inv, contents, half splitting, both ends, correctness, and duality. Matches the E5.1 invariant/strategy; empty deletion is deliberately a total extension, not the source exception.|
|Resources.SymmetricCosts / SymmetricWorkload|Actual measured length/split/reverse recursions, distinct charge/work observations, absolute-difference potential, all-end operations, trajectory bounds and endpoint square. Supplies nearly all E5.1 accounting machinery once source-interface and failure correspondence are shown.|
|Search.OrderedTree.Basic|Mathlib BinaryTree, independent inorder occurrences and All are suitable structural ingredients for splay. Its strict Ordered invariant is a set invariant and cannot certify duplicate-bearing splay trees.|
|Search.ExactPriority and Chapter3 heap work|Exact occurrences/minimum removal and the planned lawful meld/peek/empty facade should be reused. Chapter5 must consume accepted Chapter3 realizations/ExplicitMin, not recreate a competing heap hierarchy.|

The absolute-difference potential in SymmetricCosts is written as the sum of two
truncated Nat differences, which equals the intended absolute length difference.
Its source charge satisfies charge+Phi(after)<=Phi(before)+2. The actual
length/split/reverse visit counter satisfies work<=2*charge+4; consequently
work+2*Phi(after)<=2*Phi(before)+8 and whole empty runs cost<=8*m.
This explicitly connects the exercise's potential to structural work. It does
not prove the false claim that the same unscaled Phi pays every counted visit
with a fixed bound. Explain the two observations and scaling in the source
adapter. Keep independently justified exact rebalance work2*n+3 and singleton
tail work2*n+4 rather than replacing them with a cheaper invented counter.

Likewise, a batched-queue source-step model counting a reverse cons visit and
outer dispatch can reproduce the textbook m+1 tail calculation. The existing
reverseRun also counts its terminating nil, so direct reuse carries an additional
constant. Either is a legitimate declared model; prove erasure/correspondence
and the resulting bound instead of silently conflating their exact constants.

## Real potential, credit locations and multiple inputs

The source defines real potentials, and splay requires real base2 logarithms.
Do not force these into the existing Nat Potential theorem by truncating
subtraction or rounding away a claim. Reuse the same measured run and ordinary
ordered additive algebra for the required extension. Preserve the exact
identity total_actual+Phi(final)=Phi(initial)+sum_amortized, or its local-
inequality version, before dropping a nonnegative final potential. An individual
amortized charge may be signed; a chosen nonnegative upper budget is a distinct
quantity. The current Nat API remains valid for the existing clients.

The credit/potential equivalence needs an explicit common quantity domain. Sum
located nonnegative credit mass to obtain potential. Conversely, for nonnegative
real potential, placing that mass at a distinguished root and using positive/
negative parts of its change gives a prospective credit construction. Natural
indivisible token counts cannot represent an arbitrary real logarithmic potential
exactly. This is a design obligation, not a newly proved equivalence.

Book45–46 generalizes to sums over input/output objects. An actual sequential
frontier of uniquely identified live occurrences supplies a useful model: consume
the inputs once and add fresh output occurrences, with any discarded potential
accounted for. An unrestricted persistent invocation graph does not telescope by
that argument. The source's set notation must not erase repeated aliases, and a
self-meld consuming the same saved output twice must not receive its potential
twice for free.10021's unrestricted logical quiver is intentionally different
from an ephemeral single-consumption accounting discipline.

## Splay semantics, exact access cost and examples

Use duplicate-preserving inorder semantics. The naive bigger and rotated bigger
have the same selected occurrences, but different shapes. smaller retains values
equal to the pivot without a second equality test. The combined partition processes
two nodes at a time; the source explicitly warns that its phase differs from the
separate functions. Therefore prove output-content/order correspondence, not a
false literal pair-of-trees equality. Shape-sensitive measured recurrences belong
to the actual implementation being analyzed.

Let weight(t)=numNodes(t)+1, including weight(empty)=1, and
phi(t)=log2(weight(t)); total Phi sums phi over actual nodes. A binary node has
weight(node)=weight(left)+weight(right). Pinned Mathlib
Analysis.SpecialFunctions.Log.Base supplies Real.logb, logb_mul/div,
logb_le_logb_of_le, logb_lt_logb and logb_nonneg; use their actual positive/base>1
premises. Lemma5.1's strict inequality follows with positive y,z; do not replace
it by an OCR-damaged strict input assumption.

Partition's measured call count includes its terminal call. Its amortized charge
is calls+Phi(left_result)+Phi(right_result)-Phi(input), bounded by
1+2*log2(weight(input)). Prove both directions of zig-zig and zig-zag, plus empty,
one-node and the branch terminating at an empty child. The insertion expression
derived from it is2+2*log2(N)+log2(N+1), N=weight(old_heap). The printed
approximately2+3*log2(N) is an asymptotic simplification, not a uniform exact
upper bound: atN=1 the expressions are3 and2. Retain an exact additive envelope
such as3+3*log2(N) forN>=1 if proved; do not weaken the base case to fit the prose.

deleteMin follows only left branches and has no key comparisons. A model
counting only comparisons cannot establish its actual traversal complexity.
Plain findMin does no restructuring, so repeated calls can remain linear. A
combined observation/removal operation can charge both traversals together;
the generic ExplicitMin wrapper supports clients with arbitrarily many queries.
Keep this a client protocol or an actual wrapper, not an unexplained assumption
that queries occur at most once. Splay merge's source recursion and contents
must still be implemented, without promising the same amortized bound as insert.

For E5.7, use a linear inorder traversal (accumulator/difference-list or a proved
equivalent implementation). Repeated list append on a skew tree is not linear.
Ascending/descending insertion generates simple boundary cases; account for
both insertion and final traversal under the actual cost model. Duplicates and
tagged equal priorities should be retained to make tie/ordering assumptions
observable. General partially sorted-input adaptivity is source motivation
unless a precise quantitative contract is independently specified.

## Pairing carrier reuse and binary representation

Pinned Batteries66e469188fe07963e5cf666c7d4433f45b8131c5 contains
Batteries.Data.PairingHeap, read in full. PairingHeapImp.Heap is already a
child/sibling forest. Its merge, combine, singleton, head? and deleteMin are
the relevant executable operations. NoSibling, size_merge/size_combine,
WF.merge/WF.combine and deleteMin_fst supply structural facts. Complexity in
comments is not a formal potential/cost proof or global minimum proof.

Raw merge deliberately ignores sibling fields. Its content/size contract must
therefore require no siblings for each heap input; applying it to arbitrary
encoded forests loses elements. combine instead consumes the sibling forest
in adjacent pairs and a right fold, matching the requested two-pass structure.
Do not confuse it with Chapter3's repeated pair-round bulk builder.

The source multiway datatype excludes empty children. A mutually specified
tree/forest conversion can map it to this existing child/sibling carrier. Prove
contents, sizes, no-sibling at the root, half-order, conversion inverse on the
appropriate domain, and operation correspondence. Binary left subtrees represent
descendant children; right subtrees represent siblings and are not required to
be above the current node's priority. Root-only heap order is insufficient.
Duplicate occurrences and child order must survive conversion.

Extend this actual executable core with separate occurrence/minimum semantics
and measured operations, using only the comparator laws the proofs require.
The dependency's WF packages a TotalBLE conditional; do not treat it as an
unconditional minimum guarantee for a non-total strict comparison. The real
log-size potential in E5.8 is over the binary encoding, not an assumed sum of
logarithms of multiway subtree sizes. Connected cases need odd/even child counts,
0/1children, ties, mixed descendants, and nonempty-child/no-sibling failure cases.

## AppendixA is a separate realization boundary

Visually inspected BatchedQueue p186, BinomialHeap p198, SplayHeap pp198–199,
and PairingHeap pp199–200. Their value equations and explicit empty errors need
mapping to the chapter realizations. Haskell's implicit laziness is not a proof
that strict SML operation-cost recurrences transport unchanged; distinguish
finite fully observed values from demand/heap-sharing/cost statements.

Two concrete comparator differences must remain in the union:

- Main SML pairing Fig5.6 uses Elem.leq, selecting the first root on equal
  priorities; Haskell p199 uses strict x<y, selecting the second root on a tie.
- Haskell binomial p198 uses non-strict <= for link, matching the main SML
  link, but strict < for removeMinTree, where the main SML uses Elem.leq.
  Chapter3's main SML/thesis tie contracts and the existing backend-difference
  inventory remain separate. Do not assume one literal selected occurrence
  satisfies every source listing.

A 200dpi reinspection on2026-11-03 corrected the initial readiness note, which
wrongly generalized the strict comparison to binomial link. Its lower bar is
clearly visible in the higher-resolution page. This is a source-reading error,
not an erratum in the book. The original report is preserved byte-for-byte as
chapter05-readiness-initial.md. The strict minimum-tree and pairing-merge signs
were confirmed at the same resolution. No implementation, prepared Chapter3
requirement or distinct-priority counterexample changes with this correction.

Splay partition uses <= in both listings, visually confirmed. A relational
duplicate-preserving heap contract can connect different lawful tied results,
but exact source-tree equations and shape-sensitive cost analyses still need
the appropriate variant or a proved transport. This note is additional
Chapter3 source evidence for its future activation, not a replacement or an
unrecorded change to its prepared requirements.

## Future proof cases and sequencing

Reuse exact queue/deque laws through both-end clients, including empty failure,
one element in either component, odd/even half splits, and an arbitrary initialized
queue carrying explicit initial potential. For binomial, apply Chapter3 link
counts to ranks0..k-1 and show the potential drop on an actual carry; preserve
multiple-input consumption and deletion's reversed child list. For splay retain
all four partition rotations, boundary sizes, duplicate pivot, separate-functions
phase mismatch, real logarithmic inequality, sorted construction/traversal and
plain-versus-cached minimum clients. For pairing retain actual child-pair order
and a root with many singleton children.

The separate report chapter05-persistent-counterexample-readiness.md supplies
proposed reachable families for E5.9, including setup work and repeated use of
the SAME retained heap. They must later be checked through actual source
recurrences and public laws. A constant-size sample alone cannot establish an
asymptotic failure, and no counterexample refutes a theorem whose ephemeral
premise it violates.

Activate Chapter5 only after Chapter4 acceptance, selecting its real integration
base then. Requirements, connected examples, isolated whole-chapter build/audit,
both independent full-scope axes and immediate final verification remain required.
No exercise, complexity contract, chapter or10017 obligation is discharged by
this preparation.
