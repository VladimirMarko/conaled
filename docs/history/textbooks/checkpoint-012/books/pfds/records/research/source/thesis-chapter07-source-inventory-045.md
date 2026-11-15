# Thesis Chapter 7: complete source inventory for later bootstrapping work

Prepared on 2026-11-04 UTC by `/root/thesis_bootstrapping_inventory` during
recovery 045. **Source preparation only. Every proposed formal obligation in
this note is unproved.** No Lean implementation, compiler check, independent
acceptance review, ticket change, coverage closure or chapter advancement is
supplied here. Chapter 2 remains the current unaccepted frontier. These later
obligations belong principally to book Chapter 10 / local ticket 10010.

The complete thesis chapter is now inspected in this pass. The published book
PDF is absent from this recovery, so this is not a new complete book Chapter 10
inspection or a fresh comparison with its equations, exercises or appendix.
Retain the earlier book/thesis crosswalk as historical preparation and obtain
the actual missing book pages when that comparison is needed.

## 1. Source identity and inspection extent

The source is Chris Okasaki, *Purely Functional Data Structures*, CMU-CS-96-177,
September 1996, at the recorded source URL
<https://www.cs.tufts.edu/~nr/cs257/archive/chris-okasaki/dissertation.pdf>.
The actual local file inspected is
`research-pfds/source-assets/okasaki-thesis-1996.pdf`, 628,877 bytes, SHA-256
`f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072`.

All printed pages **85-104**, physical one-based PDF pages **97-116**, were
text-read. Pages 86-102 were also visually inspected from actual rendered page
images, including every mathematical/code page, all six figures, and the
complete displayed proof of Theorem 7.1. Page 85 is introductory prose;
page 103 completes related-work discussion; page 104 contains only the running
page header. All twenty pages were rendered. The PDF skill was used; system
`/usr/bin/pdftotext` and `/usr/bin/pdftoppm` produced reproducible intermediates
under `research-pfds/thesis-chapter07-045/`, outside checkpoint payloads.
The chapter contains **Figures 7.1-7.6**, **one numbered theorem, 7.1**, and
**no numbered exercises or numbered definitions**. This count does not replace
the unnumbered algorithm, invariant, translation and cost obligations below.

Supporting records consulted were `book-thesis-union.md`, the relevant
Chapter 7/Book 10 mapping in `union-scope-reconciliation.md`, the source
identities, and the `T1.04`, `T1.09`, `T1.14`, `TU.MODULES` and `TU.BOOTVAR`
entries of `thesis-obligations.json`. The exact record hashes at inspection
were:

| Record under `session/research/` | SHA-256 |
| --- | --- |
| `book-thesis-union.md` | `fd307d2221335bb8412b797b2a750be6d2752c17b487fa81d31ef89d61645ffd` |
| `thesis-obligations.json` | `d98a57b4aa508b2d2e40719e4e689ec15a7e5f67685b9029455c2e83d8b984ad` |
| `union-scope-reconciliation.md` | `1f1e008b6d183af59b91545ebd5b612210ffc08c1b7dc1cf3730bb444a2ce780` |
| `union-source-identities.json` | `937977ba7efe6e527c1dffdca7d480e2cb9a39a3ad3b3914d18fd9b7c8a5e24a` |

The local IDs in this note are navigation aids for the future chapter owner.
They are not new canonical review-finding IDs or edits to the coverage ledger.
The existing sixteen `T1.*` contracts and supplemental rows keep their actual
pending statuses.

## 2. Complete page and figure accounting

| Printed pages | Source content | Classification / future owner |
| --- | --- | --- |
| 85 | Operating-system/compiler bootstrap analogies; structural decomposition versus structural abstraction; attribution to Buchsbaum | Expository terminology and historical attribution; do not infer a compiler-bootstrap correctness theorem. |
| 86-87 | Uniform list/tree recursion, nonuniform sequence type and size function; uniform `ElemOrPair` translation and missing shape invariant | `T7-SEQ-*`; `TU.MODULES`, Book 10. |
| 87-90 | Repeated banker-queue append motivation; recursive queue of suspended blocks; normalization; uniform encoding; logarithmic middle size, iterated-log depth and operation analysis | `T7-Q-*`; `T1.04`, Book 10. |
| 89, Figure 7.1 | Complete five-operation bootstrapped queue listing and mutually recursive helpers | Source equations and failure cases; printed empty-test RHS is missing. |
| 88 footnote, 90 remark | Fixed small-list base case; depth thresholds for ordinary and size-4 base cases | Bounded-base variant and finite-threshold claims, separate from empirical advice. |
| 90 | Suspended-middle and stream-of-suspended-lists variants | Both branches of `TU.BOOTVAR`; neither follows just from the baseline log-star result. |
| 91-93 | Generic collection bootstrap templates, explicit root element, empty case and nonempty-child refinement | `T7-SA-*`; instance-specific semantic and construction premises. |
| 93-96 | Strict catenable-list tree representation and right-associated child linking; persistence failure; lazy repair | `T7-CAT-*`; Book 10. |
| 94, Figure 7.2 | Catenable-list signature: empty, isEmpty, cons, snoc, catenation, head, tail and EMPTY | Exact sequence/failure interface. |
| 94, Figure 7.3 | Node-valued tree whose preorder is the twenty-element sequence a through t | Connected traversal example; queue order is significant. |
| 95, Figure 7.4 | Tail transformation linking the four child trees a,b,c,d from right to left | Preserve all child contents and the exact depth changes used in the debit proof. |
| 96-98; 97, Figure 7.5 | Final lazy catenable-list functor; two debit invariants; Theorem 7.1 and its complete proof | `T7-CAT-DEBIT-*`; `T1.09`. |
| 99-100; 102, Figure 7.6 | Bootstrapped heap operations and worst-case transfer; final higher-order recursive functor | `T7-HEAP-*`; `T1.14`, `TU.MODULES`. |
| 100-101 | Element-type sharing constraint, recursive-module limitation, exclusion of effectful primitive functors and concrete inlining route | Generic/concrete correspondence and explicit construction assumptions. |
| 91 and 98 practitioner boxes; 101 and 103 | Performance recommendations, related algorithms, historical complexity claims, conjectured pairing-heap bounds and language-design discussion | Explicit historical/external-result classification; not new proved local results or a requirement to reproduce every cited paper. |
| 104 | Running header only | No additional mathematical obligation. |

## 3. Structural decomposition and nonuniform recursion

### T7-SEQ-01: the illustrative sequence and its size

The nonuniform sequence on page 86 is empty, or one element together with a
sequence of pairs. Its size equation is `s(nonempty(x,p)) = 1 + 2*s(p)`, whereas
the ordinary list equation is `1 + s(tail)`. The source claims linear work for
list size and logarithmic work for this sequence size under unit-cost arithmetic.

The intended formal observation must count underlying element occurrences,
not just outer constructors. At recursive depth `d`, the finite nonuniform
shape has `2^d - 1` elements. Thus the displayed datatype does not represent
every possible finite length; it is an illustration of a useful nonuniform
shape, not a complete arbitrary-length sequence interface. Prove the size
observation and actual traversal recurrence, with an explicit empty convention
such as a `log(n+1)+1` envelope. Do not turn machine-integer multiplication or
addition into a constant-time theorem about arbitrary-precision Lean execution.

### T7-SEQ-02: the uniform translation

Page 87 replaces nested element types by an `ElemOrPair` tree and an ordinary
uniform sequence. The outer component must contain an element, the next a
pair, the next a pair of pairs, and so on. This is a separate recursive
well-shapedness predicate; arbitrary values of the uniform type do not have
the original nonuniform meaning. A shape-preserving encoding/decoding and
size correspondence should be proved on that valid subset, with an invalid
mixed-depth example showing why the predicate is necessary.

The source expressly treats polymorphic-recursive SML listings as presentation
code and sketches the coercions needed for executable uniform code. Lean's
ability to express a suitable datatype does not itself establish the claimed
translation. The discussion of Standard ML and polymorphic recursion is
source-language context, not a claim that an arbitrary uniform datatype is
isomorphic to its nonuniform predecessor. [pp86-87; `TU.MODULES`.]

## 4. The baseline bootstrapped queue

### T7-Q-01: carrier, contents and independent invariants

The nonempty record on pages 88-89 contains a strict front list `F`, a recursive
FIFO queue `M` of suspended lists, a combined length `LenFM`, a reversed rear
list `R`, and `LenR`. Empty has its own constructor. Its sequence observation is

`F ++ concat(force-each-in-FIFO-order(M)) ++ reverse(R)`.

Keep the following distinct: source representation/type discipline; nonempty
front for a nonempty record; nonempty blocks in `M`; exact cached lengths;
`LenR <= LenFM`; semantic contents; and the growth property used in the cost
argument. `LenFM` counts underlying elements in `F` and all blocks in `M`, not
the number of blocks. The recursive `M` is itself a valid queue at the next
element type. Source `int` fields need nonnegative/exact-length premises in any
uniform raw representation. A type-level finite list does not justify arbitrary
stored integers.

### T7-Q-02: public operations, normalization and termination

Account for empty, isEmpty, snoc, head and tail, including observable EMPTY
failure for the last two on empty input. Inserting into empty creates a strict
singleton front. Ordinary snoc adds to the reversed rear before normalization;
tail removes one front element and decrements `LenFM` before normalization.

The normalizer first compares `LenR <= LenFM` **non-strictly**, as visibly
printed on page 88 and in Figure 7.1. On overflow it appends a new suspended
reversal to `M`, adds the old rear length to `LenFM`, and clears the rear. It
then calls the front-checker. If `F` is empty and `M` is nonempty, the checker
forces the first block, installs that block as `F` and removes it from `M`.
It leaves the combined `LenFM` unchanged during that transfer. If both are
empty, balanced exact lengths imply that the whole queue, including `R`, is
empty. That implication must precede the source's abbreviated empty return.

Prove semantic preservation and invariant restoration by these actual
mutually recursive helpers, not by specifying an arbitrary normalization
with the desired answer. Their recursive calls act on the structurally lower
queue level. Establish a genuine termination measure and sufficient domains;
do not add a public fuel bound without proving sufficiency. An invalid empty
block or bad cached length must not be accepted merely because a partial
pattern match happens to succeed.

### T7-Q-03: uniform implementation correspondence

Pages 89-90 give an `ElemOrList` representation: level-zero elements use the
element tag, and deeper blocks use the suspended-list tag. The external
snoc/head and internal block insertion/removal need the appropriate tag
introduction/elimination. The text gives a coercion sketch, not a complete
second executable listing. Formal work must define the level invariant and
show correspondence of all operations, failure observations and delayed
reversal placement. Unrestricted tagged values are not the same domain as the
nonuniform version. [Also `TU.MODULES`.]

### T7-Q-04: source demand and amortization

The text states that rear-reversal suspensions are created at the same times
as in banker queues and forced one operation earlier. This is a source demand
claim in addition to equal eventual sequence contents. It needs a comparison
of the actual relevant histories, including empty/singleton boundaries and
the adjustment of the reversal's debit payment. The claimed inherited
constant amortized reversal contribution does not prove that the whole queue
operation is constant: recursive middle-queue work remains. [pp87-90.]

Pages 87-88 also motivate the representation by the repeated processing in
left-associated stream append: the first segment is revisited by subsequent
appends and each later segment incurs its reversal plus later traversals.
Record this as a measured comparison under a declared stream-demand model.
The source's individual-block doubling justification needs the correction in
section 8; it must not be adopted as a false invariant. Empirical claims that
fewer suspensions are faster are not Lean runtime results.

### T7-Q-05: middle size, depth and actual call multiplicity

Preserve the intended chain of obligations:

1. A valid middle queue has logarithmically many blocks relative to the
   underlying element count. Use an independently proved growth condition
   compatible with all interleaved snoc/tail traces; see section 8.
2. Each recursive level reduces the number of represented elements to a
   logarithmic-sized collection. Define the iterated-log convention and derive
   a depth bound with explicit finite cutoffs.
3. Snoc invokes at most one next-level snoc. A tail can invoke both a snoc and
   a tail at the next level, but those two calls cannot both invoke another
   snoc at the following level. Prove this from the actual normalization
   branches and the state passed from the first call to the second. Merely
   counting recursive syntax as two independent branches gives the wrong bound.
4. Consequently at most one snoc and one tail are charged at each level of
   one top-level operation. Combine their actual constant amortized per-level
   work with the depth bound and persistent reversal accounting.

This is the `T1.04` target: direct head has constant worst-case cost; snoc and
tail have `O(log* n)` amortized cost. State an additive constant for small/empty
inputs. Do not replace iterated logarithm by ordinary logarithm, log-log, or a
constant merely because the practical sizes are small. [p90.]

### T7-Q-06: bounded base and the two constant-amortized variants

The page-88 footnote permits using ordinary lists for queues below a fixed
size. Page 90 cites a size-4 base and numerical depth thresholds, including
the very large `2^65536` scale in the ordinary discussion and a three-level
claim below roughly four billion elements for the modified base. Those are
separate finite size/depth claims with explicit level conventions. If retained
as formal conclusions, derive them from the actual chosen cutoff recurrence;
do not use them to infer unbounded constant complexity. The claim that this is
practically faster is empirical context.

The two `TU.BOOTVAR` constructions on page 90 remain separate obligations:

| Variant | Actual source change | Required unproved connection |
| --- | --- | --- |
| Suspended recursive middle | Store the recursive queue `M` itself in a suspension and execute its operations lazily; elements of that queue are still suspended blocks. | Give concrete force/delay placement, FIFO/refinement and failure laws, and an actual persistent debit argument yielding constant amortized snoc/tail. The baseline log-star proof does not discharge this. |
| Two-level stream middle | Replace the recursive `M` by a stream of suspended lists. Append a new block incrementally to that stream; its complete append traversal costs linear work in the old number of blocks. | Make the described sketch concrete, prove contents/demand behavior, and amortize the incremental traversal over top-level operations. Do not silently count a full stream append as one constant-time step. No polymorphic recursion is needed in this representation. |

The latter sketch refers to `[Oka96a]`, identified by the thesis bibliography
as Okasaki, *Functional data structures*, Advanced Functional Programming,
LNCS 1129, pp131-158, August 1996. That paper was not fetched or read in this
pass. If the sketch lacks a detail required for a claimed source equation,
obtain and inspect the relevant primary source; do not invent a correspondence.

## 5. Structural abstraction before its concrete instances

### T7-SA-01: the type construction and nonempty children

Pages 91-92 motivate turning a collection of elements into a collection whose
elements are smaller bootstrapped collections. A recursively nested primitive
collection alone has no explicit place for the original element. The selected
form therefore stores one root element plus a primitive collection of child
bootstrapped collections, with a separate empty case.

The source's more precise alternative has a nonempty recursive carrier and
wraps it in an optional empty/nonempty outer carrier. The concise listing
instead uses one datatype and requires that every child stored in a primitive
collection be nonempty. Keep that invariant explicit in both concrete
instances. In the heap instance it also protects the partial child comparator.
Neither the schematic recursive-type equation nor an opaque operation-only
interface constructs an arbitrary recursive carrier automatically. Any formal
generic construction must state its actual admissibility/representation
requirements and preserve them in the promised concrete instantiations.

### T7-SA-02: templates and distinguished-element selection

Singleton uses one root and an empty primitive collection; insertion and join
use primitive insertion rather than recursively calling bootstrapped join.
The page-93 templates permit swapping root roles to fit the collection. They
are design templates, not a universal ordered-sequence equation for every
primitive insertion operation. The chosen root must be the accessible
distinguished element: first element for a sequence or minimum for a heap.

Deleting that root leaves a primitive collection of nonempty children; the
essential instance-specific work is converting it into one bootstrapped
collection. Prove the appropriate sequence or occurrence observation for each
instance, instead of inferring both from an unqualified generic collection law.

## 6. Catenable lists and Theorem 7.1

### T7-CAT-01: interface, strict baseline and exact sequence meaning

Figures 7.2-7.4 and pages 93-95 supply all seven operations and their empty
failures. A nonempty tree stores one element and a FIFO queue of nonempty
children; its observation is root followed by the concatenated child
observations in queue order. Figure 7.3's a-through-t preorder is a useful
connected check with nontrivial internal fringes.

For nonempty inputs, catenation attaches the second tree as the last child of
the first. Empty is a left/right identity. Cons and snoc use a singleton on
the corresponding side. Tail removes the root, returns empty when it had no
children, and otherwise links the child queue from right to left. The source
`linkAll` is a nonempty fold-right variant: take the first child, inspect the
remaining queue, and either return that child or link it to the recursively
combined remainder. Prove nonempty inputs to its partial primitive calls and
the exact traversal/refinement equation.

Associativity here concerns observed catenation of element sequences.
Different linking associations need not produce equal tree values, force
events or later work. Preserve each fringe in Figure 7.4 and show that the
result loses precisely the old root. Repeated values and self-catenation must
retain occurrence multiplicity; this is not set union.

### T7-CAT-02: the strict implementation's boundary

Page 96 claims potentially linear work for strict tail and constant amortized
tail under ephemeral use, while warning that the same implementation is
inefficient under persistence. Supply the actual operation/cost model and
primitive-queue premises for this comparison. A star-shaped root with many
children and repeated tails of that same old version is a discriminating
branching-use family: strict `linkAll` repeats its child processing. This is
a proposed example family, not a new compiled refutation or an assertion about
automatic host optimizations.

The chapter permits persistent constant-amortized as well as constant-worst-case
primitive queues. Their operational laws and their persistent cost guarantees
are separate inputs. A queue signature by itself does not make each primitive
call unit-cost or establish the composed amortized bound. If a baseline
comparison assumes constant worst-case primitives, state that specialization.

### T7-CAT-03: the lazy repair and its actual demand

The final carrier contains a queue of **suspended** nonempty child trees.
Every recursive `linkAll` call is suspended. Removing the first child from its
queue forces that child's suspension; its remaining recursive combination is
delayed. Nonempty catenation also wraps its second, already available tree in
a trivial suspension to fit the carrier. Figure 7.5 retains all empty cases.

Prove a value/refinement relation to the strict preorder operation and also
the actual force/delay/memoization events. Root head is a direct strict read
and does not traverse the child queue. Pure extensional equality alone does
not prove that sharing protects future persistent uses. The primitive queue
must preserve the FIFO order and the identities of the child suspensions
needed by the source cost account.

### T7-CAT-DEBIT-01: both independent debit invariants

Pages 96-97 index nodes by left-to-right preorder, beginning at zero. Let
`d_t(i)` count debits on a node, `D_t(i)` the inclusive prefix sum, and `D_t`
the total over a nonempty tree. The invariants are:

- `d_t(i) <= degree_t(i)`;
- `D_t(i) <= i + depth_t(i)`, with root depth zero.

Use the actual finite-tree degree identity to derive `D_t <= |t|-1 < |t|`.
The second invariant gives zero unpaid root debits. The algorithm forces a
child suspension when its root is about to become the accessible root, so the
cost proof must establish discharge before that force. Neither invariant may
be replaced by the desired constant amortized-operation bound as an assumption.

The tree-level presentation must eventually connect to the real suspension
allocation/history model and the same actual source execution. Debit support,
occurrence multiplicity, work of forced bodies and primitive-queue costs are
not automatically identical. In particular, the bounded foundations 10021 and
10022 do not by themselves close arbitrary body work or `TU.TRACE`/10017.

### T7-CAT-DEBIT-02: catenation's one-debit budget

For two nonempty inputs, pay immediately for the trivial suspension around the
second input: its root degree did not increase. Nodes in the first tree keep
their index and depth. A node in the second shifts its index by `n=|t1|` and
its depth by one; its prefix debits gain the total of the first tree. The
strict bound `D_t1 < n` supplies the required slack. Preserve this actual
root/depth/degree calculation and empty-input cases. The one-debit statement
is a sufficient per-operation budget, not a claim that an empty-identity case
necessarily creates or pays exactly one new debit. [Theorem 7.1, pp97-98.]

### T7-CAT-DEBIT-03: tail's three-debit budget

For `m` child trees in queue order, write the child index as `j`. The right
association makes every original node in that child move from preorder index
`i` to `i-1`, and changes its depth by `j-1`. Each non-last linked child's root
gains one child edge. All links except the outermost are delayed; the final
recursive call is also delayed even though it performs no link.

Assign the new link debits to the roots whose degrees increased. Pay the final
base-call debit immediately because that node's degree did not increase.
The remaining prefix excess is bounded by two relative to the new left-linear
bound; discharge the first two available debits. Thus the intended total
budget is at most three, with fewer actual payments permitted when fewer
debits exist. Establish that the next forced root is covered before forcing.

Handle `m=0`, `m=1` and the last child explicitly. The source's intermediate
formula `D_new(i-1)=D_old(i)+j` must be assigned to the appropriate pre-payment
bookkeeping state; after the final base-call debit has been paid, an upper
bound is the uniformly safe statement. The prose on page 98 uses a strict
inequality for the old left-linear invariant, whereas its definition and the
displayed derivation use the non-strict inequality. The non-strict hypothesis
suffices. Do not silently strengthen the invariant or force an incorrect
exact-equality claim at endpoint cases. [Theorem 7.1 and Figure 7.4.]

### T7-CAT-COST: complete operation consequences

Combine the actual bounded unshared work, the two debit budgets and the
primitive persistent-queue contract to establish `T1.09`: constant amortized
cons, snoc, catenation and tail; direct head has the stronger constant
worst-case bound. Empty/isEmpty also have their actual constant observations.
This theorem concerns the stated source evaluation/cost model, not elapsed
Lean execution time, allocator bytes or a performance ranking. [pp93,96-98.]

## 7. Generic heap bootstrapping

### T7-HEAP-01: representation, order and exact contents

The nonempty bootstrapped heap holds a root element and a primitive heap `H`
of nonempty bootstrapped subheaps. The root is below every element in its
unfolded contents. The primitive ordering compares child roots using the
same fixed underlying element order. Separate nonempty-child validity,
primitive-heap validity, root/descendant order and exact occurrence contents.
The empty constructor is permitted externally but never stored as a child:
the source child comparator is undefined on it. [pp99-102; Figure 7.6.]

### T7-HEAP-02: all source operations

Empty and isEmpty expose the outer constructor. FindMin reads the root
directly and raises EMPTY on empty input. Merge preserves either empty
operand and, when both are nonempty, inserts the larger-rooted **whole child
heap** into the primitive heap beneath the smaller root. Insertion forms a
singleton first and merges it with the old heap. Prove exact occurrences,
ordering, nonempty children, persistence of the old values and failure laws.

The final Figure 7.6 branches on `Elem.leq`; on a non-strict tie it keeps the
first root. Page 99's preliminary polymorphic sketch instead writes the
comparison as `<` while explicitly calling it the chosen element comparator.
If that schematic notation is interpreted as a literal strict order, tied
distinct values choose the opposite root. Keep the interpretation explicit:
the final functor is the unambiguous source equation, and any separate strict
variant needs a qualified observation relation. No unqualified same-selected-
occurrence equality between those readings is justified by this inventory.

### T7-HEAP-03: deleteMin and selected-child agreement

After removing the bootstrapped root, an empty primitive heap yields empty.
Otherwise, obtain the selected minimum child `Heap(y,p1)` from `H.findMin p`,
remove **that same child occurrence** with `H.deleteMin p`, and merge `p1`
with the remaining primitive heap beneath new root `y`.

The same-selected-child premise matters when child roots tie: finding a child
with root 0 and descendant 1 while removing a different child with root 0 and
descendant 2 would duplicate the former fringe and lose the latter. Both
primitive operations merely returning/removing *some* minimum is too weak.
This is a required primitive interface law, not a new assertion that the
source implementation violates it. The existing Chapter 3 readiness records
already identify the earlier thesis minimum-observation/removal agreement.
Retain that connection when choosing the future exact heap capabilities.

Prove the new root's minimum property over both merged parts, exact removal
of one old root occurrence, remainder validity, and the observable distinction
between empty failure and successful deletion of a singleton to empty. A
keyed replacement/set contract is insufficient for these occurrence laws.

### T7-HEAP-04: worst-case cost transfer with real size parameters

The primitive assumptions on pages 99-100 are worst-case constant insertion
and logarithmic merge, findMin and deleteMin. The bootstrapped findMin needs
no primitive operation; nontrivial merge needs one root comparison and one
primitive insertion; insertion adds a singleton and that same merge path.
Bootstrapped deletion needs one primitive emptiness test, then the selected
minimum observation/removal and one primitive merge when nonempty.

Make the wrapper's constant work and element-comparison cost explicit. If a
primitive heap contains `m` child heaps, its own size parameter is `m`, not
the sum of their descendant sizes. Nonempty children justify bounding `m`
by the bootstrapped unfolded element count. Establish the corresponding size
bounds for both primitive heaps merged after deletion, and retain additive
constants for empty/singleton input. These are the required links to `T1.14`:
constant worst-case insert/merge/findMin and logarithmic worst-case deleteMin.
No laziness-based amortization may replace those worst-case hypotheses.

### T7-HEAP-05: higher-order modules and a real generic result

The final construction accepts a **heap-producing functor** `MakeH` and then
an ordered element structure; it does not merely accept one monomorphic heap
whose element type cannot change. The sharing constraint ensures that
`MakeH(E)` really uses `E`'s element type. To store bootstrapped heaps inside
`H`, the construction recursively ties the bootstrapped carrier/root
comparator to `MakeH` instantiated at that carrier. [pp100-102.]

Preserve the source's restriction to well-behaved effect-free primitive
functors; the text explicitly does not justify arbitrary effectful recursive
module initialization. A concrete skew-binomial inlining is the stated SML
implementation route: remove the separate module recursion so only suitable
datatype recursion remains. The generic conditional transformation and its
concrete source-faithful realization are both `TU.MODULES` obligations. A
single concrete heap does not prove the generic construction, while a
hypothetical family supplied with all desired results does not construct the
promised concrete implementation.

The future formal design must state the actual finite/recursive carrier
construction assumptions needed for its generic input representation. The
chapter's operation signature and cost assumptions alone do not justify an
arbitrary recursive type equation in Lean. This note chooses no new framework,
adds no axiom and proposes no implementation before the owning chapter opens.

## 8. Source corrections and unresolved source-level qualifications

### Already retained: the missing empty-test result

Figure 7.1 on printed page 89 visibly omits the RHS of the `isEmpty Empty`
case. The intended empty-test result is true, as required by the public queue
meaning; the nonempty case is false. This pass independently confirms the
printed omission already recorded in `book-thesis-union.md`. The second
front-checker clause also displays an unmatched closing parenthesis. Preserve
these as source transcription/syntax corrections, not alternative executable
equations. This pass does not claim a new book Figure 10.2 inspection.

### T7-Q-GROWTH: individual pending blocks do not always double

The page-90 explanation says successive lists in `M` at least double in size;
page 88 uses a related individual-block doubling explanation for the banker
queue motivation. That literal property is too strong for interleaved updates
of the page-89 queue. The following is a **hand calculation from the source
equations, not a compiled program or Lean-checked counterexample**. Here the
`M` column is its abstract FIFO sequence of suspended-block lengths, not its
internal recursive record layout.

| Public operation prefix | Outer `F` | Block lengths in `M` | `LenFM` | Outer rear length |
| --- | --- | --- | ---: | ---: |
| Start empty; enqueue a,b,c,d,e,f,g | `[a]` | `[2,4]` | 7 | 0 |
| Tail twice, removing a then b | `[c]` | `[4]` | 5 | 0 |
| Enqueue h,i,j,k,l | `[c]` | `[4]` | 5 | 5 |
| Enqueue m; the rear now overflows | `[c]` | `[4,6]` | 11 | 0 |

The first rear block contains b,c; the second contains d,e,f,g. The two tails
force/remove the first block from `M` and leave one front element c. The
non-strict balance test defers the next rotation when rear length equals 5,
then appends the six-element block h through m. Both pending blocks are
nonempty, the cached lengths agree with contents, and `6 < 2*4`.

A sufficient weaker property to prove is **superincreasing block weights**:
for every current block, its length is greater than the sum of all earlier
remaining block lengths. A newly appended rear block satisfies this because
rotation requires

`|R| > LenFM = |F| + sum(lengths of current M blocks)`.

Removing the first block only reduces the earlier-prefix sums relevant to
surviving blocks. If this invariant is established for the actual execution,
the first `m` blocks have combined length at least `2^m - 1`; induction uses
that a new positive integer weight is at least the prior sum plus one. Thus
the intended logarithmic middle-count bound still has a plausible correct
route. This is an **unproved proposed repair**, not a proof that all following
depth/amortization claims hold. Retain the old literal statement, the exact
counterexample obligation, the weaker invariant and the remaining log-star
argument separately. Do not claim either a checked Lean refutation or a new
comparison with the absent book Chapter 10.

### Other qualifications that must stay explicit

- The two page-90 constant-amortized variants are sketches with distinct
  force placement; no full code or new cost proof was supplied in this pass.
- The page-98 strict/non-strict prose discrepancy and pre-/post-payment
  prefix bookkeeping must be resolved as described above without weakening
  Theorem 7.1's actual two-invariant conclusion.
- The page-99 comparator notation and final non-strict Figure 7.6 equation
  need an explicit tied-choice interpretation; equal minimum priorities
  alone do not identify an exact selected child heap.
- Primitive queue/heap laws, their cost assumptions, source recursion
  admissibility and effect restrictions are premises, not consequences of
  merely implementing the named SML signatures.

These are later source-accounting obligations, not findings against the current
unchanged common candidate or reasons to fabricate a current gate failure.

## 9. Contextual and external-result classifications

The analogies and naming discussion on page 85 are explanatory. Page 87's
standard-language restriction and page 101's recursive-module limitation are
language context for the two explicit translation obligations above. Page 90's
claims about practical constants and the practitioner boxes on pages 91 and
98 are empirical/historical advice; no performance ranking is proved here.

Section 7.3 credits earlier bootstrapping uses and compares external catenable
structures, including AVL-based logarithmic operations, pull-based variants,
and recursive-slowdown results. Preserve the source's distinction between the
number `k` of operations and unfolded size `n` in its externally cited
log-log/iterated-log bounds. These are cited external results, not extra local
algorithm implementations silently imported into this chapter's acceptance.
The comparison explicitly distinguishes the present amortized catenable lists
from the cited worst-case constructions.

The mergeable-heap paragraph likewise distinguishes imperative amortized
claims, persistent lazy variants and Brodal/Brodal-Okasaki worst-case results.
Its pairing-heap bounds are identified as conjectured in the 1996 source;
do not turn that historical conjecture into a proved local theorem or make
a current-status claim without new source research. The polymorphic-recursion
paragraph cites type-inference undecidability and the historical Haskell 1.3
explicit-signature rule. Classify these as external language results/context,
separate from the selected representation correspondences. The relevant
external papers were not newly searched or read here.

## 10. Concrete later verification targets and stopping point

The following cases distinguish the intended claims when the owning chapter
eventually implements them:

- Nonuniform size at depths 0-3, the corresponding element counts, and a
  malformed uniform encoding whose tags do not have the required depth.
- Queue empty/singleton failures, equality versus overflow of rear/front
  lengths, front refill without changing combined length, a recursive cascade,
  and the exact `[4,6]` middle-block counterexample above.
- Baseline versus lazy-middle versus stream-middle demand observations for
  retained old versions. Equal fully forced values alone are insufficient.
- Catenable empty identities, repeated elements, self-catenation, the complete
  a-through-t preorder, four nontrivial child fringes, and zero/one/many children
  on tail. Exercise both debit invariants at equality and the actual first
  forced child; keep the last suspended base case separate.
- Repeated tails of one old strict catenable version versus the explicitly
  shared lazy work. Connect primitive-queue costs to the same operation trace.
- Heap empty and singleton removal, smaller/larger/tied roots, repeated
  occurrences, self-merge, and tied child roots with distinct descendants to
  exercise minimum-observation/removal agreement.
- At least one suitable concrete primitive heap and the generic conditional
  interface/cost transfer, preserving the effect-free recursive construction
  and exact element-type/order identity. Direct root findMin should exhibit no
  primitive heap traversal.

No test or theorem implementing these cases was written or run. No Lean/Lake
command, dependency/runtime setup, source/ref mutation, root process action,
tracker/requirement edit or external write occurred in this task. The only
durable artifact authored is this inventory. All manuscript text/rendering
intermediates remain outside `session/`. Parent/root owns checkpoint upload
and the continuing exact-candidate acceptance process.

The full thesis Chapter 7 source-preparation pass is complete at the stated
extent. All algorithm, semantic, invariant, translation, demand and cost
obligations remain **unproved**, including `T1.04`, `T1.09`, `T1.14`, both
`TU.BOOTVAR` variants and the applicable `TU.MODULES` content. Complete book
Chapter 10 and Haskell-appendix comparison, its exercises, implementation,
statement review, actual compiler/audit validation and both independent
acceptance axes remain future work in the existing chapter order.
