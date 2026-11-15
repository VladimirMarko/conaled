# Independent bounded review — #1017 Color plan

**Outcome: clear for planning after one verified provider-name correction.**
No unresolved actionable finding remains. This is independent preparation
review within the existing whole-book workflow. It is not an implementation
review axis, a Lean compiler result, execution evidence, or chapter acceptance.
Every proposed algorithm, adapter, proof, measured bound and connected
application remains an implementation obligation after predecessor acceptance.

## Frozen inputs and actual assessment scope

| Input | SHA-256 | Size |
| --- | --- | --- |
| Initial frozen plan, ../specs/1017-Color.md | 065289a5207241bbcdcf45d94d75eb5768a2b57f7a2da3c7bc60ca816e50c89e | 77,945 bytes; 822 lines |
| Corrected final plan | 8b69472e3eb9a0157375d2e47292af07ba0eaf098b5a22d418ea0021cd0ceed7 | 77,948 bytes; 822 lines |
| Complete VFA 2.1 Color.v | 67b3410af5fece56c69f4e8301fd6505e89371cfa1279d069ca945b9b2b33370 | 23,243 bytes; 602 lines |
| ../source/Color.inventory.json | 9af39e4c88d43d99c3aae211b49310ef0e9c4c2e088c8b38d8112b1abe6995f1 | Complete chapter inventory |

Root independently read all 602 source lines before reviewing the complete
822-line frozen plan. Root also read all 72 pages of the required Appel
Color.pdf text and visually inspected the consequential slides 19, 63 and 67.
The PDF identity was independently fetched and later rechecked locally:
764,823 bytes, SHA-256
37238a67dda3adc00669e1a304634831b00e527d3fd0518798a9a639605cc5ee.
The ordinary web reader returned HTTP 403; the bounded direct request succeeded.
The temporary research copy is not a checkpoint deliverable.

The inspected project baseline is
3279bacaec4087cc0d6b7e6b8ae862109cb2dfec. Actual accepted predecessor APIs remain
future inputs. AGENTS, its architecture/domain and implementation/example
guidance, README build/audit requirements, applicable ADRs and the user's local
tracker/checkpoint instructions continue to apply. No extra implementation
review loop was opened.

Root directly inspected the relevant BinaryTree, Finmap, Finset, resource and
Rocq source contracts. A separate read-only corroborator checked all 42
local/core identity rows, all four external identities, and the precise native
TreeMap/TreeSet, Pairwise uniqueness and SimpleGraph/Coloring hypotheses.
Its assessment found no additional discrepancy. The sections below distinguish
source reasoning and provider checks from future formal proofs.

## Complete source coverage

All 53 exact declaration IDs occur once and in inventory order. All fourteen
exercise names, star counts and source ranges match; each is standard and none
is optional or advanced. All 35 command kinds and line numbers match in order,
and all five alias names and source lines match. Root performed these
reconciliations against the actual inventory and rechecked the source digest.

The status counts agree: 23 definitions, twelve source-proved declarations,
sixteen admissions, one pedagogical Abort and one transparent Function proof.
The Function's termination proof depends on an admitted lemma; the plan does
not treat it as an already completed obligation. Four inner admit commands in
the set-removal exercise are explicitly discharged by the planned proof.
The earlier aborted Sremove_elements statement is preserved as an experiment,
with its intended proposition supplied by the later completed theorem; it does
not become another axiom or a duplicated public implementation.

Both multi-declaration exercises are covered. The ten cardinal_map hints and
nine Mremove_elements hints retain actual semantic counterparts. Printing a
module does not impose coverage of every unused external module member.
The source computations, imports, equality demonstrations, Boolean decisions,
fold conventions and substantive prose each have a disposition.

## Required reading and source selection

The required slides explain both low-degree removal and a heuristic that
removes a high-degree vertex when no low-degree vertex is available. The
chapter and slide 63 instead return the empty list at that point. The plan
preserves the chapter's actual program, while keeping the alternate heuristic,
planarity arguments and historical context outside its algorithm coverage.

Slide 71's prose palette condition is stronger than its displayed predicate.
The plan preserves the displayed edge-guarded source predicate and separately
requires the stronger all-bindings palette invariant for the implemented result.
The suggested coalescing paper is only a bibliographic pointer here: its body
was not used as an unstated proof or performance dependency, and its blocked
retrieval does not stand in for a completed reading.

The NP-completeness discussion is correctly qualified: fixed k at least three
is distinguished from two-colorability, and a conclusion ruling out all
polynomial algorithms is conditional on P differing from NP. No such
metatheory, planar-color theorem or verified register allocator is claimed.

## Keys, raw carriers and finite observations

The selected representation reuses PosNum and BinaryTree specializations.
BinaryTree.get really follows the low-order constructor bits: one at the root,
bit0 to the left and bit1 to the right. With optional payloads its result is
nested Option; flattening it or using getOrElse none gives source optional
binding. With Bool payloads false is the source empty membership observation.
An absent node and an internal node with absent payload have equal lookup
observations, whereas a present binding containing an empty adjacency set
remains a graph vertex.

BinaryTree.map maps every payload and preserves the raw shape. Mapping
Option.map f therefore has the source value-map result after the stated
adapter; source mapi's key-building computation is a separate cost question.
BinaryTree.numNodes counts every internal node, not only present bindings or
true set entries. The plan correctly keeps those observations distinct.

The source bit relation has the constructor order O before H before I, with
recursion when outer constructors agree. It is not PosNum's numeric order.
The plan leaves the numeric instance unchanged and keeps source equality as
literal positive-key equality. Its operations do not acquire unnecessary
numeric conversions or ordered searches.

The actual PositiveSet choose visits the current root before its left subtree,
then its right subtree. Its minimum visits the left subtree first. The example
set containing 1 and 2 therefore distinguishes source choice 1 from bit
minimum 2 and enumeration [2,1]. An ordinary ordered-container minimum cannot
replace source choice on the strength of a membership theorem alone.

All-input raw semantic laws are retained for lookup, insertion, pruning erase,
difference, cardinality, enumeration, folds and choice. Arbitrary padding is
allowed semantically; extensional equality does not identify raw tree shapes.
The finite Finmap/Finset observations are independent specifications, not
replacement executable algorithms. Finmap equality retains arbitrary payload
equality, while transport through a later adjacency-set observation needs an
explicit respectfulness premise for arbitrary predicates on raw sets.
The low-degree predicate has that respectfulness only after the relevant
cardinality bridge is proved.

## Actual provider boundaries

Root read the public Rocq 9.0 OrderedTypeEx, FSetPositive and FMapPositive
definitions. The checked external identities refer to immutable Stdlib commit
fda356e01346f7766b282ef9f44080cce2be23b3. The corroborator independently verified
that all three raw files equal the V9.0.0 bytes and that the official tag resolves
to that commit. Their identities match the plan:

| Provider | Bytes | SHA-256 |
| --- | ---: | --- |
| OrderedTypeEx.v | 15,487 | e30f31413cf5a544c1f997b02bb5ccd1f69e215c75b761fc12b184ec9af41ed5 |
| FSetPositive.v | 38,480 | 596ebe108c8baa96cbe12670e6275355a3d4a48e91898a173d8a9f26802adb9a |
| FMapPositive.v | 33,802 | 49be1b1d115a068510b265581271421ec2780265cf0b63fa4b947b57a6b2005d |

VFA specifies a version floor rather than a unique external checkout; the
plan accurately describes this explicit reconstruction choice. It also
preserves the licensing/provenance requirement for any code actually adapted.

The map's enumeration and fold carry forward prefixes, while the set's
traversals use reversed prefixes. Both folds agree with left folds over their
ordered elements. The map callback is invoked at Some payloads; value map uses
Option.map and therefore invokes its value callback only at present bindings.
These definitions justify the planned callback counts, not a unit cost for
every whole traversal. The map enumeration's append and the set enumeration's
accumulator are different source computations.

Finmap.foldl explicitly requires pairwise commutation of updates for every
accumulator. It is a multiset fold and supplies no general ordered-fold
substitution. The finite erase/domain/image/cardinality lemmas have the
expected membership and decision assumptions. They do not specify choice.

The native ordered-container alternatives have the hypotheses recorded in the
plan. TreeMap insert/erase lookup laws use TransCmp and compare the written or
erased key first and the queried key second. Literal key membership and the
simple key-aware map lookup law additionally use LawfulEqCmp. Its size_map
theorem is indeed stated under TransCmp. The map and set fold-toList equations
are comparator-unconditional; ascending order comes from separate TransCmp
theorems. TreeSet minimum's none law needs TransCmp, and its literal
member/minimality some law additionally needs LawfulEqCmp. None supplies the
missing source-choice adapter.

List.Pairwise.eq_of_mem_iff inherits Std.Antisymm from its section and adds
Std.Irrefl. Strict-order asymmetry satisfies the former vacuously. The plan
does not invent a totality or payload-order requirement. The source setoid
adapter still needs equivalence and order compatibility, and its strict
sortedness forbids repeated equivalent elements. In contrast, the mod-10
equivalent-membership examples genuinely have different lengths; they are
not permutation or count equality.

The SimpleGraph bridge also has the stated boundary. SimpleGraph stores
adjacency, symmetry and looplessness, without a finite stored-domain field.
Its Coloring is a total function satisfying adjacent-color inequality.
Restricting to the actually colored domain and using the separate all-palette
result is necessary for the proposed palette-subtype coloring. This cannot
replace the source optional map or its isolated-vertex domain information.

## Graph recursion, support and correctness

The source graph remains an arbitrary raw finite optional map. Domain
membership is successful binding, including empty adjacency sets. The full
subset_nodes characterization retains arbitrary Boolean predicates without
a graph validity premise. Removal erases one binding, then invokes set erase
on every remaining adjacency value; the whole-map recurrence is not replaced
by a neighbor-only worklist.

A successful choice is both eligible and stored. Map erasure loses exactly
one binding and value mapping preserves the remaining domain, proving the
cardinality decrease without symmetry, looplessness or positive K.
The source None branch stops even on a nonempty high-degree core. The
selection equations, fixed K, distinct chosen vertices, residual support and
adjacency restriction are all separate required obligations.

The colors_of observation counts only successful optional color lookups and
collapses repeated colors as set members. The color1 helper overwrites on
successful choice and leaves the entire old coloring unchanged on failure.
The final right fold reads the original graph at every step. Reusing residual
adjacency while painting would be a different program.

The source coloring_ok palette clause is guarded by an edge, just like its
distinct-color clause. An isolated arbitrary binding outside the palette can
satisfy that predicate. The plan does not conceal the stronger AllPalette
property in the definition; it proves it independently for results from empty.

The general phase-two proof is sound even for repeated vertices and overwrites.
For an edge touching the written vertex, exclusion of already used neighbor
colors handles the outgoing direction; symmetry handles the other endpoint,
and looplessness excludes the double-equality case. Other bindings are
unchanged. This proves the partial-correctness invariant for an arbitrary
finite processing list. Specializing it still uses the actual source
selection output and does not waive selection fidelity.

The selected-support strengthening has different dependencies and its proposed
argument is sound on raw graphs. Later selected vertices are outside the
removed prefix. A tail coloring is supported there, so colors seen through
original adjacency agree with colors seen through the current residual
adjacency at the selected vertex. The residual degree is below palette size;
the finite image bound gives an available color. This proves every selected
vertex receives a color without symmetry or looplessness, including dangling
neighbors and the empty-palette boundary. It does not prove full initial-domain
coverage, maximality or optimality. The conditional complete-selection
corollary retains its closed-class and eligible-node hypotheses.

## Counts, normalization and execution boundaries

The exact callback sums follow from occupied domain size n-t at residual stage
t, including the final failed selection stage. For r successful removals,
selection and candidate choice are called r+1 times. Predicate/degree tests
sum over t from zero through r, while adjacency-erasure callbacks sum n-t-1
over the successful stages only. The resulting triangular formulas are
correct with r at most n and Nat-safe arithmetic. Coloring performs r steps,
and its neighbor lookups use original adjacency degrees, not residual degrees.
Successful selected-support proves exactly r coloring writes.

These are planned instrumented events, not currently compiled counts.
Termination measure data is not automatically an executable cardinality pass.
Conversely, the explicit adjacency-cardinality and initial palette-cardinality
computations must be charged. A fuel adaptation would retain any setup cost.

The raw padded-carrier boundary is explicit: n may be zero while structural
size is arbitrarily large. A bound based only on present key sizes therefore
requires normalization. The proposed recursive normalization excludes
unoccupied dead subtrees and must be proved preserved by each used operation.
On normalized inputs, trie size is bounded by summed occupied key bit lengths;
the graph and palette bit bounds include mentioned dangling neighbors.

The conservative primitive expression is a plausible proof target for coloring
from the specified already constructed graph and palette inputs. Its terms
account for repeated forward-prefix map scans, repeated adjacency cardinality
work, original-neighbor lookups/color insertion, palette differences and
terminal work. Unit-cost Nat arithmetic is an explicit model choice.
Graph construction has its separate edge-list input and charges, and requested
enumeration/decoding/output has its own export work; the callback formulas
cannot silently absorb those phases. Actual measured recursion, erasure,
invariants and numeric bounds remain to be proved before any bound is accepted.
No native allocation, GC, compiler-correctness or timing result is inferred.

The exact source graph trajectory and outputs are consistent with root-first
choice: selection [4,1,2,6,5], domain enumeration [4,2,6,1,5], and color entries
[(4,1),(2,3),(6,2),(1,2),(5,1)]. Its callback counts are fifteen degree tests,
ten adjacency-erasure attempts and fourteen original-neighbor color lookups.
These are source-derived review calculations, not Lean execution evidence.
The plan separately requires kernel-checked cases and an actual future run.

The four-cycle/two-color example correctly shows a colorable graph on which
selection stops immediately. The directed and self-loop examples distinguish
raw support/termination laws from properness. The edge constructor preserves
self-loops and uses both original adjacency reads; duplicates and reversed
edges do not multiply extensional set members. These are meaningful connected
boundary cases rather than claims of total or optimal graph coloring.

## Finding, exact correction and disposition

| ID | Status | Finding and verification |
| --- | --- | --- |
| COLOR-PLAN-001 | Fixed and independently verified | Section 7 called the existing growth theorem Growth.isBigO_of_nat_bound. The actual file declares namespace Resources and theorem Resources.isBigO_of_nat_bound. The author corrected only that qualified name; the provider table already used the correct one. |

Root reported the finding before declaring the plan clear. After correction,
root checked the final digest and replaced the single corrected phrase with
its original spelling in memory. That reconstructs the initial frozen digest
exactly, proving every other byte unchanged. The independent corroborator
repeated this verification. All coverage and provider-identity results
therefore apply unchanged to the final frozen plan.

No further actionable omission, incorrect provider assumption, weakened source
contract or unsupported completion claim was found. This closes the bounded
planning review only. Chapter acceptance still requires accepted Decide,
actual Lean implementations/proofs, complete connected cases and execution,
measured erasure/bounds, integrated stable candidate build and exhaustive audit,
required regressions, both independent implementation review axes and immediate
final candidate verification.

Only this review record was written by root's assessment. The corroborator
performed no writes. No Color algorithm, compiler, benchmark, repository source,
cache, configuration, dependency or GitHub mutation was part of this review.
Root retains tracker, gate and durability-checkpoint ownership.

