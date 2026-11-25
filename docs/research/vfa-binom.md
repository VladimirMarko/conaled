# VFA Binom: exact dense queues and their costs

This ledger maps the complete Binom primary, every optional exercise, the source
module and Eval command to the actual Lean owners and connected examples.
The raw queue, occurrence/rank theory, full maximum-deletion contract, measured
recursions, capacity histories, amortized bounds and machine-key correspondence
have checked implementations. The companion [runtime note](vfa-binom-runtime.md)
specifies the executed public seam and the final comparative validation protocol.
Chapter qualification is derived from the exact candidate's complete independent
CONTENT acceptance. Artifact reconstruction, secured publication and receiving
whole-library acceptance remain separate gates.

## Authenticated source and reading provenance

The primary is VFA 2.1 `Binom.v`, 400 lines and 13,042 bytes, SHA256
`f73f18cac4c3a6a38a0e83d4194429eb7ab684ee68068a88025610a13d5c31ed`.
The release identity is 2.1 (2026-08-24 10:11, Coq 9.0.0 or later); the chapter
footer separately says 2026-08-24 09:43. The original26,914-byte inventory had
SHA256 `a353316c6502b49edd90d11b98171ecd396db60f940bfc17a77b5247bd2c1680`.
Its mathematical coverage has ordinary owners in this note's
[44-record map](#complete-44-record-lexical-mapping) and
[21-exercise map](#all-21-exercise-headings), plus [CTB-97](../textbooks/CTB.json).
The44 records comprise22 definitions,20 source admissions, one proof in the
source and one grading record. The21 exercises, one module and one Eval command
are separate denominators. The old inventory's pending label is historical;
its former scratch path is not needed to read these complete maps.

The complete canonical specification is
`docs/history/textbooks/checkpoint-012/books/vfa/records/research/specifications/1015-Binom.md`,
71,393 bytes, SHA256
`956eacc44542fc26fe5dee1b7a4cd119acb00f6f92ed82d46dc17ccdbdec77c7`.
The full primary and full canonical plan were read before implementation by the
coordinator and the mathematical authors. The plan's architectural and semantic
requirements remain the chapter scope, including every optional exercise.

Required readings are [Andrew W. Appel, *Binomial Queues* (2016)](https://www.cs.princeton.edu/~appel/Binom.pdf)
and [Robert Sedgewick, *Algorithms*, third edition in Java, section 9.7 (2002)](https://www.cs.princeton.edu/~appel/BQ.pdf).
Their research copies remain external to deliverables. Root's historical
reading record, dated2026-11-17 00:40:55 UTC, reports complete text reading of
both documents; its old scratch receipt is not assumed available here.
visual inspection covered Appel pages 10–20 and Sedgewick PDF pages 2, 3, 6, 8, 9.
No full visual review of the remaining pages is claimed. A and B also read the
complete text extractions; their authorship receipts do not substitute that work
for root's precisely attributed visual boundary.

| Required reading | PDF identity | Complete text identity |
| --- | --- | --- |
| Appel, 20 pages | 820,707B; `b5e6e8f3e7115ed4e7faffc629ac18f777fd21b77ffb5b061819e276f9d78b69` | 9,502B; `05b769b55e6fd38f6434fecbcc076aff1675dac8a1d134fe54088bd13dc3d329` |
| Sedgewick, 11 PDF pages | 236,099B; `300abc44d593f97ed609dab095f3b4db08c956d21d0f2f129dafbef9e3e73d69` | 39,191B; `3dad4726c2d2b7bf9d14c3163fc142d32906a28a97a6449b675ccfca21bdd739` |

Appel supplies the first-child/next-sibling picture, dense slots, links and
root-spine traversal. Its slide wording about strict heap dominance is reconciled
with the actual source's non-strict bound, which permits duplicate keys.
Sedgewick Definition 9.4 supplies the non-strict left-heap interpretation;
pages 409 and 413–414 distinguish resized arrays from capacity controlled by a
historical maximum, and Property 9.8 motivates the comparison potential below.
The external imperative implementation's tie choices, resizing and three-occupied
merge branch do not replace VFA's actual recursions. The required reading is
fully accounted for without claiming to formalize Sedgewick's separate numbered
exercises or Java API extensions.

## Implementation and observation owners

`Applications/Search/BinomialQueue/Core.lean` is the single raw program owner.
It factors only the key comparator and retains every literal branch.
`Contents.lean` owns the inductive occurrence relations and aliases the accepted
`Trees.preorder`; it does not introduce a competing traversal. `Ranked.lean`
owns shape/order validity, rank and mass, occupancy and exact stored lengths.
`Maximum.lean` owns the actual CPS and first-root/deletion proofs.
`Contract.lean` instantiates all eleven accepted `Search.MaximumQueue.Laws`
fields and reuses `MaximumQueue.exactQueueOnValid` with the explicit contents
witness. The source list realization remains
`Applications/Search/ListMaximumQueue.lean`; keyed map-style
`PrioritySearchQueue` semantics are not substituted for occurrence queues.

Connected fixtures are in `Examples/BinomialQueues.lean` (A) and
`Examples/BinomialQueueDeletion.lean` (B). In the tables below, unqualified Lean
names mean `Search.BinomialQueue.*`; `A.` means `Examples.BinomialQueues.` and
`B.` means `Examples.BinomialQueueDeletion.`. Existing `Nat` and `BinaryTree`
are named explicitly. The named application/witness column distinguishes a
concrete proof use from closed inhabitants that demonstrate a theorem's premises.

## Complete 44-record lexical mapping

“Checked” below refers to the retained author elaboration/root export and the
actual bodies presently inspected. It is not a whole-chapter qualification claim.
Every stable ID is retained in source order; the grading row receives only its
administrative disposition.

| Stable source ID and provenance | Mathematical disposition | Existing Lean declaration(s) | Application/witness and semantic assessment |
| --- | --- | --- | --- |
| `Binom.BinomQueue.key@30` (definition) | Nat specialization | `natOperations`, `natGreater` | A.singleton_rank. The source key is Nat. The reusable raw layer is polymorphic; natOperations selects the literal Nat comparator. |
| `Binom.BinomQueue.tree@32` (definition) | Existing carrier | `BinaryTree`, `BinaryTree.nil`, `BinaryTree.node` | A.singleton_mass; A.singleton_height. Reuse BinaryTree, with Leaf mapped to nil and Node mapped to node; no second tree datatype. |
| `Binom.BinomQueue.priqueue@44` (definition) | Existing list carrier | `Queue` | A.source_fold_shape. Queue K abbreviates List (BinaryTree K); positions are dense rank slots, including holes. |
| `Binom.BinomQueue.empty@46` (definition) | Definition checked | `empty`, `empty_eq` | B.empty_delete. The literal empty list; its validity and empty occurrence witness are separately proved. |
| `Binom.BinomQueue.smash@48` (definition) | Definition and branch laws checked | `smash`, `smash_nodes`, `smash_bad_left`, `smash_bad_right` | A.tied_smash_shape; A.malformed_smash. Exactly two proper outer nodes link. The true branch keeps the first root; ties take the second. Malformed outer shapes return nil. |
| `Binom.BinomQueue.carry@56` (definition) | Definition and branch laws checked | `carry`, `carry_nil_nil`, `carry_nil_node`, `carry_hole`, `carry_leaf`, `carry_occupied` | A.carry_empty_leaf; A.carry_first_hole; A.carry_three_places. Retain all five ordered source cases and the actual recursive smash t u argument order. |
| `Binom.BinomQueue.insert@65` (definition) | Definition checked | `insert`, `insert_eq` | A.source_fold_shape; A.insertion_occupancy. Construct the singleton and call carry; no preprocessing or rank cache. |
| `Binom.BinomQueue.join@80` (definition) | Definition and branch laws checked | `join`, `join_nil_left`, `join_nil_right`, `join_nodes` | A.join_000 through A.join_111; A.join_empty_left; A.join_empty_right. Both empty-input carry bases and all eight occupancy choices are exposed. Three occupied inputs emit c and link the two operand heads. |
| `Binom.BinomQueue.unzip@92` (definition) | Definition and CPS/occurrence proofs checked | `unzip`, `unzip_eq_append`, `unzip_node_id`, `unzip_contents` | B.unzip_nonidentity; B.unzip_continuation_suffix; B.unzip_continuation_not_wrapper. Right-sibling recursion builds source closures. For arbitrary cont the result is unzip t id ++ cont []; it is not cont (unzip t id). |
| `Binom.BinomQueue.heap_delete_max@98` (definition) | Definition and child-forest proofs checked | `heapDeleteMax`, `heapDeleteMax_node`, `heapDeleteMax_bad`, `heapDeleteMax_valid`, `heapDeleteMax_length`, `heapDeleteMax_mass`, `heapDeleteMax_bound` | B.rankTwo_unzip; B.rankTwo_children_ranks; B.malformed_heap_fallback. Only a proper outer node detaches children. A rank-r heap yields r occupied slots starting at rank zero, mass 2^r-1, bounded by its removed root. |
| `Binom.BinomQueue.find_max'@104` (definition) | Definition and literal provenance checked | `findMaxAux`, `findMaxAux_eq_or_mem`, `findMaxAux_first` | B.tagged_first_scan; B.tagged_distinct_equivalent. The actual accumulator returns its literal seed or the first literal root in the winning preorder class; equal priorities do not force key equality. |
| `Binom.BinomQueue.find_max@111` (definition) | Definition and first-maximum specification checked | `findMax`, `findMax_eq_none_iff`, `findMax_some_split`, `findMax_some_valid_split`, `findMax_some_bound` | A.source_fold_maximum; B.tagged_first_scan; B.padded_empty_delete. Skip nil, initialize at the first occupied root, then use the strict scan. None means all slots nil; some 0 remains distinct. |
| `Binom.BinomQueue.delete_max_aux@118` (definition) | Definition and exact reconstructed split checked | `deleteMaxAux`, `deleteMaxAux_of_split`, `deleteMaxAux_valid`, `deleteMaxAux_contents`, `deleteMaxAux_fst_length`, `deleteMaxAux_snd_length_lt` | B.middle_auxiliary; B.last_auxiliary; B.shifted_child_base_zero; B.malformed_auxiliary_prefix. The first output is prefix ++ nil :: suffix with unchanged base/length. The selected absolute rank is i+prefix.length; the detached children always start at zero. Preserve the raw fallback. |
| `Binom.BinomQueue.delete_max@129` (definition) | Definition and complete source chain checked | `deleteMax`, `deleteMax_some_iff`, `deleteMax_some_valid`, `deleteMax_some_relate`, `deleteMax_some_count`, `deleteMax_length` | B.first_delete; B.middle_delete; B.last_full_contract; B.repeated_counts. Use actual find, auxiliary split and native join. Successful deletion removes exactly one literal maximum occurrence, preserves validity and stored slot length. |
| `Binom.BinomQueue.merge@136` (definition) | Native definition checked | `merge`, `merge_eq`, `merge_valid`, `merge_relate`, `mergeValid_entries` | B.native_meld_shape; B.native_meld_entries. Merge is join p q nil, never reinsertion or sorting. Its source relation and separate ExactQueue native-meld observation retain all occurrences. |
| `Binom.BinomQueue.pow2heap'@143` (definition) | Predicate and shape/bound facts checked | `Pow2HeapAux`, `pow2HeapAux_mono`, `pow2HeapAux_bound`, `pow2HeapAux_numNodes`, `pow2HeapAux_height` | A.sibling_example_rank; B.rankTwo_not_binary_heap_order. At successor rank, the left child uses the current root bound and the right sibling keeps the external bound. Inner size+1 is 2^n and height is n. |
| `Binom.BinomQueue.pow2heap@154` (definition) | Predicate and exact size facts checked | `Pow2Heap`, `pow2Heap_iff`, `pow2Heap_numNodes`, `pow2Heap_height` | A.source_fold_rank_three; A.source_rank_three_size; A.source_rank_three_height. A proper outer root wraps the inner predicate; outer rank n means 2^n keys and BinaryTree.height n+1. |
| `Binom.BinomQueue.priq'@162` (definition) | Generalized predicate checked | `ValidFrom`, `validFrom_cons`, `validFrom_append`, `validFrom_getElem`, `getElem_numNodes` | B.shifted_valid; B.shifted_first_base_two. Every position advances the absolute rank, including nil. Splits and indexed slots use i+offset. |
| `Binom.BinomQueue.priq@170` (definition) | Base-zero specialization checked | `Valid` | A.padded_valid; B.lastForest_valid. The source invariant permits arbitrary trailing holes; it does not include canonicality. |
| `Binom.BinomQueue.empty_priq@182` (source_admission) | Admitted source theorem proved | `empty_valid` | A.build_valid; nat_laws.empty_valid. The actual empty value is valid; no premise or extra axiom. |
| `Binom.BinomQueue.smash_valid@187` (source_admission) | Admitted source theorem proved | `smash_valid` | A.tied_smash_rank; B.rankThree_valid. Equal-rank proper heaps link to rank n+1 under the lawful total-preorder comparator contract. |
| `Binom.BinomQueue.carry_valid@193` (source_admission) | Admitted source theorem proved | `carry_valid` | A.carry_three_places; insert_valid. Preserve arbitrary starting rank n and the source nil-or-rank-n carry premise. |
| `Binom.BinomQueue.insert_priq@200` (source_admission) | Admitted source theorem proved | `insert_valid` | A.build_valid; nat_laws.insert_valid. Insert the rank-zero singleton into a valid base-zero forest. |
| `Binom.BinomQueue.join_valid@207` (source_admission) | Admitted source theorem proved | `join_valid` | A.one_slot_join_valid; deleteMax_some_valid. Both forests and the nil-or-rank-n carry retain the same generalized starting rank n. |
| `Binom.BinomQueue.merge_priq@211` (proved_in_source) | Source proof completed through checked dependencies | `merge_valid` | mergeValid; nat_laws.merge_valid. Reuse the proved join_valid with nil carry; the original source proof no longer depends on an admission. |
| `Binom.BinomQueue.delete_max_Some_priq@217` (source_admission) | Admitted source theorem proved | `deleteMax_some_valid` | B.last_full_contract; B.tagged_deletion_contract; nat_laws.deleteMax_valid. Actual successful deletion of a valid forest returns a valid forest through both correctly based auxiliary outputs and join. |
| `Binom.BinomQueue.tree_elems@228` (definition) | Inductive occurrence relation checked | `TreeElems`, `TreeElems.nil`, `TreeElems.node`, `tree_elems_iff` | A.tied_smash_occurrences; A.tied_smash_permuted_witness. Genuine nil/node constructors include arbitrary permutation witnesses in the original direction; equivalence to Trees.preorder holds on all raw trees. |
| `Binom.BinomQueue.priqueue_elems@247` (definition) | Missing source relation constructed and checked | `QueueElems`, `QueueElems.nil`, `QueueElems.cons`, `queue_elems_iff` | A.source_fold_occurrences; B.repeated_source_contract. The empty placeholder is completed with genuine nil/cons constructors and arbitrary Perm witnesses; all raw forests have witnesses, closure and uniqueness. |
| `Binom.BinomQueue.manual_grade_for_priqueue_elems@251` (grading_metadata) | Administrative disposition; no theorem credit | `QueueElems` | The completed relation and its independent witnesses. The source None-valued grading hook is metadata. No Lean grading stub, axiom or algorithm is added; the mathematical exercise is discharged by QueueElems and its laws. |
| `Binom.BinomQueue.Abs@254` (definition) | Definition checked | `Abs` | nat_laws; B.padded_empty_abs. Abs aliases the completed forest relation; it is not state equality and does not erase duplicates. |
| `Binom.BinomQueue.tree_elems_ext@263` (source_admission) | Admitted source theorem proved | `tree_elems_ext` | A.tied_smash_permuted_witness. Permutation transports an existing witness in the source direction; contents equivalence supplies the proof. |
| `Binom.BinomQueue.tree_perm@269` (source_admission) | Admitted source theorem proved | `tree_perm` | A.tied_smash_occurrences and A.tied_smash_permuted_witness inhabit its premises. Any two witnesses of the same raw tree are permutations. No order or validity assumption is introduced. |
| `Binom.BinomQueue.priqueue_elems_ext@279` (source_admission) | Admitted source theorem proved | `priqueue_elems_ext` | A.source_fold_occurrences. Every permutation of an existing forest witness is a witness; the full source direction is preserved. |
| `Binom.BinomQueue.abs_perm@285` (source_admission) | Admitted source theorem proved | `abs_perm`, `abs_perm_raw` | nat_laws.abs_perm; B.repeated_source_contract. The source validity-guarded wrapper is retained; the stronger raw witness uniqueness is available separately. |
| `Binom.BinomQueue.tree_can_relate@292` (source_admission) | Admitted source theorem proved | `tree_can_relate`, `tree_elems_contents` | A.tied_smash_occurrences. Every raw tree has the explicit preorder witness, without choice. |
| `Binom.BinomQueue.can_relate@296` (source_admission) | Admitted source theorem proved | `can_relate`, `can_relate_raw`, `queue_elems_contents` | nat_laws.can_relate; exactQueue. The source validity premise remains visible; explicit contents witnesses exist even on raw forests. |
| `Binom.BinomQueue.empty_relate@304` (source_admission) | Admitted source theorem proved | `empty_relate` | A.build_relate; nat_laws.empty_relate. The actual empty queue has the literal empty witness, ensuring nonvacuity. |
| `Binom.BinomQueue.smash_elems@313` (source_admission) | Admitted source theorem proved | `smash_elems`, `smash_contents_nodes` | A.tied_smash_occurrences; A.tied_smash_two_maxima. The result witnesses bt ++ bu, keeping every duplicate. The source equal-rank shape hypotheses remain visible. |
| `Binom.BinomQueue.carry_elems@326` (source_admission) | Admitted source theorem proved | `carry_elems`, `carry_contents` | insert_relate; A.build_relate. The source witness order is eq ++ et, with generalized rank and a nil-or-rank-n carry premise. The separate contents theorem needs only proper outer shapes. |
| `Binom.BinomQueue.insert_relate@336` (source_admission) | Admitted source theorem proved | `insert_relate` | A.build_relate; nat_laws.insert_relate. The output witness is k :: al. The left-fold example separately accounts for reversed insertion order up to permutation. |
| `Binom.BinomQueue.join_elems@342` (source_admission) | Admitted source theorem proved | `join_elems`, `join_contents` | A.join_three_occurrences; merge_abs. The source observation is ce ++ pe ++ qe, with all three validity premises retained. |
| `Binom.BinomQueue.merge_relate@356` (source_admission) | Admitted source theorem proved | `merge_abs`, `merge_relate` | mergeValid_entries; B.native_meld_entries; nat_laws.merge_relate. Construct pl ++ ql as a witness, then prove the source permutation claim for every supplied output witness al. |
| `Binom.BinomQueue.delete_max_None_relate@366` (source_admission) | Admitted source theorem proved | `deleteMax_none_relate`, `deleteMax_none_relate_raw` | B.padded_empty_abs; B.padded_empty_delete; nat_laws.deleteMax_none. Preserve Abs p [] iff deleteMax p=none under the source validity premise; allnil padding is included. |
| `Binom.BinomQueue.delete_max_Some_relate@372` (source_admission) | Admitted source theorem proved | `deleteMax_some_relate`, `deleteMax_some_mem`, `findMax_some_bound`, `deleteMax_some_count`, `deleteMax_some_mass` | B.last_full_contract; B.repeated_source_contract; B.tagged_deletion_contract; nat_laws.deleteMax_relate. For all actual witnesses, input permutes to selected::residual and every residual key is <= selected. Membership, original bound, exact count loss and mass loss follow without dropping repeated maxima. |

## All 21 exercise headings

The source spelling of an exercise can differ from its theorem spelling:
`insert_elems` is witnessed by `insert_relate`. `can_relate` includes both the tree lemma and forest theorem.
The `priqueue_elems` exercise includes the administrative grading hook, which
adds no theorem credit. Optional status changes no completion obligation.

| Exercise heading and source span | Stars / optional | Witness and execution boundary |
| --- | --- | --- |
| `empty_priq` at 181–184 | 1 / no | Checked body: `empty_valid`. |
| `smash_valid` at 186–190 | 2 / no | Checked body: `smash_valid`. |
| `carry_valid` at 192–197 | 3 / no | Checked body: `carry_valid`. |
| `insert_valid` at 199–202 | 2 / yes | Checked body: `insert_valid`. |
| `join_valid` at 204–209 | 3 / yes | Checked body: `join_valid`. |
| `delete_max_Some_priq` at 216–220 | 5 / yes | Checked body: `deleteMax_some_valid`. |
| `priqueue_elems` at 236–252 | 3 / no | Checked body: `QueueElems`, `QueueElems.nil`, `QueueElems.cons`, `queue_elems_iff`. Grading metadata is administrative only. |
| `tree_elems_ext` at 259–266 | 2 / no | Checked body: `tree_elems_ext`. |
| `tree_perm` at 268–272 | 2 / no | Checked body: `tree_perm`. |
| `priqueue_elems_ext` at 274–282 | 2 / no | Checked body: `priqueue_elems_ext`. |
| `abs_perm` at 284–289 | 2 / no | Checked body: `abs_perm`, `abs_perm_raw`. |
| `can_relate` at 291–299 | 2 / no | Checked body: `tree_can_relate`, `tree_elems_contents`, `can_relate`, `can_relate_raw`, `queue_elems_contents`. |
| `empty_relate` at 303–307 | 1 / no | Checked body: `empty_relate`. |
| `smash_elems` at 309–318 | 3 / no | Checked body: `smash_elems`, `smash_contents_nodes`. |
| `carry_elems` at 325–333 | 4 / yes | Checked body: `carry_elems`, `carry_contents`. |
| `insert_elems` at 335–339 | 2 / yes | Checked body: `insert_relate`. |
| `join_elems` at 341–353 | 4 / yes | Checked body: `join_elems`, `join_contents`. |
| `merge_relate` at 355–363 | 2 / yes | Checked body: `merge_abs`, `merge_relate`. |
| `delete_max_None_relate` at 365–369 | 5 / yes | Checked body: `deleteMax_none_relate`, `deleteMax_none_relate_raw`. |
| `delete_max_Some_relate` at 371–379 | 5 / yes | Checked body: `deleteMax_some_relate`, `deleteMax_some_mem`, `findMax_some_bound`, `deleteMax_some_count`, `deleteMax_some_mass`. |
| `binom_measurement` at 391–398 | 5 / yes | The complete checked Int64 transport and actual `binom-workload` seam are described below and in `vfa-binom-runtime.md`. Exact final execution, both-mode parity and comparative timings are bound by the checkpoint runtime receipt; the earlier Eval smoke run retains its historical identity. |

## Source module, Eval command and substantive prose

The single `BinomQueue <: PRIQUEUE` module at line 28, ending at 386, is adapted
as Lean namespaces, explicit operation parameters and a concrete law record.
`natOperations` uses source empty/insert/deleteMax/merge, and `nat_laws` supplies
all eleven conditional fields with `Valid` and the completed `Abs`. The explicit
`queue_elems_contents` witness and empty witness rule out a vacuous realization.
The existing valid-state adapter supplies the Unit/OrderDual Nat exact queue;
`mergeValid_entries` supplies native merge's separate occurrence law. No source
admission, module emulator or global queue axiom is assumed.

The checked `nat_laws` field assignment is explicit:

| Accepted source-contract field | Actual provider |
| --- | --- |
| `can_relate` | `can_relate` |
| `abs_perm` | `abs_perm` |
| `empty_valid` | `empty_valid` |
| `empty_relate` | `empty_relate` |
| `insert_valid` | `insert_valid natGreater natGreater_eq` |
| `insert_relate` | `insert_relate natGreater` |
| `deleteMax_none` | `deleteMax_none_relate natGreater` |
| `deleteMax_valid` | `deleteMax_some_valid natGreater_eq` |
| `deleteMax_relate` | `deleteMax_some_relate natGreater_eq` |
| `merge_valid` | `merge_valid natGreater natGreater_eq` |
| `merge_relate` | `merge_relate natGreater` |

The adapter's carrier is `{q : Queue Nat // Valid q}`; its contents are mapped
through the accepted Unit/OrderDual Nat encoding. `exactQueue_remove_some` and
`exactQueue_remove_val` expose the literal source deletion, while
`exactQueue_add_singleton_val` and `exactQueue_add_val` expose source insertion.
Native meld uses `mergeValid`, with its raw value and full occurrence observation
proved separately. The adapter does not silently remove the source validity guard.

The unique line 68 `Eval compute` is the left fold of
`[3,1,4,1,5,9,2,3,5]` from empty. Its independent exact constructor expectation is:

```lean
[ .node 5 .nil .nil,
  .nil,
  .nil,
  .node 9
    (.node 4
      (.node 3 (.node 1 .nil .nil) (.node 1 .nil .nil))
      (.node 3 (.node 2 .nil .nil) (.node 5 .nil .nil)))
    .nil ]
```

`A.source_fold_shape` kernel-checks the whole forest. The distinct
`source_fold_valid`, `source_fold_occurrences`, `source_fold_mass`,
`source_fold_maximum`, `source_fold_rank_three`, `source_rank_three_size` and
`source_rank_three_height` connect it to its four slots, nine occurrences,
maximum 9, rank-three size 8 and height 4. This is the source's left fold, distinct
from the accepted ExactQueue adapter's right-fold batch insertion.

A **separate historical executable evaluation** was recorded; the filenames
below are external historical identifiers, not present repository dependencies:
`evidence/checkpoint045/runtime-source-fold-green-command.json` records
`BinomialRuntime.test_source_fold`, exit 0, 0.159273s, completed
2026-11-17 01:25:28.663263 UTC. Its nested retained driver invocation is
`R/source-fold-green/test_source_fold-001.json`: `extract-searchtree binom-examples`,
exit 0 in 0.031321s. The full output has schema 3/kind `binomial-examples`, the exact
four-slot preorder/null forest, original ordered input and maximum 9. The independent
`expected_binomial_examples()` fixture is maintained in
[`scripts/test-extract-searchtree.py`](../../scripts/test-extract-searchtree.py);
it constructs the expected literal tree and serializes it without reimplementing
insertion/linking. Its old retained input copy was
`R/source-fold-green/input-0.txt`. The historical output was
`R/source-fold-green/test_source_fold-001.stdout`, SHA256
`2a235ddda2ee4188eabd4ccc1078ab8973106a874e400900d30311f16d8f6003`.
These are test/command elapsed times, not an operation-only comparative benchmark.
This observation retains its actual historical executable/source boundary.
Old raw-output availability is not inferred from the filename/hash.
[CTB-97](../textbooks/CTB.json) owns its qualification, and CTB-78 must bind any
receiving rebuilt executable and workload checks separately.

| Primary prose/command scope | Disposition |
| --- | --- |
| Lines 3–8, performance and Nat comparison caveat | Preserve as a complexity obligation under the explicit modeled tariffs and padding/capacity conditions below; no unconditional current-mass bound or native comparison-cost theorem is inferred. |
| Lines 11–19, both required readings | Authenticated identities and exact read/visual attribution above; preserve the child/sibling distinction and Sedgewick comparison-count claim. |
| Lines 24–26, imports | Reuse accepted Lean dependencies. Strings.String is for grading metadata; no missing mathematical grading framework remains. |
| Lines 28 and 381–386, source module/final claim | All eleven conditional Nat laws and explicit valid-subtype ExactQueue realization have concrete checked proofs. Full source qualification awaits the later chapter gates. |
| Lines 36–42, rank slots | `validFrom_getElem`, `getElem_numNodes` and `mass_eq_value` preserve rank offsets and holes. Occupied position is not a compact tree index. |
| Lines 68–78, Eval and output | Exact kernel forest plus separately retained actual driver execution, as above. |
| Lines 141–170, invariant explanation | Preserve perfect inner shape and its two bounds; outer rank n has height n+1; trailing holes are permitted. |
| Lines 178–220, validity exercise guidance | Every admission, including five-star optional deletion validity, has a matching checked proof. Induction implementation may differ without changing hypotheses. |
| Lines 225–254, relation and grading | Construct both inductives and their all-raw contents equivalences; preserve every permutation and occurrence. Grade stub is administrative. |
| Lines 257–299, sanity checks | Totality, permutation closure and uniqueness have explicit nonvacuous witnesses. |
| Lines 302–379, operation and optional proofs | Complete all source directions and guards, including full successful/empty deletion. |
| Lines 389–398, measurement | Complete public replay/drain/mixed/native-merge/padding protocol and independently checked observations; final comparative executions are bound by the candidate-specific runtime evidence. |
| Line 400, footer | Chapter 09:43 footer is distinct from release 10:11 cover time; preserve primary identity. |

## Exact semantic boundaries

The raw representation is dense `List (BinaryTree K)` with actual nil slots;
there is no sparse heap, sorted-list substitution, rank cache or normalization
pass. A `Node`'s left child describes smaller-rank children, while the right
pointer is a sibling chain. In `Pow2HeapAux (n+1) m (node k l r)`, the left
recursive bound is k and the right recursive bound stays m. The checked example
`node 10 (node 3 (node 1 nil nil) (node 8 nil nil)) nil` is valid at rank 2 even
though 8 exceeds 3. Treating this as an ordinary binary max heap would reject the
source representation.

Smash ties choose the second root; maximum scanning ties retain the first literal
root. Ordered proofs assume only `Preorder K`, `Std.Total (· ≤ ·)` and
`greater x y=true ↔ ¬x≤y`. The explicit tagged Nat×Bool preorder compares only
Nat priority. Its distinct equal-priority keys witness that first-maximum
provenance and exact deletion do not rely on antisymmetry. The false theorem that
preorder-equivalent keys are equal is never used.

CPS unzip physically follows descending-rank right siblings and returns their
proper outer trees in ascending-rank order. Its arbitrary continuation is invoked
at `[]`; the exact law is `unzip t cont = unzip t id ++ cont[]`. For a rank-r outer
heap, children have r occupied slots starting at zero, mass `2^r-1`, and all keys
are bounded by the old root. The selected deletion split exposes the literal
root occurrence. Every occupied prefix root is strictly smaller; the untouched
suffix roots are weakly smaller. This prevents deletion from discarding an
unrelated equivalent key or reaching a malformed fallback on valid input.

For generalized base i and selected prefix length j, the chosen heap's absolute
rank is i+j. Auxiliary deletion returns the original prefix, a hole and the
original suffix, still at base i; its child forest starts at zero. The source
base-zero final join combines the actual two residuals. All abstraction witnesses
obey input~selected::residual, with a non-strict maximum bound so repeated maxima
can remain. The original selected key belongs to the input, query counts lose
exactly one at that literal key, and residual mass+1 equals original mass.

Allnil padding has empty abstraction and yields None without being the raw empty
list. Key 0 yields `some 0`. Successful singleton deletion returns `[nil]`. Raw malformed
outer right subtrees deliberately trigger source fallbacks and can lose additional
occurrences; `B.malformed_occurrence_loss` exhibits this. The proper/rank premises
on preservation theorems are material and cannot be erased.

## Rank accounting, stored capacity and the performance claim

The existing `Resources.BinaryCounter` observation is reused on the actual
occupancy list. Checked rank facts give, under `ValidFrom i q`,
`mass q = 2^i * BinaryCounter.value (occupancy q)`, with each occupied slot j
contributing exactly `2^(i+j)`. Base-zero validity gives
`mass q < 2^q.length`, hence `Nat.size (mass q) ≤ q.length`.

Canonicality is a separate observation: the forest is empty or its final slot
is occupied. Only with valid canonical input is stored length exactly
`Nat.size (mass q)`; nonempty canonical input also has
`q.length = Nat.log 2 (mass q)+1`. Arbitrary valid allnil forests have mass 0
and arbitrarily large stored length. The source deletion operation does not
preserve canonicality, even for a singleton.

These exact source endpoint laws are already checked:

- `insert_length`: new stored length is `max oldLength (Nat.size (oldMass+1))`.
- `merge_length`: new length is `max (max leftLength rightLength) (Nat.size (leftMass+rightMass))`.
- `deleteMax_length`: every successful deletion preserves stored length exactly.

Raw carry never shortens and grows by at most one; raw join stays between the
maximum input length and that maximum plus one. Strict growth implies a final
occupied slot. The successful-deletion length proof combines these raw facts with
validity and one-occurrence mass loss; it does not insert a trim operation.

`Capacity B H q` means `q.length ≤ max B H.size`. The actual
`commandRun` dispatches insertion, native merge and deletion; `runCommands`
reuses the existing `Resources.run` executor. `AdmissibleHistory` constrains each
instruction at its actual prefix state. Insertion's new mass must fit H, while
each stored merge operand must independently be valid, fit the same capacity,
and keep the combined mass within H. `runCommands_invariant` and
`runCommands_prefix_invariant` preserve validity, mass and capacity at every
actual prefix. There is no free assumption about a separately retained operand.

`build_drain_padding` proves that building N inputs from empty and deleting N
times produces exactly `List.replicate N.size nil`. For N=2^r,
`build_drain_power_padding` gives r+1 retained holes, and
`delete_after_power_drain` bills one full deletion entry and r+2 scan entries for
the next failed deletion. This is a reachable counterexample to an unrestricted
logarithmic bound in current live mass.

The explicit fixed-tariff capacity inequalities imply
`insertRun_isBigO_log`, `mergeRun_isBigO_log` and `deleteMaxRun_isBigO_log` for
families with the stated capacity bound and fixed initial padding B. Deletion
also requires valid ordered queues and the lawful comparator. The historical
family theorem `runCommands_isBigO_n_log` requires length n, initial mass ≤n,
initial capacity and admissibility of all actual prefixes and stored operands.
Its comparator-work ceiling, tariffs and B are fixed across the family.
These are real `Asymptotics.IsBigO` results, reached through explicit bounds,
`Nat.size`, `Nat.clog` and `Real.logb`; they assert no native timing property.

## Measured source work, explicit bounds and amortization

[`Applications/Resources/BinomialQueue/Measured.lean`](../../Applications/Resources/BinomialQueue/Measured.lean)
is the maintained measured provider. Its historical export pass belongs to
CTB-97 and is not current receiving verification. Its18 `Metric` coordinates
distinguish the12 source function
entries, comparison calls, actual comparator work, cons expressions, node
expressions, closure creation and continuation application. `Cost` is the
ordinary pointwise Nat cost, and `weighted` uses explicit nonnegative tariffs.
Pairs, Options, nil trees and nil lists are explicitly uncharged; every named
source wrapper contributes one entry. These are syntactic event prices, not
native allocation, memory, stack, CPU or elapsed-time statements.

The executable `emptyRun`, `smashRun`, `carryRun`, `insertRun`, `joinRun`,
`unzipRun`, `heapDeleteMaxRun`, `findMaxAuxRun`, `findMaxRun`,
`deleteMaxAuxRun`, `deleteMaxRun` and `mergeRun` use actual recursive returned
values and the actual Boolean returned by the measured comparator. Their checked
`*_value` results erase to the literal raw program even for malformed inputs and
unlawful comparators. `unzipRun_value` retains the arbitrary continuation's
actual returned value; its cost is not silently constant. `unitComparator`
charges one unit of work per comparison. A nonunit comparison bound must constrain
the actual encountered comparisons, not follow solely from Boolean reflection.

`Bounds.lean` proves the following counts and inequalities on the actual
measured executions. `Amortized.lean` supplies the actual multi-step histories.
`Examples/BinomialQueueWork.lean` connects the general results to independent
constructor expectations and exact numerical bills. Root read all four complete
source bodies and exported their final checked providers.

| Actual operation | Proved exact/bounded count and scope |
| --- | --- |
| Empty | Fixed entry; no scan or comparison. |
| Proper smash | One comparison, two node expressions, no descendant traversal. Malformed fallback compares nothing. |
| Nonnil rank-matched carry | For r initial occupied slots, r links/comparisons, r+1 carry entries and cons expressions, 2r node expressions. General carry includes nil and terminal cases. |
| Insert | Carry counts plus one singleton node: r comparisons, r+1 cons, 2r+1 nodes; r≤stored length. |
| Join/native merge | Paired steps≤min lengths; join+carry entries≤max lengths+2; links/comparisons≤max lengths; cons≤max lengths+1; two nodes per link. Keep all occupancy branches and bases. |
| Root scans | Combined find/findAux entries exactly L+1. Find uses max(O-1,0) comparisons, an accumulator scan O comparisons. Descendants are not traversed. |
| CPS unzip | For r sibling nodes: r+1 unzip entries, r closures, r detached nodes, r cons. Identity continuation applications total r+1; arbitrary continuation cost stays explicit at its actual argument `[]`. |
| Heap deletion | Rank r produces r slots with no key comparisons; malformed/nil fallback performs no child traversal. |
| Auxiliary deletion | At selected base-zero slot j: exactly j+1 auxiliary entries and reconstructed first-output cons, at most j+1 comparisons/restored node expressions, plus rank-j child unzip. For base i, child rank is i+j. |
| Full deletion | None pays the full scan. Some charges scan, auxiliary, unzip and join; comparisons≤3L and an explicit constant times L+1 structural bound under the stated prices. |
| Weighted/family transport | Preserve comparison count versus comparator work, actual input-sensitive/uniform cost premises, zero and nonzero tariff cases, empty endpoints and the declared growing family. |

The principal count providers are `smashRun_counts`, `carryRun_leading_counts`,
`insertRun_leading_counts`, `joinRun_bounds`, `findMaxAuxRun_counts`,
`findMaxRun_counts`, `unzipRun_cost`, `unzipRun_identity_cost`,
`heapDeleteMaxRun_rank_cost`, `deleteMaxAuxRun_selected_counts` and
`deleteMaxRun_comparisons_le`. The nodes-per-link equalities are separate
`carryRun_nodes`, `insertRun_nodes`, `joinRun_nodes` and `mergeRun_nodes`.
`deleteMaxRun_none_bill`, `deleteMaxRun_padding` and `deleteMaxRun_empty`
retain the full failed scan. The `*_comparisonWork_le` and `*_weighted_le`
families keep the actual comparator work and all prices explicit.

`insertRun_occupancy` is exactly `BinaryCounter.inc`. The comparison count is
`leadingOnes`, one less than the terminal-write-inclusive `flipCost`.
`insertRun_potential` proves comparisons+Φ(after)=Φ(before)+1; the finite
`insertionsRun_potential` uses the accepted
`Resources.run_potential_map_exact_of_invariant` on actual measured states.
From empty, zero insertions cost zero comparisons and
`insertionsRun_empty_comparisons_lt` gives strictly fewer than N comparisons
when N>0. The initial potential remains explicit for a nonempty or padded start.
`insertionsRun_weighted_potential` also retains both weighted boundary credits;
`insertionsRun_isBigO` proves linear total fixed-tariff work from empty.

Separate persistent branches each need their own initial credit.
`persistent_branch_credit` exhibits two insertions from the same saved forest
whose combined comparisons exceed a once-counted initial credit plus two.
`source_build_bill` gives seven comparisons and final potential two for the
source's nine insertions, with unit-price bill 85. `mixed_history_value_and_bill`
computes the actual insert/insert/native-merge/delete state and bill 55;
its admissibility, capacity and general work-bound examples consume the proved
history theorems. Nonunit comparison, arbitrary-continuation, rank-offset,
malformed-fallback, zero and reachable-padding cases have separate witnesses.
The Sedgewick insertion comparison claim is thereby connected to the actual
source trajectory, separately from worst-case bounds and finite timings.

## Machine-key adaptation and mandatory executed measurement

`Applications/Representations/DecodedBinomialQueue.lean` proves transport of
each complete raw result through label mapping, including smash, carry, insert,
join, arbitrary-continuation unzip, heap deletion, both scans, auxiliary/full
deletion and native merge. Pointwise Boolean comparison agreement is explicit;
the raw laws require neither order nor injectivity nor validity and allow
independent label universes. The runtime's `int64Greater` reverses the accepted
`SignedComparison.int64Ltb`; the `decode_*` laws preserve entire Options, pairs,
forests and CPS results, not only comparison truth values.

`checkedInt64` and `checkedNat64` prove exact decoded round trips and rejection
guards. `NatBounded`, `decode_encode_tree`, `decode_encode_queue` and the `nat_*` results connect the bounded
textbook domain to the native signed implementation. `map_select`,
`decode_listDeleteMax` and `nat_listDeleteMax` separately connect the source list
baseline to the accepted comparison-first selector. There is no new list-queue
algorithm hidden in the benchmark.

`Examples/BinomialQueueClients.lean` applies the same accepted generic
build/native-merge/two-removal client to the source list and binomial adapters.
Three copies of 7 yield two successful removals and one remaining 7; input
versions remain available. The examples also cover bounded Nat whole-result
transport, exact duplicate remainders, negative/zero/positive keys, both signed
endpoints and adjacent range rejection. All 77 root-owned introductions
(65 theorems and 12 definitions/abbreviations) had their imported actual types
and complete bodies read, with the retained development attempts.

The required execution uses signed Lean Int64, with decoded range
`-2^63 ≤ x < 2^63`; it is not a 63-bit BitVec backend. The Nat comparison workload
uses checked `0≤k<2^63` inputs and rejects larger keys. Signed examples also cover
negative/zero/positive values and both endpoints. Queue keys are compared only;
generation, conversions and counters still require explicit honest bounds.
Proof-only label maps/contents must not become execution-time preprocessing.

The final runtime evidence must bind actual checked executions and raw evidence
for every condition below; passing mathematical proofs alone does not discharge
the measurement exercise:

1. Binom and accepted source ListMaximumQueue receive identical retained keys and schedules, with actual native meld.
2. Explicit seeds, generator/range conventions and workload digests support exact replay. Inclusive random endpoints are handled correctly; no distribution theorem is asserted.
3. Deterministic empty/singleton/equal/ascending/descending/duplicate/padded growth-drain cases and randomized insert-drain/mixed/merge cases exercise complete observations.
4. An independent finite occurrence/maximum oracle checks every Some/None, complete deletion sequence, residual multiplicity and merged multiplicity. A checksum alone is insufficient. Saved old queue versions remain observationally unchanged.
5. Generation, checked conversion, independent validation, printing and optional instrumentation are outside the operation-only `IO.monoNanosNow` interval. Any separately reported end-to-end time is labelled with its actual scope.
6. Full commands, exits, inputs, seeds/digests, repetitions, warmup/order policy, host/target/compiler/pin identities, compile timing boundaries and raw observations/timings are retained. The user-authorized exact native profile and no-artificial-resource-cap exception remain in force; finite logical workloads are explicit.
7. Monotonic elapsed nanoseconds are not labelled process CPU time. Successful Lean runtime execution is not a compiler-correctness theorem; Int64 native comparison overrides remain the ordinary execution boundary.
8. Final replay/observer rejection cases and legacy driver regressions pass against the exact final executable. The earlier source-fold smoke receipt is retained with its own historical input identity, not reused as a final new-binary measurement result.

The accepted `scripts/ExtractSearchTree.lean` /
`scripts/test-extract-searchtree.py` seam now supplies `binom-examples` and
`binom-workload`. Both source implementations execute random, replay, ascending,
descending and equal inputs with drain, key-dependent mixed, native-merge and
padding schedules. The executable itself checks complete results after timing;
the Python observer additionally checks raw tree structure, child/sibling ranks,
heap bounds, exact capacity, occurrence bags and every saved version.
The final comparative test fixes sizes 32/128/512, universe 17 and seed 1729,
one warmup and three measured repetitions, alternating implementation order.
The runtime note defines the exact commands, boundaries and evidence routing.
Numerical observations and final test counts come only from actual retained
candidate receipts; no native speedup or compiler-correctness theorem is asserted.

## Validation and qualification boundary

The complete source/exercise maps and meaningful A/B/C/R case connections are
in this note and the ordinary source/Examples owners named above. Their former
external chapter-ledger, handoff, imported-type and review files remain historical
records; they are not needed as a second copy of these maps, and no claim is made
that the raw files were moved into this repository. Any unresolved evidential
availability belongs to [CTB-97](../textbooks/CTB.json), not a fabricated source link.

One useful audit distinction remains: the Prop-valued `taggedTotal` declaration
is actual theorem information despite being lexically an instance. Generated
support and authored statements must be accounted for by actual declaration
kind rather than by source spelling alone. Author probes and type exports do not
replace whole-scope candidate validation or independent review.

CTB-97 retains its historical donor qualification. CTB-78 requires current
receiving validation, affected runtime checks and both independent review axes
on the actual integrated tree. Source qualification, executable observations,
archive reconstruction and durable publication remain separate properties.
No whole-library receipt or receiving pass is manufactured by this note, and
historical instructions to start Decide after checkpoint045 do not govern the
current continuation. Processed type dumps, old reviews and recursive execution
envelopes need not be copied into future checkpoints.
