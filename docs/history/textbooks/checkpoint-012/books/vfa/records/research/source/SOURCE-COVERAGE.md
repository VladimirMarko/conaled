# Verified Functional Algorithms: pinned source and coverage obligations

Source reconnaissance on 2026-11-02. This record is an inventory and implementation
guide, not a claim that any chapter has been formalized or accepted in Lean.

## Pinned reference

The primary source is Andrew W. Appel, *Verified Functional Algorithms*, Software
Foundations volume 3, version **2.1 (2026-08-24 10:11, Coq 9.0.0 or later)**.

- Cover: <https://softwarefoundations.cis.upenn.edu/vfa-current/index.html>
- Contents: <https://softwarefoundations.cis.upenn.edu/vfa-current/toc.html>
- Official release: <https://softwarefoundations.cis.upenn.edu/vfa-current/vfa.tgz>
- Release SHA-256: `f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8`.
- License: MIT; archive notice is `Copyright (c) 2026`.
- License SHA-256: `6fcd23f1728be522ac23586b7e8b066d272fa60d45aac298142afeaefddae4ec`.

`VFA-LICENSE.txt` preserves the license notice. The chapter JSON files record
each source file's exact hash, URL, source lines, explicit declarations,
exercise tags, module context, and proof terminators. The release's top-level
README contains an obsolete VFA.v navigation hint; the current TOC and actual
chapter files determine order. The Preface footer time differs from the cover;
the cover version and release bytes are the reference identity.

The Preface requests that exercise solutions not be made publicly searchable.
Local development and private recovery checkpoints follow the user's requested
workflow. No public publication is part of this task.

## Scope and inventory counts

The ordered scope is the Preface plus all sixteen substantive chapters below.
Optional and advanced exercises remain included. Counts are lexical source
records, not numbers of independent mathematical obligations or accepted Lean
theorems. A record can be a definition, interface parameter, axiom in a Coq
module signature, anonymous goal, grading stub, tactic, failed command, or
abandoned proof. Repeated pedagogical attempts retain separate source-line IDs.

| Order | Chapter | Explicit records | Exercises | Source admissions | Aborted attempts |
|---|---|---:|---:|---:|---:|
| 0 | Preface | 0 | 0 | 0 | 0 |
| 1 | Perm | 30 | 4 | 3 | 2 |
| 2 | Sort | 17 | 8 | 9 | 0 |
| 3 | Multiset | 22 | 14 | 13 | 0 |
| 4 | BagPerm | 19 | 9 | 11 | 0 |
| 5 | Selection | 33 | 20 | 20 | 0 |
| 6 | Merge | 17 | 6 | 6 | 1 |
| 7 | Maps | 23 | 6 | 6 | 0 |
| 8 | SearchTree | 90 | 35 | 41 | 1 |
| 9 | ADT | 254 | 12 | 43 | 0 |
| 10 | Extract | 34 | 4 | 3 | 0 |
| 11 | Redblack | 45 | 13 | 16 | 4 |
| 12 | Trie | 55 | 12 | 15 | 0 |
| 13 | Priqueue | 43 | 2 | 6 | 0 |
| 14 | Binom | 44 | 21 | 20 | 0 |
| 15 | Decide | 32 | 2 | 3 | 1 |
| 16 | Color | 53 | 14 | 16 | 1 |

Total: **811 explicit records, 182 exercise markers, 231 source admissions**.
Of the exercises, 44 have an optional tag and 28 have an advanced tag; these
sets overlap. Names inside explanatory comments are not live Coq declarations.
Consequently a raw regular-expression count over the book text overcounts some
declarations and admissions, while a column-zero-only count misses much of ADT.

The generator masks nested comments, respects strings, tracks module contexts,
and correlates every active Qed, Defined, Admitted, and Abort terminator. An
independent line-oriented scan matched all captured named declaration starts;
all proof terminators were accounted for. This is not a Rocq AST parser and
does not certify the upstream proofs. Constructor names and automatically
generated induction principles are represented by their owning inductive
declaration rather than counted again. Imports and module includes must be
examined when resolving a chapter's exact dependency closure.

## Completion criteria

For each mathematical source obligation, the implementation ledger should name
a Lean declaration, a precise specialization of existing code, or a proved
bridge to an existing declaration. Merely importing a related library does not
establish source coverage. Preserve the source algorithm's behavior and the
strength and assumptions of its specification. Optional proof exercises,
negative examples, and representation-invariant side conditions must be
accounted for before closing a chapter.

For Coq-specific mechanics, record the corresponding Lean proof or executable
technique and its boundary. Grading markers and browsing commands are not
mathematical claims. Open-ended exercises need concrete written treatment or
new checked examples; an empty grading stub is not completion. Keep the source
inventory immutable and track accepted Lean coverage separately so regenerating
the inventory cannot erase accepted progress.

Conaled completion additionally requires checked specializations and
applications, statement review of new claims, public import/build/audit
coverage, the applicable repository acceptance command, and independent
Standards and Spec review. The source admission counts above provide no
permission to introduce Lean admissions or application axioms.

## Chapter-specific obligations and integration boundaries

### Perm

Cover arithmetic examples (including truncated subtraction), Boolean/proposition
comparison reflection, maybe_swap, its idempotence, permutation and first-two
ordering contract, the butterfly rearrangement, both concrete permutation
exercises, and Forall transport. The open-ended Permutation_properties exercise
requests three additional desirable properties beyond the four supplied
examples; useful checked choices are reflexivity, transitivity, and preservation
of occurrence counts or membership. Map bdestruct/inv to existing Lean tactics
and explicit reflection laws. Two aborted attempts are later proved in the
source and need only one accepted mathematical result plus the pedagogical map.

### Sort, Multiset, BagPerm

Retain the actual recursive insertion algorithm and prove sortedness and
permutation correctness. Sort also asks for the equivalence of adjacent and
index-based sortedness specifications and the alternative proof route. Multiset
uses natural-valued multiplicity functions, including values of infinite
support as specifications; do not silently replace that whole function space
with finite Mathlib Multiset values. Relate finite list contents precisely.
BagPerm separately represents bags as lists modulo count equality. Both chapters
require the converse from equal multiplicities to permutation, not only the
forward implication. Their proof-preference questions receive a documented
comparison, not invented mathematical theorems.

Conaled already has generic stable insertion and merge sorting in
Applications/Sorting/Sort.lean and checked payload examples in
Examples/StableSorting.lean. Reuse those contracts where applicable and prove
source-equation bridges; do not create a competing natural-number-only sorting
interface when the generic one fits.

### Selection and Merge

Selection includes both fuel-indexed and well-founded selection-sort
definitions, select's minimum/permutation/length properties, and optional
multiset and alternative sortedness specifications. Preserve their relationship
and do not replace selection sort with insertion sort just because outputs agree.

Merge uses an **alternating-element split**, two-step list induction, a nested
merge, and well-founded recursion on length. Current conaled mergeSort uses
contiguous halves and supplies stability. Alternating splitting can reorder
equal-key payloads, so a stable-sorting bridge is generally false. Natural-number
output equality can follow from sortedness and permutation; generic payload
semantics need the weaker source contract or an explicitly changed algorithm.
The abandoned split_len_first_try statement is true but needs a stronger
induction principle, demonstrated by the later successful proof.

### Maps, SearchTree, ADT

Maps requires total and optional maps and update algebra. SearchTree includes
bound and lookup, BST preservation, enumeration's completeness/correctness,
sortedness and duplicate-free keys, efficient accumulator enumeration, algebraic
enumeration laws, and both model-based abstraction relations. Preserve default
values, absence and explicit binding as distinct observations. The source's
elements_complete_broken specification is false: default lookup on an empty
tree does not imply a stored binding. Its Lean treatment should refute the
broken specification and provide the corrected contract.

ADT includes function, list and tree realizations of tables; corrected
enumeration interfaces; encapsulation; model-based contracts; both list and
two-list queues; even-number subsets, vectors and subset-packaged BSTs.
Coq Module Type axioms become explicit law fields or parameters; actual
implementations discharge them. The intentionally unsuccessful
TreeETable_first_attempt.elements_correct is admitted in the source but false
without a BST invariant. Use a malformed-tree counterexample and the repaired
interface, rather than inheriting this admission. The table ADT observes a
default-valued total map, unlike an optional finite-map interface.

Open-ended ADT exercises NatFunTableExamples, elements_spec and TreeTableModel'
have no active named declarations in the starter file. They still require
checked examples or a concrete interface/proof completion. Two-list FIFO queues
must not be conflated with the existing priority queues.

### Extract and Redblack

Extract combines executable adaptation, correctness for sorting/tree lookup,
and finite-integer representation boundaries. Its global int/Abs/comparison
parameters and axioms must become explicit interfaces with proved realizations.
No compiler or runtime correctness follows merely from a Lean value theorem.
Preserve the source's warning about overflow; do not transport unbounded integer
addition equations to fixed-width words. The optional int_elements exercise is
open-ended and must still receive an implementation and proof.

Redblack uses the actual Okasaki-style balance/ins/blacken implementation,
ordered-tree and red-black invariants, lookup correctness, and the advanced
height-versus-minimum-depth bound. Existing generic TreeMap theorems alone do
not show that this source algorithm is covered. Its four aborted attempts are
replaced by later declarations; preserve the final theorem plus the explanation
of case-analysis automation. Report cost and extracted-code measurements
separately from semantic and height proofs.

### Trie, Priqueue, Binom

Trie includes positive binary numbers, successor/addition/comparison proofs,
the nat/positive bijection, trie lookup/insert laws and a Table realization.
The open-ended constant-time successor discussion needs a precise model;
Lean's native Nat representation does not automatically inherit the source's
unary-versus-binary cost statements.

Priqueue supplies a maximum-priority-queue abstraction and list realization.
Retain exact occurrence multiplicities and delete-max contracts. Current
conaled Search.LeftistQueue and PrioritySearchQueue are useful reusable
consumers/realizations but have different algorithms and, for the keyed queue,
deduplication semantics. A minimum-priority convention needs explicit order
duality when serving the VFA maximum interface.

Binom requires the concrete binary-carry binomial forest, pow2heap and forest
invariants, abstraction totality and permutation compatibility, and all
smash/carry/join/insert/merge/delete-max proofs. The optional five-star deletion
proofs remain in scope. The binom_measurement exercise asks for randomized
executable comparisons; its Lean adaptation should preserve a reproducible
input workload and separate observations from formal complexity claims.

### Decide and Color

Decide contrasts Boolean reflection, proof-carrying decisions and logical
excluded middle, including executable insertion and membership. Its two global
decision axioms illustrate noncomputation and must be represented by explicit
parameters or proved Lean decisions. Do not reproduce the axioms as new trusted
facts. The aborted opaque-decision example needs both a mathematical result and
an accurate Lean explanation of proof erasure/reduction boundaries.

Color requires finite map/set observations and cardinality laws, termination of
node selection, the actual Kempe-Chaitin partial coloring algorithm and its
palette/adjacency correctness under no-self-loop and undirected hypotheses.
It does not promise all nodes will be colored or minimize spilling. Its opening
informal inference from NP-completeness to absence of polynomial-time algorithms
is not an unconditional theorem to port; no P != NP assumption should be hidden.
The initial Sremove_elements Abort is replaced by the later exercise proof.
Preserve the concrete graph test as a checked execution/example.

## Recovery and provenance use

Download the official archive and verify its SHA-256 before regenerating this
inventory. Run `inventory_vfa.py SOURCE_DIRECTORY OUTPUT_DIRECTORY --archive
ARCHIVE_PATH`. It writes only inventory JSON, not project code. Preserve these
files and the local ticket/coverage/review state together in checkpoints. The
full downloaded textbook is a research reference, excluded from deliverables
under conaled ADR 0001; its URL, hashes and license suffice for reconstruction.
