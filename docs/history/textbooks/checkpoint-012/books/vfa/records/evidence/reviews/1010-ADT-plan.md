# Independent bounded review — #1010 ADT plan

**Outcome: clear for planning; no actionable findings.**
This is a source/reuse-plan review, not either ordinary chapter implementation
review axis and not chapter acceptance. No proposed adapter, source algorithm,
counterexample, or cost theorem is compiler-certified by this review.

## Exact reviewed inputs

- Plan: `../specs/1010-ADT.md`, SHA-256
  `f53d2e54b8d587e27e486f5a08fb1746cc8e2ee16810d0c28c9e44c8e3bfa3e8`,
  66,173 bytes, 765 lines. The author announced it frozen before this assessment.
  Its identity was checked before and after the source assessment.
- Full VFA 2.1 `ADT.v`: SHA-256
  `87d7ca279b38d22f31ff56bf9f2b11103b382c325969a269bc542de27e4a8fe2`,
  45,447 bytes, 1,492 lines. I read the entire chapter independently, including
  all prose, interfaces, proof attempts, commands and exercises.
- Inventory: `../source/ADT.inventory.json`, SHA-256
  `9b051b24d6eb89247480b06c932fafd4511cae179cced0614565a6839e04201a`.
- Accepted baseline for ADT is still unavailable: implementation must await
  #1009 SearchTree acceptance. The inspected project was clean at
  `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`; this review changes no source.
- The preceding SearchTree plan is
  `7bd10a9e771d38364bc806d28b38e6cca8f042a7701e3b852fe331d4cd0819e3`.
  Its mathematical source contracts were independently read for that planning
  assignment and rechecked at the ADT consumption boundaries here.

The review followed the user requirements and repository architecture/domain
guidance, GLOSSARY, ADRs 0001/0010 and build/audit boundaries. It is the bounded
planning review requested by root, within the existing whole-book workflow.

## Coverage verification

The plan's record table contains all **254 inventory IDs exactly once, in
inventory order**, with no extra IDs. Every one of the **12 exercise names and
source ranges** is present. The stated exercise classification is correct:
four optional, three advanced, two both. All **11 pedagogical command records**
and all **39 module/module-type records** have an accounted-for treatment.

This mechanical comparison is supplemented by the complete chapter read; it
does not treat the lexical inventory as a complete source parser. In particular:

- The multiline sharing-constrained implementation at line 675 is correctly
  identified as an actual module implementation despite the inventory's alias
  classification and resulting short `ADT.*` IDs for its ten declarations.
- `NatFunTableExamples`, `elements_spec`, `TreeTableModel'` and the two
  substantive grading-stub exercises are not lost because their declaration
  maps are empty or contain only metadata.
- The five failed declaration records and the separate in-proof
  `Fail reflexivity` command are all distinguished and adapted.
- The failed raw-tree `elements_correct` attempt is not scheduled as an
  unconditional theorem to prove. The plan retains its valid completeness
  direction, explains the missing BST premise and requires a counterexample.

## Consequential statement and architecture checks

### Table and enumeration contracts

The three source Table equations remain unconditional on raw states. The plan
uses the shared table law seam with `Valid := True` for that scope and keeps
ETable's representation validity separate. ETable's three bound laws also stay
unconditional; its two displayed membership laws retain their validity premise.
The stronger raw inverse-correctness result available from SearchTree is
preserved when the optional `elements_spec` interface is strengthened.

All ETableAbs orientations match the source, including update on the left and
the concrete decoder after set on the right. Presence is preserved through
`Option`, `isSome`, and explicit-default lookup. The legitimate raw-list model
with `Valid := True`, prepend set and identity elements is correctly described
as the weaker map-observation contract. It does not imply raw-list membership
soundness, unique keys or sortedness. The final ListsETable exercise instead
requires unique keys in its carrier, exact elements projection, invariant-
preserving replacement and every ETableSubset law.

Both optional tree-model implementations remain explicit. The plan consumes
the accepted enumeration decoder and the distinct structural decoder with
their BST hypotheses and records overlap-cancelling union. It does not erase
their difference on malformed trees or mistake a proof-bearing subtype for
an unconditional theorem about its raw carrier.

The proposed reuse fits the repository: operations and laws remain separate;
no new generic ADT hierarchy replaces existing table observations, square
composition or FIFO clients. Mathematical laws can retain independent
universes while concrete square packages meet the current same-universe
restriction. Payload ordering/equality and global default instances are not
introduced without need.

### Queue contracts and cost boundary

The six Queue algebraic equations are preserved literally, including the
changed default in `peek_nonempty`, actual state equality in dequeue laws,
and the original q in the empty branch. The ListQueue implementation uses the
corresponding list operations. The pair queue retains every source branch and
the four QueueAbs laws for all raw pairs, without an invented invariant.

QueueAbs's missing `is_empty` law is visible. Correct emptiness for the actual
pair realization is a separate additional theorem, and an arbitrary-empty-test
variant is a proposed checked boundary case. Reuse of the existing Option-head
FIFO interface requires an actual optional-head adapter; a generic
default-valued observation does not silently manufacture it.

The recorded concrete pair-state counterexample follows by hand from the
displayed source recurrence: with q=([],[1]), dequeue after enqueueing 2 gives
([2],[]), while enqueueing 2 after dequeue gives ([],[2]). Both decode to [2].
The plan accurately labels this a pending checked case, and does not assign
the pair implementation the stronger raw-state Queue contract.

Resource prose is scoped to explicit instrumented operations with erasure.
The repeated-peek obstruction retains unchanged state, reachable long back
lists, full reversal work, and cancellation of state-only potential. The
positive enqueue/dequeue result is conditional on a separately justified
linear reverse model and a linear state history. It is not attributed to the
quadratic structural-reverse instrument or to arbitrary persistent reuse.
Initial/final potential, bounded local work, and the distinction between a
traversal lower bound and total runtime remain visible. Linear list enqueue
and unique-key update require their own actual recurrences and worst cases.

### Encapsulation, subtypes and vectors

The fully hidden, exposed-payload-only and exposed-payload/default cases are
kept distinct. Generic clients reason through laws without fabricating a
Lean reproduction of Rocq's module sealing, coercion or expected-error rules.
Module sharing is correctly about type/value agreement, not heap sharing.

The computational witness package reuses Subtype and its value/property
projections; propositional Exists remains a different elimination boundary.
Classical noncomputable selection is not substituted for an executable witness
constructor. The source vector stores a list and length together; the plan
retains that exact subtype or requires a projection-preserving equivalence to
`Σ n, List.Vector V n`. It correctly distinguishes root Array-backed Vector.
All three vector exercises and both cons/append projection laws are retained.

## Provider inspection and evidence limits

All **30 source/provider hashes in the frozen plan** match the actual files.
Consequential declarations were read directly, including:

- The complete staged table observation draft and queue-peek cost draft.
- `AList`'s carrier, unique keys, insert/entries/lookup laws, and the relevant
  dependent-list lookup/insert facts; `Equiv.sigmaEquivProd` has the stated
  constant-family Sigma-to-product type.
- `List.Vector`'s subtype carrier, cons/append constructions and list-projection
  theorems; core Vector's Array carrier; core Subtype and Exists definitions;
  the actual Even witness and `even_two` provider.
- Core `List.headD`, its two constructor equations, `tail_append` and its
  nonempty specialization, with the exact argument/branch directions.
- Squares/Relational carrier and commuting/preservation fields;
  `ListFusion.foldl_reachable` with invariant base, preservation and commuting
  step hypotheses.
- AbstractFIFO operations/simulations/clients, the distinct Symmetric queue
  recurrence, FIFOContracts' explicitly uncharged endpoint head, and actual
  resource run/potential/budget statements.

The first default-shell attempt to read the installed Lean core path could not
see that native installation. An approved read-only execution then read the
exact pinned files and verified their hashes and types. No installation,
environment change, compiler, project validation command or artifact mutation
was performed. This routing detail is not a plan finding or integrity claim.

## Findings and disposition

| ID | Status | Finding |
| --- | --- | --- |
| — | None | No actionable omission, false API assertion, weakened source contract or unsupported acceptance claim found in the frozen plan. |

The plan may proceed as preparation for later chapter implementation. Every
proposed definition, proof, instance, adapter, measured theorem and connected
case remains pending the predecessor gate and the ordinary integrated build,
exhaustive audit, independent Standards/Spec reviews and final candidate
verification. This review grants no chapter acceptance and changes no ticket.

Only this review file was written; the author's plan remains unchanged and
frozen at its recorded hash.
