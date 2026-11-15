# Frozen requirements — FDSA-XH01 priority-queue observations and merge

Frozen before source authoring on 2026-11-02 after complete root reading of
all three stopped preflights and the full requirements draft. This file fixes
the complete mathematical scope and original review base. It is not an
implementation or acceptance claim. Root must record the clean start state,
create/expose/successfully upload pre-code checkpoint **0050 before any XH01
source authoring**, and then explicitly release the disjoint source owners.
An upload pending or failed does not release authoring. Root owns control,
Git, validation coordination and durability operations.

The complete original draft is retained unchanged as
`priority-queue-requirements-draft.md`, 31,782 bytes / 538 lines, SHA-256
`ded238065a0e9e02202c162111e60d4cd262dae25a9bbd678fa84c079446123d`.
Finalization resolves names, the two-field merge evidence packaging and source
ownership below; it does not reduce the draft's mathematical obligations.

The user's cross-cutting exception permits the proposed shared work while
Chapter 1 remains the active prerequisite. All shared units and chapters are
unaccepted. This draft does not activate Chapter 14 or change the whole-book
scope, chapter order, previous requirements, or original integration history.

## 1. Original base and exact candidate paths

Local unit: **FDSA-XH01**. Original review base and immediate parent:
`07e480f6ec9958d4975bb90151005b84f2907614`, the still-unaccepted repaired
Chapter 1 candidate. Isolated worktree:
`/workspace/scratch/845aa1048b05/conaled-priority-observations`; branch
`work/fdsa-priority-observations`. The separate start JSON records the actual
clean checkout, absent new paths and input identities before source authoring.

Accepted repaired Chapter 1 is required before this unit's integration and
acceptance. There is no dependency on XA01 or any other unaccepted shared
branch. Later Chapter 1 fixes must be merged normally while preserving the
original base, full requirements, and findings history. The initial Chapter 2
integration prefix remains
`c80eec92f5458eccfd1c34c8314d666c2a1e3847`; this unit adds no prerequisite
to that prefix.

The complete authorized source diff has exactly these six paths:

1. `Applications/Search/PriorityMultiset.lean` — new ordinary operation views,
   entry/priority observations, exact-law consequences, source minimum bridge,
   observed-removal agreement, finite realizability, and direct-root access
   correspondence on the existing leftist carrier.
2. `Applications/Search/PriorityMerge.lean` — new compatibility evidence for a
   supplied merge, actual existing merge witnesses, observational algebra, and
   an ordinary merge–insert–remove client with its validity/content proof.
3. `Examples/PriorityModels.lean` — new compact connected positive cases and
   consequential boundaries specified below.
4. `SquareApplications.lean` — one added import of `Examples.PriorityModels`.
5. `docs/research/fdsa-priority-queues.md` — new reconstruction, source/license,
   architecture, statement assessment, examples, and truthful status note.
6. `docs/research/fdsa-reconstruction-map.md` — append only the XH01 support and
   remaining-obligation section; retain every existing row and historical claim.

Keep `Operations`, `ExactLaws`, `ExactQueue`, all existing queue implementations,
and all existing consumers **byte-identical**. Do not edit `PriorityInterface`,
`ExactPriority`, `LeftistQueue`, `PrioritySearchQueue`, Huffman modules, or old
examples. New lemmas/helpers may use the existing namespaces in the two new
modules. No new queue carrier, parallel queue hierarchy, executor, ADT language,
or retrofit of the old fields is in scope. There is no toolchain, dependency,
validator, warning policy, integrity-guard, audit-root, or cache-layout change.

## 2. Complete retained evidence and source scope

All three completed preflights were read in full for this draft, and their
ordinary byte hashes were checked against the supplied identities:

| Report under `fdsa-control/research/` | Bytes / lines | SHA-256 |
|---|---|---|
| `priority-queue-source-preflight.md` | 29,031 / 416 | `79fff00277221c6c5279841a5eb88517f57a2e52cf8b0f1ac393492a87bdec79` |
| `priority-queue-api-preflight.md` | 31,737 / 257 | `12927ddbc7198cd6d9e8f23587671fe42134373b699d8a99282930108a36b2f8` |
| `priority-queue-case-preflight.md` | 26,693 / 424 | `4b642e8382a65e4369bb9e84e0a141fa8ec29d2104651b4bc51c478c15445278` |

Root's complete-read assessment and chosen bounded design are retained in
`reviews/priority-queue-preflight-readback.md`. These records are source
preparation, not a passing independent review or compiler result. Additional
coordinator clarifications incorporated here are the fixed-observation keyed
counterexample and a compact cross-universe central-theorem specialization.

The source is the July 27, 2026 official book, Chapter 14 printed pp. 179–182
/ PDF pp. 185–188, with PDF SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The complete extraction `book-source/chapter14.txt` has SHA-256
`b566830b6c95d218e3fe8095914a336a35d45e0f51df8203588c02b36589fe3a`.
The complete companion `Priority_Queue_Specs.thy` and `Heaps.thy` were read at
Isabelle revision `f86f290225eebcc52c1ae7dba2e098f405f51c21`, respectively
SHA-256 `c8ef42fadf9964735af07a9d0c6a5ec1c6a89ffe5ae2bce04865e003eda7d09a`
and `662b2bc74840ad46a54e95ed5b62b7117806b9e0cf1407a7d70968e4d2dc95fe`.
The support revision postdates the manuscript and is not asserted to be its
generation revision. Preserve the applicable Isabelle BSD-3-Clause attribution
and notice for adapted contracts/laws, with the exact URLs and license identity
from the source preflight. Do not reproduce the manuscript or invent a project
license. Existing Mathlib/Batteries dependencies retain their own notices.

The common mathematical scope is **C14-001–013**: source operations and finite
minimum observation, seven displayed base laws, two merge laws, the companion's
additional `is_empty` reflection, and the general payload/priority specialization.
Proving this shared unit does not itself close those rows' concrete chapter
instantiations. All original obligations remain mandatory.

## 3. XH01-01 — ordinary views and exact occurrence observations

Reuse `Search.PriorityInterface.Operations`, `ExactLaws`, and `ExactQueue`
without redefining them. Retain independent payload, priority, and carrier
universes. Concrete executable comparison assumptions remain those of the
existing implementations; abstract observation results require only the
capabilities they actually consume.

Define generic executable views using **`Operations` only**, not an observation,
validity predicate, or law bundle. The mathematical definitions are:

```text
insertOne ops e q       = ops.add [e] q
peekEntry? ops q        = (ops.remove q).map Prod.fst
peekPriority? ops q     = (ops.remove q).map (fun z => z.1.2)
deleteMin ops q         = match ops.remove q with none => q | some (_,r) => r
isEmpty ops q           = (ops.remove q).isNone.
```

The operation helpers are in `Search.PriorityInterface.Operations`, with the
names and argument order above. Their meanings and separation from evidence
are fixed. The remaining public coordination is specified in Section 11. These views need no order,
decidable equality, finite type, or inhabitance on payloads/priorities. They are
views of the supplied computation, not a new executor. The semantic peek and
emptiness definitions make no cheap-access claim. Identity on `none` is the
explicit chosen state-valued deletion convention, not a law forced on every
source implementation.

For an actual `Q : ExactQueue α π`, define ordinary observations in the existing
`Search.PriorityInterface` namespace:

```text
entryMultiset Q q    = (Q.entries q : Multiset (α × π))
priorityMultiset Q q = (entryMultiset Q q).map Prod.snd
popObs Q q          = (Q.remove q).map
                       (fun (e,r) => (e.2, priorityMultiset Q r)).
```

Prove public consequences from the actual `Q.lawful` fields:

- Empty entry/priority multisets and `Q.Valid Q.empty`.
- Unconditional batch insertion equations for entries and priorities, with
  singleton specialization to the actual `insertOne`; inserted validity under
  `Q.Valid q`. Preserve duplicates and original batch semantics.
- Unconditional equivalences among `remove q = none`, empty entries, zero entry
  multiset, zero priority multiset, and the Boolean empty reflection. Also
  establish nonempty observation implies an actual `some` result, without
  falsely requiring validity for this existence fact.
- For `Q.Valid q` and an actual equation `Q.remove q = some (e,r)`, prove
  `Q.Valid r`, selected-entry membership, `E(q) = e ::ₘ E(r)`, selected-priority
  leastness `IsLeast {p | p ∈ P(q)} e.2`, and `P(q) = e.2 ::ₘ P(r)`.
  Here `E` and `P` abbreviate the two named observations, not new data types.
- Exact cardinality consequences: observations have the existing entry-list
  length, insertion adds batch length, and successful valid removal satisfies
  residual cardinality plus one equals input cardinality. No mere support
  inclusion or set equality may replace multiplicity equality.
- Connect the ordinary optional peek and state-valued deletion views to the
  same actual successful result and their stated empty branches. On valid
  inputs carry residual validity through those views; preserve the source's
  nonempty domain when presenting source minimum/deletion laws.

Entry decomposition, priority projection, cardinality and failure statements
must not acquire payload equality decisions or a global linear order. The
existing abstract law package needs `[LE π]`. Existing `add_exact` and
`remove_none` are unconditional on raw states, while `add_valid` and
`remove_spec` require validity. Do not weaken the former or generalize the
latter. A book ADT instance is not automatically an `ExactQueue`; the adapter
from these existing stronger laws to the source is one-way.

## 4. XH01-02 — central atomic observation agreement

For `Q : ExactQueue.{u,w,z} α π` and
`R : ExactQueue.{v,w,z'} β π`, use independent payload and carrier universes
and a common priority type/relation. Under only `[LE π]`, explicit

```text
hantisymm : ∀ p q : π, p ≤ q → q ≤ p → p = q,
```

both input-validity proofs, and equality of initial priority multisets, prove
`popObs Q q = popObs R r`. The result must compare the **actual** `remove`
results and residual priority observations. It may not assume the desired
post-removal equation or introduce a substitute sequence of abstract minima.

The proof uses raw failure reflection, leastness/membership, antisymmetry of
the two selected priorities, and cancellation of one common multiset cons.
Do not require `DecidableEq` on either payload or priorities, a `LinearOrder`,
transitivity, totality, a finite universe, or a shared carrier. A convenient
concrete realization may keep its existing stronger order assumptions.

The agreement claims neither selected-payload equality, residual full-entry
equality, raw-state equality, insertion stability, tie-selected tree equality,
nor cost equality. The tied and non-antisymmetric examples below are required
to delimit these conclusions. No new equivalence-class or queue hierarchy is
needed to state this ordinary observation theorem.

## 5. XH01-03 — seven source laws, companion reflection, and realizability

Specialize payloads to `Unit` and priorities to the source element type `σ`.
Singleton source insertion is actual `ops.add [((),x)] q`, and source content
is the priority multiset `P(q)`. Under `[LinearOrder σ]` and `P(q) ≠ 0`, use
the existing finite support minimum

```text
(P(q)).toFinset.min' (Multiset.toFinset_nonempty.mpr hnonempty).
```

Prove the actual optional priority observation is `some` of this minimum on
valid nonempty input. This is a nonempty finite-support selector, not a global
finite-type assumption or a total default-valued getter. At this local
linear-order boundary, prove the singleton-subtraction presentation for the
actual residual/deletion view. Decidable equality is supplied on priorities
here; it must not leak into the general payload interface or XH01-02.

Expose and document all seven displayed laws, using the explicit Option/domain
adaptation for get-min:

1. `P(empty) = 0`.
2. `Valid(empty)`.
3. Valid input gives `P(insert x q) = P(q) + {x}`.
4. Valid input gives valid insertion.
5. Valid nonempty input gives `P(deleteMin q) = P(q) − {minimum P(q)}`,
   with agreement to the actual observed `some` minimum.
6. Valid nonempty input gives valid deletion.
7. Valid nonempty input has optional minimum `some (minimum P(q))`.

Include the companion's **eighth** law separately:
`Valid q → (isEmpty q = true ↔ P(q) = 0)`. Its generic consequence can be
stronger because `remove_none` is unconditional; do not miscount it as a line
of Figure 14.1. A Boolean reflection is not a Bool/Prop equality. Preserve
the different stronger empty-deletion premise in `Heaps.Heap` as a documented
source qualification; this unit does not implement that plain-tree locale.

Also prove the small finite-realizability consequences:

- For every `m : Multiset (α × π)`, there exists an actual state `q` with
  `Q.Valid q ∧ entryMultiset Q q = m`. The proof must construct the state as
  `Q.add xs Q.empty` from a list representative and use the existing insertion
  and initialization laws. It must not assume surjectivity or a new inverse.
- For every `m : Multiset π` and an explicit supplied `a0 : α`, construct a
  valid representative of `m` by inserting entries with payload `a0`. `Unit`
  supplies `()`. Do not replace that explicit value by a global `Inhabited`
  requirement.
- The empty multiset remains representable without a payload witness, while
  Empty payloads cannot realize a nonempty priority multiset. No representation
  uniqueness, raw-state equality, or unrestricted abstract-map analogy follows.

## 6. XH01-04 — actual root access and merge compatibility

### Direct access on the existing leftist carrier

In a new module, add a plain optional root match on `Search.LeftistQueue.PQ`:
`null ↦ none` and `fork _ x p _ _ ↦ some (x,p)`. The definition requires no
order, equality decision or validity. Prove its equality with
`(LeftistQueue.deleteQ q).map Prod.fst` on every raw tree, using only the
parameters needed to run the existing deletion. Connect actual `nullQ` to
empty entry and priority multisets on all raw trees. Retain heap-order versus
rankedness distinctions; if a direct-root leastness lemma is exposed, use the
existing `Heap`/`root_all` route without demanding rankedness for that root fact.

These are value correspondences. There is **no** measured operation, access
bound, allocation claim, compiler-erasure assumption, or runtime comparison in
XH01. Existing deletion actually computes its child merge; projecting it does
not inherit the execution behavior of the new direct match.

### Supplied merge and its two laws

Keep `Operations` and `ExactQueue` unchanged. For a supplied actual
`merge : Q.Carrier → Q.Carrier → Q.Carrier`, require separately, for valid
`q,r`, occurrence compatibility and output validity:

```text
(Q.entries (merge q r)).Perm (Q.entries q ++ Q.entries r)
Q.Valid (merge q r).
```

Use the proposition-valued **two-field** `MergeLaws entries Valid merge` record
fixed in Section 11, against the supplied existing carrier, entries and validity.
The operation is a parameter, not a new carrier or queue family. No extra
operation, observation, validity, execution or hierarchy field is permitted.
Both represented input states keep their actual validity premises.

Derive entry/priority multiset addition and cardinality; preserve stronger
unconditional occurrence theorems where the actual implementation has them.
Provide the two concrete witnesses:

- Existing `LeftistQueue.combineQ`, using actual `combineQ_entries` and
  `combineQ_valid`, with all current rank-aware behavior unchanged.
- Actual `List.append` for the existing `exactList` carrier with its selected
  identity entry observation and `True` validity predicate.

Prove small entry/priority-observational commutativity, associativity, and
left/right empty identities on valid inputs. The associativity argument must
carry the required intermediate merge-validity proofs. None of these are raw
state equalities. Overlap and self-merge add every occurrence; no disjointness,
`Nodup`, unique key, stable tie, destructive ownership, or amortized-consumption
premise is introduced. The Braun source's base-only queue remains permissible.

## 7. XH01-05 — ordinary sequential client

Define an operation-only client with supplied `Operations`, supplied merge,
inserted entry `e`, and two input states. Its executable result is exactly

```text
ops.remove (ops.add [e] (merge q r)).
```

There are no observation, validity, or law parameters in this operation's
definition. Its theorem consumes an actual `ExactQueue`, the two merge laws,
and both initial validity proofs. Establish the validity and observation of
the merged state, then of the singleton-added state, then nonemptiness caused
by that inserted occurrence, and an actual successful removal. Establish the
returned state's validity, exact entry/priority decomposition, least returned
priority, and exact cardinality. In particular the final cardinality is the
sum of the two initial cardinalities: one insertion and one removal cancel
in the count, not necessarily in the identity of the selected entry.

The proof must use the actual client expression and actual intermediate
states. A proposition merely assuming its final multiset, or an independent
arithmetic reconstruction with no public-client connection, is insufficient.
The leftist/list realizations below must consume this common client theorem
and XH01-02, in addition to establishing independent concrete expectations.

## 8. XH01-06 — compact connected examples and boundaries

All examples belong in `Examples/PriorityModels.lean`. Use ordinary allowed
kernel proofs and the actual public results, retaining separately calculated
expected outcomes. Do not add a new queue implementation or a duplicated
Huffman proof. Old Huffman examples/clients are context and remain unchanged.

For the Unit/Nat leftist shapes below, write `E = PQ.null`,
`N k p l r = PQ.fork k () p l r`, and `S p = N 1 p E E` as explanatory
notation for the existing raw constructors; smart `fork` retains its behavior.

### Positive occurrences and the nontrivial common client

1. **Duplicate minimum.** Actual `makeQ [((),1),((),1),((),3)]` is valid and
   removes one priority `1`, leaving priority multiset `[1,3]` of cardinality
   two. Its raw shape is `N 1 1 (N 1 1 (S 3) E) E`; the actual residual is
   `N 1 1 (S 3) E`. Connect the new public decomposition/minimum statements,
   not merely evaluation. Include source finite-support minimum and the
   subtraction presentation on this nonempty duplicate input.
2. **Merge–insert–remove.** Build `A` from priorities `[1,3]` and `B` from
   `[1,2]`, merge them with actual `combineQ`, insert priority `2` by singleton
   `exactLeftist.add`, and remove the actual minimum. The concrete evidence is:

   | Stage | Actual entries' priorities | Required content/count connection |
   |---|---|---|
   | `A`, `B` | `[1,3]`, `[1,2]` | Valid states, each size 2. |
   | `M = combineQ A B` | `[1,3,1,2]` | `{1,1,2,3}`, size 4, both initial validity proofs consumed. |
   | `I = add [((),2)] M` | `[1,1,2,2,3]` | `{1,1,2,2,3}`, size 5, actual merged validity consumed. |
   | Actual removal of `I` | selected `1`, residual `[1,2,2,3]` | Residual size 4 and valid; inserted `2` survives. |

   The residual shape is `N 2 1 (S 2) (N 1 2 (S 3) E)`. Use the generic
   client and actual sequential validity, not only these shape calculations.
3. **Different realizations, one atomic observation.** Construct the matching
   `exactList` states using its actual empty/add, append merge, and final
   singleton add. Before removal its raw list is `[1,3,1,2,2]`. Apply XH01-02
   with the actual validity/content evidence to show both clients' atomic
   observations equal `some (1,{1,2,2,3})`. No mergeSort tie-stability premise
   is needed and no equality of input lists or carriers is asserted.
4. **Overlap, self-merge, and algebra.** The main operands already overlap at
   `1`; retain that fact. On an actual valid `[1,3]` state, self-merge has two
   occurrences of each priority, not idempotent union. Consume the merge
   witness and the new observational algebra, including empty identities.
5. **Independent universes.** Give one compact actual specialization of XH01-02
   between `exactLeftist` with Unit payloads/Nat priorities and `exactList`
   with `ULift.{1} Unit` payloads/Nat priorities. Insert the same duplicate
   priorities `[1,1,3]` through actual add/empty and derive the common atomic
   observation `some (1,{1,3})`. This checks independent payload/carrier
   universes without a new instance hierarchy or Huffman dependency.

### Ties and the precise order boundary

6. **Tied payloads.** Let `F` and `T` be actual valid singleton leftist heaps
   with `(false,1)` and `(true,1)`. `deleteQ (combineQ F T)` is
   `some ((false,1),T)` and reversing merge operands gives
   `some ((true,1),F)`. Use XH01-02 to obtain the shared priority observation
   `some (1,{1})`, while proving selected payloads and residual **entry**
   multisets differ. This refutes raw commutativity and a stronger full-item
   agreement, without refuting the positive observational theorem.
7. **Antisymmetry is necessary.** Use a local decidable indiscrete preorder on
   Bool priorities, `p ≤ q := True`. Existing leftist realization assumptions
   are satisfied locally. Merging valid singleton priorities false/true in
   opposite orders gives the same input priority multiset but selected values
   false and true. Both satisfy leastness; `popObs` equality fails. Do not
   install this relation globally or claim all preorders are antisymmetric.

### Empty types, finite realizability, and keyed replacement

8. **Empty behavior/types.** Connect actual empty leftist/list states to raw
   failure, Boolean reflection, direct `nullQ`, and optional none; retain a
   valid singleton's one-step empty residual. With Empty payloads and Nat
   priorities every entry/priority observation is empty and removal is none
   on every raw state. With Unit payloads and Empty priorities the analogous
   optional-none boundary holds using only local vacuous instances. An Empty
   carrier cannot supply `Operations.empty`. Do not add default elements.
9. **Actual finite realization.** Consume the entry-realizability theorem and
   explicit-payload priority-realizability theorem on duplicate occurrences,
   with the actual add-to-empty construction. Unit provides a positive payload.
   Prove that Empty payloads with Nat priorities cannot realize `{1}`; do not
   assert non-surjectivity of the finite entry-multiset observation itself.
10. **Fixed keyed replacement counterexample.** Use actual
    `Search.PrioritySearchQueue.keyed (fun x : Nat × Nat => x.1)`, its chosen
    operations, `entries := id`, and `Valid := Unique key`. The existing
    `exact_same_key_tie` gives
    `add key [((3,10),7),((3,20),7)] [] = [((3,10),7)]`.
    Connect the actual lawful keyed coverage/length facts and show that these
    fixed operations and entry observation fail exact insertion by length
    one versus two. Any no-`ExactLaws` conclusion is only for those fixed
    operations/entries/validity. Do not claim impossibility for every keyed
    queue or every imaginable alternative observation. Retain the existing
    forward weakening `ExactQueue.keyed` and make no converse claim.

### Three independent malformed-state phenomena

11. Use the distinct raw Unit/Nat trees:

    | Raw state | Exact required distinction |
    |---|---|
    | `C = N 9 1 E E` | Heap order true, rankedness false, therefore invalid; actual removal is `some (((),1),E)`, whose minimum/content/residual happen to be correct. Invalidity does not imply every result is wrong. |
    | `H = N 1 3 (S 1) E` | Rankedness true, heap order false; removal returns `3` with residual `S 1`. Content and residual validity hold, but selected priority is not least. |
    | `K = N 1 0 C E` | Heap order true but descendant rank invalid; removal returns minimum `0` with residual `C`, which is invalid. A correct minimum/content observation does not imply residual validity. |

    Connect direct-root and raw deletion/nullQ correspondences on these states.
    Preserve unconditional concrete content facts through actual
    `combineQ_entries`; do not apply abstract valid-removal laws to invalid
    inputs. Also use actual insertion `insertQ () 0 C = N 1 0 C E`, whose
    entries are `[0,1]` but whose corrupt child remains invalid, to consume
    unconditional `add_exact` without pretending it repairs validity.

Cases may share fixtures and proofs; they do not require independent redundant
test harnesses. Each new public theorem must have a meaningful retained use;
ordinary mathematical examples must not be replaced by assumptions restating
their desired conclusions. Exact source expressions and public argument orders
must be read before clients are written.

## 9. XH01-07 — documentation, source limits, and statement readback

The new reconstruction note must map all C14-001–013 claims to the actual new
and reused declarations, explain the seven/eight-law distinction, nonempty
source domains, stronger raw-state exact laws, and one-way source adaptation.
Include exact source/version/license references and the preserved difference
between the book PDF and its later companion-source revision.

Explain operations versus observations/evidence, full entries versus projected
priorities, one-occurrence deletion, explicit antisymmetry, optional empty
behavior, realizability domains, and actual intermediate validity. Explain why
source `Unit` specialization neither orders payloads nor makes ties stable.
Record direct peek versus deletion-derived value equality with **no cost claim**.
The source later leftist analysis counts `mht`/`node` as zero helpers under its
selective tariff; retain its distinction from positive local-access models.

Document actual reuse by later leftist/binomial/skew/pairing contracts, the
Braun base-only boundary, and Huffman's independent cache-validity obligation.
Existing Huffman is supporting context only; no duplicated algorithm, new
Huffman dependency, or tie-specific output-equality theorem is required here.

All C14-014–040 remain mandatory and queued: the sorted-list implementation
with constant-time minimum/deletion, actual naive plain-node merge and its
proofs, ordinary heap interpretation, heap enumeration with its quadratic
work claim, and inorder-preserving heap construction/existence/distinct-label
uniqueness with duplicate counterexample. `exactList` sorts at removal and
does not supply Exercise 14.1; `combineQ` swaps children/ranks and is not the
printed naive merge. Every later concrete heap algorithm, structural/cache
invariant, recurrence, cost/amortized premise, exercise and Chapter 26 source
correspondence remains under its original obligation. No new resource,
ownership, translator, or history framework is made mandatory by this exclusion.

Perform and retain full mathematical statement readback for **every** new or
changed formal claim, including hypotheses, universes, selected observations,
validity, Option branches, finite support, and actual operation connection.
Distinguish source-only proof assessment from elaborated/compiled evidence.
State the actual draft/validation/review/acceptance status in the new note and
appended map; no unsupported claim of chapter completion is permitted.

## 10. XH01-08 — later validation, independent review, and recovery

This section specifies future acceptance requirements and authoring controls;
it authorizes **no validation now**. Chapter 1 session 83124 on the fixed 07e
candidate remains the sole compiler/checker. Until root releases that gate,
no second compiler, Lake command, checker, project integrity/hash helper, or
speculative cache operation may run.

Before source authoring, root must finalize/freeze the complete requirements,
record actual original base/index/worktree/untracked state, establish the
isolated branch, and create/expose/successfully upload checkpoint 0050. Preserve
this draft, all three original preflights, the final requirements, root readback,
source pins, local tracking, and start identities. An upload still pending or
failed is not the authoring-release condition. Root then assigns disjoint files
and coordinates stable API signatures before consumers are written.

Before acceptance, capture the entire immutable candidate against the original
fixed base. Later matching validation must include focused compilation of the
changed formal targets, the applicable full guarded candidate check with both
pre- and post-build integrity passes, complete integrated build/coverage and
source-policy checks, and the exhaustive transitive axiom audit of all relevant
local declarations, including private/generated declarations. Follow the current
README and retained incident runbook; do not change tooling or weaken checks to
obtain a pass. Focused/source-only evidence is not a full-candidate success.

Use the retained independent Standards and Spec workflow against the **same**
complete frozen scope and immutable candidate. Preserve original findings and
fix histories; concrete corrections do not rewrite the original requirements
or review base. Both axes must pass with matching applicable validation, and
root must immediately run the matching candidate-record verification before
acceptance. A later changed tree/commit requires evidence appropriate to that
candidate; stale records or reviews do not carry over silently.

No admissions, new axioms, unsafe or partial definitions, native-evaluation
proof shortcuts, warning/audit weakening, or invented checked results are
allowed. Apply the existing example-driven and implementation/review standards
within the current loop; this draft does not create another review loop.
Acceptance also requires the repaired Chapter 1 prerequisite, and no chapter
is accepted merely because this shared unit is saved or checked.

Root owns Git, local tickets/control records, integration, immutable capture,
and durability uploads. Authors change only assigned source files and stop
before capture. Commit non-main worktree source before its durability snapshot;
save full source history, requirements, provenance, findings, truthful validation
status, local tickets and recovery instructions, then expose and upload each
completed checkpoint promptly. No GitHub write or push is permitted.

## 11. Final public coordination and ownership

The following authoring names and parameter order are fixed for the new code;
they are intended declarations, not a claim that new source already exists:

- In `Search.PriorityInterface.Operations`: `insertOne ops e q`,
  `peekEntry? ops q`, `peekPriority? ops q`, `deleteMin ops q`, and
  `isEmpty ops q`, with exactly the definitions in XH01-01.
- In `Search.PriorityInterface.ExactQueue`: `entryMultiset Q q`,
  `priorityMultiset Q q`, and `popObs Q q`. Their namespace supplies ordinary
  method notation while retaining the selected existing ExactQueue.
- The central theorem is `ExactQueue.popObs_eq Q R hantisymm q r hq hr hobs`,
  where both payload/carrier universes are independent and `hobs` is equality
  of the input priority multisets. Its conclusion and weakest assumptions are
  exactly XH01-02. The author must publish its actual complete signature before
  the case author consumes it.
- In `Search.LeftistQueue`, the new direct-root optional observer is `peekQ? q`.
  It is defined in PriorityMultiset, with no edit to the old LeftistQueue file.
- In `Search.PriorityInterface`, use the small evidence record below and the
  ordinary operation `mergeInsertRemove ops merge e q r` with exactly the
  expression in XH01-05. The real witnesses are named `leftistMergeLaws` and
  `appendMergeLaws`; the latter is an ordinary append law applicable to the
  existing exactList realization, not another list queue.

The merge evidence has no order premise of its own and exactly these fields:

```text
MergeLaws {C : Type z}
  (entries : C → List (α × π)) (Valid : C → Prop)
  (merge : C → C → C) : Prop
  entries_perm : ∀ q r, Valid q → Valid r →
    (entries (merge q r)).Perm (entries q ++ entries r)
  valid : ∀ q r, Valid q → Valid r → Valid (merge q r)
```

The alpha, priority and carrier universes are independent. The actual existing
Q instantiation is `MergeLaws Q.entries Q.Valid merge`. This small evidence
package is justified by the two real witnesses, repeated actual client uses
and observational algebra; it adds no carrier, operations field or hierarchy.
Other supporting theorem names/argument order are ordinary implementation
choices, but their actual declarations must be read before clients are written.
No naming adjustment may change the fixed mathematical obligations silently.

After successful checkpoint 0050 and root's release, disjoint source ownership
is: architecture author owns only PriorityMultiset; book/source author owns
only PriorityMerge; case author owns only Examples.PriorityModels; root owns
the note, single public-root import, append-only source map and all control
records. Publish core signatures before consumers; stop all source writes
before root's exact byte capture and local commit. No author runs Lean, Lake,
a compiler/checker, project hash helper, Git/ref/cache or remote operation.
Root's existing Chapter 1 gate remains the sole compiler/checker.

The start record and successful checkpoint receipt are the remaining release
steps. The frozen scope, original base, retained draft/preflights and complete
findings history remain unchanged through later proof corrections; any needed
mathematical clarification is an explicit addendum, never a quiet rewrite.
