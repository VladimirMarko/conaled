# Frozen requirements — FDSA-XA01 shared Set/Map contracts and refinement

Frozen 2026-11-02 before any XA01 source edit, after root read all three complete
preflights and the actual relevant source/APIs. Preserve this document unchanged;
record later clarifications as explicit addenda. Source authoring is not released
until the clean original base is recorded and the pre-code checkpoint is created,
exposed and successfully uploaded. The user's cross-cutting exception permits
this shared work; Chapter 1 remains active and no chapter, appendix or shared
unit is accepted.

## 1. Base, dependency and complete candidate scope

Local ticket: FDSA-XA01. Original review base and immediate parent:
`07e480f6ec9958d4975bb90151005b84f2907614`, the focused-pass but still
unaccepted repaired Chapter 1 candidate. Isolated worktree:
`conaled-adt-refinement`; branch `work/fdsa-adt-refinement`.

Accepted repaired Chapter 1 is required before this unit's integration and
acceptance. There is no dependency on an unaccepted tree, partition, potential,
probability or other shared branch. If Chapter 1 requires later corrections,
merge them normally while preserving this original base and findings history.
The initial Chapter 2 prefix remains exactly
`c80eec92f5458eccfd1c34c8314d666c2a1e3847`; this unit adds no prerequisite
to that prefix and does not activate Chapter 6.

Expected complete changed paths:

1. `SquareKit/ValidGraphs.lean` — one unbundled relation and two thin bridges.
2. `Applications/Collections/Set.lean` — operation-only Set interface, exact
   laws, schema connections and a small ordinary client.
3. `Applications/Collections/Map.lean` — operation-only Map interface, exact
   laws, function-update/schema connections and a small ordinary client.
4. `Applications/Collections/Modify.lean` — modified interface and both
   law-preserving translations, with correctly qualified round trips.
5. `Applications/Collections/AList.lean` — adapter for the actual standard
   finite association-list operations and their existing proofs.
6. `Examples/SetMapContracts.lean` — generic/concrete model and paired-state
   cases, AList client connections and observation boundaries.
7. `Examples/MapModify.lean` — both translations and the hidden-counter
   counterexample to an unjustified stronger round trip.
8. `Examples/ADTRefinement.lean` — actual existing-square composition,
   role/product/nullary/observation connections and missing-premise cases.
9. `SquareApplications.lean` — add the three example imports only.
10. `docs/research/fdsa-adt-refinement.md` — source/architecture/proof scope,
    complete statement assessment, examples and applicable source notice.
11. `docs/research/fdsa-reconstruction-map.md` — append support and remaining
    obligations while preserving every existing row and history.

No existing operation, relation, square, compiler or client is redefined.
No toolchain, dependency, validator, integrity guard, warning policy or audit
root-selection change is within this unit. A concrete inherited defect belongs
to its retained owner and must not be silently folded into this source work.

## 2. Source and completed preparation

The official book is the July 27, 2026 edition, SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Read Chapter 6 printed pp.77–83 completely, including both directions of
Exercise 6.2 on p.83. The blank p.84 adds no omitted tail. The companion pin is
`f86f290225eebcc52c1ae7dba2e098f405f51c21`, not asserted to have generated
that PDF. Exact `Set_Specs.thy` and `Map_Specs.thy` identities and related
ordered-list files are in the source/API reports and Chapter 6 inventory.
Retain the pinned Isabelle BSD-3-Clause notice for adapted contracts/laws.

Completed preparation:

- `research/adt-refinement-source-preflight.md`, 22,132 bytes / 342 lines,
  SHA-256 `5db706e4afc85913cfd92c8aeace3de2e8aea174fe813b828aa9a30a3d1d8994`.
- `research/adt-refinement-api-preflight.md`, 28,486 bytes / 445 lines,
  SHA-256 `4d63f2616dee5af5e358cc59696745f215698973517dad9d4d77c1310b09e391`.
- Root readback and the separate bounded design assessment are in
  `reviews/adt-refinement-preflight-readback.md` and
  `reviews/adt-refinement-design-decision.md`.
- `research/adt-refinement-case-preflight.md`, 29,841 bytes / 466 lines,
  SHA-256 `98bf8c5e68cb8eecbedbedfde8caf8ed1587c5219a0df8c2d794085ef9738e52`.
  Its author stopped and root read the complete final file. The separate source
  author assessed the complete pre-freeze draft and found no concrete omitted
  obligation or false premise within this bounded shared scope. Neither that
  assessment nor the preflights supplies an independent final approval.

Root and authors must use actual existing `Relational.RelSquare`,
`existentialSquare`, `transportRelations`, `AbstractFIFO` operations/laws/client
pattern, pinned `Relator.LiftFun`, `Relation.Comp`, `Function.eq_update_iff`
and AList interfaces. Source investigation does not constitute a passing gate.

## 3. Shared valid-graph bridges

Namespace `SquareKit.ValidGraphs`, independent type universes. Define only

```text
validGraph I decode c a := I c ∧ decode c = a.
```

Prove the precise preservation equivalence:

```text
Relator.LiftFun (validGraph I decode) (validGraph J decode') impl spec
  ↔ ∀ c, I c → J (impl c) ∧ decode' (impl c) = spec (decode c).
```

Prove the precise relational-composition equivalence:

```text
Relation.Comp (validGraph I decode) (validGraph J decode') c b
  ↔ (I c ∧ J (decode c)) ∧ decode' (decode c) = b.
```

Use the existing existential relation; no second composition operation is
needed. Its grouping makes the result the valid graph of the composite decoder
with invariant `I c ∧ J (decode c)`. Neither bridge requires inhabitance,
decidability, injectivity, surjectivity or common type universes. No assertion
on malformed input is supplied by the valid-state preservation theorem.

The Set/Map operation theorems must consume the first bridge. The actual
two-stage examples must consume existing `existentialSquare`, with its actual
pointwise middle-operation equality, and `transportRelations` using the second
bridge. `Relational.compRel` is definitionally the same existential predicate.
Bundled examples may use Type 0; retain the old bundled API unchanged and keep
the new domain contracts universe-independent. No new generic ADT language,
refinement record, LiftFun composition hierarchy or universe retrofit is needed.

## 4. Exact Set contract and ordinary client

Use `Collections.Sets.Ops` and separate proposition-valued `Laws` (or consistent
equivalent local names communicated before clients are written). For independent
`α : Type u`, `S : Type v`, the operational fields are exactly empty, insert,
delete and `isin : S → α → Bool`. The decoder `S → Set α` and `Valid : S → Prop`
are separate specification parameters, not operational inputs.

The seven source laws are unconditional empty observation and empty validity;
under valid input, insertion observes union with a singleton and preserves
validity, deletion observes singleton subtraction and preserves validity, and
`isin s x = true ↔ x ∈ decode s`. Require no order, equality decision, finite
semantic support, global decidable invariant or default element/state.

Provide insertion/deletion valid-graph preservation through the shared bridge,
and explicit initialization and membership-schema connections. Bool membership
uses reflection, not an equality between a Bool value and a proposition. A
reflection relation or decoder `fun b : Bool => b = true` into Prop is suitable;
do not claim arbitrary sets have executable membership decisions.

Define one operation-only client that inserts a, inserts b and deletes a, with
no decoder, validity or proof arguments in its executable definition. From
the laws, prove each needed intermediate validity and its final set observation
on arbitrary valid input. From corresponding initial observations, derive
agreement of this client's membership queries across lawful implementations.
The result at a is false; if b ≠ a, the result at b is true. Include the same-key
case, where the final inserted key is absent, and preserve unrelated initial
membership. The theorem must consume the actual client operations and law
fields, not a premise restating the desired final observation.

## 5. Exact Map contract and ordinary client

Use independent key, value and state universes. Operation-only fields are empty,
update, delete and `lookup : M → α → Option β`. Lookup is also the decoder;
do not add a separate abstraction field or seventh independent lookup law.
Keep the model the unrestricted function type `α → Option β`.

The six laws are empty lookup equal to constant none; empty validity; and,
under valid input, update/delete semantics plus their separate validity laws.
Each mutation semantic field groups the changed-key equation with all
unaffected-key equations. No global `DecidableEq α` belongs to Ops or Laws.
For update the changed result is `some b`, for delete it is none. Both must
leave every other lookup unchanged.

Under a supplied key decision, prove correspondence to the exact source
`Function.update` equations using `Function.eq_update_iff`, and use that
correspondence with validity preservation in the shared valid-graph bridge.
A local classical decision may be used in proofs that need a case split, but
must not be hidden in an allegedly executable general implementation. Formally
account for lookup's reflexive schema with trivial output validity.

Define one ordinary client that updates a with x, updates b with y, then deletes
a. Derive its validity and whole observation from the laws, applying them to
the actual preceding results. Its query at a is none; at b it is some y when
b ≠ a, and none when the keys coincide; every other query is unchanged.
Prove observation agreement across lawful implementations whose initial
lookup functions agree. Do not claim parametricity for arbitrary Lean functions.

Empty value and key types remain legal. No value order, value equality,
default value or surjectivity onto the abstract model may be added. `none`
and `some false` are different observations, and deleting an absent key may
change a concrete representation while leaving all lookups unchanged.

## 6. Modified interface and both translations

The operation-only modified interface retains empty and lookup and has
`modify : α → (Option β → Option β) → M → M`. Its four law fields are the two
empty laws, mutation semantics at the selected key and every other key, and
mutation validity. In the function-update form, the new value is exactly
`f (lookup m a)`. No `f none = none` restriction is allowed.

From this interface define update by the constant-some callback and delete
by constant-none. Prove all six original Map laws solely from the modified
laws. Conversely, from original Map operations, case-split on the single
displayed expression `f (lookup m a)`: none selects deletion, some b selects
update. Prove both modified mutation laws in both branches, retaining empty
and lookup. These translations must not inspect the representation.

Retain the correct asymmetric round trips:

- Original Map → case-based modify → constant-callback Map recovers the
  original operations even on raw invalid states, by the explicit definitions.
- Arbitrary lawful modify → derived Map → reconstructed modify preserves
  validity and the whole lookup observation on valid input. Concrete returned
  states need not be equal.

The connected negative case uses keys `Fin 2`, values Bool, state
`(Fin 2 → Option Bool) × Nat` and validity True. Modify performs the specified
point update and adds one to the hidden counter if `f none = none`, otherwise
two. At the map containing key 0 ↦ false and key 1 ↦ true with counter zero,
identity modification at key 0 returns counter one. Its reconstructed version
uses constant `some false` and returns counter two. Prove equal full lookups
through the public round-trip theorem and unequal states via the counter.
This witness is separate from the even-counter realization below: requiring
evenness here would invalidate its odd increment and the alleged law witness.

No execution cost, callback-sharing semantics or one-traversal theorem follows
from these pure interface translations.

## 7. Existing AList realization

Adapt `AList (fun _ : α => β)` using actual empty, insert, erase and lookup.
Use the existing key uniqueness embodied in that carrier and standard lookup
lemmas. The realization may require `[DecidableEq α]`; it must not acquire
value equality or an `Inhabited β` merely to prove the six laws. Validity True
is appropriate because malformed duplicate-key states are excluded by AList.

Instantiate the ordinary Map client and one modified client at this adapter.
Connect both to the public generic law theorems, with a nonempty actual finite
example containing false and true values. AList insertion prepends and erases
the old binding; this is a distinct realization, not the source ordered-list
`upd_list`, unrestricted raw `map_of`, or a BST implementation. Preserve those
later obligations and do not infer arbitrary-model surjectivity from these laws.

## 8. Required connected examples and boundaries

The complete case preflight supplies the independent calculations and required
public connections for the following minimum family. Optional observations
in that report do not create a separate framework or additional chapter scope.
Precise helper names may follow local style and must be shared before use.

1. Function-valued two-key models and paired representations with a natural
   hidden counter, incremented by two per mutation. The paired invariant is
   even counter, with an actual invalid odd state. The Set client starting
   empty gives memberships `(false,true)` and counter six; the Map client gives
   `(none,some true)` and counter six. Use the generic client theorems, and
   separately calculate the private counter. Same-key, unaffected-key and
   absent-deletion cases consume the corresponding public laws.
2. An actual two-stage tag/counter representation. The first decoder forgets
   a Bool tag with validity tag=true; the second forgets the counter with
   validity even. Compose the actual matching mutation squares and retain
   `tag=true ∧ even counter`. A true-tag/odd-counter state demonstrates the
   second predicate is independent; a false-tag/even-counter state shows the
   other direction. Neither alone is called a semantic failure of the +2 model.
   Initialize and run the same nonempty ordinary client through the composed
   route, actually composing the three mutation squares and endpoint observation.
   One full Map specialization suffices; Set's own generic bridge and paired
   client connections remain required independently.
3. Separate small counterexamples to dropping intermediate validity and to
   dropping actual middle-operation agreement. Establish each honest route's
   preservation, then refute the proposed overstrong composite statement. For
   the first, use identity decoders on Bool, I=True, J(a)=(a=true), constant-true
   first/middle operations and identity final specification; the actual middle
   arrows agree, but retaining only I would assert true=false at false. For
   the second, use equality relations, first implementation/specification not,
   and second implementation/specification identity. Both honest squares
   preserve equality, but the middle arrows disagree and the proposed pasted
   equation fails at false.
4. Generic role/product cases: ordinary parameters use identity/equality even
   if their Lean type equals the state type; two represented inputs retain
   both validity premises; nullary initialization is unconditional; ordinary
   observations have trivial output validity with explicit Bool reflection.
   For the products, use even Nat state n decoded as n/2. With ordinary k=3
   and represented n=4, n+2*k is 10 and decodes to 5=2+3; k is not required
   even or decoded to 3/2. Addition of represented 4 and 6 gives 10 and
   observation 5=2+3. Retaining only the first validity permits (4,1), whose
   output 5 is invalid; the symmetric case exposes the other premise. Use
   the actual existing product relation and the valid-graph bridge.
5. Both modify translations on insertion from none, overwrite, deletion,
   identity and an unaffected second key; the counter-one/counter-two witness
   consumes the actual public observation round trip. For the even-counter
   sequence, start at lookups (none,some true), counter zero; callbacks at 0
   are constant some false, identity, Option.map Bool.not, constant none.
   Results at 0 are some false, some false, some true, none; key 1 remains
   some true and counters are 2,4,6,8. Use the derived law and actual successive
   validity. For the raw first round trip, an invalid counter-one state updates
   to counter three in both original and twice-translated operations; invoke
   the unconditional definitional round trip, not an invalid-state law.
6. Empty key/value boundaries and `none ≠ some false`. These do not replace
   the nonempty examples. Lack of decoder injectivity/surjectivity must not be
   introduced as a hidden premise. With Empty values and Fin 2 keys, actual
   deletion can change the paired counter from zero to two while all lookups
   stay none. Empty keys still permit the unconditional initialization laws;
   an Empty state cannot supply the Ops.empty field. A stored false and absence
   remain distinct even when the some-true Set observation forgets both.
7. The AList client at Fin 2 has entries [] then [(0,false)], then
   [(1,true),(0,false)], then [(1,true)], where pairs abbreviate Sigma entries.
   At Nat keys start with [(2,true)]; update 0 false, update 1 true and delete
   0 end with [(1,true),(2,true)]. Lookup 2 stays some true at every step via
   the unaffected-key law; the generic valid-initial-state client theorem must
   supply its final query. This prevents the all-three-steps unaffected-key
   clause from being tested only vacuously on Fin 2. Include the single finite
   AList versus constant-some-false-on-Nat non-surjectivity boundary, using the
   finite actual key list; do not build a new infinite-map representation.

## 9. Coverage and acceptance boundaries

This supports the general schema and exact contracts in C06-001–019 and
C06-034–043, shared composition principles for C05 and C06-066–067, and the
mutual interface derivations in C06-068–074. Coverage is per actual statement;
do not mark every cited row closed merely because its abstraction is present.
In particular, later BST/interval instantiations of the generic client remain
required, as do the complete ordered-list/tree operations and their refinements.
The Set-as-partial-Boolean-map discussion is not fully formalized by the single
`none ≠ some false` boundary case; retain C06-035's embedding obligation.

All interval-list Exercise 6.1 operations, early termination, argument direction
and linear work, all Set2 binary operations/instances, ordered map refinements
with extra invariant J, concrete trees, heaps, balancing/cache proofs, costs,
and the direct Chapter 5 Exercise 5.3 proof remain mandatory and queued. No
chapter is activated or completed by a shared draft.

Before acceptance, capture the complete immutable candidate from the fixed
base; compile all changed targets and run the applicable full guarded candidate
check, both integrity passes, full integrated build and exhaustive axiom audit.
Use the retained independent Standards and Spec workflow against the full
frozen scope, fix concrete findings without rewriting the original requirements,
then immediately verify the matching candidate record before acceptance.
No admissions, new axioms, unsafe/partial code, native decision shortcuts or
warning/audit weakening is allowed. Every new claim needs statement review
and meaningful retained public-interface uses; source-only assessments are
not compiler evidence or passing reviews.

Until Chapter 1's current session 83124 terminates, no second compiler/checker,
project integrity/hash helper or speculative cache operation may run. Root
owns Git, control records, integration and checkpoint creation. Authors own
only assigned disjoint source paths and stop before immutable capture. Commit
all non-main worktree source changes before checkpointing, then expose and
upload each completed self-contained checkpoint immediately. No GitHub write.
