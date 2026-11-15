# Independent review of the shared table-observation draft

Date: 2026-11-02. Reviewer: `/root/environment`.

Scope: independent formal-statement, source-contract, architecture and checked-client
review of the bounded staging draft. This is not a mandatory chapter review,
integrated proof audit, or acceptance of Maps, SearchTree, ADT, Extract, Redblack or
Trie. No compiler, build, cache, dependency, main-source, ticket or status action
was performed during this review.

## Reviewed identity and evidence

| File, relative to `work-state/staging/table-specs/` | SHA-256 reviewed |
| --- | --- |
| `TableObservations.lean` | `0233781d210056e9a61ae9a355120429e55007e72713434d25a5338aa6489b57` |
| `README.md` | `1f7064f58aadc2a64f73d0ce65863bd1eb8de63fa601758c93f819884d944d05` |
| `validation.txt` | `e146b203118acd8a960fda299a10b96f6b5adfe1df818103976273549533591a` |

The source hash matches the requested review candidate and the hash in the
owner's focused-validation record. That record reports a final exit code of 0
with no diagnostics from the pinned Lean 4.35.0 command, with
`LEAN_NUM_THREADS=1`:

```text
nix develop --command lake env lean /workspace/scratch/0c54f2db1fdf/work-state/staging/table-specs/TableObservations.lean
```

The recorded working directory and Nix environment are in `validation.txt`.
This review reuses that recorded result; it does not independently rerun the
compiler or treat the textual record as a full transitive axiom audit. The
record correctly distinguishes the earlier failed elaboration attempt and
checkpoint003's older uncompiled draft from the final checked source. The
reviewed source contains no `sorry`, `admit`, new axiom or `native_decide`.

## Outcome and actionable finding

Formal statements: pass for the declared staging scope. Connected client:
pass. Source-contract and architectural boundaries: accurate, subject to the
integration obligations below. There is one low-severity documentation finding;
no Lean correction or further compilation is requested.

**TS-1 — describe the initial ListFusion-cache limitation historically.**
`README.md` lines 40–45 currently say that the main checkout has no cached
`SquareKit.ListFusion` module. A later, separately authorized resource-target
build supplied that module. Read-only inspection during this review found
`conaled/.lake/build/lib/lean/SquareKit/ListFusion.olean` present. The original
reason for choosing the bounded two-write client remains valid historical
evidence, but the present-tense environment claim is stale. Suggested replacement:

> At the time of the initial draft, the main checkout had no cached
> `SquareKit.ListFusion` module. This preparation was restricted to focused
> checking without building project dependencies, so it used cached Mathlib
> function/list basics and a bounded two-write client. A later authorized
> resource build supplied the ListFusion module. Any later arbitrary
> update-history client should reuse ListFusion; this preparation does not
> duplicate its fold induction.

The past-tense statement in `validation.txt` records the initial preparation and
need not be rewritten as though that later build had occurred first. TS-1 is
open at the README hash above. Root owns the documentation correction and any
subsequent hash record; this reviewer did not edit the draft or its README.

## Formal-statement assessment

| Declarations | Independent assessment |
| --- | --- |
| `Ops`, `Laws` (lines 17–29) | Operations carry no proof fields. Validity is explicit, empty validity witnesses that the permitted state class is inhabited, and preservation supplies intermediate-state validity. The three observation laws have the needed quantifiers and the correct distinct-key direction. |
| `ObservedEq`, `observe`, `Laws.observe_set` (32–46) | The contract is equality of total query results. The update theorem proves equality of functions using pointwise laws; it does not assert injectivity of the decoder, equality of raw states, a representation isomorphism or binding-sensitive equivalence. The key inequality reversal in the proof is correct. |
| `Laws.empty_observed`, `Laws.set_observed` (48–64) | Both realizations share key/value types and default, and retain independent validity predicates. The old observational relation is used at unrelated keys. Local classical reasoning splits key equality in a proposition; it does not provide an executable equality implementation for `Ops`. |
| `twoWrites_equivalent` (70–77) | The shared client writes first `(k₁,v₁)`, then `(k₂,v₂)`, and queries. It derives validity of each intermediate representation using `set_valid` and consumes `empty_observed` and `set_observed` twice. The desired equality is not included as an assumption. |
| `twoWrites_latest`, `twoWrites_first`, `twoWrites_other` (79–94) | Latest-write priority includes coincident write keys. Retention of the first value requires the second key to differ. Default lookup requires the query to differ from both write keys. These are the appropriate separate cases. |
| `functionLaws`, `associationLaws` (101–125) | Both use `Valid := True`, proving the observation laws for every function or raw list, including lists with repeated keys. Association updates prepend and lookup selects the first matching key, so stale tail bindings are permitted. No finite support, ordering or equality on values is assumed. |
| `withDefault_update`, `lookup_cons_update` (132–141) | Partial updates insert `Some v`; absence is forgotten only at the default-observation boundary. Both connections use the existing `Function.update` operation. |
| `binding_iff` (144–146) | The explicit bound bit and defaulted value together characterize one optional binding, including a binding to the default itself. The theorem does not claim that the defaulted value alone determines membership or enumeration. |
| `forget_default_not_injective` (149–159) | An actual key and value are supplied. The construction separates the all-absent partial function from one storing the default at that key and proves equality only after forgetting absence. It makes no false claim for an empty key domain. |

Extensional update shadowing, idempotence and commutation should later be reused
at the decoded function level from Mathlib, or transported to `ObservedEq`.
They must not be promoted to raw association-list equality: prepending a
binding retains the older list entries. The current file makes no such
promotion. It also makes no runtime, sharing, allocation or enumeration claim.

## Checked clients and meaningful cases

The generic two-write client is connected to both actual realizations by the
proved laws. The examples do not merely posit a client-preservation premise:

- Lines 164–172 recover the four observations of `Maps.examplemap`, using the
  distinct-write, miss and latest-write theorems.
- Lines 175–184 apply the same public latest-write theorem to the association
  list and function realizations, and the miss theorem to an absent query.
- Lines 187–190 instantiate the generic equivalence with Boolean keys and
  arbitrary payloads, query and default. This exercises both concrete law
  witnesses without requiring numeric ordering or value equality.
- Lines 193–200 prove that explicit `false` and absence have equal total
  observations but different bound bits. The equality uses
  `lookup_cons_update`, `withDefault_update` and Mathlib's update law.
- Lines 203–205 give a direct, checked counterexample to treating a shadowed
  raw list member as the current binding. Direct decision is appropriate for
  this counterexample; it is not presented as a shared-client proof.

These cases establish the bounded preparation's intended connection. They do
not establish an arbitrary-history interpreter, source chapter completion,
human usability, extraction correctness or a complexity result.

## Source scope and integration requirements

Source pointers below refer to the pinned official VFA 2.1 `.v` files in
`reference/vfa/vfa/`. The relevant ranges were read independently; a read-only
source cross-check by `/root/environment/lean_info_read` confirmed the same
boundaries.

| Source | Preserved distinction and remaining integration obligation |
| --- | --- |
| `Maps.v` 28–54, 83–146; 161–166 | Total maps supply a default; partial maps retain `None` versus `Some v`. The draft preserves this distinction and uses Mathlib update primitives. The draft does not claim to discharge all six source update laws or all chapter exercises. |
| `ADT.v` `Table`, 50–87 | Source lookup laws are unconditional over its carrier. The draft's two `True` instances recover this requirement. Any future adapter to the source `Table` interface must prove laws with `Valid := True`, or expose a carrier already restricted to valid representations. It cannot silently replace the source laws with weaker raw-state invariant premises. |
| `ADT.v` `ETable`, 375–414 | `Table` lookup laws and the stated bound laws remain unconditional; enumeration soundness and completeness use `rep_ok`. A shadowing raw list cannot serve unchanged as the source `elements` list, as the checked counterexample demonstrates. A future adapter needs the appropriate invariant/canonicalization or removal operation and all separate enumeration obligations. |
| `ADT.v` `ETableAbs`, 806–847; `SearchTree.v`, 986–1020 | Abstraction to partial maps retains binding. `map_of_list` gives first-binding precedence. `ETableAbs`'s equality through `map_of_list (elements t)` differs from ETable's raw-membership specification: shadowed entries can disappear under that abstraction. The draft's warning is correctly scoped to ETable, not a blanket impossibility for ETableAbs. |
| `Extract.v`, 110–156, 293–301 | A generic key type does not supply the chapter's integer abstraction, injectivity, reflected comparisons, representable range, or overflow qualifications. The source explicitly lacks a reverse surjectivity assumption. An eventual extraction/word adapter must discharge its concrete representation and comparison obligations; the current table laws imply none of them. |

The README accurately calls this bounded cross-cutting preparation, records the
source `Table` distinction, and leaves later algorithms and source-to-Lean maps
unimplemented. It also correctly leaves positive/natural conversion for Trie
as a later proved transport obligation. Source sequencing and the whole-book
scope are unchanged.

## Architecture and the arbitrary-history extension

The operation-only `Ops`, separate `Laws`, explicit observations and ordinary
client fit the pattern inspected in
`Applications/Sequences/AbstractFIFO.lean` (`Ops`, `Simulation`, client
preservation). The finite Vector-specific store in
`Applications/Dijkstra/Store.lean` is useful existing evidence, but does not
already provide a generic finite-binding map interface. This small draft does
not introduce a general container hierarchy or require unrelated categorical
structure from its clients. Its current proofs do not yet claim an actual
`RelSquare` adapter; that distinction is appropriate for staging.

The scoped observations and retained invariant premises agree with
`docs/adr/0002-relations-and-synchronization.md` and
`docs/language-direction.md`: a noninjective exact decoder is allowed, while
adding binding/enumeration observations requires additional preservation laws.
The use of Mathlib's `Function.update` and its existing algebra avoids a
parallel update theory.

For an eventual chronological list of updates, the existing
`SquareKit.ListFusion.foldl_reachable` is directly applicable. The intended
instantiation, not code checked by this review, is:

| Fold parameter | Table instantiation |
| --- | --- |
| Input `α` | `K × V` |
| Concrete accumulator `β` | `T` |
| Abstract accumulator `γ` | `K → V` |
| Concrete step `f t kv` | `ops.set kv.1 kv.2 t` |
| Abstract step `g m kv` | `Function.update m kv.1 kv.2` |
| Decoder `h` | `observe ops` |
| Reachability predicate and seed | `Valid` and `ops.empty` |
| Base, closure, commuting equation | `empty_valid`, `set_valid`, `Laws.observe_set` |

That theorem transports an ordinary `List.foldl` client to canonical function
updates. `get_empty` identifies the decoded seed with the constant default;
two realizations then agree through that common decoded history. Preserve
left-to-right chronological order: replacing this with `foldr` changes update
priority unless the history convention also changes. Use the existing
`scanl_reachable` if every intermediate state is part of the client contract.
No fresh word executor or duplicate fold induction is needed.

A binding-sensitive history client needs a decoder retaining `Option` or
equivalent bound/value observations, plus the corresponding preservation
equations. The current total `ObservedEq` is deliberately insufficient for
that stronger contract. These are concrete follow-up requirements, not
already checked additions or chapter acceptance conditions discharged here.

## TS-1 resolution and final review freeze

Date: 2026-11-02. Root applied the proposed historical paragraph. This reviewer
read the revised paragraph and verified that reversing precisely that
replacement reconstructs the originally reviewed README SHA-256. No other
README content changed.

| Artifact | Final verified SHA-256 |
| --- | --- |
| `TableObservations.lean` (unchanged) | `0233781d210056e9a61ae9a355120429e55007e72713434d25a5338aa6489b57` |
| `README.md` (TS-1 corrected) | `696abdd37c463da1e010be9a1841bca12feed591100155f11294337fc741f58c` |
| `validation.txt` (unchanged historical record) | `e146b203118acd8a960fda299a10b96f6b5adfe1df818103976273549533591a` |

TS-1 is resolved. There are no unresolved findings from this bounded staging
review. The earlier open-finding section is retained as review history and is
superseded by this resolution. The formal assessment and future integration
obligations are unchanged. This follow-up used only read-only file inspection
and hash comparison before appending the resolution; no compilation or cache
action was performed. The review record is now frozen for the next checkpoint.
