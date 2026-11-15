# Shared persistence: source-to-statement check

Date: 2026-11-02. Local ticket: #10013. Reviewer task: read-only comparison of the cross-cutting prerequisite with the primary-inspected PFDS list material (printed pp. 7–11, including Exercise 2.1). This record is a mathematical statement inspection, **not** independent Standards/Spec acceptance, a compilation result, or an axiom audit. The candidate was still being edited/compiled by its implementer. No compiles were run by this reviewer.

Source evidence is recorded in `book-source-inventory.md`. This check does not require or claim coverage of uninspected book pages, search trees, or the explicitly excluded full custom-stack correspondence.

## Inspected scope

`Applications/Sequences/SharedList/{Basic,Copy,Suffixes,Observation}.lean`, `Examples/SharedList.lean`, `docs/research/pfds-shared-persistence.md`, and `session/requirements/shared-persistence.md`.

At the final reread, repository HEAD was `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`; the files were working-tree candidate changes. SHA-256:

```text
Basic.lean        ef62f66166b1934ebd52e68783ea7865c678dea792f66632bd5c5eb7c4bf674b
Copy.lean         8604ffc06c4e03cae537e07af6efcccd7c78dda964126e72db0d6a9964c3124f
Suffixes.lean     69f2f2896c8ffa88eb39e7620c7cbf8d68884ed75b8367443ce954c2d8d80738
Observation.lean  f5e47ad7c23e3d79344aeb05ba742dfeaf0e39377967dbba2bcb558145695d62
Examples          9f1bcccff38ac2f04bee47273c6f01cdc60d1df40029f9149d6445375d16e09b
Research doc      f78228507880fc5a5c2eb2ba1d4c0ac6e028a76c897de93b66ba6822fa7ba324
Requirements      8b7b3a364ebeebc606ba627abf52b7533048dd2b9c76c0016a068ab649bf50b6
```

## Findings and fixes

### Shared-space justification: substantive gap corrected in the statements

Initially, `sharedSpace` counted non-null root entries plus outer-list entries. Correct suffix values and distinct roots did not establish that these root entries enumerated all reachable cells.

Counterexample: cells `0=(2,null)`, `1=(1,0)`, `2=(2,null)`, with root list `[1,2,null]`, represent `[[1,2],[2],[]]` through distinct roots. The entry count is five, but there are three reachable element cells plus three outer cells. This was not an algorithmic counterexample: the actual suffix traversal from root 1 returns `[1,0,null]`. It exposed the absent formal connection between the implemented traversal and the shared graph.

The revised statements supply that connection:

- `Reaches` and `ReachableFrom` define graph-address reachability independently of list values.
- `SuffixChain` records the actual tail fields followed until null.
- `suffixesRunFuel_chain` derives that chain from successful execution.
- `SuffixChain.closed` and `ClosedRoots.reachable_iff` identify all reachable addresses with listed non-null roots.
- `suffixesRun_reachable` applies that result to the actual public operation.
- `nonnull_nodup` turns the valid-input root distinctness result into a duplicate-free address enumeration.
- `suffixes_storage` connects the public operation, reachability enumeration, distinctness, and exact count in the retained example. The unshared-tail counterexample is also retained and fails closure.

These statements now justify reading the exact `2*n+1` count as reachable element cells plus outer root-list cells in the declared fixed-cell model. No remaining conceptual counterexample was identified in this scoped use.

`Reaches.here` intentionally counts a root address as reachable by zero edges without asserting occupancy. Thus `Reaches` alone is not a well-formed/live-cell predicate for arbitrary roots. In the reviewed suffix-space application, successful `SuffixChain` traversal and the represented-input contracts ensure that every non-null enumerated root is occupied. Future generic uses must retain that validity distinction.

### Invalid-input wording: corrected

Raw traversals do not validate every supplied root. An empty-left append can return an untraversed invalid right root, and index-zero replacement can retain an untraversed invalid tail. Their represented-input theorems remain correct. Requirements and prose now state rejection of encountered missing cells and non-null fuel exhaustion, without promising validation of untraversed roots.

### Zero-fuel wording: corrected

Null append/suffix cases succeed with zero fuel and one visit; null update fails with one visit. The zero-fuel failure with zero visits applies at a non-null root. The revised prose distinguishes these cases.

## Other inspected contracts

Append preserves every old occupied cell, copies exactly the left prefix, and reaches the original right root. Successful update preserves the original version and shares the exact untouched suffix; the index-equals-length failure is explicit rather than a `List.set` no-op. Empty-tail failure and successful singleton removal remain distinct. Equality of list observations does not imply equality of roots or persistent identities.

The counter measures structural visits, not elapsed time. Frontier changes count model allocations; the claims do not establish Lean runtime allocation, physical retention, reclamation, payload size, capacity behavior, or branch-safe amortization. These boundaries match the prerequisite's stated scope.

## Status

The previously identified conceptual/wording issues are addressed in the inspected statements. Formal compilation, exhaustive proof audit, immutable candidate review, and independent acceptance remain the implementer's workflow obligations. This record must not be used as a substitute for those gates or as chapter completion evidence.
