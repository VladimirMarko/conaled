# C03-RANDOM-TRACE-CONNECTION-001: concrete support client

## Immutable successor and hold

- Candidate: `0fa717b8c150e0ae6edb9d538dd2b86d73f02b2d`
- Tree: `a4c5ecdda90a57383e9fcce181b9faad3517e60b`
- Parent: `b87cd1a6c9318ad06f9dae15d6393910e6fa7211`
- Branch: `work/fdsa-ch03-random-selection`
- Status: clean. Author source and provenance writes are held after this record.
- Commit: `test(selection): connect actual trace support witness (#174)`; actual exit 0, tool `8870d9`.

This is a response to root's implementation checked-connection finding. It is not a response to a compiler failure or an independent Standards/Spec finding. No trace-pair compilation has yet occurred. Root remains the sole serial compiler owner; no author compiler, environment, dependency, cache or output action occurred.

## Exact bounded change

One public example, `Examples.RandomSelectionTrace.middle_path_supported`, was added to `Examples/RandomSelectionTrace.lean`: one path, nine inserted lines. It states that the actual trace `[(3,1),(2,0),(1,0)]` belongs to the support of `traceLaw 1 ([3,1,2] : List Int)`.

The proof directly applies `traceLaw_support.mpr`. Its witness is the actual complete outcome with value 2, that trace, and source cost 33. Support follows from the existing `middle_path_atom = 1/6` and finite-cast inverse nonzeroness. This is a concrete use of the new support interface on an unsorted interior-rank request, with no mathematical assumptions in the example.

The expected support conclusion was saved before the source addition in `expected-support.json`, using the pinned independent model's already saved positive 1/6 row. No finite matrix was rerun. Pre-code record/read: `743cc5`; SHA256 `6b26dcc4030cdb6cc21e667e52cea0a5b2aeb45a62d52edb9ab8eddfcb8ee9b9`.

Removing exactly the new documented theorem block restores the parent example file byte-for-byte. Every existing declaration, proof, definition, import, option and instance context is unchanged. All other 15 source files, including all 14 pre-trace sources and the trace core, remain byte-identical. All earlier records and expectations are retained.

## Source, statements and cases

The cumulative authored inventory now has 289 public names, 18 private helpers, 25 definitions and 307 declaration headers. All previous 306 headers/contexts, 25 definitions and 18 private helpers are preserved. The private inverse-product helper is unchanged.

The complete changed example module and exact patch were read in `24baf5`. `precommit-assessment.json` retains the full scope inventory and reviews the new statement, its closed input/rank, lack of assumptions, exact actual pushforward semantics, positive support witness and direct checked-interface use. The current `traceLaw_support` connection assessment now names this concrete client; its statement and proof remain unchanged. Assessment readout: `145200`.

The final input `/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control/provenance/chapter03-random-selection-implementation-20261104/trace-connection1-20261104/Statements289-trace-connection1.lean` retains all 288 previous explicit @ checks in order and adds the new example. It is 16,690 bytes with SHA256 `e13e022e1727aeb2ec1cc896906a639530fa1c67a5cb5afed990b192dca23db2`. It is bound to this exact candidate and all 16 source blobs. Prepared input and source inventory do not establish actual elaborated types.

Current example file: 8,686 bytes, SHA256 `5abb356eeecb3d6a046cd529db4701f88056a4ef95bb4cbff294a86747b11f9d`, blob `92858210b6689d6b172071c8d0fbfca2d91e6391`.

Exact delta: `source.diff`, 1,062 bytes, SHA256 `a43af0824abf5aa7637769a5353304f0d2077b296ecd7840af9a5ccd1edbef53`.

## Root validation and remaining scope

Requested first focused pair remains:

- `Applications.Resources.RandomSelectionTrace`
- `Examples.RandomSelectionTrace`

The new client is authored and uncompiled, and awaits root's actual check. No focused pass, actual type output, full check, audit, independent review outcome or Chapter 3 acceptance is asserted. The original Karp source remains inaccessible, with no new source recovery or quotation.

The complete universal endpoint path remains pending and held: every arbitrary distinct input and every valid worker rank; target retention to singleton under minima while rank positive and maxima at zero; exact projected trace probability 1/n!; triangular scan attainment; an unbounded Nat family; and actual source-cost lower/upper transport.
