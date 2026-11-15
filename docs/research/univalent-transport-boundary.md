# Native paths through the bounded transport facade

Issue [#577](https://github.com/VladimirMarko/conaled/issues/577) adds an explicit
native boundary to the [bounded transport facade](../../Examples/CubicalAuthorTransport.lean).
Callers supply the original native map and its `HomotopyEquivalence` to
`Change.nativePath`, together with complete package-preservation evidence.
The result has the native path type directly. `Change.native_path_recovery`
exposes recovery with that same type. Both preserve the exact supplied witness
and both complete dependent-package endpoints.

```lean
-- E remains the originally supplied native contraction.
def mainPath : NativePath E sourceLength targetLength :=
  Change.nativePath nativeMap E (length_preserved E)
```

The existing `Change` API remains available for carrier observations, native
sections, decoded transport, composition and reversal. `Change.path` remains
appropriate when the required type is `Change.PackagePath`. An implicit
conversion from its result to a separately spelled concrete native family can
still exhaust Lean's default heartbeats. The repair gives that conversion an
explicit boundary; it does not make every definitionally equal presentation
cheap to elaborate.

## Construction and recovery

`nativePath` constructs the existing `Change.path` for `Change.mk f E` and
passes it through a private bridge. The bridge unfolds only `PackagePath`,
`line` and `carrier` while its parameters are still abstract. It does not
rebuild the witness from a host equivalence or discard any package fields.
`nativePath_eq` proves equality with the existing native
`uaStructureIdentity f E p q` inverse, including the full native path term.
Recovery uses that fixed-equivalence inverse law, the same law underlying
`Change.path_recovery`.

The direct native constructor remains a valid alternative. Its result already
has the required type, and it completed the original trial. The new entrypoint
lets the facade own the conversion while retaining its path construction. It
requires the map and witness at the call site, rather than obtaining them by
normalizing projections of a bundled `Change` inside a concrete native family.
There is no new family-admission interface or generic frontend framework.

## Reproduction and checked consumers

The original failed attempt was replayed against accepted #534 revision
`352efcfe1fdb8fc103c0536060b0211361499220`. Only its task import was redirected to
the integrated copy. Both native path constructions and their recovery
statements reproduced the default 200000-heartbeat failures. The attempt's
separate concrete `decide` errors also remained. The
[original cohort](../../experiments/univalent-package-authoring/cohort-01/results/README.md),
including its sources and logs, is unchanged.

Making the facade aliases reducible did not resolve the path boundary. Neither
did spelling the admitted families directly in `PackagePath`, making the path
constructor reducible, or changing only the caller's `Change` to an abbreviation.
A diagnostic run showed conversion expanding cubical and category implementation
data. A helper returning the native family with bundled projections still
failed on the journal case. The selected helper takes native parameters before
that comparison and normalizes the facade aliases once.

[The regression module](../../Examples/CubicalAuthorTransportNative.lean)
retains the original arbitrary `E`, paired-journal construction and changed
invariant. Its two paths use `nativePath`; its two native recovery statements
use `native_path_recovery`. The known concrete predicate correction uses the
accepted author's `simp` proof. The remainder of the task and its complete
native oracle are mechanically adapted into new namespaces. They check:

- Both complete decoded records and their universal initial, transition and
  invariant observations.
- The actual native sections, endpoint decoding, complete section recovery,
  path endpoints and recovery of the supplied native paths.
- The invariant-erasure rejection and the separating journal observations.

The existing public calibration remains in the build. An additional consumer
constructs a native path using the generic composition of two native
contractions for integer successor. It recovers preservation from that path,
uses the recovered evidence to identify the complete decoded package, and
checks initial state 2, transition from 4 to 6, admission of 2 and rejection of
3. This exercises a composite witness and subsequent observation, rather than
another host-isomorphism witness for the journal task.

## Scope and evidence

Statement review compares the native map, original contraction, endpoint
packages and complete native terms in the new declarations. The bridge is a
definitional conversion; `nativePath_eq` records its connection to the native
constructor. Existing admission remains the discrete proof-bearing package
fragment. No higher-family admission, equality of independently selected
universe paths, executable evaluation or source conversion is claimed.

The mathematical contract and preservation proofs are reused. The observed
elaboration improvement is completion of these native-typed consumers at
default limits through the new entrypoint. It is not a timing comparison or a
claim that the facade now improves author productivity. The journal task is
public regression evidence, not a fresh author trial. Any further author trial
must use an independently prepared and frozen new task and oracle, with equal
baseline access and the retained repairs.
