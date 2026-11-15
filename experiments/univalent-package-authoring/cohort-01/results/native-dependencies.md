# Native witness and statement review

The task and oracle quantify over the original
`E : HomotopyEquivalence nativeMap`. `NativePath E` uses the admitted line for
that exact map and E. Both final submissions retain E in every path, filled
section and decoded package. Their carrier helper proves equality of the
observed carrier equivalence by its forward map; it does not prove equality
of contraction witnesses or replace E with `HomotopyEquivalence.ofIso`.
The oracle's separate concrete admitted witness establishes inhabitation of
the task contract, while all universal declarations still quantify over E.

The direct paths use `uaStructureIdentity ... .symm` on full preservation
records. Its sections use `transported`, their recovery uses
`transported_recovery`, and decoded targets use `targetPackage_eq`. The facade
submission packages the original map and E as `Change`, uses `nativeSection`,
`native_recovery`, `transport`, and `transport_of_preserves`, and uses the
baseline `uaStructureIdentity ... .symm` for both final paths and its inverse
law for recovery. The facade's first three attempts preserve the unsuccessful
path-conversion approaches. Neither final path is supplied by an unrelated
host equality without the native structure-identity bridge.

Both authors prove complete package preservation using `statePackage_ext`,
including initial state, transition and predicate. Existing proof-field
extensionality covers initial validity and preservation certificates. The main
predicate is equal lengths; the changed field is equal sums. The independent
oracle checks every state's initial/transition/invariant observations, the
selected pairs separating those predicates, native path endpoints, decoding
of the submitted sections themselves, complete section recovery at all
generalized points, path recovery, and rejection of invariant erasure. These
claims do not assert arbitrary higher univalence, source conversion, an
executable compiler or a runtime cost theorem.

The explicit rejected input keeps operational fields but replaces the invariant
with True. The authors derive a contradiction at a concrete pair of unequal
length journals. Empty journals provide valid initial data, so positive
preservation is not vacuous. The distinguishing pairs outside the initial orbit
are necessary observations of the complete invariant field.

## Integrated copies

`Task.lean` is byte-identical to the frozen public `TrialTask.lean`.
`Direct.lean` and `Facade.lean` replace only `import TrialTask` by the integrated
module path and `JournalTrial.Author` by `JournalTrial.DirectAuthor` or
`JournalTrial.FacadeAuthor`. Oracle copies replace the first import, their
`JournalTrial.Oracle` namespace, and corresponding `Author.` references.
No proof statement, proof body, option, mathematical definition or hypothesis
is repaired during this integration. `reproduce.py` checks these exact
transformations against archived originals. This is an artifact-identity check,
not a substitute for elaboration or mathematical statement review.

The original oracle logs include transitive axiom queries for the native paths,
section recovery, decoded target equalities and rejection. All recorded queries
use only the three permitted foundational axioms. The integrated oracle modules
are imported by `SquareApplications`, so final repository acceptance audits
all their declarations, rather than relying on that selected query list.
