# First existing-language frontend: bounded Haskell and Agda comparison

Research for [#491](https://github.com/VladimirMarko/conaled/issues/491), at conaled
`d1a1a0484f2f753455adf81d888503e13367ed73`, 2026-11-12. This comparison recommends
an implementation experiment; it neither delivers an importer nor selects a
primary language or proof-evidence architecture. Lean and Agda remain desired
frontends. Haskell compatibility is useful without making Haskell the shared
compiler's semantic model.

The [reproduction kit](../../experiments/existing-language-frontends/README.md)
contains the actual client sources and retained evidence. Probe results are
reported separately from the proposed importer acceptance rules below. The
original [GHC assessment](ghc-frontend-assessment.md),
[Agda/core assessment](agda-core-and-slean-frontends.md), and
[completed internal inspection](agda-internal-retention.md) remain applicable.
This study addresses their unresolved *computational first client* comparison;
it does not repeat the Monodromy/Cubical proof-transport investigation.

## Matched library clients

The selected existing declarations are Haskell `Data.Either.either`, supplied
by `base` and implemented in `GHC.Internal.Data.Either`, and Agda standard-library
`Data.Sum.Base.[_,_]′`. The latter specializes its dependent sum eliminator to
a constant result type. Both select one of two supplied functions according to
a sum tag. The source pins are
[GHC 9.10.3 Either](https://raw.githubusercontent.com/ghc/ghc/ghc-9.10.3-release/libraries/ghc-internal/src/GHC/Internal/Data/Either.hs)
and [stdlib 2.3 Sum.Base](https://raw.githubusercontent.com/agda/agda-stdlib/v2.3/src/Data/Sum/Base.agda).

The new wrappers import these definitions; they do not reimplement their cases.
`choose mask input` applies Boolean xor with a captured mask to a left payload
and Boolean negation to a right payload. `step state input` emits the previous
state and stores `choose state input`. Both use existing Boolean, sum, product
and list libraries. The list runner is a diagnostic harness around the proposed
single-step import, not an attempt to include general recursion in the first
frontend fragment. A library combinator specialized inside a stateful client is
a smaller integration claim than importing a whole package, but it tests real
cross-module declarations, closure capture, case analysis and dependency access.

The comparison deliberately avoids numeric representation, FFI and unbounded
source data. It therefore cannot rank numerical Haskell packages, dependent
Agda algorithms or large applications. Haskell's Bool inequality goes through
an instance implementation; Agda's xor is an ordinary library function.
Haskell `either` is nondependent, while Agda's implementation includes erased
levels/types and a dependent eliminator. Those differences are part of the
export work rather than reasons to replace either body with a toy definition.

## Executed evidence and limits

The [manifest](../../experiments/existing-language-frontends/evidence/manifest.json),
[results](../../experiments/existing-language-frontends/evidence/results.json), and
[readable excerpts](../../experiments/existing-language-frontends/evidence/artifacts.txt)
retain the final probe. It used GHC **9.10.3**, bundled `base-4.20.2.0` and
`ghc-internal-9.1003.0`, the official Agda **2.8.0.2** binary, and stdlib **2.3**.
The manifest pins compiler executables, installed packages/interface, source
archive and selected upstream files. The installed GHC binary is trusted;
matching its version to an upstream source tag is not a reproduced compiler
build. This executed pin differs from the earlier GHC report's 9.12.2 source
baseline.

Both clients produced the same independently specified 18 Booleans: all eight
mask/tag/payload combinations, followed by four prior-state outputs and the
final state for each of two initial states. Agda also checked the source equality
`observations ≡ expected` by `refl`. This is a proof of that closed vector in
Agda, not a universal source-to-conaled theorem. The Haskell unused-bottom
control returned `True`; forcing a bottom scrutinee exited 1. Agda rejected the
private safe-postulate control with exit 42. Unknown callback rejection is a
proposed importer obligation, not an executed rejection here.

GHC Core Lint passed at `-O0` and `-O1`. The former retains an `either` reference;
the installed interface independently exposes its case-analysis unfolding.
The optimized client exposes the sum cases and negation, but still references
`GHC.Classes.$fEqBool_$c/=`. Thus optimization supplies useful body access
without completing dependency/primitive admission. No dump parser was built.

The reused #115 decoder found the client's real stdlib references and the
library eliminator's type/clause information in freshly checked interfaces.
Its bounded traversal explicitly omits sorts, levels, literals and binder
metadata. The generated library Haskell contains the eliminator's two cases;
the client calls that generated declaration with its captured mask. Its checked
proof becomes `erased` at runtime. Executing this generated program with GHC
checks those observations through Agda's ordinary backend; it does not implement
a direct Agda import into conaled or obtain a Treeless dump. A compiler-linked
exporter and an independent source/residual correspondence remain unexecuted.

Checking and backend generation succeeded with stdlib `UnsupportedIndexedMatch`
warnings about computation on cubical transports in transitive modules. Counts,
log hashes and a representative warning are retained. This positive ordinary
computational client does not establish those stronger cubical properties or
warning-free compatibility for the whole library. Earlier attempts are recorded:
a version-output guard was corrected to allow the binary's build-flags lines,
and the private configuration directory was created to prevent Agda's home
configuration fallback. The final run repeated every check with that directory
present. No compiler or full library build was introduced, and no Lean proof
input changed.

## Existing target capabilities and missing connections

| Current construction inspected | What this experiment can reuse | What it does not supply |
| --- | --- | --- |
| [Compiler](../../Compiler.lean), `Ty`, `Term`, `eval`, `Sound`, `compile_sound` | Typed variables, products, sums, functions, nonrecursive lets and supplied primitives; compilation to an admitted target | GHC/Agda parsing, source semantics, external binding resolution or a correspondence theorem |
| [FirstOrder](../../FirstOrder.lean), `Term`, `Sound`, `compile_sound` | A target route without function objects | A sum case or closure eliminator merely by naming this API |
| [FiniteSum](../../Applications/FRP/FiniteSum.lean), `Term.source`, `decode_iff`; [lowering](../../Applications/FRP/FiniteSumLowering.lean), `lower_correct` | Boolean/product/sum terms, canonical tagged storage and an actual finite circuit | Importing arbitrary source constructors, lazy partial branches or dependent values |
| [FiniteSumReactive](../../Applications/FRP/FiniteSumReactive.lean), `Source.step_correct`, `run_correct`, `tick_reject` | Ordered finite outputs and final state, initialized execution and rejection of noncanonical encoded input | A proof relating an external `step` declaration to the native source term |
| [StaticFunctionSpecialization](../../SquareKit/StaticFunctionSpecialization.lean), `Expr.residual`, `residual_correct`; [StaticFunctionReactive](../../Applications/FRP/StaticFunctionReactive.lean), `selected_execution`, `stored_uniform` | Capture-avoiding finite static application and stored executable admission for its stated fragment | A universal specializer for Core or Agda; its first-order body types do not themselves contain sums |
| [Graph emission contract](../../SquareKit/Internal/GraphEmissionContract.lean), `ArtifactDenotes`; [primitive environment](../../SquareKit/Internal/GraphPrimitiveEnvironment.lean), `checkExactEnvironment` | A precedent for separating typing, meaning, exact environment and installation | A mandatory frontend certificate format or an existing checker for either language |

The smallest target for `choose`/`step` is the finite-sum term/circuit route.
Statically instantiate the imported eliminator's function arguments, then
reconstruct its Boolean cases and products. If a larger syntax bridge is needed,
`Compiler.Term` already expresses those functions and sums, but connecting it
to the restricted finite-sum syntax still needs a checked translation. Do not
claim that #483's product-only static specializer already handles this sum
client. The existing reactive run theorem can carry a proved step relation to
arbitrary finite traces; this is useful reuse beyond evaluating a truth table.

## Observation contract and admission

For a related, fully defined Boolean sum input and captured Boolean mask,
observe the exact result of `choose`. For stateful use, observe the ordered
output sequence and final Boolean state, from the same specified initial state.
Source and target are allowed different evaluation strategies. Neither elapsed
time, allocation, exception text, Haskell function definedness nor equality of
proof witnesses is included in this first positive contract.

The Haskell admissible closure initially consists of selected specialized
nonrecursive Core bindings, Bool constructors/cases, sums/products, lexical
binders, and an explicit Boolean primitive/library environment. Type lambdas
and applications are processed during specialization, not silently erased from
arbitrary Core. The closure must account for the actual Bool instance selected
by `/=` and all imported unfoldings. Unknown globals, effects, dynamic or
escaping functions, unsupported casts/primops, and recursive residual bindings
are rejected unless separately admitted. `run` and enumeration remain the
external test harness; only the selected step closure is imported.

For Agda, select the completed ordinary safe declarations and their computational
specialization, with resolved constructor/builtin identities and a type sidecar.
The same target Bool/sum/product result must be reconstructed independently.
Reject residual runtime dependence not represented by these types, unresolved
metavariables, incomplete or scope-only checking, unknown primitives, executable
postulates, unapproved foreign code and unsupported cubical conversion. The
positive declaration can depend on polymorphic library definitions whose
*selected runtime specialization* is first-order; importing their full dependent
typing judgments is a separate milestone.

Total related inputs and total admitted operations suffice for these clients.
They are not the only possible admission argument. Haskell's `unusedBottom`
selects the total left branch even though the right function would fail if
called; a demand proof can justify that observation without claiming the whole
environment total. A reachable-state invariant can establish that only a subset
of inputs reaches an operation, or a supplied proof can establish a particular
primitive's preservation. Conversely a bottom sum scrutinee has no total Bool
result. The existing finite-sum circuit evaluates both branches, so source
non-demand by itself does not justify executing an unsafe target branch:
translate away that branch or prove the target's chosen evaluation safe.
The prior [GHC assessment](ghc-frontend-assessment.md#why-the-semantic-model-grows)
retains eta/seq and partially defined product counterexamples beyond this slice.

## Export boundaries and comparison

GHC's [versioned plugin/library API](https://downloads.haskell.org/ghc/9.10.3/docs/users_guide/extending_ghc.html)
provides Core access after GHC has parsed, resolved and typechecked the source.
A pinned plugin should export structured binders, types, coercions, literals,
constructor/global identities and selected dependencies at a named phase.
Readable dumps are inspection evidence, not an interchange parser. Changing
optimization phase can change whether an imported function is a reference or
its exposed body. Package installation is not proof that its unfolding is
available to every plugin invocation.

Agda's pinned [backend interface](https://github.com/agda/agda/blob/v2.8.0.2/src/full/Agda/Compiler/Backend/Base.hs)
provides per-definition callbacks and distinguishes whether scope checking
suffices. The [backend module](https://github.com/agda/agda/blob/v2.8.0.2/src/full/Agda/Compiler/Backend.hs)
exports `toTreeless`. The
[conversion implementation](https://github.com/agda/agda/blob/v2.8.0.2/src/full/Agda/Compiler/ToTreeless.hs)
starts from compiled clauses and accepts an evaluation strategy. It may return
no standalone body for an always-inlined definition; its comments require name
normalization before using concrete returned names as identities. This is a
specific exporter obligation, not evidence that a name hash suffices.

For this computational goal, recommend a small compiler-linked Agda backend
which pairs selected completed declaration/type/environment information with
a runtime residual. Treeless is a candidate runtime residual, not the sole
interchange representation: its
[syntax](https://github.com/agda/agda/blob/v2.8.0.2/src/full/Agda/Syntax/Treeless.hs)
contains erased terms, runtime sorts, coercions and errors, and does not carry
full dependent function types. Its let semantics also preserve non-demand.
Reject unsupported residual forms, or justify their removal. A restricted
compiled-clause route remains an alternative if typed residual reconstruction
would cost more; compare on this same corpus before generalizing the adapter.

This refines rather than reverses #115: internal syntax plus its environment is
needed when the goal is preserving dependent declarations, conversion and
proofs. It need not force computational code through a full dependent proof
transport. Generated Haskell/JS is useful inspection and differential execution
evidence, but would add an extra source-correspondence link if adopted as the
import path. Agda need not pass through a Haskell frontend.

| Obligation | Bounded GHC Core route | Bounded Agda route |
| --- | --- | --- |
| Export access | Plugin/library Core pass; freeze phase and flags | Backend callback over completed definitions; request selected residual and retain signature/environment |
| Typed reconstruction | Instantiate selected polymorphism/dictionaries; check lexical scope, constructor result types and allowed coercions | Validate runtime erasure/type association, constructor arities, implicit/level parameters and residual scope; reconstruct the same finite target types |
| Primitive contract | Pin Bool operations/instance and package identity; no numeric or algebraic-law inference from a class name | Pin Bool/sum builtins and library bodies, relevant options and backend pragmas; safe checking is not itself an export theorem |
| Source correspondence | GHC elaboration/optimization/export is trusted or separately justified; typed Core export alone is insufficient | Agda checking/compiled clauses/erasure/export is trusted or separately justified; checked source proofs do not prove an unverified exporter correct |
| Dependencies | Selected imported body availability may depend on interface unfoldings; explicit unavailable-body failure | Signature closure and generated declarations must be selected from checked modules, including implicit dependencies; module closure is only an upper bound |
| Diagnostics | Preserve source span/name plus Core binding and offending residual/global | Preserve qualified declaration and source hash, typed internal/residual location and unsupported primitive/erasure reason |
| Maintenance | Compiler-specific Core/type/coercion/package APIs and phase-sensitive output | Compiler-specific internal/backend/treeless APIs and serialization; do not promote #115's bounded binary decoder into a stable interface |
| New mathematics | A semantic connection for the selected source fragment and admitted environment | A computational erasure/specialization connection for the selected fragment and environment |
| Engineering rather than new mathematics | Version manifest, structured export, binding/type checks, dependency discovery and rejection diagnostics | Corresponding adapter work plus runtime/type association; obtaining a callback does not require modelling full cubical Agda |

Both routes need binding correctness and source association even if their output
has the same target type. A corrupted exporter replacing xor by conjunction can
produce well-typed code. Hashes identify which inputs were inspected; they do not
prove the relationship. Differential tests, Core Lint and a source `refl` proof
are useful checks with distinct conclusions, not substitutes for that theorem.

## Decision and bounded implementation proposal

Prefer a **direct Agda computational frontend experiment** if the selected
compiler-side export gate below succeeds. This advances a desired frontend on
a finite, useful contract without demanding full proof transport. Haskell has
better off-the-shelf Core inspection access, but neither a proof that it is
less work overall nor demonstrated savings on Agda's signature, erasure,
conversion or environment obligations follows. If the Agda export gate cannot
expose the selected library closure within this bounded adapter, retain that
failure and reassess the already specified Haskell alternative rather than
building a general Agda interchange framework.

The common work is a finite observation contract, explicit primitives,
independent binding/type reconstruction, rejection diagnostics and a source-to-
artifact association. Those patterns can benefit Lean as well as Agda. A GHC
plugin, dictionary specialization, unfolding access and partial-lazy semantics
do not eliminate the Agda backend, dependent erasure or source checking work.
A shared finite target fragment may be useful; one universal source AST is not
an acceptance condition. Haskell-first would be justified by a concrete need
for an existing Haskell client or measured reusable implementation, not by an
assumed mandatory stepping stone.

Proposed follow-up: **Import one pinned Agda library specialization into the
existing finite-sum reactive compiler**. Keep the original GHC client as a
comparison and regression reference, not an implementation prerequisite.

1. Freeze executable/compiler-library/stdlib revisions, selected declarations,
   source modes, export phase, primitive identities, initial state and observation
   relation. Obtain actual completed signatures plus selected residuals for
   `choose` and `step`, following `[_,_]′` into its real library body. Preserve
   implicit dependencies and distinguish inlined from standalone declarations.
   Stop this export gate with a readable failure if the body/type association
   cannot be obtained; do not silently substitute source equations.
2. Implement a deliberately finite adapter and independently checked binding,
   type and admission path. Reconstruct a native finite-sum term with supplied
   Boolean operations. Keep the chosen proof evidence transport local and
   replaceable; do not assume #489's deferred interface decision.
3. State the exact source boundary and trusted compiler/export premises. Prove
   selected residual-to-native denotation preservation, then compose with
   `lower_correct` and `Source.step_correct`/`run_correct` for ordered outputs
   and final state on arbitrary finite input sequences. Keep any missing
   source-to-residual link explicit in the theorem and report. Typed export,
   finite testing or a host proof alone cannot discharge it.
4. Accept all four sum values under both masks, captured-mask specialization,
   both initial states and stateful continuation. Import the actual library
   declarations, not handwritten target copies. Run the resulting stored
   artifact through the existing admission/execution seam and reject
   noncanonical sum storage without advancing state.
5. Reject unknown globals/primitives, altered constructor or Boolean semantics,
   malformed binders/types, stale source association, incomplete exports,
   runtime-dependent result types, escaping callbacks and unsupported recursive,
   cubical or foreign definitions. Include a deliberately well-typed semantic
   mutation to test correspondence checking; if source export is trusted,
   report that mutation as beyond the trusted boundary rather than falsely
   claiming the checker detects it.
6. Retain direct native clients, exact provenance, target proof audit and public
   runtime checks. Report adapter-specific code and obligations versus reusable
   pieces. No throughput, resource or proof-transport claim follows from value
   preservation; any such extension needs its own contract.

#36/#235 own interpretation/generalization questions; #481 owns frontend/backend
admission integration. #490's evidence comparison and #492's theory-network
study leave the exact architecture open, and #489 implementation remains
coordinated with that decision. This proposal does not reopen their completed
research or adopt a mandatory native-Lean certificate API. #116 surface design
and #117 authoring comparisons concern different questions. Current scheduling
and adoption decisions belong in the tracker; this record preserves the tested
baseline, recommendation criteria and bounded obligations.
