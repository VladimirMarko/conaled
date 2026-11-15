# Exact acceptance of the emitted graph family (#135)

The pure ConLeche checker accepts the canonical emitted graph family at verified
mode and fuel 32. `EmittedAcceptance.accepted` proves

```lean
checkDeclsPure .verified (fueledOps .verified 32) []
  EmittedEnvironment.declarations = .ok EmittedEnvironment.environment
```

This is equality of the full environment, including constants, generated
recursor records and rules, and projection tables. `AcceptedEmission.model_exists`
applies upstream `checkDeclsPure_sound_of` and `Model.ofEnvModelM` to this concrete
proof. It produces a model for every explicit `[SetTheory V]`; no SetTheory
instance or unconditional consistency theorem is asserted.

These modules remain an isolated experiment. They do not change the main Lake
dependency graph or select one universal compiler representation. The exported
`Cached.checkDecls` equation is **unproved** and separately owned by
[#417](https://github.com/VladimirMarko/conaled/issues/417). Pure acceptance and
model construction do not establish that equation.

## Artifact and proof scope

The accepted list is the preserved primitive stream, nine helpers translated
from the actual native environment, and both declarations produced by
`GraphEmissionPure.emitCore`. The native and relative theorem telescopes are
`A B C f g z x`; helper applications remain in the bodies. The existing
`EmittedGraph.forward_native_identity` and `backward_native_identity` prove the
encoded type/body roundtrip to the native producer. The older handwritten
`GraphDeclarations` family has a different telescope and Eq.rec construction;
it is not the accepted family in this theorem.

`PrimitiveAcceptance` checks Eq, And and Exists in order. And and Exists use
symbolic phase composition through the actual positivity and recursor operations.
The final installer equations include every predicted metadata field, including
the dependent Exists projection guard and field universe levels.
`NativeHelper0` through `NativeHelper8` check the helpers in dependency order:
`rfl`, `Eq.symm`, `Eq.trans`, `congrArg`, `And.left`, `And.right`, `Exists.casesOn`,
the native private Exists matcher, and `Exists.elim`. Their actual theorem or
definition kind and reducibility hints are preserved. The two emitted-declaration
modules check the actual encoded type and body against the preceding environment.

Named intermediate definitions are introduced by proof-producing normalization.
Each exports an equation from the original operation to the named result. A
separate success theorem establishes that extracting an Option value with a
default has not hidden failure. The composition lemmas take actual operation
successes as premises; the closed family theorem discharges all of them.
No Boolean execution replaces a theorem premise. No native-evaluation axiom,
new global axiom, or modified upstream checker is used.

## Semantic comparison and applications

`AcceptedEmission.source_comparison` specializes the existing general source
formula correspondence to the constructed model. Its interpretation laws,
encoding equations and assignment compatibility remain explicit.
`AcceptedEmission.emission_comparison` covers the admitted declaration/code
fragment, combining native artifact typing/denotation, exact type/body encoding,
and the relative formula implication. It derives the primitive laws from the
accepted environment's records. It does not claim checker acceptance for every
other declaration in that general fragment.

`EmittedApplications.closed_graph` uses `EmittedClosed.closedTruth` with the
constructed model. That path reads the two actual stored theorem records through
`Model.mem`, specializes their exact telescope, and observes their formulas.
`three_step` applies the resulting comparison twice, with a composed function
proved to inhabit its Pi set. Concrete natural-number and native-artifact
specializations remain checked alongside these relative applications. The
relative results retain carrier/function memberships and SetTheory explicitly.

`EmittedRejections` proves three controls: the wrong Exists parameter count
returns an error; the actual forward body checked against the backward statement
returns a theorem-type-mismatch error; and the accepted family cannot return an
environment with its projection tables deleted. The third is an output-contract
inequality, not an input rejection. Historical executed checks remain available
in `GraphChecks`, but none supplies an acceptance proof.

## Measurements and trust boundary

The prescribed first experiment preserved the exact And `nestRoot` equation,
state and fuel. It succeeded and passed its axiom audit before the implementation
extended to other stages. The [And checkpoint report](relative-and-root-checkpoint.md)
and committed checkpoint records retain the successful measurements, the earlier
unrecoverable timing disclosure, and capped failed attempts with exact sources.
Concrete-state reduction and rewrite attempts sometimes reached generation
heartbeat limits or wall timeouts. Their failure does not establish an intrinsic
kernel-checking limit. Symbolic bind/state/fold assemblers removed those repeated
reductions while preserving the exact operations and outputs.

[Final development measurements](../../experiments/relative-graph/checkpoint-135-emitted/measurements.json)
bind module-source and measurement-helper hashes to the captured run records.
Generation, synchronous checked declaration insertion, and bounded type rendering
are distinct measurements. Checked insertion includes `addDecl` overhead;
normalization's insertion measurement also includes code generation. Whole-file
wall time is separate. `sizeWithoutSharing` measures expression-tree nodes, not
stored bytes, allocation or peak memory; heavily shared terms can have very
large tree counts and short checking times. Diagnostic wall time with no captured
stage marker is not attributed to kernel checking.

The development runs use private prepared upstream outputs and existing native
outputs. Every new formal module passed its permitted-axiom module audit, but
these runs are not a fresh dependency-closure receipt. The detailed
[statement review](../../experiments/relative-graph/checkpoint-135-emitted/statement-review.md)
records this distinction.

## Portable final validation

The selected upstream source is ConLeche
`8e166ca53cd1f864b63c13cc1d326d38316d00ea`, with
`leanprover/lean4:v4.35.0`. From any working directory, use a clean committed
candidate and a new absolute output directory:

```sh
direnv exec /absolute/candidate python3 \
  /absolute/candidate/experiments/relative-graph/reproduce-acceptance.py \
  --run-dir /absolute/new-run
```

Coordinate shared builds with the repository's build lock. `--plan` inventories
the closure without validating it. The acceptance runner creates a fresh private
upstream checkout and outputs, rebuilds the focused native import closure and all
graph modules in dependency order, then enforces an exhaustive axiom audit of the
built upstream/native/graph closure. It excludes prepared main-project outputs
from the native/graph search path. External pinned package outputs are reused and
recorded under the repository's validation contract.

The closure audit checks every kernel-safe declaration, including unused roots.
It reports upstream unsafe runtime/elaboration declarations separately and rejects
unsafe source declarations in the local native/graph closure. This is not a claim
that the third-party implementation contains no unsafe code. The runner binds
source hashes, compiler/dependency identities, search paths, exits and final audit
to the candidate; it rejects source changes and output-directory reuse.
`test-reproduce-acceptance.py` exercises public runner boundaries and failing audit
controls. The historical reproduction scripts and pinned checkouts are preserved.

The isolated pipeline is the formal closure gate for this experiment. The main
checkout additionally requires ordinary `./check.sh --candidate HEAD` and
`./check.sh --verify-candidate HEAD`; those checks alone do not certify isolated
modules. Final fresh receipts and independent Standards, Spec and originator
review must match the frozen candidate. This report records proved statements
and development results; it does not assert an unrun final pipeline passed.
Neither #107 nor #108's independent-author repair/retest gate is selected or
bypassed by this work.
