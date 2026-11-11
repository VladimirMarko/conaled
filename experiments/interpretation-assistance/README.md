# Finite interpretation assistance (#462)

This prototype offers a finite registry of native transport routes. It checks
supplied evidence with Lean and writes the generated result and diagnostics.
It does not discover arbitrary theorems, choose weakest assumptions, or replace
the distinct contracts of diagonal representation and resource execution.

From the repository's direnv shell, build its support once:

```sh
lake build SquareKit.InterpretationDiagnostics SquareKit.InterpretationAssistance Examples.DiagonalCoverage Examples.ConstructionTransport
python3 scripts/interpretation-assist.py composition --out /tmp/transport-composition
python3 scripts/interpretation-assist.py omitted --out /tmp/transport-omitted
python3 scripts/interpretation-assist.py resource --out /tmp/transport-resource
```

Each output directory must be new. `receipt.json` records input/tool hashes,
compiler, commands, individual checks and status. The generated `.lean` files
are the evidence; their logs print the actual requirement expressions and the
result's retained expressions/types. `result.lean` can be checked again with
`lake env lean`. The request entry records source construction, target and
observation. No cached success is reused. Work in an immutable accepted checkout;
this local wrapper is not an artifact-authentication mechanism.

`--omit extension` removes a default certificate. To supply your own declaration,
use `--support proofs.lean --certificate extension=MyProof.extension`.
The support source is inserted before `namespace Requested` in every request,
then checked and audited. Its imports must appear before its definitions.
Certificate overrides are qualified declaration names; trusted registry entries
may contain Lean expressions. Both files are trusted local inputs, not untrusted
remote code. The registry and support can run Lean commands. The tool is not a
sandbox and does not claim protection against a malicious metaprogram.

The default registry includes extension, composition, omitted-code, image-only,
erasure and measured-resource cases. `--registry path.json` selects a frozen
alternative data registry. The supported schemas are `extension`, `image`,
`erasure` and `resource`; adding arbitrary schemas is outside this experiment.
The resource schema accepts arbitrary additive source/target cost types and
uses `seeded_reweight`, which reuses `reweight_bind` and `reweight_run`.
Connecting the supplied seed/transition to a compiler program and simplifying
its resource formula remain explicit caller obligations.

| Status | Meaning |
|---|---|
| `checked` | The result exists at its generated Lean type; all current-module logical declarations and transitive dependencies pass the axiom audit. |
| `missing evidence` | A requested sufficient law has no supplied proof. Read the actual proposition in `requirements.log`. |
| `rejected evidence` | Supplied evidence failed checking or its axiom audit. This does not refute the proposition. |
| `refuted obligation` | A separate registered proof of the exact obligation's negation passed checking/audit. Alternative routes or observations are not thereby refuted. |
| `registry exhausted` | No entry has that ID. This is not mathematical impossibility. |
| `checker failure` | Imports, request schema, generated application or environment failed. Broken support source also belongs here. |
| `budget exhausted` | The external trial runner refused another check. No mathematical conclusion follows. |

The omitted-code case rejects full-target extension but the image-only route
retains a representative on a narrower input domain. The erasure case checks
failure of injectivity of the witness projection, not impossibility of selecting
some representative. The resource result observes value and mapped modeled
charges, not CPU time. Requirement inspection is an actual Lean invocation;
each certificate and final application are checked separately.

Run real executable tests with a new output directory:

```sh
python3 scripts/test-interpretation-assist.py --out /tmp/transport-tests
```

The suite retains successful and failed source snapshots, compiler logs and
receipts. It checks wrong evidence, absence, a proved negation, unknown registry
entries, unavailable imports, forbidden axioms, unused private helper axioms,
external budget limits, cutoff snapshots and author-supplied declarations.

During the prospective author trial, the coordinator initializes
`scripts/interpretation-trial-check.py --state STATE --initialize`. Every direct
Lean check uses `--state STATE --source FILE`; the assisted CLI receives
`CONALED_TRIAL_BUDGET=STATE` or `--budget STATE` and sends each internal invocation
through the same runner. The coordinator separately runs `--state STATE --watch
AUTHOR_OUTPUT` to retain a cutoff snapshot. This is cooperative experimental
access control, not an OS sandbox. Authors may not bypass/reset the runner.

No author trial has run. The [protocol](protocol.md) and its readiness gates
must be completed and independently reviewed before dispatch. The implementer
has seen task descriptions, but not private solutions or their transcripts;
they are held-out proof/application clients, not blind discovery tasks.
