# Lean module-system adoption assessment

Issue [#593](https://github.com/VladimirMarko/conaled/issues/593), following
[#592](https://github.com/VladimirMarko/conaled/issues/592).

Retain the production layout and visible import diagnostics. The trial below
checks a conversion preserving the exercised source-level interfaces of the
standalone foundation, but detects generated-name export changes. Its
potential benefit is allowing module-system clients to import that foundation.
No current client requiring that conversion has been identified. Removing the
advisory Mathlib import warnings would require different, larger dependency
closures, and is not by itself a reason to migrate.

Reconsider when a concrete client needs to import this foundation as a Lean
`module`, or a pinned compiler/dependency update makes the legacy boundary an
actual compatibility failure. At that point, rerun the trial, identify the
client's required exports, and validate its downstream closure before adoption.
This decision does not prescribe indefinite deferral of all module-system work.

## Slice and compatibility obligations

The trial uses the six modules in [check-foundation.sh](../../check-foundation.sh).
The production Lean header parser, reached through the real source inventory,
confirms that these are exactly the local dependency closure of `Verification`:

| Module | Explicit imports |
|---|---|
| `Squares` | `Lean` |
| `Compiler` | `Std` |
| `SquareCompiler` | `Compiler`, `Squares` |
| `FirstOrder` | `Std` |
| `Dependent` | `Lean` |
| `Verification` | The preceding five modules |

Lean also supplies implicit `Init` imports. A single compiler module would be a
smaller closure, but would not make the existing standalone verification
entrypoint available to module clients. This is the smallest closure for that
specific prospective capability, not a claim that every useful trial needs six
modules. The rest of the production library stays unchanged.

Before conversion, the harness enumerates canonical public declaration names
from the compiled legacy slice, including generated declarations. It later
compares both inventories and checks the shared names through `Verification` in
both client modes. It separately checks the removed names are unavailable. Its
machine-readable report also records all direct production importers of the
slice. Those consumers include the categorical, relational, AD and FRP compiler
layers; converting a foundation does not justify assuming all their behaviors
remain unchanged.

| Contract | Trial use |
|---|---|
| Public and transitive declarations | Full public-name inventory comparison; common names through `Verification`; explicit rejection of removed generated names |
| Definitional reduction | Compiled square of 7 reduces to 49; dependent compiled application at 8 reduces to 8 |
| Instances | Derived `DecidableEq CategoricalCompiler.Ty` and `Repr FirstOrderCompiler.Ty` via `inferInstance` |
| Notation | Existing list/product syntax; a separate scoped-notation boundary fixture because the foundation declares no custom notation |
| Execution | Original `Verification` evaluations, plus the client evaluations of the two reduction cases |
| Private declarations | Explicit private theorem in the boundary fixture remains unavailable by its user-facing name; the audit must still include its kernel declaration |
| Generated and local roots | Independent environment scan includes recursors and a private declaration in the current audit module |

The arithmetic case exercises the real compiler, target and interpreter rather
than a replacement implementation. The dependent case uses the existing
`appliedCert`. The numeric expectations are also checked by kernel reduction;
execution alone does not establish them. The notation equality tests name
resolution only. No new mathematical interface or theorem is added to the
production library.

## Isolated conversion policy

The compatibility-oriented copy adds `module`, public imports, and an exposed public section
to each foundation source. `Verification` also imports executable dependencies
for meta use. The explicit private declaration in the boundary fixture remains
private. The legacy and module clients use the same proof and execution bodies;
the module client adds its required meta import.

This broad policy is deliberately a compatibility experiment. It preserves the
exercised definitions and downstream reduction rather than designing a new
abstraction boundary. It therefore establishes no encapsulation benefit.
Selective exports would require a caller inventory and a deliberate API design;
hiding existing definitions or their reduction behavior merely to remove a
warning is not acceptable.

Separate negative controls use the actual `Compiler` source. Default-private
conversion compiles but hides `square`. A public conversion without exposure
fails while compiling `Compiler` itself: Lean reports a compilation-type
mismatch involving `Val` and refuses reductions through unexposed definitions.
The exposed copy supplies separate missing-meta-import and non-public-re-export
controls. The unchanged legacy dependency is also rejected by a module client.
These are concrete constraints of the pinned compiler, not evidence that the
mathematical interfaces need weakening.

## Reproduction and evidence

Run from the repository root with a new output directory:

```sh
direnv exec . python3 scripts/assess-module-system.py --output /tmp/module-system-trial
```

The [harness](../../scripts/assess-module-system.py) writes only to that new
directory. It discards caller `LEAN_PATH`, uses the pinned compiler and Lean/Std,
and does not use Lake or any production compilation output. It preserves the
copied sources, commands, diagnostics, input hashes, actual production import
graph, public-name inventories and audit summaries. `summary.json` is written
only after every expectation passes. A changed closure or compiler version
requires investigation rather than silently changing the expected result.

Both isolated variants execute the original `check-foundation.sh`. Each also
runs the production source preflight and filesystem inventory. The production
`ProofAudit.lean` is copied with only its public-entrypoint import redirected to
the trial slice and boundary fixture; its enumeration and axiom policy are
unchanged. Its exact root set and per-module counts are compared with a separate
scan of every environment constant using module ownership. The check includes
an empty `Verification` module, private and generated roots, and current-module
roots. Removing the inventory helper must cause the audit to fail.

This is an auxiliary assessment harness and report. Compiler/dependency pins,
production definitions, Lake configuration, scheduler, source-policy guard,
integrity guard and proof-audit implementation remain unchanged. Validation
runs the harness against the immutable review candidate; a cold full-library
build would add no evidence about this isolated conversion.

## Observed export and audit differences

With the pinned Lean 4.35.0 and the foundation at `268324a3`, the inventories
contain 952 public names each, with 950 in common. The isolated audit and
independent scan agree exactly: 1,275 logical roots in
legacy mode and 1,277 in the converted copy, including the boundary and local
audit fixtures. The difference is not permission to skip private roots.

Lean changes these generated names under the tested exposure policy:

| Namespace | Removed public name (now private) | Added public name |
|---|---|---|
| `CategoricalCompiler` | `instReprTy.repr.match_1` | `Val.match_1` |
| `FirstOrderCompiler` | `instReprTy.repr.match_1` | `Val.match_1` |

The two Repr matchers remain audit roots under their private kernel names.
The two Val matchers add roots. These are generated auxiliaries, not explicitly
written public mathematical declarations. Nevertheless, callers can name
legacy generated declarations, so the conversion is not a claim of perfect
export compatibility. A future adopter must search the affected clients and
choose whether compatibility aliases or a documented boundary are needed.
The harness asserts the exact delta for this toolchain instead of ignoring all
generated names.

## Adoption cost and limits

The exercised module client can be supported by this conversion, but it
requires explicit choices about imports, visibility, exposure and execution.
The six-file trial supplies compatibility evidence for this particular
foundation and its exercised clients. It does not certify the entire library,
other import closures, future Lean versions, or a narrower export policy.

No build-time or memory improvement is claimed; the trial does not benchmark
performance. Its observed benefit is access from a prospective module client,
not an established need from a production consumer. Retaining the layout avoids
maintenance and downstream migration work without weakening any mathematical
contract. The import-warning category remains visible under this disposition;
[#591](https://github.com/VladimirMarko/conaled/issues/591) continues to own the
broader native verification tooling direction.
