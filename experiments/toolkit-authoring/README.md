# Toolkit author trials (#249)

This archive retains the independent trial evidence behind
[the research assessment](../../docs/research/toolkit-author-effectiveness.md).
The [protocol](protocol.md) was frozen before dispatch at source revision
`f071f18966d1ee875cdb5f328903d18a714732dd`, SHA256
`0b105d0877b81b88aa8777e98618be85b2af46edc9ba2f87a19c6604f1b84500`.
Both authors completed the established DList client and new reverse-list
realization through direct and shared routes, with the fixed positive and
negative cases. These are isolated experimental proofs, not integrated library
modules or additions to the public entrypoint.

| Evidence | Contents |
|---|---|
| [Author A](author-a/report.md) | Exact dispatch, supplied protocol, exposure hashes, per-attempt source/log/metadata, statement review and assistance |
| [Author B](author-b/report.md) | Exact dispatch, exposed public texts/hashes, per-attempt source/log/metadata, statement review and assistance |
| [Preparation](setup/record.md) | Copied-cache failure, focused reproduction and coordinator repair |
| [Checksums](SHA256SUMS) | Every archived file except this README and the checksum file |

Both used the inherited configuration without an override. Exact serving
revision, effort, token use and price were unavailable. A worked in the order
A direct/shared then B direct/shared; B worked B shared/direct then A
shared/direct. Both read public examples and had earlier-route exposure.
Report completion was approximately 5m36s for A and 5m18s for B, inside the
15-minute caps. These intervals include tools, setup and reporting; they are
not controlled productivity measures. Each author retained one failed Lean
proof attempt and one shell setup failure. No mathematical hints were supplied.

## Accepted checks and replay

The accepted sources are [A Final.lean](author-a/Final.lean) and
[B Final.lean](author-b/Final.lean), each byte-identical to the corresponding
archive-local `Examples/ToolkitAuthorTrial*.lean`. Their supported commands
from the repository root are:

```sh
direnv exec . lake env lean --root=experiments/toolkit-authoring/author-a experiments/toolkit-authoring/author-a/Examples/ToolkitAuthorTrialA.lean
direnv exec . lake env lean -R experiments/toolkit-authoring/author-b experiments/toolkit-authoring/author-b/Examples/ToolkitAuthorTrialB.lean
```

Dependencies must first be built under the repository's README instructions.
Use an isolated checkout of the frozen source revision and copy this archive
there to reproduce the library inputs. Current-checkout replay can detect later
compatibility changes but does not recreate original author effort. No generated
Lean artifacts are included in this archive.

[A's accepted log](author-a/FinalRoot.log) explicitly includes
`Examples.ToolkitAuthorTrialA`, 38 logical declarations and 28 named theorems.
[B's accepted log](author-b/Final-root-audit.log) explicitly includes
`Examples.ToolkitAuthorTrialB`, 25 logical declarations and 20 named theorems.
Both exhaustive audits passed with the permitted axiom union
`propext`, `Classical.choice`, `Quot.sound`. Anonymous checked examples and
explicit type checks accompany the named claims. The differing counts reflect
different author factoring, not a usability ranking.

The original protocol instructed authors to import ProofAudit and audit the
experimental source directly. Its expectation of local audit coverage was
wrong: the project's module filter excludes arbitrary experimental paths.
Both original successful logs omitted the local trial module. Passing a virtual
Examples filename through `--stdin` also failed to establish local coverage.
The explicit package-root invocation above fixes module identity without
changing proof source or audit implementation. Author A also retained an
API probe and a superseded in-source module-identity harness; neither is the
accepted replay route. Inspect the explicit local-module audit row, not merely
the success message. These repairs are recorded deviations from the frozen
validation procedure, with unchanged mathematical contracts.

Failed attempt files and superseded harnesses are historical evidence. They
are not accepted theorem artifacts and are not expected to pass a bulk check.
The individual Python runners preserve metadata and merged raw diagnostics;
their own exit status need not equal Lean's recorded `exit` field. Shell setup
failures lack exact timestamps, and the first coordinator preparation output
was tool-truncated; those limitations are disclosed in the reports.
