# Preservation author trials

This archive records the first independent author comparison for
[#235](https://github.com/VladimirMarko/conaled/issues/235). The conclusions and
continuing obligations are in the
[architecture assessment](../../docs/research/preservation-architecture.md).

The [protocol](protocol.md) was frozen before dispatch against commit
`dc3aad963f49759623728b28dbdb15490ee1567a`. Two independent agents received the
same tasks, public documentation and source access, with opposite route orders.
Neither designed the interfaces. The budget was 20 minutes per author or task
completion, with no paid model calls or private proof hints. Both returned
before that limit. The exact serving model revision and token counts were not
available; the agents inherited the session model without an override.

| Record | Contents |
|---|---|
| [Author A](author-a/report.md) | Prompt, exposure, obligations, statement review, timing limitations and setup errors; versioned sources and compiler logs in the same directory |
| [Author B](author-b/report.md) | Prompt/protocol, exposure, obligations, statement review, start/finish times and setup errors; versioned sources and compiler logs in the same directory |
| [Checksums](SHA256SUMS) | Archived author evidence and frozen protocol, excluding this explanatory README and the checksum file itself |

Each author completed the operational bound and indexed transport through both
routes on its first actual Lean source submission. Setup failures are recorded
separately from mathematical failures. Author A disclosed one overwritten
missing-file diagnostic; its preserved shell error and report retain the failure
and repair, but the archive is not a complete transcript of that diagnostic.
No failed proof was replaced by a weaker theorem or additional hypothesis.

The exact successful proof bodies are integrated in
[PreservationAuthorA](../../Examples/PreservationAuthorA.lean) and
[PreservationAuthorB](../../Examples/PreservationAuthorB.lean). Integration adds
outer namespaces, replaces the combined audit import with the two library
imports for B, and removes `#print axioms`/`#audit_project_axioms` commands.
Their definitions, theorem statements and proof bodies are otherwise retained.
Task letters inside a file identify the operational task A and indexed task B;
they do not always identify the author. The integrated files are covered by the
normal build and exhaustive audit. Archived scratch files are historical trial
artifacts, not additional integrated library modules.

To check a successful archived file against a checkout with its dependencies
built, use the development shell, for example:

```sh
lake env lean experiments/preservation-authoring/author-a/Combined.lean
lake env lean experiments/preservation-authoring/author-b/AllAudit01.lean
```

The latter audits the loaded project and its local trial declarations. To
reproduce the frozen library inputs, use an isolated checkout of `dc3aad9`, copy
the archived file there and build those pinned sources first. Logs retain
absolute paths from the original scratch checkouts. Current-checkout counts or
diagnostics may differ from the frozen records. A successful replay does not
reproduce author effort, model behavior or missing diagnostics.

The public optional-coverage example and dependent transport implementation
were available to both agents. Route order was counterbalanced, but each author
had already seen one solution when writing the other. Wall time includes tooling
and uncontrolled host contention. These trials support the reported comparison
of exposed obligations; they do not establish general human usability or a
causal speed improvement. No #108 task was selected or exposed.
