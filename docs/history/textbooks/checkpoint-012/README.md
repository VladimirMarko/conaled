# conaled textbook checkpoint — VFA, FDSA and PFDS

> **STOP after a wipe or missing/incomplete source: ask the user to attach the latest durable checkpoint and wait before project work. Cleanup and delegates are included. A checkpoint is complete only after integrity/recovery checks AND an observed successful owner-root `create_library_file` upload. Upload failure blocks further accumulation. See [DURABILITY](docs/DURABILITY.md).**

This is the `conaled-textbooks` checkpoint series, begun with generation 001.
Current combined integration is owned by [books/common/README.md](books/common/README.md),
including the full user requirements, local issue tracker and current status.
`checkpoint.json` owns the current delivery serial; an archive filename or this
README does not establish successful upload. The package preserves the three projects' existing Lean history, paper mathematics,
review evidence and unfinished work. Packaging has not rebased, integrated,
compiled or mathematically accepted their code. It does not itself claim upload.

## Read in order

1. [DURABILITY](docs/DURABILITY.md), then [AGENTS.md](AGENTS.md).
2. [RESUME](docs/RESUME.md) for verified recovery and bounded setup.
3. The selected book's [VFA](books/vfa/README.md), [FDSA](books/fdsa/README.md) or
   [PFDS](books/pfds/README.md) page and its `STATE.json`.
4. [WORKFLOW](docs/WORKFLOW.md) before implementation/review;
   [INTEGRATION](docs/INTEGRATION.md) before planning common code integration.
5. [CHECKPOINTS](docs/CHECKPOINTS.md) before every delivery milestone.

## One owner for each concern

| Concern | Canonical owner |
|---|---|
| Recovery, durability and interruption gates | `docs/DURABILITY.md` |
| Setup and bounded troubleshooting | `docs/RESUME.md` |
| Review and validation procedure | Actual checkout guidance, routed by `docs/WORKFLOW.md` |
| Code identities and stored ref roles | `source/refs.json` and the single `source/repository.bundle` |
| Current book progress and next bounded scope | `books/<book>/STATE.json` |
| New paper progress and explicitly uncompiled drafts | `books/<book>/work/` |
| Original mathematical/review evidence | Frozen `books/<book>/records/` |
| Checkpoint mechanics and guards | `docs/CHECKPOINTS.md`, `tools/checkpoint.py`, package policy |
| Retrieved integration references | `reference/SOURCES.json` and its named files |

The old source base is preserved at `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
The old guidance snapshot `a887a8d9a58401683f68cdfffd8688147d4e9d4f` remains historical.
The new full integration baseline is `9175737c2b14ef738cfb6c2cdc68d885c0805ddd`,
pinned from master before implementation. Follow its actual checkout instructions
with the current user exceptions in `books/common/REQUIREMENTS.md`.

All required project source and history are in this archive; no previous project
checkpoint is required. Compiler/dependency installation and new textbook-page
audits have their own external inputs, documented by setup and source provenance.
Historical absolute paths, session IDs, setup commands, process holds and private
tracker labels inside records are inactive. Follow the current owners above.
