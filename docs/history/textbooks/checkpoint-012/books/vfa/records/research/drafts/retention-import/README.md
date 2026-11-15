# Local #1024: isolated Retention import check

Frozen staging evidence, 2026-11-02. **All three authorized compiler checks
passed.** This is a focused import check; it does not accept a VFA chapter,
establish downstream compatibility, or replace the full candidate gates.

## Exact source and statement preservation

The requirements are `../../specs/1024-Retention-imports.md`, amended SHA256
`a06c5512cb30a686693bff2828b6fe99d7b2fe206d0345b831baf0af0ad84bd5`.
Both checkouts were at `de575a81266ac98194c7c5c83e91628098aac92e` before and
after the experiment. Their three original sources matched byte-for-byte.

| Source | SHA256 |
| --- | --- |
| Original Retention | `df3c0e1715a9967078183266f8c30b36cdec00cd4f9e328ffa8168ecad93eba3` |
| Proposed Retention | `628bf59c4789148005c2304027e29020d2dcd62a63a3326170c03da89ab421b6` |
| Unchanged RelationTransport | `2b7fe19802d4667d4eca355f16845a339606a15e01544845bd51e0631c06197e` |
| Unchanged InteractionContracts | `0ccc54b5aec0bd4e266e1345bea40cd4d97748781c3e7ed1b1257a440122e6c4` |

`imports.patch` is the complete proposed change: replace Retention's one
`Mathlib.Tactic` line with `Mathlib.Tactic.SplitIfs`, then
`Lean.Elab.Tactic.Omega`. Every other source byte is identical. The two
prerequisites are unchanged copies, required because neither checkout had
their compiled outputs at preflight. No other project prerequisites were built.

Statement-preservation review covered the full three sources. RelationTransport
keeps its relational images and universally quantified backward requirements;
InteractionContracts keeps partial-correctness, interference, observation and
run invariance contracts. Retention keeps the existential full-history witness,
finite retained suffix, prefix parity, bounded append precondition, admitted
range boundary, exact read/classify observations and bounded freshness theorem.
Their assumptions, conclusions, executable definitions, proof bodies, instances
and comments have no edits. The specialist tactics needed by Retention are
`split_ifs` and `omega`; compilation checked their providers together with all
remaining elaboration, simplification and instance requirements in this module.

## Invocation provenance and isolation

No original Retention, RelationTransport or InteractionContracts setup/trace
existed. The amended requirements explicitly permit direct `LEAN_PATH` checks.
No setup file or import map was created, adapted or supplied; no source imports
were overridden. Both `lakefile.toml` files declare no custom `leanOptions` or
module arguments, and all three source files use the legacy format without a
`module` command. Each emitted module name was independently checked below.

`environment-command-source.trace.json` is an exact copy of the completed
candidate **Finite** trace, SHA256
`c71294375fdc4a6cee39a8a658cc98cb45bc940211ea3ff58da48f50b12ee961`.
It supplies the pinned compiler path, candidate package search paths and
`-o/-i/-c/--json` flag provenance. It is not a Retention trace. The compiler is
Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
The inherited search path is retained exactly, preceded only by this folder's
`generated` directory so consumers use the actual successful staged artifacts.

The corrected outer invocation was:

```text
python /workspace/scratch/0c54f2db1fdf/work-state/staging/retention-import/run-chain.py
```

The runner's working directory for each compiler was this staging folder;
relative `SquareKit/…` and `Applications/…` paths retained their module names.
It invoked the pinned Lean executable through
`nix develop /workspace/scratch/0c54f2db1fdf/conaled --command`, with
`LEAN_NUM_THREADS=1`. Every invocation retained `-o`, `-i`, `-c`, `--json` and
had its own `timeout --signal=TERM --kill-after=5s 180s` bound. These were
strictly sequential; a failed exit, wrong emitted module/import list, changed
protected input or changed generated prerequisite would stop the chain.
Each numbered directory's `STARTED.json` and `result.json` records the exact
argv, working directory, full staging-first `LEAN_PATH`, environment additions,
source identity and prerequisite artifact identities. `inputs.json` records
the setup-free rationale and complete protected-input identities.

The frozen `frp-imports/Spec.setup.json` artifact map was read only to confirm
the actual completed external dependency files. It was not supplied to Lean.
All four direct Mathlib roots and the pinned core Omega artifacts were present;
the recorded root artifacts include their public/private/server and IR files.

## Preserved prelaunch failure

The first Python runner launch stopped at an overly broad assertion that every
directory in the inherited successful Finite `LEAN_PATH` must exist. Its unused
`vfa-validation/.lake/packages/Cli/.lake/build/lib/lean` directory was absent.
No `STARTED.json`, output directory or compiler invocation existed at that point.
`prelaunch-guard/` preserves the exact first runner, returned traceback and exit
code 1. Its runner SHA256 is
`5ee7046e3eddadaad161031e457ed1de69498398624c3a5134a6a51e92ca2f9c`.

Root authorized replacing only that search-directory assertion with a presence
record, while retaining the unchanged inherited search path and required-file
guards. The corrected runner additionally protected the failure evidence.
The three successful checks below are the first and only compiler attempts.

## Actual results and emitted imports

| Module | Exit | Elapsed seconds | Emitted direct imports |
| --- | ---: | ---: | --- |
| `SquareKit.RelationTransport` | 0 | 27.309331 | `Mathlib.Logic.Relation`; `Mathlib.Data.Set.Lattice.Image` |
| `SquareKit.InteractionContracts` | 0 | 43.274868 | `SquareKit.RelationTransport` |
| `Applications.Durability.Retention` | 0 | 27.595111 | `SquareKit.InteractionContracts`; `Mathlib.Data.List.TakeDrop`; `Mathlib.Tactic.SplitIfs`; `Lean.Elab.Tactic.Omega` |

All three diagnostics files are empty: no compiler errors, warnings or other
messages. Each emitted module name matched the table. The extracted metadata
preserves the complete direct-import rows, declaration names, version and C
initializer names. Each successful module generated exactly its `.olean`,
`.ilean` and `.c`; every actual output was hashed before a consumer started.
The runner checked all earlier generated identities again before each consumer.
`generated-output-identities.json` preserves all nine final output identities.

All 62 protected identities and both HEADs matched afterward. These include
original and staged sources, dependency/configuration pins, direct imported
artifacts, compiler binary, trace provenance, requirements and prelaunch failure
records. The generated output tree was removed after evidence extraction;
`postcheck.json` records its absence and the absence of newly created setup files.
Main/candidate source and project caches were not staging destinations. No broad
build, cache fetch, ProjectiveMotion experiment or primary-process signal ran.

Elapsed times are actual observations under concurrent primary validation;
they are not a controlled performance comparison. The source-closure reduction
in the requirements remains a static topology observation. The full candidate
must still check the eight affected non-aggregate clients and all ordinary
audit/review gates after any root-owned integration. `SHA256SUMS` covers the
frozen evidence files; it excludes itself.
