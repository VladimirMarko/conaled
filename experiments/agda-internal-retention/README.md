# Agda internal-declaration inspection (#115)

This experiment inspects completed Agda interfaces before runtime erasure. Its
assessment is [Agda internal retention](../../docs/research/agda-internal-retention.md).
It supplies neither an importer nor a proof certificate.

## Reproduce

Use the repository's pinned Nix environment. Obtain the official
[Agda 2.8.0.2 Linux archive](https://github.com/agda/agda/releases/download/v2.8.0.2/Agda-v2.8.0.2-linux.tar.xz),
SHA-256 `2bcf24bb561b1be859bba841e5d67962d1616b3251bc147f878e4f60a2fbd9f7`.
Extract its `agda` executable. The script checks executable SHA-256
`3fe070780fa370f5b74e5716ebe42fb60ec6b0ad90d13f8ab45d2903abf39b84`.
It copies sources from the repository and extracts only the Cubical directory
from the already retained checkpoint 022. It creates private compiler data,
configuration, interfaces and backend output in a **new** directory.

```sh
direnv exec . python experiments/agda-internal-retention/reproduce.py \
  --agda /absolute/path/to/agda --work-dir /absolute/path/to/new-directory
```

The recorded run used `taskset -c 2` before `python`, restricting this process
and its children to one allowed CPU while a separate Lean validation ran.
Choose an allowed CPU on another machine, or omit `taskset`. No project
heartbeat, toolchain, library option or runtime-mode changes are required.
The script expects a successful ordinary and cubical check, successful JS and
Haskell generation for the ordinary probe, and exit 42 for attempted full
cubical compilation. It does not call GHC or execute the generated programs.

`evidence/receipt.json` records commands, statuses, source closure hashes and
script hashes. Paths in logs are normalized to `$WORK` and `$AGDA`.
`*.json` declaration excerpts were collected **before** backend compilation,
which may rebuild interfaces with different options. The private root also
contains complete raw node/string tables and the undecoded numeric tail for
each inspected interface. Those diagnostic tables are not committed.

For a different selected declaration in an existing checked interface:

```sh
direnv exec . python experiments/agda-internal-retention/inspect_interface.py \
  /absolute/path/to/Module.agdai qualified.declaration \
  --raw-tables /absolute/path/to/raw-tables.json
```

Names may be exact qualified names or final qualified suffixes. A suffix can
match more than one declaration. Read the returned names before using output.

## Inspector limits

`inspect_interface.py` accepts only interface version `202507030`. Its schema
comes from the following files at Agda commit
`cccf42fa88eae25ccbe2623f489021d2075f6f73` (the peeled `v2.8.0.2` tag):

- [Serialise.hs](https://github.com/agda/agda/blob/cccf42fa88eae25ccbe2623f489021d2075f6f73/src/full/Agda/TypeChecking/Serialise.hs): header, gzip payload and table order.
- [Serialise/Base.hs](https://github.com/agda/agda/blob/cccf42fa88eae25ccbe2623f489021d2075f6f73/src/full/Agda/TypeChecking/Serialise/Base.hs): table types.
- [Instances/Internal.hs](https://github.com/agda/agda/blob/cccf42fa88eae25ccbe2623f489021d2075f6f73/src/full/Agda/TypeChecking/Serialise/Instances/Internal.hs): signatures, declarations, types, terms, clauses and function metadata.
- [Instances/Common.hs](https://github.com/agda/agda/blob/cccf42fa88eae25ccbe2623f489021d2075f6f73/src/full/Agda/TypeChecking/Serialise/Instances/Common.hs): argument metadata, names, maps and primitive tables.
- [Instances.hs](https://github.com/agda/agda/blob/cccf42fa88eae25ccbe2623f489021d2075f6f73/src/full/Agda/TypeChecking/Serialise/Instances.hs): interface envelope.
- [Monad/Base.hs](https://github.com/agda/agda/blob/cccf42fa88eae25ccbe2623f489021d2075f6f73/src/full/Agda/TypeChecking/Monad/Base.hs): meanings of the envelope fields and function flags.

The summary traverses term positions and records definition/constructor
references. It deliberately leaves sorts, levels, literal payloads, binder
metadata, patterns, options and most environment fields as raw references.
It therefore does **not** certify the absence of all metavariables, enumerate
all logical dependencies, or decode the full environment semantically.
`unresolvedTermPositions: []` means only that no `MetaV` or `Dummy` occurred
in the traversed term positions. The raw tables preserve the other fields for
inspection; integer/double table bytes remain an undecoded hex tail. The
reader is intended for these trusted local compiler artifacts, not hostile
input, other compiler revisions or use in an acceptance pipeline.

The release binary did not emit `tc.signature:60` debug output. No actual
`TTerm` dump was obtained. The backend files are actual generated output;
claims about the intermediate treeless datatype are separately sourced in the
report. Reflection was considered but is not substituted for full internal
syntax or environment evidence.

## Provenance and reuse

The compiler is BSD-3-Clause licensed; see its pinned
[LICENSE](https://github.com/agda/agda/blob/cccf42fa88eae25ccbe2623f489021d2075f6f73/LICENSE).
The selected Cubical library is MIT licensed; its license is retained in
checkpoint 022 and extracted alongside the source. This experiment uses the
same library revision as the retained Monodromy/FrozenMemo development,
`b150186d2544e7efeddd31e5d14a8b9ecbb100f7`. Checkpoint 096-10 supplied a
matching compiler binary for the recorded run, **not** its source/library
closure. `IdentityPattern.agda` is this experiment's small ordinary probe.
The repository's retained source provenance continues to govern Monodromy and
FrozenMemo. Generated backend excerpts illustrate erasure and are not added to
the library API.
