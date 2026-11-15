# #1027 — Optional recovery of completed project compilation

## Origin, scope and unchanged requirements

Source: the user's 2026-11-02 request to preserve recoverable progress after
workspace or chat loss, including explicit permission to expose and upload
checkpoints immediately. The user did not require build caches to be excluded.
That exclusion was an initial local interpretation. It must not be silently
overridden: implement and independently review an explicit amendment first.

Historical requirements remain byte-identical:

- `work-state/REQUIREMENTS.md`, SHA256
  `85fbb013efa28c2aa1827dfaaab9cca5c3498f1da51b446972aa67dd690a7f84`.
- `work-state/specs/1002-full-requirements.md`, SHA256
  `43dbf2c1104ec2503a0dc89206001fd541daaf7f677ad7e89c7fcbda61f5939a`.

Complete source/history/ticket/review checkpoints remain mandatory and
cache-free. The amendment may permit a separate optional cache companion that
is incomplete without its explicitly named complete source checkpoint. This
is an explicit exception to both the cache exclusion and the requirement that
every recovery archive be standalone. Credentials and downloaded research
copies remain excluded. No new GitHub write is authorized.

The first formal candidate remains
`3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`. Do not change that checkout, its
configuration, dependency pins, source, active artifacts, validation process,
or acceptance sequence. No later chapter algorithm is in scope. #1025 remains
open and nonblocking under its existing evidence-based disposition.

## Implementation and review boundary

Root implements in the new, separate local Git repository
`work-state/cache-companion/`. Its clean empty base is
`6f48c1ab7f1e96056c217ca025390aa58a7955b6`. Every new amendment, guide, utility,
test and exact vendored adapter belongs to the full review diff. The existing
checkpoint generator remains unchanged. The normal checkpoint workflow copy
preserves this small operational repository, including its reachable Git
history; it contains no build cache or credentials.

Use one implement/code-review loop with separate Standards and Spec axes,
immutable candidates and this fixed base. Validate each candidate in an
isolated checkout using the pinned Nix environment. Tests for the operational
utility are artifact-appropriate; it changes no conaled build tooling, formal
source or proof claim and does not substitute for integrated Lean validation.
Keep the review record and test results outside this implementation diff.

The amendment becomes effective only after both axes pass the same tested
candidate and root verifies the delivered files match it. Do not copy actual
project cache artifacts into recovery staging, finalize a cache archive, or
upload one before that acceptance. Synthetic fixtures are permitted for tests.

## Required capture behavior

1. Bind the companion to a successfully uploaded complete source checkpoint by
   exact filename, SHA256, byte size, Library file ID and source commit. Refuse
   a different source commit or a dirty source/dependency checkout.
2. Record the current clean Git commit/tree, integrated source inventory,
   configuration/toolchain/manifest/Nix file identities, all resolved Git
   dependency pins, actual compiler version and compatible host platform.
   Verify these identities before and after capture. This states where the
   cache was captured, not that every retained artifact was compiled there.
3. Inventory the same root, SquareKit, Applications and Examples Lean sources
   as the project gate; exclude ProofAudit. Accept only fixed paths for complete
   module output families described by the pinned supported Lake trace schema.
   Include all declared olean parts, ilean, C and any declared IR/bitcode/archive
   outputs. Preserve the raw trace, including its inputs and depHash.
4. Reuse byte-identified copies of the existing guard and hash helper. Refuse
   a changed project adapter. Never invoke its repairing entry point against
   the active checkout. Omit setup JSON, hash sidecars, undeclared/stale files,
   native object/shared-library facets and verification success records.
5. Read fixed paths without following symlinks; require singly linked regular
   files. Make private ordinary copies, computing SHA256 while copying.
   Compare descriptor/path identities before and after each read, and recheck
   the trace and retained live families after the cohort hash step. Reject an
   individual incomplete, unsupported, mismatched or racing family as a whole;
   record the reason and do not retry indefinitely. Abort on changed source,
   dependency or configuration inputs. Do not mutate any live cache entry.
6. Validate the fixed private cohort with the unchanged pinned Lake helper,
   using one worker, an absolute pinned Lean executable, private cwd, no
   LEAN_PATH or output flags, and one bounded invocation (60 seconds). This
   elaborates executable tooling and imports installed Lake; it does not build
   project formal modules. The helper reads each artifact in memory. Bound
   individual files to 128 MiB, the cohort to 750 MB, and check adequate free
   disk capacity for staging, packing, an extraction check and 500 MB reserve.
   No automatic helper retry, cache repair, project build or alternative hash
   implementation is allowed on failure. A helper failure aborts capture.
7. Every retained artifact's actual Lake hash must equal its trace description.
   SHA256 is separately used for archive/transport integrity. Neither check
   proves compilation from the claimed inputs or authenticates hostile data.
   Consistent older entries may be retained for Lake to revalidate normally.
8. Write the archive to a private temporary name. Check its complete member
   inventory, regular-file types, paths, sizes, SHA256 values and family/trace
   consistency by extracting into an empty private directory before publishing
   the final filename. Never overwrite an existing archive. Report whole-file
   SHA256 and size, module/file counts, omissions and actual checks. Once
   finalized, root must expose and upload it immediately, then retain receipts
   in the next complete source checkpoint.

## Required recovery behavior

Restore the named complete source checkpoint first. Recreate its pinned Nix,
Lean and dependency environment separately. This optional companion must be
safe to ignore; an unavailable/incompatible cache never loses source progress.

Verification must require the companion's independently recorded whole-file
SHA256, its named source checkpoint binding, exact clean source/configuration/
dependency/compiler/platform identity, supported schema, complete member set,
safe regular-file paths and all payload digests. Reject traversal, symlinks,
hardlinks, duplicates, extra members, missing files and inconsistent families.
Do not extract unvalidated arbitrary archive paths.

Installation is allowed only with explicit idle-checkout acknowledgement and
an absent or empty project build directory in a separate isolated checkout.
Refuse a nonempty destination; do not merge or overwrite project outputs.
Create independent ordinary files, preserve raw traces, and regenerate setup
files through Lake. Never restore `.lake/verification.json`. Cross-root reuse
is not guaranteed: allow the normal guard/Lake input tracking to rebuild.

The full unchanged guarded build and exhaustive audit, managed ProofAudit
prerequisite, regression fixtures, both independent reviews and immediate final
candidate verification remain required. The companion is unaccepted cache
data, not proof, provenance certification, a success record or chapter credit.

## Tests and concrete validation

The public capture/verify/restore API and CLI are the implementation's test
boundaries. Selecting these necessary recovery interfaces is an implementation
choice within the user's already authorized durability work, not a new action
requiring a separate permission request. Follow the repository's TDD cycle
one behavior at a time. Use real temporary directories and small synthetic Git
projects; substitute only the external Lake runtime boundary for deterministic
unit fixtures, never internal collaborators.

Cover a complete round trip; complete-family omission for missing, malformed,
mismatched, racing or linked inputs; source/binding drift; archive corruption,
unsafe/extra/duplicate members; refusal to overwrite archives or nonempty build
destinations; explicit idle acknowledgement; and preservation of excluded
files/active inputs. Exercise the actual unchanged Lake helper once on a tiny
private literal fixture under the pinned environment, checking its documented
result shape and no generated artifacts. This bounded tool-only check is
permitted during implementation, without copying active cache artifacts.

Record honest limitations and exact commands/statuses. After tool acceptance,
create and immediately upload a new complete source checkpoint containing the
amendment, tool, full review and test evidence. Bind the first cache companion to
that checkpoint. Restore-smoke-check the actual archive before finalization;
do not install it into the active validation checkout.
