# Requirements: local #1024 — explicit retention proof imports

Recorded 2026-11-02 during the unchanged de575a8 full Preface/Perm gate.
This is a narrowly scoped cross-cutting build-load correction, not a later
chapter implementation or acceptance. The enclosing review base remains
7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd.

## Concrete motivation and scope

The initial required project-wide validation is progressing without an actual
Lean error but has compiled only a small part of the 953 integrated source
modules. A read-only source-graph investigation identified Retention as a
bounded remaining umbrella import with eight uncompiled non-aggregate clients
that have no independent Mathlib.Tactic path. Static dependency counts are
topology observations, not measured time or memory improvements.

Only Applications/Durability/Retention.lean is proposed for source modification.
Replace its one Mathlib.Tactic import by these two explicit providers, retaining
all other bytes and import order:

```lean
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
```

Current source SHA256:
df3c0e1715a9967078183266f8c30b36cdec00cd4f9e328ffa8168ecad93eba3

Proposed source SHA256:
628bf59c4789148005c2304027e29020d2dcd62a63a3326170c03da89ab421b6

Every definition, theorem, proof, comment, instance, observation and operational
model must remain byte-identical. Do not broaden the scope to the independently
investigated ProjectiveMotion header or any client without recording a concrete
need and amended requirements first.

## Focused evidence before integration

Prepare the exact complete module in a separate work-state staging directory.
Preserve both main and active isolated source trees, their HEADs, dependency
pins, configurations and build caches. No generated staging artifact may be
installed in a project cache, and the primary validation process must continue
unchanged while the focused check runs.

The first experiment is one compiler process, one Lean worker, with a 180-second
timeout and bounded termination grace. Record the actual pinned compiler,
command, flags, import paths, setup provenance and any justified module-name
adaptation. Use real completed dependency artifacts; do not fabricate import
maps or override imports. Protect and compare the source/configuration/setup
inputs actually used. Retain the actual return code, diagnostics, elapsed time,
emitted module/import metadata and generated artifact hashes, then remove the
generated outputs. No retry is authorized by this initial specification.

## Preflight finding and bounded prerequisite amendment

The first preflight found no compiled InteractionContracts artifact in either
checkout. Its sole project prerequisite, RelationTransport, is also uncompiled.
No focused compiler had started, so there is no failed compilation or retry.
Root independently checked the complete missing project chain: unchanged
RelationTransport (71 lines), unchanged InteractionContracts (92 lines), then
Retention. RelationTransport has no project imports.

The experiment is therefore amended to permit exactly those two unchanged
prerequisite modules to be compiled sequentially in this staging directory before
the one proposed Retention check. Each compiler has one worker and its own
180-second bound plus five-second termination grace; at most one auxiliary
compiler runs at a time. No additional project prerequisite, retry or source
correction is authorized without another recorded decision.

Copy the prerequisites byte-for-byte from the independently matching main and
candidate sources and record their identities. Generated prerequisite outputs
remain inside staging. If setup artifact entries must change, change only the
two entries for actual successfully generated prerequisites, recording exact
old/new fields and output hashes. Do not invent artifacts, retain missing-file
mappings as if successful, override the source imports, or claim setup identity
after an intentional adaptation. An explicitly documented pinned direct
LEAN_PATH invocation without setup is also permissible if the compiler can
faithfully resolve the actual completed artifacts and all relevant source flags
are retained. Preserve all unrelated setup/configuration data.

Record every actual prerequisite result before proceeding to its consumer. Stop
on failure. After target metadata and all generated hashes are preserved, remove
the complete generated output tree. None of these outputs may enter a project
cache. The unchanged primary gate continues throughout; its ordinary cache is
not a staging output destination.

## Integration and acceptance

Root assesses the exact result before any integration. Focused success alone
does not establish downstream compatibility. If integrated, preserve the current
gate's actual outcome and safely stop only its verified task-owned process
group before replacing the isolated checkout. Keep ordinary completed outputs
under the existing integrity guard. The complete enclosing candidate then needs
the unchanged guarded build, exhaustive audit, managed ProofAudit prerequisite,
required audit regression, both independent Standards and Spec reviews, and
immediate final --verify-candidate before acceptance. No source/toolchain/build
configuration change outside the stated header, and no gate waiver, is implied.

Record local tracking and exact candidate evidence. Create, restore-check,
expose and immediately upload a durability checkpoint for an integrated candidate
and again upon acceptance. No GitHub write is authorized.
