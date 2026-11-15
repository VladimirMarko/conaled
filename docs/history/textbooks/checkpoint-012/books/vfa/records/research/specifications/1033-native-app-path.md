# #1033 — Native executable-path compatibility

## Scope and motivation

The user authorizes the exact pinned toolchain outside Nix and supplied a working
QEMU route. That route is preserved unchanged in checkpoint038. The actual first
fresh module, Squares, required111.21seconds under emulation. This bounded
environment adaptation investigates native execution without changing the
official compiler binaries, project pins, host permissions, or formal gates.
Fresh3 continues while the prototype is evaluated. A prototype failure does not
invalidate the already-working QEMU route or justify bypassing any check.

## Required behavior

Lean's pinned Linux runtime calls libc readlink on /proc/<its own PID>/exe.
The proposed external compatibility library may return only the already-known
executable path, only for /proc/self/exe or /proc/<actual getpid()>/exe, and only
when an explicit absolute CONALED_SELF_EXE equals the process's AT_EXECFN value.
It does not read denied procfs data. All other readlink calls pass unchanged to
the kernel; no other process, statm/RSS, resource limit, or host capability is
emulated. Preserve readlink's truncation, no-NUL and zero-buffer behavior.

Per-program launchers must select the correct executable path separately for
Lean and Lake. The byte-identical official binaries remain together under a
separate native overlay so Lake's child search uses the same selected runtime.
Clear inherited Lean selectors as in the existing QEMU adapter, preserve the
fresh checker's own LEAN_PATH, and do not put the whole checker inside lake env.
The known official distribution and source/dependency pins remain unchanged.
The compatibility library is an explicit additional execution input, with its
complete source, build command/compiler version, hashes and scope retained.

## Validation and review

Before use for formal acceptance, establish narrow readlink behavior, rejected
mismatched executable identity, passthrough of ordinary symlinks, actual bare
and Lake-child Lean/Lake versions, and kernel-checked proof smokes. Compare the
native first module against the already completed QEMU module where possible.
Record actual outcomes, diagnostics and timing; do not infer kernel validity
from timing or from a successful startup alone. Review both the implementation
and intended behavior independently within the existing enclosing workflow.

If supported, preserve equivalent native reproduction instructions alongside
the exact QEMU fallback and upload a complete checkpoint before starting a new
formal validation attempt. Stop an obsolete owned attempt only through an
available ownership-preserving execution control and record its real outcome;
never signal a historical PID. Do not restore a prior verification record or
combine partial runs into a passing full check. The full fresh/guarded/audit/
regression/review/final-verification sequence remains required on one candidate.

The original user requirements and previous execution failures remain historical
evidence. No VFA chapter or source-policy change is part of this ticket.

## Explicit user steering received during the prototype

The user said:

> My apologies.
>
> `conaled-nix-workaround-lean-lake-4.35.0.md` seems to prescribe emulated tooling. This seems to be way too slow. Let's find an alternatives.

This confirms the native-alternative investigation. The whole-book objective,
correct pinned versions, local-only tracking, durability, and formal gates
continue unchanged.
