# Direct-toolchain amendment and runtime handoff review

Date: 2026-11-03. Scope: operational evidence and resume instructions only.
Formal candidate remains `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`; formal
Standards and Spec outcomes remain Blocked. This record grants no chapter credit.

## Environment assessment — /root/environment_options

The required main validation chain does not call Nix, direnv or elan. The exact
official Lean4.35.0 distribution supplies the matching Lake5.0.0-src+eb6cafb;
the guard uses its Lake.Build.Trace implementation. Python3.11+ is required by
tomllib, and the available Python3.12.14 meets that requirement. Git has no
explicit numeric checker requirement. The separate test-check.py suite includes
an elan-specific case, but the retained candidate acceptance chain does not.

Independent exact-commit source inspection confirmed the startup chain:
native lean_main initializes search paths before parsing options; the internal
Lean.getBuildDir calls IO.appDir; Linux lean_io_app_path reads /proc/<pid>/exe
and returns an error on failure, without environment or argv fallback.
LEAN_SYSROOT affects external findSysroot and Lake detection, not this path.
No supported flag or ordinary launcher override was found. No patch or workaround
was implemented. Source URLs and hashes are in the toolchain evidence record.

The final operational evidence review found no concrete defect in
validation/1031-direct-toolchain.json, STATUS.md, the appended environment section,
or the amendment specification. It correctly distinguishes verified distribution
identity from successful compiler startup, combined-shell return values from
individual command results, Lake success from Lean failure, library loading from
application-path discovery, and rejected escalation from actual execution.
It limits the conclusion to the exposed sandbox and retains the complete formal
gate sequence under the user's narrow Nix exception.

Review limits: the assessor did not rerun smoke commands, independently rehash
the distribution, or reissue the rejected escalation. No formal approval is
implied by its clear operational disposition.

## Recovery/gate assessment — /root/recovery_audit

The recorder has no /proc or Nix dependency in its inspected source. Its direct
argv launch can be used unchanged once the compiler runs, with a new fresh3
attempt directory. Its actual process facilities and failure behavior still need
to work at launch; source inspection is not a recorder execution test.

The handoff correctly preserves the user exception, immutable original
requirements/review/checklist, compiler and dependency pins, fresh and separate
guarded validation, audit prerequisite/regression, both independent review axes,
immediate final verification and acceptance checkpoint before Sort. Fresh3 is
not launched. Historical fresh1/fresh2 outcomes remain unknown; the old raw
records are byte-identical. No formal source changes or acceptance are invented.

One current-state defect, RH-1031-1, was raised: ticket1030 still named Nix in its
current blocker and next_action fields. Root moved those old values into
historical_nix_blocker_before_user_exception and replaced the current fields with
the direct compiler's /proc/<pid>/exe requirement and continuation under #1031.
The assessor checked the exact correction and confirmed RH-1031-1 fixed.

Final scoped disposition: no remaining reported operational handoff defects.
Formal approval remains pending. Checkpoint037 creation and upload are separate
later actions, not certified by this read-only review.

## Root disposition

Apply the user exception without reimposing Nix. Preserve the unchanged acquired
distribution identity and actual unsuccessful Lean startup. The outside-sandbox
read-only version check was rejected before execution because sandbox escalation
is disabled; no bypass was attempted. Current continuation requires normal
process-executable path access in the execution surface. No formal gates are
waived, and no successful compiler invocation is claimed.
