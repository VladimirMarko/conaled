# #1035 — Separate native launcher with explicit Lean CLI worker count

## Authority and decision

The user requested alternatives to slow QEMU emulation and authorized pinned
non-Nix tooling. Continue the existing operational review loop for this
cross-cutting environment work. The accepted native route runs unchanged official
Lean 4.35.0 and Lake 5.0.0-src+eb6cafb using the scoped executable-path shim.

The original Squares probe with explicit `-j1` and experimental MADV_RANDOM
completed in 6.9525 seconds; a subsequent `-j1` control using only the accepted
readlink shim completed in 2.4449 seconds. Both compiled files match the prior
known digest. Cache/order/concurrent conditions are uncontrolled, and RSS was
higher in both fast observations. These results do not prove causal speedup,
reduced memory requirements, or safe increased compiler-process concurrency.
Do not adopt the mmap prototype: the simpler route supplies the useful observed
result. Preserve the prototype, tests and actual outcomes as experiment evidence.

## Production change

Add a separate `pinned_native_j1_toolchain.py` and `NATIVE-J1.md` under
work-state/tooling. Leave every existing helper, shim, guide, overlay, formal
source and active fresh4 input byte unchanged. Use a distinct generated overlay
`toolchains/lean-4.35.0-native-j1`, with unchanged official Lean/Lake payload
copies and the same accepted readlink shim. Pin all execution input digests as
in the accepted native helper. The only intentional compiler invocation change
is an explicit `-j1` in the Lean launcher. Lake itself receives no `-j1`; retain
`LEAN_NUM_THREADS=1` for Lake's ordinary task pool.

Retain the accepted helper's selector clearing, fixed sysroot/library paths,
private fresh-check LEAN_PATH behavior, relocatable reconstruction, input checks
and changed-wrapper refusal. Do not add the mmap library or experimental opt-in
variables. Explain that later explicit CLI arguments may override the initial
thread setting; the supported acceptance commands pass no later thread override.
Use one external compiler job in fresh validation. Do not claim this constrains
every OS thread or that unavailable procfs RSS enforcement is supplied.

The guide must include exact reconstruction/usage instructions, version and
identity requirements, the three distinct concurrency controls, the limited
measurement claim, and the unchanged proof/build acceptance requirements. Refer
to the existing NATIVE.md for base installation and readlink-shim construction;
retain the original user QEMU fallback instructions. Full formal validation
through this new overlay requires a new complete run: partial attempts cannot
be combined.

## Validation and acceptance

Capture a stable operational Git candidate from base
`0afe0faa014512a0375bb158b6c8a56817075319`, including exactly the two new production
files. Validate the captured candidate in isolation. Reuse unchanged native
shim and official-payload checks only with matching exact identities. Check
generated wrappers, pinned versions, direct Lean compilation, Lake's actual
child compiler selection, an Init proof with its axiom report, and the known
original Squares output digest. Keep outputs outside active formal checkouts.

Retain actual commands, exits and source/runtime/output identities. Independent
Standards and Spec must review the same complete candidate and requirements;
root must compare delivered bytes immediately before operational acceptance.
Save and upload the complete checkpoint before a new full formal attempt.
No operational acceptance grants chapter credit or resolves the open formal
validation findings. Keep the formal candidate and chapter order unchanged.
