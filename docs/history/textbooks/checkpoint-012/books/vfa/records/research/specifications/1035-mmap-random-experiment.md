# #1035 — Bounded native random-access advice experiment

## Motivation and limits

The user requested alternatives to slow emulation. Native execution is established,
but fresh4 has repeated long Mathlib-dependent compilations, while smaller modules
finish much faster. Prior bounded samples show substantial major faults and
input-block counters. These observations suggest an I/O hypothesis; they do not
identify the current process's bottleneck or establish readahead causality.

The pinned Lean compacted-region loader uses private, writable file mappings at
saved addresses. A one-page capability probe has confirmed that the required
MAP_FIXED_NOREPLACE operation and collision refusal work here. Pinned source
inspection found no existing madvise/fadvise/readahead advice in module.cpp or
compact.cpp. Do not force the malloc/relocation fallback or eagerly copy regions.

## Prototype contract

Prepare a separate, opt-in experimental shared library that forwards mmap and
may issue only MADV_RANDOM advice after a successful mapping. Match the exact
loader shape: nonanonymous file descriptor, offset zero, PROT_READ|PROT_WRITE,
MAP_PRIVATE|MAP_FIXED_NOREPLACE, and the requested preferred address actually
returned. Require explicit experiment opt-in and a current executable identity
matching AT_EXECFN. Preserve mapping result, mapped bytes, flags/protections,
collision behavior and the original mmap errno. Advice failure is recorded but
must not turn a successful mapping into failure or change its errno.

No advice is issued for other mappings, absent/mismatched identity or disabled
opt-in. Anonymous allocator mappings, shared mappings and executable mappings
must retain their behavior. No procfs reads, mounts, permission changes, eager
region copies, file mutations, proof shortcuts or compiler-byte patches.

Keep the accepted readlink shim, native helper/overlay, official distribution,
dependency trees, formal candidate and fresh4 inputs unchanged. All prototype
code, binaries, fixtures and evidence live in separate owned paths. The
prototype is not approved for full formal validation merely by being built.

## Bounded checks and decision

1. Record the exact C source/compiler/command/binary identities. Check the
   one-page advisory branch and passthrough/error boundaries with small isolated
   fixtures, including private-write isolation and collision non-overwrite.
2. Root may run one bounded standalone compiler probe of the existing original
   Squares source, with explicit -j1, separate outputs, actual child ownership,
   a 60-second limit, complete diagnostics and resource accounting. This is an
   environment experiment, not the current candidate's full gate. Reuse the
   exact earlier source/output identities; do not silently alter proof bodies.
3. A successful result must have matching expected .olean bytes before any
   stronger claim. The concurrent active full run and cache conditions are
   uncontrolled; no causal speedup follows from a single timing comparison.
4. Stop this branch if the bounded experiment provides no useful improvement or
   reveals a semantic/resource problem. Preserve failure and timeout outcomes.
   Any further comparison needs a concrete remaining question and a bound.
5. Production adoption requires an exact operational candidate, independent
   Standards and Spec review, explicit environment identities and an uploaded
   complete checkpoint before a new full formal attempt. Existing partial runs
   never combine into a successful check; all formal acceptance gates remain.

This is a cross-cutting environment experiment under the user's existing task
authorization. It grants no chapter credit and changes no book/source scope.
