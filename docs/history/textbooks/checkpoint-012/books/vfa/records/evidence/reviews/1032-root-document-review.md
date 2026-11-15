# Root review of the VFA environment recipe

Scope: recovery tooling and instructions only; no formal candidate approval.

The complete VFA tooling README was read against the user-supplied guide and
the exact Appendix A adapter. The candidate and fixed review base are those of
VFA, not the guide's unrelated ADWH task. The recipe preserves official program
bytes and all dependency pins, explicitly wraps parent and child Lean routes,
uses a direct checker wrapper to avoid an inherited LEAN selector, and gives
the explicit QEMU invocation for the cache executable. The recorded startup
and two Init-only proof checks are actual successful runs. The cache-tool build
now has actual child/recorder/tool success; cache retrieval is still in progress.

The guide, complete adapter, provenance inputs, exact source recipes, relocation
warning and all candidate validation gates are included in the next checkpoint.
The setup does not close ST-002/SP-VAL-001 or accept any VFA chapter. Both formal
review outcomes remain Blocked until their applicable evidence is complete.

No source, compiler, pin, proof-policy or formal-gate change was made.
