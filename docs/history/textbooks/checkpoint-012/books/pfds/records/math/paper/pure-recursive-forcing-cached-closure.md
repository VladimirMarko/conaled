# Cached recursive closure from the existing source — local10019

Status: GREEN on the first focused check (r1). The example and evidence are frozen, and no compiler or queue remains active from this worker. This closes the assigned connected-client implementation gap, not full-gate or independent-review acceptance.
This closes preparatory finding PREP-10019-01 from
session/research/pure-recursive-forcing-preacceptance.md. It is a new example
and report only; every checked core module and CachedProgram remain frozen.

## Existing source and discriminating behavior

Use Examples.SuspensionPureMachine.returningClosure exactly. Its source is
`s = $(fn b => if b then 7 else (force s) true)` followed by `(force s) false`.
Identifiers remain s=1, b=2; force is the existing derived function application
with generated pattern variable0, not a new bind-based approximation.

The first force returns and caches a closure whose captured raw environment
contains (1,address0). Its pure capture contains the suspension with the same
finite returningGroup descriptor. The closure itself has no extra recursive
component: its already-closed capture carries the back reference. Applying
it to false forces s again after the earlier body has finished; this is a
cache hit and the resulting closure is applied to true, returning integer7.

The complete existing source should take raw53/pure51 transitions. The raw
one-binding recursive prefix takes5 versus pure1; the second force saves2
raw transitions by a hit instead of pure body-entry/function-formation/return.
Thus raw=51+4-2=53. The remaining source body is raw48/pure50. Its raw trace
should contain exactly one allocate0, body0, cacheWrite0 and hit0.

For a later observation, bind identifier3 in the initial client environment to
the recovered cached closure and evaluate `variable3 false`. This actually
takes the back-reference branch. Expected counts: raw36/pure38. Both prefixes
of18 transitions reach the suspended-variable0 pattern on s; the actual raw
hit takes1 while replaying the stored two-transition closure-formation
certificate takes3 pure transitions. The common suffix then takes17 more
transitions to integer7: variable0 matching/selection, force-function return,
true argument evaluation/application, true branch and both caller returns.
Hence18+1+17=36 and18+3+17=38. The full cached raw memory remains unchanged.

## Recovery and composition plan

A final integer result does not expose an address-world lookup. StateRep is
one-way, so final StateRep alone is insufficient to recover lookup0. Instead:

1. Use actual recursive_entry and independently computed raw5/pure1 prefixes
   to identify the exact reached configurations. Extract the represented s
   binding from ConfigRep.control/EnvRep.lookup and recover its exact immutable
   meaning by address/value inversion. No semantic world is postulated.
2. Strip the creation prefix from the actual raw53 and existing pure51 source
   evaluations. Apply finite_correspondence to the residual raw48 evaluation,
   identify the pure50 result using uniqueness, and transport lookup0 through
   the returned immutable-world extension.
3. Inspect the actual cached cell using cached_lookup_allowed. Identify its
   stored body evaluation with the independently expected two-transition
   function-formation run. Invert the cached closure ValueRep to recover its
   capture relation and exhibit the same recursive address/meaning lookup.
4. For the later false application, use its actual18-transition prefixes and
   the concrete continuation stack at the back-reference force. Apply
   reuse_cached with that stack and the recovered final StateRep. Compose its
   inferred stored certificate/replay with the actual17-transition suffix,
   proving raw36/pure38 and retaining the complete cached memory exactly.

No library facade or core API change is needed. No final cache witness,
acyclicity, no-reentry condition or source type-safety assumption is supplied.
These are explicit evaluator-transition counts, not a universal write bound or
host-time/source-complexity claim. Full gates and independent acceptance review
remain parent-owned.

## Focused validation

The first target is Examples.SuspensionPureCachedClosure. Its complete imported
local closure plus pinned configuration/check scripts are hashed before queueing
and at lock acquisition, then frozen until the actual terminal result.
Evidence: active-validation/suspension-pure-cached-closure-r1.{json,log}.
No existing Lean file was edited for this client.

## Passing evidence

Examples.SuspensionPureCachedClosure passed its first focused target check:
exit0, 768 jobs, 21-second example module. Every independently stated count
and observation passed unchanged: raw53/pure51 source, one allocation/body/
write/hit at0, raw5/pure1 creation prefix, residual48/50, two-transition stored
closure-body certificate,18-step later prefixes, raw hit1/pure replay3, and
17-step tails yielding complete later36/38.

- Started: 2026-11-02T21:58:20.780582+00:00
- Ended: 2026-11-02T21:58:56.362447+00:00
- Local source/config inputs: 45; all before/start/after hashes agree.
- Source SHA-256: `e8afed46093e0dab9a1fdb2e13787c461c0cc48271f351a933dda1510aa21c65`.

Terminal session11161 was collected and the focused lock released. Pinned
offline Nix/Lean4.35, LEAN_NUM_THREADS=1, default proof limits and project
linters were retained. No admissions or native_decide were introduced. The
log retains existing dependency module-system warnings.

## Statement review and connected public API

- raw_source_trace checks the original returningClosure term, including its
  one body/write/hit observations. raw_source_execution erases that actual
  trace. pure_source_execution reuses the existing checked pure source case.
- creation_recovers_self_meaning consumes recursive_entry and actual5/1
  observations. Its world lookup comes from the reached control's EnvRep and
  address-value inversion, not a manually supplied map.
- source_recovers_cached_recursive_closure strips those real prefixes and
  feeds the residual run to finite_correspondence. Immutable extension retains
  the recovered meaning at0. cached_lookup_allowed then supplies the actual
  cached closure representation and successful body certificate; uniqueness
  identifies their exact expected value and count. Inverting that closure
  representation recovers the self-capture relation. Both the raw address
  lookup and the pure finite-descriptor lookup are exposed in the conclusion.
- cached_closure_back_reference_hits uses that recovered state and capture.
  Its actual18-transition prefix reaches the force of s under the force-clause,
  force application-result, pending true-argument, and outer application-result
  frames. reuse_cached advances through that same stack. The raw36-step proof
  prepends the18 actual transitions to its returned hit plus checked17-step
  tail; the pure38-step proof composes the corresponding Reaches prefixes and
  the same semantic suffix. The answer contains exactly finalMemory, and its
  cached payload remains the self-referential raw closure.

The original source is not replaced by a different program. The later separate
observation binds variable3 to the recovered closure so its false branch must
use the actual captured s back reference. The first closure body has already
returned before the hit; this is not active body reentry. No acyclicity or
no-reentry premise is assumed, and no manually constructed StateRep.memoize
certificate is used. The one-write observation belongs only to this concrete
53-transition source trace; it is not a universal successful-write bound.

Root's preparatory statement pass found the intended missing connection
present before the compiler returned; that pass is not an independent
acceptance review. PREP-10019-01 now has this focused-green connected client.
Core files, CachedProgram, tracker, entrypoint, Git index/refs and checkpoints
were untouched by this worker. Root owns integration and remaining gates.
