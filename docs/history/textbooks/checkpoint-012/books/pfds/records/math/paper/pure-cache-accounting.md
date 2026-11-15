# Local 10020: raw cache accounting

Owner: chapter02_ordered, within the existing local10020 implementation loop.
Scope: only Applications/Suspensions/CacheAccounting.lean,
Examples/SuspensionCacheAccounting.lean, and this note. Root owns integration,
Git index/refs/commits, tracker and acceptance. Original task base ea8afa12706d30cdc69ece1a172d5f21a3ea1809;
root has incorporated the docs-only corrected 361f5f3 tip, with the revised
bounded review-base record owned by root. No GitHub actions.

**Status:** the complete owned library and client passed focused attempt r3
on 2026-11-02, exit0/758 jobs, with all 29 recorded local import/configuration
inputs unchanged. Both source files are frozen. No candidate acceptance,
exhaustive proof audit or independent review is claimed by this handoff.

## Intended statement and boundary

Machine.FreshEntries quantifies every actual unfinished Prefix.observe state
and requires its body-event address to be absent from pendingAddresses of its
current stack. It neither bounds writes nor assumes purity, typing or finite
completion. after_step shifts observations through the actual transition;
observe_pending_nodup derives stack distinctness along actual prefixes.

Observation.cacheWrites is an additive homomorphism from the existing
FreeAddMonoid Event trace to Nat. It is definitionally the List.count of the
selected cacheWrite address; cacheWrites_eq_lift identifies it with the
framework's additive indicator reweighting. No new evaluator/event producer is
introduced. The successor equation follows the existing measured workload;
already delivered answers add zero events and no count.

Root subsequently requested the bounded structural extension
cacheWrites_observe_mono and cacheWrites_observe_zero_of_finished. The first
uses workload_append and nonnegative additive counting. The second proves
zero at every budget from an actual completed zero-write observation, using
monotonicity before completion and absorption after it. It needs neither
bounded memory nor purity, and its completion premise is explicit. Root owns
the connected unforced and exception-retry source cases.

cacheWrites_observe_settled uses ConfigBounded and CacheWrite's Settled to prove
zero future writes at an address, for every budget. The value payload is not
asserted constant. cacheWrites_observe_le_one assumes ConfigBounded, initially
distinct pending addresses, and FreshEntries, and bounds the actual trace's
count by one. A first successful write uses cacheWrite_settles to make its
suffix zero; other continuing steps retain boundedness/distinctness/freshness.
This raw conditional theorem is separate from root's forthcoming admitted pure
source theorem, which must discharge the hypotheses using actual finite
execution/nonreentry. It does not establish unrestricted uniqueness or a bound
on attempted body entries.

## Opening case and statement review

The existing literal firstForce from Examples.SuspensionPending is reused.
Its independent expected trace is body0, core, cacheWrite0, core, core (five
actual transitions). The opening missing connection is from those transitions
to an additive observed count under the universal raw theorem; the concrete
trace itself is already reducible. No unrelated compile error is presented as
a mathematical gap.

The client establishes FreshEntries by the five exact live prefix states and
the existing absorbing-answer theorem after its actual completion. It applies
the universal bound for every address/budget, derives pending distinctness
through the public law, retains exact one/zero counts for addresses0/1,
promotes the latter to zero at every budget through completed-zero/monotonicity,
and uses the public finished-suffix theorem for arbitrary extra budgets. A later
force starts from the completed cached memory, obtains boundedness from the
actual evaluation, emits hit0 and uses settled preservation for zero writes at
all budgets. Its reweighted observation explicitly consumes cacheWrites_eq_lift
and the actual trace theorem through existing Resources.reweight.

The raw hypotheses are substantive: older duplicate memoize frames permit a
later overwrite despite a value cell. Root/Map retain the existing unrestricted
two-write example. The task's pure-source cases, exception cases, and allocation
identity comparisons remain root-owned; this file does not advance their status.

## Development evidence and retained failures

Draft written 2026-11-02; original draft captured in checkpoint024 at 78ed1a1.
The requested monotonicity/zero-extension declarations were added after that
capture. Compilation began only after root released the green Pending and
CacheWrite dependencies. All three attempts used the prescribed
`session/validation/run-focused-development.py`, pinned offline Nix, the shared
focused lock, LEAN_NUM_THREADS=1 and default Lean limits. No project
configuration, axiom/linter setting, index/ref, commit or entrypoint was changed
by this worker. The only added external import is the narrow pinned
`Batteries.Data.List.Count` module for its exact singleton-count theorem.

Every terminal session was collected and closed by this worker. The records
retain the complete command and before/after local input hashes. All attempts
had both queued_inputs_unchanged=true and inputs_unchanged=true.

## Focused attempt r1

`active-validation/suspension-cache-accounting-r1.json` and `.log` preserve
the first focused run (session30967, terminal exit1, unchanged input hashes).
It reached CacheAccounting and found three local proof-normalization issues:
the count homomorphism application needed an explicit List.count `change`;
the finished-suffix proof needed to unfold the observe wrapper; and the
positive-write branch left a reflexive Nat inequality after `simpa only`. No public
statement, hypothesis, algorithm, expected example result, budget or linter
was changed. The client did not run. The subsequent correction attempted an
explicit reflexive proof after rewriting; r2 showed that the rewrite already
closes that goal. Core had not yet passed at this stage.

## Focused attempt r2

`active-validation/suspension-cache-accounting-r2.json` and `.log` retain
the second attempt (session95709, terminal exit1, unchanged inputs). The
finished-suffix proof passed in this attempt. Two local issues remained: the singleton
List.count lemma is not a default simp rule, and `rw` already closes the final
reflexive inequality, making the added `exact` redundant. The r3 correction
used the exact pinned `List.count_singleton'` theorem via the narrow
`Batteries.Data.List.Count` import and removed that redundant tactic. No
statement/premise/result/budget changed. Before its first compilation, the
resource example was connected explicitly to cacheWrites_eq_lift. The client
was not reached in this second attempt.

## Focused attempt r3: passing handoff

`active-validation/suspension-cache-accounting-r3.json` and `.log` record
terminal exit0, 758 jobs. CacheAccounting passed in147s and the example module
passed in98s. Session83908 is closed; the focused slot was released to root
immediately on terminal for Pure/CacheCounts and its source clients. No optional
checks or further source changes followed this sufficient focused validation.

| Attempt | UTC start → terminal, 2026-11-02 | Result |
| --- | --- | --- |
| r1 | 23:20:27.949413 → 23:22:15.247645 | exit1; local proof-normalization issues; client not reached |
| r2 | 23:23:08.052074 → 23:27:49.010887 | exit1; exact singleton lemma and redundant tactic; client not reached |
| r3 | 23:28:49.907016 → 23:33:18.609614 | exit0; library and all owned clients green |

All three commands recorded HEAD78ed1a1501a955a5579a7a098910a5d4bc1361be.
The later proof edits were working-tree changes: the file/input hashes, not
that original WIP commit alone, identify the passing bytes. Root owns the
subsequent complete-candidate commit and its mandatory acceptance gates.

Passing source SHA256 values:

- Applications/Suspensions/CacheAccounting.lean:
  `c8468574f8b2efb72b212efd9261c789ac209381dedd342d70a8c84ff2bfab53`
- Examples/SuspensionCacheAccounting.lean:
  `277a6259f141d2f82c9cac1dcc297c895d1b86bb4ba4d840909b1a03198327e4`

Terminal evidence SHA256 values (JSON then log):

- r1: `784c9f5687152adae591850930d1ca31afc1907004445b47f8b974677b673ca0`;
  `c52e80d9b1824747bd821bc2018ec273e1d1f917c9dd1a1083b0ddc935dd1230`.
- r2: `8af5e60cf898f15ea655cefc0706fea3df8113f5991658e9f3a82cdcff7741c4`;
  `92ed279854cfd5740b3979aa6131c032bde35273d33d57f4b05a66c00dcd8329`.
- r3: `3a487946d56ebd5c603d2c269830fd697e8173e6e9847192d1f10c00f20e374f`;
  `3f530b71192dd6c01b4ff35f5beec66f29657c7319766e514895319374ea982a`.

## Remaining scope and statement-review conclusion

The owned raw conditional slice and its connected cases are complete at the
focused-development level. Every expected event/count and all theorem
hypotheses remained fixed across proof corrections. The proof uses the actual
machine/observer and its existing state invariant, not a second evaluator,
body-count assumption, payload-constancy assumption or circular write bound.
FreshEntries is a real raw premise; initial pending distinctness and bounded
configuration are also explicit and substantive. The pure-source theorem is a
separate root-owned connection that must derive these premises from its actual
finite execution and hereditary/representation hypotheses.

Root still owns full integration, source clients (including exceptions,
distinct allocation identities and cached recursive closures), stock full
check/exhaustive audit, independent Standards/Spec review and immediate final
verification. This report is the author's statement review and implementation
handoff, not independent acceptance. No Chapter2/3/4 frontier was changed.
