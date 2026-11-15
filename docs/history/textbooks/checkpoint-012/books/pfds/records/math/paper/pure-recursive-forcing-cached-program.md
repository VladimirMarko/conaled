# Successful source cache reuse — local 10019

Status: GREEN on first focused check (r1). The example and evidence are frozen; no compiler or queue remains active from this worker. This is not a full-gate or acceptance claim. This is an example-only
continuation of the existing10019 loop; all checked library files stay frozen.
Root owns commits, entrypoints, checkpoints and acceptance. Checkpoint020
a0ceaca91d86107d2365e82c50a92e1147ef46e8 preceded this new client.

## Source and independently expected observations

The source expression is:

```text
bind (variable 0) (delay (integer 7))
  (bind (suspended wildcard) (variable 0) (variable 0))
```

The initial environment and memory are empty. The delayed literal captures
the empty environment before variable0 is bound; its immutable meaning has no
recursive group. After the source completes, the raw result is address0, the
raw memory has frontier1 and cached integer7 at0, and the pure result is the
suspension of integer7 with empty capture and no group. Both runs take15
actual machine transitions.

Independent count: outer binding setup/allocation/value-to-pattern/matching/
body entry takes5; inner binding setup/lookup/value-to-pattern takes3; forcing
body entry/literal evaluation/cache-or-force return/wildcard match/bind return
takes5; final lookup/delivery takes2. Total5+3+5+2=15.

The later matching caller retains the binding of variable0 to the returned
address/suspension, making the caller distinct from the original empty body
capture. Starting a suspended wildcard match on that value takes3 raw
transitions: cache hit, wildcard match, matched-result delivery. The pure run
takes5: body entry, literal evaluation, force return, wildcard match, delivery.
The isolated literal body takes2 transitions including value delivery, so
reuse_cached expands its actual stored certificate into a3-transition pure
prefix before inner matching. The final raw matching answer retains the whole
cached memory exactly, including cached7/frontier1; matching returns the empty
binding environment in both machines. These are evaluator transition counts,
not host-time or source-language cost claims.

## Connected proof plan and statement boundary

1. Check the actual raw/pure source runs with Progress.search_sound and proved
   run equalities, without native_decide.
2. Apply finite_correspondence to the actual raw source run from the empty
   StateRep and admitted code domain. Use the independently checked pure run's
   deterministic uniqueness to identify the returned pure result/count.
3. Invert ResultRep and ValueRep for the returned raw address0. Recover the
   exact immutable literal meaning from the suspension constructor fields.
   The final world, StateRep and world lookup are conclusions of the source-run
   theorem; no final world or cache certificate is assumed or constructed by
   manually calling StateRep.memoize.
4. Apply reuse_cached to that inferred StateRep/lookup and the actual reached
   cached-cell equality. Recover its stored body evaluation, identify its value
   and two-transition count by uniqueness, and compose the raw hit and pure
   replay with the actual two-transition wildcard/delivery tails.
5. Expose the actual hit event, recovered body certificate, pure replay prefix,
   complete3/5 matching evaluations and unchanged reached memory in public
   example theorems. No library facade, new execution semantics, termination
   assumption or nonreentry assumption is added.

This client complements the now-checked general finite interpretation and
nonreentry results. Its later success is not a full-gate or acceptance claim.

## First focused check

Target Examples.SuspensionPureCachedProgram, with the complete local imported
closure/configuration hashed before queueing and rechecked under the shared
focused-build lock. All input sources are frozen. Evidence is written to
active-validation/suspension-pure-cached-program-r1.{json,log}; the actual
terminal status and immutable identities are recorded below.

## Passing validation and statement review

The first focused target check passed: exit0, 764 jobs, 23-second example
module check. Both15-step source evaluations and the later3/5-step runs
compiled without changing any independent expectation. The inferred body
certificate was identified as2 steps and its replay prefix as3.

- Started: 2026-11-02T21:51:01.759045+00:00
- Ended: 2026-11-02T21:51:31.756399+00:00
- Recorded local source/config inputs: 41; before/start/after hashes all agree.
- Source SHA-256: `abf9a7014ced9705deb20bbfb59b38270384e8b8513cbfb19c7950d43a2f3dd0`.

Pinned offline Nix/Lean4.35, LEAN_NUM_THREADS=1, default proof limits and project
lint settings were retained. No admissions or native_decide were introduced.
The log contains the existing dependency module-system warnings. Terminal
session88431 was collected and the shared lock released.

Public connected claims:

- program_allowed establishes the existing hereditary source domain.
- raw_source_execution and pure_source_execution check the exact source
  outcomes and15-transition counts through Progress.search_sound.
- source_recovers_cached_suspension consumes finite_correspondence. Its
  existential final world and StateRep are produced by that theorem, and
  ResultRep/ValueRep inversion recovers world0 = some meaning, where meaning
  is exactly literal7, empty captured environment, no recursive group.
- recovered_cache_replays_certified_body obtains that recovered StateRep and
  uses reuse_cached. Its public conclusion retains the actual stored2-step
  body certificate, hit0 event,3-step pure prefix to the unmatched wildcard,
  resulting ConfigRep, complete raw3/pure5 evaluations, and exact finalMemory
  retention with cached7/frontier1.

Statement review: no final-world/cache witness is supplied as a premise; no
manual StateRep.memoize proof constructs the final invariant. Deterministic
uniqueness identifies witnesses already returned by the generic library
results. The later caller contains variable0 while the original body capture
is empty; the exact meaning lookup retains that distinction. Matching returns
empty bindings, rather than claiming the wildcard returns integer7. The
replayed pure steps and raw cache-hit steps are intentionally different
operational counts and carry no host-time cost interpretation.

Root's preparatory statement pass also found no issue before compilation;
that was not a formal acceptance review. The only implementation file added
is Examples/SuspensionPureCachedProgram.lean. All core files stayed frozen.
No Git/index, entrypoint, tracker or checkpoint mutation was performed by this
worker. Root owns the entrypoint integration, checkpoint, full gate and review.
