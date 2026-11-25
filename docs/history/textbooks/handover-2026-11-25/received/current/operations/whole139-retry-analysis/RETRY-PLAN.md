# Prepared normal-route retry plan — NOT RUN

The root is the sole compiler and output owner. This file contains proposed
commands, not an executed script or a success claim. The candidate remains
`50581179674f0ccf364ca3c372b5e07e5c70c80e` in
`/workspace/scratch/ae71b485b114/work/acceptance139`.

## Terminal and ownership gate

Wait for the original whole139 invocation's actual terminal. Read its actual
`whole139.child-exit.json`, `whole139.result.json` and complete log; retain them
unchanged. Check agreement on candidate/project/command and actual exit status,
and inspect the full result's input invariance. Missing evidence is unresolved,
not permission to relabel the result. A successful original run needs the
existing post-whole verification/review plan, not a gratuitous retry.

Root must establish no overlapping compiler/output writers on the acceptance
checkout before beginning another build. No time/resource cap, signal,
environment override, source change or cleanup is part of this proposal. Select
a new record name if any suggested name already exists; never overwrite actual
evidence. Root should retain relevant diagnostics about unresolved `lake env`
startup before choosing whether one retry is useful.

## Preferred minimal fully guarded retry

For an ordinary failed original invocation with unchanged effective inputs and
no separate integrity concern, run the same full incremental child command
through the existing recorder. The original input-list file is a JSON list;
retain it unchanged.

```sh
python3 -B /workspace/scratch/ae71b485b114/work/continuation/run_recorded.py \
  --project /workspace/scratch/ae71b485b114/work/acceptance139 \
  --inputs /workspace/scratch/ae71b485b114/work/continuation/whole139.inputs.json \
  whole139-normal-retry-attempt1 -- \
  ./check.sh --candidate 50581179674f0ccf364ca3c372b5e07e5c70c80e
```

This invokes the preserved native adapter, the unchanged checker, pre/post
guards, full inventoried module target set and exhaustive audit. It adds no
job/thread/heartbeat/recursion or resource setting, performs no whole-cache
cleanup, and supplies no outputs or trace metadata. Ordinary Lake reuse is
permitted by the normal route.

One actual success requires exit0, completed unchanged-input receipts, the
complete audit result and matching `.lake/verification.json`. One failure or
new concern is recorded and investigated; this plan is not an automatic retry
loop. A source edit/new candidate would require its own exact validation and
review record.

## Optional focused preparation, if root chooses it

After the same terminal/ownership gate, an ordinary supported target build can
be run and recorded one invocation at a time. The following is an example for
the first observed failed module; it has not been run:

```sh
python3 -B /workspace/scratch/ae71b485b114/work/continuation/run_recorded.py \
  --project /workspace/scratch/ae71b485b114/work/acceptance139 \
  --inputs /workspace/scratch/ae71b485b114/work/continuation/whole139.inputs.json \
  whole139-prepare-CartesianFilling-attempt1 -- \
  lake --no-cache --rehash build +Examples.CartesianFilling
```

The seven prefix targets, subject to the **complete terminal** log, are:

- `Examples.CartesianFilling`
- `Examples.CartesianLargeFamilyConstructors`
- `SquareKit.Internal.Cubical.CartesianUniverse`
- `Examples.CubicalConstructorState`
- `SquareKit.Internal.Cubical.CocycleOrdinaryAction`
- `Examples.CubicalFrozenActionHomotopy`
- `Examples.DependentFunctionConversionSemantics`

Use one distinct receipt name per actual invocation, and await its actual result
before starting the next. Lake may also build dependencies using its unchanged
default scheduler. Do not convert the list into a parallel shell loop or change
jobs/thread limits. There is no guarantee that focused preparation resolves the
exit137 events or delayed workspace loading.

These direct builds bypass the project's integrity guard and do not reproduce
all of the checker's source/inventory/environment/audit work. They can create
ordinary Lake artifacts under the supported development route; they cannot
claim guarded acceptance. If this optional preparation is used, finish with the
**exact same full guarded retry above**, retaining all preceding failures and
preparation results. The whole checker remains responsible for its original
internal environment normalization and artifact guard. Do not manually inject
fresh-reference outputs, copy oleans, fabricate traces or hashes, or reinterpret
focused success as a full pass.

## After a usable exact success

Follow `work/review/post-whole139-plan.md` for the actual nonrepairing
`--verify-candidate` check, supported exact-content comparison and continuation
with the same two independent review axes. Bind the newly successful receipt
and actual retry result rather than pointing to a failed earlier invocation.
Review findings about candidate139's continuation metadata remain independent
of compiler success; this retry does not resolve those findings or accept later
source snapshots.

The eventual checkpoint should contain the original failure, retry outcomes,
useful diagnostics and this plan in the single complete archive for its cutoff.
No progress update to issue558 is part of the plan.
