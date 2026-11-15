# Actual body-entry observations and shared debit support

Author handoff for local10022, 2026-11-03. This is a source-only implementation
and statement review within the existing implementation/review loop. No Lean
compilation, proof audit, candidate acceptance or independent review is claimed.

Requirements: `requirements/body-entry-counts.md`, version1, SHA256
`1483d8bfc4470c4aa700c809209b3083db89fa713def40821e1968d9e3ce2a58`.
Design: `research/body-entry-counts-design.md`. Fixed bounded and original
integration base: `577be121e074ddb5de6727a7481c115cb61b3b27`.

The delegated author owns only the following two new files in `body-counts/`
and this handoff. Root owns compilers, active input closures, integration,
candidate capture, trackers and durability checkpoints. No existing module,
entrypoint, Git state, cache, validation record or live compiler handle was
changed or operated by this author.

## Missing connection and implementation

The existing source examples supply actual ordered events and the new
BodyAccounting theorem bounds entries at a selected address. Those ingredients
do not by themselves connect the body-entry observation to the unchanged
persistent debit interpreter. This is an interface connection to establish,
not a claim that a concrete finite-list equality was mathematically unavailable.

`Applications/Suspensions/BodyRealization.lean` adds the following observations
and laws in `Suspensions.Core.Observation`:

- `bodyAddress` selects the address of a body event; `bodyAddresses` filters the
  existing `FreeAddMonoid Event` trace, retaining order and multiplicity.
  `bodyAddresses_add` preserves ordered concatenation. The public
  `bodyAddresses_count` identifies every address occurrence count with the
  existing `bodyEntries` additive observation.
- `bodyAddresses_nodup_iff` uses ordinary `List.nodup_iff_count_le_one`.
  `bodyAddresses_length_eq_card` uses ordinary finite-support cardinality under
  Nodup. Neither result derives nonrepetition from cache-write uniqueness.
- `totalBodyEntries` is the additive length of the projected list. Its
  `totalBodyEntries_eq_lift` law identifies it with the zero/one body-event
  indicator. `totalBodyEntries_workload_reweight` applies the existing
  `workload_reweight` law to exactly the same measured machine workload.
- `bodyDebits` gives each body event its singleton physical address and gives
  every other event empty support. `realizationSupport_bodyDebits` identifies
  the unchanged interpreter's support with the projected list's finite support.
  `body_realization_cost` applies unchanged `realize_run_cost` with zero
  unshared charge, for an arbitrary event word, including words with repeats.
- `body_realization_cost_of_nodup` and `_of_counts` establish equality with
  actual body-entry occurrences only under the explicit nonrepetition/count
  premise. `bodyAddresses_observe_nodup` invokes the raw
  `bodyEntries_observe_le_one` theorem under `ConfigBounded`, `FreshEntries`
  and per-address `NoMemoizeUnwind`. `body_realization_observe_cost` gives the
  corresponding interpreter equality for every actual observation budget.

No new machine evaluator, continuation interpreter, trajectory, graph or
resource execution function is introduced. Both the source observation and the
debit interpretation use their existing `Resources.run` implementations.

## Independent cases and their public connections

The expected source programs, captures and completion budgets predate this
bridge. Expected body order follows the actual sequence of forces, and expected
debit charges follow singleton-address union. These expectations were recorded
before any compilation of the bridge and must survive elaboration repairs.

| Case | Independent source account | Expected projected body list | Occurrences | Distinct support / interpreter charge |
| --- | --- | --- | --- | --- |
| Repeated force, budget21 | Allocate address0, enter it on the first force, cache its result and hit on the second force | `[0]` | 1 | 1 |
| Two identical thunks, budget34 | Allocate equal atom7 bodies with empty captures at addresses0 and1; force0 and then1 | `[0, 1]` | 2 | 2 |
| Handler inside the body, budget30 | Catch the raised packet above the memoize frame, return successfully, then hit the cache | `[0]` | 1 | 1 |
| Handler outside and retry, budget50 | Unwind address0's memoize frame without caching, then force the same still-uncached address again | `[0, 0]` | 2 | 1 |

`Examples/SuspensionBodyRealization.lean` consumes public source results rather
than reproducing their admission/freshness proofs:

- `Repeated.all_nodup` uses
  `SuspensionPureBodyCounts.Repeated.all_counts address budget` through the
  new count/Nodup equivalence. `Repeated.all_budgets` applies the new conditional
  debit equality. Its exact completed charge1 then uses the independently
  specified body list `[0]`, rather than independently evaluating the debit run.
- `Distinct.all_budgets` uses the public source `Distinct.all_budgets` bound
  for every address. `identical_thunks_distinct_charge` retains the public
  source witness that two actual cells hold identical code and empty captures,
  alongside the ordered list `[0, 1]` and the derived charge2. Code equality
  does not merge the two physical identities.
- `InternalHandler.all_budgets` similarly uses the public source bound. That
  source result proves the actual no-unwind premise while allowing its raised
  control under the body's own handler. The completed charge1 follows through
  the new conditional theorem and the independently expected list `[0]`.
- `ExternalHandler.not_nodup` applies the new equivalence in the reverse
  direction and contradicts its count consequence with the existing public
  `two_attempts_without_write` observation. The latter is the unchanged
  fifty-step body/write/hit2/0/0 case. The combined retry theorem retains all
  three counts, occurrence length2, support cardinality1 and interpreter
  charge1. Its charge uses the general arbitrary-word `body_realization_cost`
  theorem, which does not require Nodup. `no_unwind_fails` reuses the existing
  source proof of failure of the extra condition.

The positive source theorems already discharge raw boundedness and freshness
from the admitted finite pure source premises; they also prove no-unwind for
their particular executions. The bridge does not assume the desired source
bound, remove its finite execution witness, or infer no-unwind from purity.

## Statement review before compilation

This is the author's source statement review; elaborated-type inspection and
independent Standards/Spec outcomes remain root-owned validation/review work.

1. **Domains and quantifiers.** Generic projection/support laws quantify over
   all event words. The conditional raw observation law quantifies over every
   budget after taking actual valid/fresh/no-unwind premises. It does not assume
   termination or an initially unique pending stack. All addresses are natural
   physical addresses, not syntax classes, thunk payloads or event positions.
2. **Observation semantics.** The list filter selects only the `.body`
   constructor. It does not deduplicate the ordered projection. Selected-address
   counts agree with the existing actual body-event counts. The total observation
   counts occurrences by list length; its lift law confirms additivity across
   event concatenation. Finite-support cardinality is not claimed additive.
3. **Interpreter semantics.** Each body singleton carries the same address as
   its actual event. Non-body events have empty support and the selected
   interpreter has zero unshared charge. The general cost theorem therefore
   counts distinct addresses, including on repeated-address traces. Only the
   explicit count/Nodup premise permits replacing support by occurrences.
4. **Premise necessity and nonvacuity.** Positive source executions provide the
   premises at all budgets, including unfinished prefixes and absorbing suffixes.
   The internal handler permits raised control without memoize abandonment.
   The external retry preserves finite pure normal return while violating
   no-unwind and Nodup; zero cache writes do not establish body nonrepetition.
   Separate raw reentry/freshness and pending-frame cases remain in their owning
   local10022 modules, without modifications by this author.
5. **Meaningful reuse.** Positive charges depend on the new conditional bridge,
   which depends on public source body-count bounds. The negative charge depends
   on the unconditional support bridge. Exact ordered list reductions supply
   independent instance data; they are not substitutes for applying those laws.
6. **Scope.** Zero charges for non-body events select an observation; they do
   not assert zero runtime work. No unit cost for evaluating an arbitrary body,
   primitive cost, total transition-work bound, source operation-incidence graph
   or algorithm complexity theorem follows. This supports later local10017 but
   does not close it or advance chapter acceptance.

## Validation status and frozen files

No compiler, gate, stock hash adapter or proof audit was run by this author.
The parent's active seven-module focused input closure was left untouched.
Source-only inspection checked the referenced public declarations, ordinary
List/Finset facts, unchanged resource interpreter and the connected proof paths.
A lexical read found no admission, new axiom, unsafe/native proof shortcut,
proof-budget increase or linter suppression in the two new Lean files. This is
not a substitute for the required compiler, audit and independent reviews.

Frozen SHA256 values for the initial author handoff:

- `Applications/Suspensions/BodyRealization.lean`:
  `466774be79114b0f42ab391c3644681025cd4f106d9646b4c7aefc58e8491b2f`.
- `Examples/SuspensionBodyRealization.lean`:
  `42c57e3cc7a0dc989ac27678f1a75345b72c8b1ae7ba8d10baad7695e67865dd`.

Root must integrate both modules through the public entrypoint and obtain
their own focused evidence before the exact candidate's full build/audit and
independent review. Any concrete elaboration correction should preserve the
listed source cases and mathematical statements and be retained in this loop.
