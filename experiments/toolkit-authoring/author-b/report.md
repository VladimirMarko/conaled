# Independent author B trial

All four routes completed in the required order: B shared, B direct, A shared,
A direct. `Final.lean` is self-contained relative to its public imports and
passed compilation and `#audit_project_axioms`. It contains no admissions or
new axioms. The failed `Attempt01.lean` is evidence, not an accepted artifact.

The trial began at 2026-10-29 23:12:30 UTC, from the clock tool. The first final Lean
run finished at 23:15:14.447372 UTC. The corrected current-module audit
finished at 23:17:27.583679 UTC. Archiving and this report followed within
the 15-minute bound; `completion.json` records the end. The UTC date differs
from the repository's local-date context because the local timezone is Zurich.
The source revision was checked as `f071f18966d1ee875cdb5f328903d18a714732dd`.
The protocol SHA256 matched
`0b105d0877b81b88aa8777e98618be85b2af46edc9ba2f87a19c6604f1b84500`.

The exact assignment is in `prompt.txt`; the frozen protocol and every public
text exposed are preserved in `public-exposed/`, indexed with checksums and
partial-read boundaries in `public-exposed.json`. The public OrderedSummary
source, examples, and implementation record were read before writing the first
attempt. This exposure includes the existing DList specializations and the
library's own batch proofs. No other author's artifacts were read. Later routes
had exposure to earlier routes; their elapsed times are not independent causal
measurements of interface benefit.

The model and effort were inherited without override. Exact serving revision,
configuration, token usage, and pricing are unknown. No external model call or
nested agent was used. `help.txt` records the environment-only messages from
the coordinator, including the relayed audit-coverage diagnosis. There was no requested or received mathematical assistance.

## Attempts and validation

Each attempted source was written to a new file before compilation. None was
overwritten. Each `.json` records its exact command, source checksum, UTC start,
UTC finish, and Lean exit status; its separate `.log` contains raw merged stdout
and stderr. The Python runner's shell exit status is not the Lean status; use
the `exit` field in these records.

| Source | Change | Lean exit | UTC completion |
|---|---|---:|---|
| Attempt01 | B shared and all B cases | 1 | 23:13:30.431417 |
| Attempt02 | Repair invalid-cache negative example | 0 | 23:13:44.768855 |
| Attempt03 | Add B direct, retaining B shared | 0 | 23:14:12.000721 |
| Attempt04 | Add A shared | 0 | 23:14:28.254534 |
| Attempt05 | Add A direct | 0 | 23:14:46.393004 |
| Final | Add ProofAudit import and explicit type checks; local audit coverage later found absent | 0 | 23:15:14.447372 |
| Final-current-module | Identical source via stdin with virtual Examples filename; local coverage still absent | 0 | 23:16:48.314847 |
| Final-root-audit | Identical source under archive-local Examples path and explicit package root; local coverage confirmed | 0 | 23:17:27.583679 |

The first attempt failed because `simp [FreeMonoid.of]` in the invalid-cache
example recursed through the free-monoid simplification rules. The repair took
`congrArg FreeMonoid.toList` of the purported equality and contradicted the
unequal Boolean lists. No theorem statement or expected example changed.
One shell setup failure occurred before Lean was invoked: `python3` was absent
outside the Nix shell. `setup-failure.txt` preserves the command and output;
its exact event time was not exposed, so only a time interval is recorded.
Invoking the runner with `direnv exec . python3` repaired this failure.

The initial Lean command for each source is `direnv exec . lake env lean <source>`.
The corrected audit command adds `-R experiments/toolkit-authoring/author-b`
and checks `experiments/toolkit-authoring/author-b/Examples/ToolkitAuthorTrialB.lean`.
That source has exactly the same SHA256 as `Final.lean`.
`toolchain.log` and `toolchain.json` record the compiler query. The pin is Lean
4.35.0. Attempts imported only `Applications.Sequences.OrderedSummary`; the
final source additionally imports `ProofAudit`. Cache preparation and the
reported stale GraphEmission object repair were coordinator-owned. This author
ran no build command and changed no public source or interface.

The first audit's experimental module name excluded local claims from its
project-module filter, despite an exit-zero result. The coordinator relayed
this coverage issue; no proof source or contract changed. The preserved
`Final-current-module` stdin attempt also failed to supply a recognized module
identity, as its counts remained unchanged. Lean's `--help` documented `-R`;
using an archive-local `Examples` directory and that root supplied the required
module identity without writes outside the assigned archive.

The corrected audit covered 41,274 kernel-safe declarations and 23,076 theorem
declarations across 915 project modules. It explicitly reported
`Examples.ToolkitAuthorTrialB: 25 logical declarations; 20 theorem declarations;
0 unsafe runtime declarations`. These are the trial's five common definitions
and twenty named theorems. The transitive axiom union was exactly `propext`,
`Classical.choice`, and `Quot.sound`. `Final-root-audit.log` retains the complete
accepted audit output; `Final.log` and `Final-current-module.log` preserve the
prior insufficient-coverage runs. The early report asserted local coverage
incorrectly; this report corrects that assertion. This isolated experiment was
checked with focused commands, not presented as a new integrated-library
candidate or a fresh full repository build.

## Obligations and reuse

B uses one common set of definitions in both routes: `decode r = r.reverse`,
`push r a = a :: r`, `append x y = y ++ x`, `valid measure (r,m)` as cache
agreement, and `appendC` multiplying cached summaries in logical order.
There is no invariant restricting the plain lists.

B shared passes `True` as the representation invariant, discharges closure
with `trivial`, and discharges the observation equations using native reversal
laws. Empty and append validity come from `empty_valid` and `append_valid`.
The local equality-only cache predicate is converted to shared `Valid` by
adding `True`, and converted back by taking the second conjunct. `appendC` is
definitionally the shared `appendCache` at the local append operation, so no
conversion theorem is needed. `batch_decode` and `batch_summary` supply the
batch guarantees. `simp` removes the empty seed's observation.

B direct proves empty and cache append from reversal and primitive summary
laws. It generalizes the initial list accumulator and uses native list
induction separately for full decode and ordered summary. A direct uses the
same induction shape, replacing reversal equations with
`Batteries.DList.toList_push` and `toList_empty`. Neither direct namespace uses
shared validity, append, batch, or reachable-fusion theorems. A shared uses the
existing `dlist_batch_decode` and `dlist_batch` specializations directly.

The examples use `FreeMonoid Bool` with `FreeMonoid.of` as measure. This keeps
ordered words and requires no additive or commutative wrapper. Direct-route
helper theorems generalize the seed only to support induction; their public
empty-seed conclusions are exactly the fixed contracts.

## Statement review and cases

The explicit `#check @...` output in `Final.log` confirms arbitrary independent
universes for `A` and `M`, arbitrary measures, and only `[Monoid M]` for summary
claims. Full decode theorems do not require a monoid. No commutativity,
decidability, nonempty-input, or cache-validity assumption was added to the
batch theorems. The fold multiplies the running summary on the right by the
new measurement. Each full decode conclusion is equality to the entire input
list, independently of summary equality.

For B, cache validity is equality to the summary of the decoded representation.
The empty theorem supplies a usable inhabitant. Append assumes exactly cache
agreement for its two inputs, and combines `y ++ x` in storage with `m₁ * m₂`
in logical sequence order. The concrete append case starts with valid caches
for `[true]` and `[false]` and obtains the concatenated valid cache through the
route's append theorem. Reversal makes the resulting stored list
`[false,true]`, whose decoded order is `[true,false]`.

Every route has empty and two-element full-decode cases derived from its own
batch theorem, and empty and nonempty free-monoid summary cases derived from
its own ordered-summary theorem. The independent expected word is
`[true,false]`; the reversed word is proved unequal. Equal-length lists
`[true,false]` and `[false,true]` are proved distinct, so length does not imply
full sequence equality. In each B route, the cache with stored `[true]` and
cached word `[false]` is proved invalid. These negative cases test the limits
of observation and cache agreement without changing the positive contracts.

No runtime, allocation, bounded-storage, cost, new mathematical setting, or
broad model-capability conclusion follows from this completed local trial.
