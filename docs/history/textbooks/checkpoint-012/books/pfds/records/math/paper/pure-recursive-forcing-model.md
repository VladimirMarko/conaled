# Local 10019: first finite pure-model slice

Implementation base: `b422800fb5b6dc1253823057c0ea71644274d77c`.
Worktree/branch: `purity-foundation` / `pfds/pure-suspensions`.
Requirements version 1 and the existing parent-owned review loop apply.

## Scope and initial case obligations

The existing core values contain heap addresses and finite raw recursive
environments. They do not provide the immutable, memory-free suspension
meaning needed for the proposed no-reentry argument. The missing connection
is a finite representation in which repeated unrolling of one group member
has exactly the same body environment. No compiler failure is claimed as
evidence for that mathematical gap.

The intended first example is `f () = force s; s = $(f ())`. Looking up s in
the group must find a suspension with the original outer capture and the
same group descriptor; entering its body must find f with that same capture
and descriptor. An older binding of f must be shadowed, while an unrelated
outer binding remains available. This case makes no termination claim.

The second intended example is the body-produced closure for
`s = $(fn b => if b then 7 else (force s) true)`. Its ordinary capture must
contain the same suspension meaning, and following that descriptor must
recover the original body environment. It must not require a cyclic Lean
value or an acyclic raw cache. Actual execution and result 7 are later work.

## Interface decisions

`Pure.Syntax` defines effect predicates on existing `Core.Expr` and
`Core.Pattern`. They exclude reference expressions, reference patterns and
new exception generation. Fixed exceptions/handlers, recursive groups,
functions, data and suspensions remain. The primitive predicate is a selection
of operations, not an adequacy assumption. `force_allowed` and
`lazyFunction_allowed` concern only these effects; the existing static layer
retains the separate hygiene and typing conditions.

`Pure.Value` introduces only the two-form `Rhs` wrapper and finite
value/group representations. `Rhs.toExpr`/`ofExpr` preserve the original
source payloads, and `ofBindings` preserves order and reports the first invalid
RHS name. `Group.mk` contains these RHSs plus the earlier pure environment;
it contains no newly created members. `Group.members` constructs members in
reverse source order to match the actual creation fold, placing the same
descriptor in every closure/suspension. `bodyEnvironment` supplies member
bindings over the capture. Lookup laws expose this without requiring clients
to unfold the implementation.

The association-list helper is polymorphic so the same lookup handles RHS
wrappers and pure values. `lookup_eq_core` states its agreement with the
existing raw lookup. Source shape restrictions, binder uniqueness, nonempty
matches and type/name rules remain separate from effect predicates; a retained
example is effect-free but correctly rejected by the RHS decoder.

## Focused implementation status

The three owned Lean files and all retained value/effect clients passed their
focused target on 2026-11-02 at 20:25:41 UTC. This completes the first assigned
representation slice, not ticket10019 or candidate acceptance. There is no
running or queued compiler owned by this slice.

### Development evidence
The first focused wrapper (`suspension-pure-values-r1`) acquired the lock but
Nix stopped before Lean with unavailable `/proc/self/exe` inside the restricted
sandbox. Its tracked inputs were unchanged. The identical pinned offline
command and source ran as `suspension-pure-values-r1-retry` through the
established approved execution route. This was an environment startup failure,
not a failed mathematical case or a reason to change the statements.

The retry acquired the focused lock at 20:18:44 UTC and ended at 20:19:13 UTC,
exit 1, with every tracked input unchanged. `Pure.Syntax` passed in 11 seconds.
`Pure.Value` exposed only local decoder-proof issues: an unused tactic
combinator, an induction equation hidden by unfolding, explicit `Except.map`
reduction, and `List.Forall`'s True/conjunction representation. The descriptor
and value API had no reported errors. After checkpoint017 released its write
barrier, these proof scripts were corrected without changing any statement,
case expectation or API. The next coordinated batch will run the values client
first and the separate pure-machine client only if that succeeds.

The combined `suspension-pure-machine-r1` batch stopped at two residual Value
proof details, before compiling the machine: eliminating impossible decoder
equations had already closed some goals, and `List.forall_cons` needed to be
applied explicitly to the mapped source head. The corrections again retained
all statements and examples. The combined r2 batch acquired the focused lock
at 20:24:19 UTC with Value SHA-256
`4e18d73b7c6b40f18a9291297310d93643033160cd36e8b58b2083f1cde8b821`.
Its complete frozen-input record is in active-validation.

The r2 batch left only two successful-decoder inverse goals; their existing
constructor equality was transported through `Rhs.toExpr` explicitly. The
combined r3 batch then passed `Examples.SuspensionPureValues` (505 jobs;
`Pure.Value` 1.9 seconds, client 1.6 seconds). That target ran from
20:25:34.126792 to 20:25:41.829609 UTC with exit0. The shared worker's
`Pure.Machine` also compiled afterward, but its separate client had a name
qualification error, so the **whole combined batch** exited1. This does not
claim a passing result for that separate client. All recorded source/config
inputs remained unchanged through the batch.

The separate worker then qualified three `Group` type annotations in its own
example file. Its client-only r4 check passed from 20:26:23.550402 to
20:26:29.712249 UTC, exit0, with unchanged inputs (741 jobs; client 2.8 seconds).
The original expected execution counts were retained. Evidence is the separate
`suspension-pure-machine-r4` record/log; no owned value/effect source changed.

Evidence: `active-validation/suspension-pure-machine-r3.json` and `.log`,
including the per-target exit codes. The command used the exact pinned offline
Nix shell, `LEAN_NUM_THREADS=1`, a private project build directory and the shared
focused-build lock. The record marks acceptance false.

Final owned source SHA-256 values:

| File | SHA-256 |
|---|---|
| Pure/Syntax.lean | `57075f43a93a941144b656f73dd642926deb001c0324734b6243f7b02c4b469c` |
| Pure/Value.lean | `b02154383a7a00b1324ac8f85d1fb66ba7ee99e692c72118191c91e466ce2abf` |
| Examples/SuspensionPureValues.lean | `81c333becd68cbe9f6b3e1838eb56c2f56066b12cab0878382a86c93323ef46c` |

No public statement, expected client result, effect boundary or constructor
API changed during the proof corrections. No admissions, new axioms, proof
budget changes or linter suppressions were introduced. Parent-owned integrated
build/audit and review remain required; these focused checks do not replace
them. The current branch includes checkpoint017 draft commit
`6f2290f2ab916468d499e5de388ed7be7408dc96`; the final Value proof corrections
are ready for the next parent-owned commit/checkpoint. The fixed review base
remains `b422800fb5b6dc1253823057c0ea71644274d77c`.

No execution/bridge/no-reentry result is asserted. Root owns commits,
entrypoints, exact candidate validation, audits, reviews and checkpoints.
The separate pure-machine worker consumes the public representation API;
the root owns an all-outcome continuation-decomposition extension.

## Statement review and retained connections

* `Rhs.ofExpr_success_iff` covers exactly the existing `Core.RecursiveRhs`
  predicate; it imposes no nonemptiness or typing claim. `ofBindings_toBindings`
  and `toBindings_ofBindings` preserve the complete original source list, and
  `toBindings_names` preserves the original binder order.
* `Group.lookup_function` and `lookup_delay` expose the same original capture
  and descriptor. `members_names` records reverse creation order rather than
  silently imposing map uniqueness. `bodyEnvironment_lookup` and
  `bodyEnvironment_outer` state new-binding precedence and unaffected outer
  lookup. The mutual client uses these public laws, including an older
  shadowed binding of f and a retained unrelated outer binding.
* `mutual_round_trip` exhibits a concrete finite suspension/function capture
  and exact recovery of the original body environment. It has no termination,
  acyclicity or nonreentry premise and makes no execution claim.
* `cached_closure_backedge` exhibits the ordinary closure capture containing
  the same suspension descriptor and its exact recovered environment. The
  source function body is also admitted by the effect predicate. No claim is
  made that this representation fact alone establishes actual memoization.
* The fixed-exception client discharges the permitted pattern/expression
  constructors. A reference pattern inside a function clause is rejected,
  not merely direct reference expressions. The effect-free invalid recursive
  RHS is admitted by the effect predicate and rejected by the separate
  decoder, making the domain distinction concrete.

The primitive predicate still only selects operation names. A useful operation
implementation/interpretation and its compatibility proof are later work.

## Remaining bridge obligations

See `pure-recursive-forcing-feasibility.md`: primitive operations and their
interpretation must precede compatibility laws; the pure machine should reuse
`Progress.Evaluates`; actual recursive creation/closing must establish durable
group provenance and immutable address meanings; the finite-run bridge must
construct successful cache witnesses without assuming termination of unforced
thunks; each actual nested body entry needs a proper pure-run occurrence
certificate. Only after that bridge can count uniqueness establish actual
no-reentry and support separate cache/write-count corollaries.

Effect purity alone does not imply permitted recursive RHS shapes. For an
unsupported later RHS the raw machine retains earlier creation allocations,
whereas the memory-free decoder reports the fault without a heap. A bridge
must use an explicit permitted-RHS source premise, or represent those
abandoned fresh cells as unobserved garbage in its fault case. It must not
derive this source restriction from `ExpressionAllowed`.
