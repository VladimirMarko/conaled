# Private allocation and observable effects

Root-owned work within local10014, fixed base69f6f00. This supplies the missing
private-allocation treatment in requirement8; it does not claim10019's pure
nonreentrancy result. Source: bookChapter4 force/delay observation, with the
AppendixA mutable memory semantics retained.

## Independent expected case before the theory

Start with an old reference at address0 containing5 and frontier1. A body that
updates that reference to7 and returns a freshly allocated reference containing9
returns address1 when run directly. Running it after creating the extra delayed
cell instead returns address2. The old reference must still contain7 in both
runs. The returned references must both contain9. Forcing adds its own private
cache at address1 in the second run. Literal result-address equality or whole-
memory equality would be false; matching allocation identities is required.

The intended relation fixes every old address below the original frontier and
shifts every later allocation upward by one. It renames addresses throughout
records, constructor payloads, closure captures and finite recursive bindings.
It compares memory at corresponding addresses and retains exception names.
The extra private cell is omitted from this comparison. Alias identity remains
observable because the address map is injective.

## Obligations and architectural fit

No source expression/pattern contains a literal runtime address. Primitive
operations may nevertheless expose one, so equivariance is an explicit law
separate from Machine.Parameters. Initial captured values must be fixed by
the chosen renaming; address bounds give a structural sufficient condition.
Reference writes, exceptions, nested allocation and SRec must be preserved by
the actual transition, rather than assuming body evaluation is memory-independent.

First stage: address/value/environment renaming and the existing Store actions.
Then actual transition/finite-execution transport using Progress.Evaluates.
Finally connect Derived's exact force/delay laws and an observable relation to
the independently computed effectful case above. No competing generic evaluator
or resource model is introduced. Extra operational steps remain visible.

Current status: all address-algebra, execution-transport and force-observation
modules and connected clients have successful focused checks. No full acceptance
evidence exists yet. The dated development rounds below preserve earlier states. The general observational result is not established merely by defining its
relation. No change to the default machine, no blackhole rule, and no implicit
purity assumption are authorized by this auxiliary proof.

## Draft statements and connected cases at checkpoint014

AddressRange.lean exposes effective lookup-based target membership and invariance
under Env.rec, including shadowed bindings. Renaming.lean drafts structural
value/environment relocation, lookup/extension/Rec laws, related Store replacement,
allocation and SRec, and the one-cell address shift. Relocation.lean drafts
all-control transition/event preservation and forward/backward finite-execution
transport with equal counts. These are conditional on the actual primitive
equivariance law, not on the desired body equivalence.

ForceObservation.lean drafts fresh private-delay initialization from bounded
memory and fixed initial finite cells/captures, then applies the execution
transport and Derived laws to normal and raised body runs. The result is a
related value and observable store, with explicit +12/+10 transitions. The
normal client is uniform over arbitrary closed bodies in empty memory, including
allocation/reference/recursive constructs when the given finite run exists.
It is not an unconditional termination theorem and not pure nonreentrancy.

The independently counted reference body takes13 transitions directly and25
through force-after-delay. Its general-transport client expects oldref0=7, new
returnedref1/2=9 and corresponding frontiers2/3. The reflection client uses
finite-execution uniqueness to retain13 body transitions. These are complete
proof-script drafts, not compiled claims. First algebra check is queued;
Relocation/ForceObservation have not yet been submitted for a focused check.

## First algebra compiler feedback

AddressRange compiled successfully. Renaming r1 ended exit1 with all tracked
inputs unchanged. Its mutual well-founded functions are not definitionally
reducible at symbolic constructors; the failed rfl scripts now invoke their
proved defining equations. Constructor-specific public simplification laws
also replace duplicate private clauses in Relocation. The two deprecated
if_pos/if_neg names are replaced by the pinned toolchain's ite_eq_left/right.
Operations, hypotheses and previously stated conclusions are unchanged. The
next focused algebra/client check remains required. Exact terminal evidence
is retained, and AddressRange is available to the Recursive worker unchanged.

## Capture-side-condition case before checking

Take empty memory (frontier0), the captured environment [(1,address0)], and
the body `read (variable1)`. The memory is bounded and every existing cell is
fixed vacuously, but this captured dangling address is not fixed by shift0.
The direct computation should fault with missingAddress0 after3 transitions.
Force-after-delay first occupies address0 with its private thunk, so the body
should fault with expectedReferenceValue after10 total transitions. The
reached memory is that just-allocated state. These cases test the necessity
of the capture premise; they are not a counterexample to the stated theorem.
No public conclusion or assumption is changed. Verification remains pending.

## Post-checkpoint015 statement review

The closed_value_observed helper actually quantifies over arbitrary bodies
started with empty memory and environment and assumes their given finite value
run. Its documentation now says exactly that: it does not require or prove a
syntactic free-variable closure judgment. This is a wording correction, not a
change to the already stated theorem or its hypotheses. The empty initial
environment discharges the capture side condition uniformly.

## Pre-compilation execution review

A separate read-only peer review checked all control/event constructors, shared
reference/thunk identities, exception-name freshness, fault address fields and
effective SRec targets. It found no missing semantic premise in the stated raw
configuration relation; the frontier inequality ensures future allocations
commute with the shift. It independently confirmed the13/25 normal,13/23 raised
and3/10 dangling-capture counts. This is statement review, not acceptance.

For the empty recursive-binding transition, the proof now explicitly obtains
the existing SRec transport law and normalizes its Rec/environment equations.
This avoids relying on conditional simp matching a WF-renaming equation
definitionally. The first focused Relocation check is still required.

## Algebra focused round2

Renaming.lean compiled successfully. The complete r2 target ended exit1 solely
because its shadowed-binding client listed an unused Env.lookup simp argument.
All recorded inputs remained unchanged. Removing that redundant argument
preserves every claim and default linter. Module transport laws are now checked,
but the connected client still needs a successful complete target. Relocation
r1 is queued against the unchanged compiled algebra; the client correction
is outside that frozen closure. Exact r2 terminal evidence is retained.

## Algebra clients verified; first execution feedback

Renaming r3 passed all745 jobs with every tracked input unchanged. The connected
old/new identity, nested closure and effective shadowed-target clients now pass.
The only change from r2 was removal of the unused simp argument.

Relocation r1 ended exit1 with unchanged tracked inputs. The new-exception
branch needs its already available state-update law normalized alongside the
goal. The large value classifier reached the unchanged default heartbeat
budget; its function application, branching and reference cases will be factored
into private lemmas with explicit source discriminants. Primitive equivariance
will be applied once in its actual operation branch, avoiding unrestricted simp
rewriting. A reserved binder spelling also needs correction. No operation,
public theorem, premise, expected count or proof limit changes.

## Execution transport round2 and correction

Relocation r2 ended exit1 with all tracked inputs unchanged. The new-exception
case and factored value cases checked except for one allocation relation that
needs its existing lemma supplied explicitly. Primitive application also had
one unused simp argument. The remaining large pattern classifier reached the
unchanged default heartbeat budget. Round3 factors its six discriminating
pattern cases into private source-first lemmas, supplies the allocation fact,
and removes the redundant argument. Public definitions, statements, premises,
counts and proof limits remain unchanged. This correction is submitted for
focused checking; it is not yet a passing execution-transport result.

## Execution transport round3

Round3 ended exit1 with unchanged tracked inputs. The value classifier and
five pattern helpers checked; exception-pattern classification still exceeded
the default budget because the source environment lookup was not discriminated
first. Record-pattern splitting also left impossible product/list shapes. The
next proof-only correction splits the actual looked-up exception binding first
and destructures record fields/pattern pairs before applying renaming equations.
No public statement, semantics, premise, expected result or proof limit changes.

## Runtime interruption and unchanged resumption

Round4's execution connection disappeared without terminal compiler feedback;
no matching task compiler remained on read-only inspection. Its preserved
record marks interruption, not proof failure or success. Round5 resumes the
identical source hashes and command. The same runtime event affected the
separate full prerequisite gate; its guarded incremental resumption is recorded
separately. No output hash, gate, source, proof budget or dependency was changed
to recover the connections. The cause is not established.

## Resumed execution transport result

Round5 terminated normally with exit1 and unchanged recorded input hashes.
Every remaining proof obligation closed; the only diagnostic is a redundant
local found argument to simp_all in the exception-pattern helper. Round6 removes
that argument, retaining all proof statements and default linters/budgets.
The full relocation client target still needs successful terminal evidence.

## Execution transport core checked

Relocation r6 checked the complete core module with unchanged inputs. The target
ended exit1 in Examples.SuspensionRelocation: initial configuration projections,
an ambiguous control name and concrete renamed-integer observations needed
explicit normalization. The core
transition/event transport and both finite-execution directions are now focused-
compiled. Root handed the unchanged expected reference client and subsequent
ForceObservation check to the shared worker; complete target success remains
required. The client problem does not change the public operation law or count.

## Complete focused chain passed

The shared worker corrected the client projections, qualified Relocation.control
and unfolded scalar/frontier wrappers at the concrete observation sites. The
Relocation example passed during ForceObservation r1; both ForceObservation
core and all clients passed r2,751 jobs, unchanged recorded inputs. The public
transition/event law, equal-count finite transport, normal/raised forward and
reflected force observations and13/25,13/23,3/10 clients are all checked.
See research/suspension-force-observation.md and its exact r1/r2 records.
These remain focused results, not whole-candidate build/audit/review acceptance.
