# Chapter1 cost-model completeness addendum

Recorded 2026-11-02 before repair implementation. This supplements, and does
not overwrite, `chapter01-requirements.md` and the full request in
`../REQUEST.md`. It resolves the newly confirmed SPEC-001, SPEC-002 and
SPEC-003 source omissions. The existing Chapter1 equations, algorithms,
examples, proof audit and independent review requirements remain in force.

## Evidence, identity and validation boundary

Primary source: FDSA July27,2026 edition, printed pp.7–9; PDF SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The actual text is recorded by page in the local reading copy
`book-source/chapter01.txt`. The source explicitly asserts the three mathematical
comparisons below and explicitly declines a full compiler/runtime/hardware proof.

Frozen previous candidate: `1aabd512284fe86254278ac631eda061d311050b`.
Its active guarded check in `conaled-ch01-review` must remain unchanged. Even
success on that candidate cannot close Chapter1 while these findings remain.
The repair starts from that exact commit in a separate development worktree,
`conaled-ch01-cost-models`, branch `work/fdsa-basics-cost-models`. The original
review base remains `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.

Preserve historical source reviews and validation attempts. Review the full
repaired chapter against the original base plus this explicit addendum, on an
immutable committed candidate. No source/pin/checker changes are authorized in
the running validation checkout. Reuse its idle normal build cache only after
the current process has completed and its result has been recorded.

## SPEC-001: fixed-program coarse and refined tariffs

The book first counts each user-defined call entry, including terminal calls,
and assigns zero charge to local variables, primitives and constructors. It
then asserts that adding their unit charges changes asymptotic counts by at
most a constant factor, because each fixed defining equation has bounded local
work. Formalize that conditional argument rather than assuming a whole-run
inequality or asserting a machine-time theorem.

Required content:

1. Represent one actual finite trace of charged call occurrences and a
   nonnegative extra local charge attached to each occurrence. Reuse standard
   lists, sums and existing measured observations; do not add a second
   execution framework. The refined observation counts the same call entries
   plus those extras. State clearly how local work is assigned to its
   enclosing entry and when a root entry is included.
2. Derive `coarse <= refined <= (K+1)*coarse` from a per-entry bound by one K.
   K must be fixed independently of the completed trace/input. Retain empty
   traces and zero extra tariffs. The theorem may expose a uniform local bound;
   also justify such a bound from a finite catalogue of fixed-program local
   body cases, using standard finite maxima. This must not require a finite
   payload type or assume a bound on total work as a premise.
3. Derive the standard real-cast asymptotic comparison for arbitrary input
   families/filters under those uniform hypotheses. Preserve both comparison
   directions. Do not silently apply it after entry ticks have all been erased.
4. Connect a concrete source recurrence to this model. Append's branch trace
   has one cons event per input element and one terminal event. Its coarse
   observation must agree with the existing actual `appendRun` count. A
   concrete refined tariff may charge one local variable access in the empty
   branch and four local operations in the cons branch, giving `5*n+2` versus
   `n+1`; explain that this is an explicit illustrative tariff, not an asserted
   unique compiler instruction count. Prove the trace equations, exact counts
   and comparison through the general public results.

The finite local-body/charged-entry coverage premise is substantive. Variable
bit-width arithmetic, unbounded primitive work, external callback work and
other work absent from that catalogue need separate charges or bounds.
The source's finite-word/RAM rationale remains an explicitly conditional
interpretation, with no hardware stack postulated.

## SPEC-002: omitting nonrecursive entry ticks

1. Prove `T <= T+1 <= 2*T` for natural T with `1 <= T`, and retain the
   unconditional first inequality. Connect the added unit to existing
   `CallCount.tick_cost`; returned values must remain unchanged.
2. For a family of natural counts and an arbitrary filter, derive the
   `T+1 = O(T)` consequence under eventual positivity, using Mathlib's standard
   asymptotic interface and explicit real casts. The reverse upper bound is
   unconditional. Keep the zero qualification in the formal statement.
3. Retain a checked zero example showing that a positive constant cannot be
   bounded by any multiple of zero. Also show why non-identically-zero is too
   weak: for a family that is zero on even natural inputs and n on odd inputs,
   the unit-added family is not O(the original) at infinity. The source does
   not promise a uniform comparison on zero-cost inputs.

These requirements cover omission of the indicated entry charge at the
modeled boundary. If the repair also discusses transitively inlining a family
of definitions, it must supply the additional fixed-program coverage bound;
the one-tick lemma alone must not be advertised as such a compiler theorem.

## SPEC-003: a qualified shared-demand upper bound

The source says lazy evaluation may cost less than eager evaluation, but does
not define a lazy evaluator or explicitly name sharing. Give that claim a
precise call-by-need interpretation with a defined shared-demand model and
explicit correspondence assumptions. Do not identify unshared call-by-name
with this model.

Required content:

1. Use a finite catalogue of pure computations with stable occurrence/sharing
   identities and explicit measured results. The finite index is the eager
   execution catalogue, not the payload universe. Define actual request
   processing with a cache: the first uncached request stores its computation's
   value and charges its given modeled work; later requests for that identity
   return the stored value with no repeated computation charge. Reuse
   `Resources.Measured`, `Resources.run`, ordinary options/updates and existing
   invariant/potential laws where they fit.
2. Separate cache validity, returned-value correctness and cost accounting.
   Prove validity from an empty cache and preservation; prove every demanded
   observation agrees with the corresponding pure/eager value, including
   repeated requests. A theorem may state this through arbitrary request
   prefixes rather than storing an unnecessary output history.
3. Derive the work bound against the sum of eager catalogue work from the
   actual cache transition and at-most-once charging. Do not assume the final
   total-cost inequality. A remaining-work potential or an independently
   proved charged-event injection is an acceptable route. Finite work weights
   are nonnegative; retain the empty catalogue and empty request boundaries.
4. State the external-program correspondence required to apply this bound:
   requested identities refer to this eager catalogue, computed values are
   stable, and the catalogue's work observation matches the eager source
   count. The cache model itself does not establish that simulation for every
   program in an unspecified language. Cache lookup/update/administrative
   operations are not accidentally included in a nonprimitive-call count.
5. Include meaningful connected cases: repeated demand for one computation
   is charged once; an unused expensive catalogue computation is skipped;
   the same demanded values are retained. Include a boundary showing why
   unshared duplication is different. The recurrence for a duplicated
   let-bound recursive result has eager/shared call count `n+1` but unshared
   count `2^(n+1)-1`; a concrete instance or an explicit recurrence family must
   connect to the stated interpretation, without claiming automatic inference
   for Lean source syntax.

Keep operation, semantics and laws separate. No global inhabitance/order or
decidable equality on payloads is permitted merely to implement the cache.
Any equality/finiteness requirement on cache identities must be local to the
operation or proof that actually uses it. Do not import a separate unrelated
memoization library when the existing measured executor and standard maps
provide the required construction.

## Statement review, validation and completion

Develop connected cases with the generic results and record their independent
expected calculations. Review uniform quantifier order, satisfiable coverage
premises, zero-cost behavior, value/cost separation, pure-computation identity,
sharing and the exact modeled observation. No axiom, admission, unsafe proof,
partial definition or kernel-check bypass is permitted.

Update the Chapter1 source inventory and reconstruction map to replace the
earlier explanatory-scope dismissal; preserve the legitimate exclusion of a
verified physical execution stack. Integrate the new examples through the
public entrypoint. Focused builds and the full guarded candidate check/audit,
both independent review axes, and final candidate identity verification must
all cover the repaired candidate. No chapter or shared draft is accepted by
this addendum or by a source preflight alone.
