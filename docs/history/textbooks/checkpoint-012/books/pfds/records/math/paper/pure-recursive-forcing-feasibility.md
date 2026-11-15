# Local 10019: feasibility of the finite pure interpretation

This is a design investigation following the version-1 requirements and
`pure-recursive-forcing-methods.md`. It is not an acceptance review, a
no-reentry theorem, or a change to the unrestricted suspension machine. The
first implementation slice was subsequently authorized in the separate
`purity-foundation` worktree from fixed base
`b422800fb5b6dc1253823057c0ea71644274d77c`.

## Recommended pure boundary

Use predicates on the existing `Core.Expr` and `Core.Pattern`, retaining
atoms, variables, ordinary constructors, records, ordered functions and
matches, application, bindings, branches, simultaneous recursive groups,
delay and suspension patterns. Retain fixed exception constructors, raising
and handling: deterministic exceptional evaluation is useful and need not be
confused with mutable or generative effects. Derived `force` and the book's
`lazyFunction` should inherit these predicates.

Exclude reference allocation, read and assignment expressions; exclude
reference patterns everywhere, including clauses and nested patterns; exclude
`newException`. The reference-pattern restriction is essential because the
raw machine reads the same heap and can distinguish an unforced thunk from a
cached value. Restricting expressions alone misses that observation.

Keep source well-formedness separate from this effect predicate. In particular,
permitted recursive RHS forms, distinct recursive binders, nonempty function
matches, record/binder uniqueness and identifier classification are not the
definition of absence of effects. Existing static derivations can discharge
many such obligations for clients. Neither purity nor well-formedness should
assume termination, acyclicity, guardedness or absence of active reentry.

The minimum useful basis supports deterministic arithmetic and comparison on
finite first-order data; higher-order algorithms and comparison functions can
be expressed with source closures. A later basis operation and interpretation
must come before its compatibility law. A concrete first-order adapter can
decode atoms/constructors/records, reject nondata inputs deterministically, and
return encoded data or fixed exception packets. A more general adapter can
use a value-representation compatibility law quantified over immutable
meaning maps, including maps that identify distinct raw addresses. Merely
assuming `Relocation.Equivariant` is insufficient: pointer equality can satisfy
renaming equivariance while observing sharing. A law that only preserves
address bounds is also insufficient.

Initial environments and the reachable suspension portion of memory need an
explicit representation invariant. The empty-memory, pure-basis environment
specialization should be immediate; an eventual generic theorem may leave
unrepresented, unreachable cells outside its footprint. All executable code
in represented closures and thunks must satisfy the effect predicate. No
global type-preservation theorem for the published effectful extension is
available or needed for this boundary.

This domain contains recursive functions over finite data, lazy streams and
recursive suspension groups. A productive cached value may refer back to its
own suspension. The domain is substantially larger than a literal-only or
acyclic fragment.

## Finite descriptors and stable identity

The proposed finite group descriptor contains only the source binding list
and an interpreted outer environment. It must not contain the newly created
member values. Pure function and suspension values can each retain an optional
descriptor. `members group` constructs finite member values carrying that
same descriptor; the body environment is the group members overriding the
captured outer environment. This mirrors the raw `Env.extend` lookup order.

Ordinary closures/thunks retain their finite captured environment and no
recursive descriptor. Functions or thunks created while executing a group
member can capture already constructed member values; this remains finite.
Repeated use of the same recursive member produces literally the same body
environment, rather than successively larger nested recursive environments.

For the raw correspondence, recursive closure components need a separate
group-template/provenance relation. A raw closure's third component is the
original created environment, not an ordinary pointwise interpretation of
already closed members. Provenance records the source group and outer capture
and remains valid after group thunks have become caches. It cannot require
those addresses to stay unforced forever.

Creation should remain a pending phase until `create` and SRec closing have
finished. `Recursive.evaluates_iff` exposes exactly that creation-only prefix,
so no ordinary body simulation is needed during pending creation. The new
meaning map can be extended with all final group meanings at the close. The
construction must prove that older meanings are unchanged and only freshly
allocated group cells are closed. Existing `Closes` supplies the concrete
store equations; it does not itself provide semantic group provenance.

Discriminating clients for the first slice:

1. `f () = force s; s = $(f ())`: both directions of the mutual dependency
   unroll through one finite descriptor. No termination claim is made.
2. `s = $(fn b => if b then 7 else (force s) true)`: the value cached by its
   first force is a closure referring to `s`; the later force during the
   function call is a completed cache hit, not active body reentry. The first
   slice should check the finite representation and stable environments;
   execution and result 7 belong to the later machine/bridge slice.
3. A productive cyclic stream shape, with a constructor containing a delayed
   tail, is a useful later discriminator against accidental acyclicity.

## Reuse `Progress.Evaluates` for the pure machine

A domain-specific nonmemoizing transition over these pure values is a good
fit for the existing `Progress.Machine` and `Progress.Evaluates`. It has no
mutable store and never changes a suspension value into a cache. Forcing
evaluates the suspension's fixed body environment every time. Its transition
must reproduce the inherited strict order, ordered matching, exceptions and
faults of the allowed core.

`Progress.Evaluates.unique` then supplies both final-answer uniqueness and
exact transition-count uniqueness. This avoids a competing generic evaluator
and a separate generic determinism development. The pure count is an auxiliary
unshared execution count; it is not the raw machine count or a source cost
bound. Expanding a raw cache hit can add arbitrarily much pure work.

A counted source natural-semantics/certificate layer can expose the nested
expression, pattern and clause evaluations of the two machines. Its public
meaning must remain connected to actual `Progress.Evaluates` runs. The current
`Correspondence.evaluation` and `matching` predicates existentially hide their
transition counts, so they are useful semantic views but do not yet supply
the decreasing measures or occurrence correspondence needed here.

## Non-circular bridge

Define the pure transition first, independently of any heap-validity relation.
Then attach an immutable pure suspension meaning to every represented raw
address. Raw addresses need not have distinct meanings.

For an unforced cell, validity states that its code/capture represent the
fixed meaning's body/environment. It does **not** require a terminating pure
body evaluation. For a cached value, validity includes a finite successful
pure body run for that same meaning and a representation of its result.
Representing a raw address consults the immutable meaning map rather than
recursively reading the current cache. Thus cached values can contain
backedges without cyclic proof terms or an acyclic-cache premise.

Prove finite-run interpretation and preservation of cache validity together,
by induction on the actual finite run/counted decomposition. An uncached
forcing rule uses the smaller actual body run to construct its pure witness,
then installs that witness when the actual successful write occurs. A cache
hit expands the witness already retained in the incoming invariant. A failed
body does not install a successful cache witness. This does not assume every
thunk terminates or that the run was nonreentrant.

Do not demand that active cells remain thunks while proving this bridge:
that would smuggle the desired conclusion into its invariant. The intermediate
invariant can permit an inner successful write, and even an outer overwrite,
provided each cache carries its own derived pure witness. No-reentry is a
later consequence of the occurrence argument and count uniqueness.

The bridge needs an explicit occurrence certificate: each actual unforced
body entry occurring during an enclosing actual body evaluation must map to
a proper nested evaluation of the corresponding pure body. The certificate
must retain strict pure-count decrease, including across clauses, exceptions,
and recursive creation macro steps. Equality of final values alone is not
sufficient. A cache expansion adds pure work without creating a raw body-entry
occurrence, so raw and pure event lists must not be equated.

If address `a` is entered while its earlier `.memoize a ...` frame is still
pending, immutability and provenance identify the two pure body/environment
inputs. Proper nesting makes the inner pure count strictly smaller, while
`Progress.Evaluates.unique` makes the two counts equal. This contradiction
would prove the desired actual no-reentry statement for finite completed
runs. A later prefix corollary can state that a reachable reentry cannot have
a finite completion. It should not assert that no divergent run ever reaches
a reentry configuration.

## All-outcome continuation splitting

The existing `Machine.evaluates_split` assumes a delivered boundary for the
whole answer and therefore excludes final `.stuck` answers. This is a real
decomposition gap if the new theorem covers all raw finite outcomes. Avoid
filling it with assumed type safety.

The proposed extension suffices if it concludes either:

* an isolated stuck run, with exactly the same whole answer and count, for
  which appended frames are never resumed; or
* an isolated delivered boundary (`value`, `raised`, `matched` or `mismatch`)
  followed by the caller run, with the existing count equation
  `total = (isolated - 1) + residual`.

In the second case the resumed caller may itself become stuck. The cases are
not distinguished merely by whether the final answer is stuck. Existing
`step_append`, `step_boundary` and `step_stuck_append` give the needed local
facts. This extension resolves boundary decomposition, not the separate
occurrence-preserving body-entry certificate.

The result correspondence must also state its fault mapping. For example,
the raw machine calls forcing a nonaddress `expectedAddress`, while the pure
machine can call forcing a nonsuspension `expectedSuspension`. These are
corresponding failures, not literally equal values of one fault datatype.
Missing raw addresses should be excluded by the represented-address/store
invariant rather than by assumed type preservation.

## Exact existing public results to reuse

* `Progress.Evaluates.unique`, `search_sound`, `search_complete`: deterministic
  finite runs and checked finite clients. Fuel exhaustion remains unknown.
* `Machine.body_transition`, `hit_transition`, `memoize_before_match`,
  `raised_skips_memoize`: actual entry, cache and exceptional boundaries.
* `Machine.evaluates_append`, `evaluates_split`, `step_stuck_append`: existing
  continuation composition/decomposition and the all-outcome extension basis.
* `Correspondence.suspension_match_iff`, `matching_cached_iff`,
  `alternatives_iff`: already connected source forcing and ordered alternatives.
* `Recursive.create_exists`, `create_preserves`, `CreatedThunks.targets`,
  `close_correct`, `enter_body_prefix`, `evaluates_iff`,
  `realizes_recursive_binding`: actual creation, readiness, closing, and the
  exact `3 * bindings.length + 2` prefix.
* `Env.lookup_rec`, `rec_closure`, `rec_address`, `lookup_extend`, and
  `mem_addressRange`: the raw finite Rec and lookup algebra.
* `Return.expression_result`, `pattern_result`: control-result classes,
  explicitly not value-type preservation.
* `Machine.start_evaluates_bounded`, `evaluates_domain`, plus
  `Suspensions.allocate_extends`, `delay_captures`, `memoize_other` and
  `srec_other`: allocation/domain facts and unchanged cells.
* `Static.HasType.recursive`, `RecursiveBindingsHaveType.domain`,
  `force_type`, `lazyFunction_fresh_type`: source-valid typed clients and
  explicit freshness/scoping conditions, not unrestricted dynamic safety.
* `Renaming.MemoryRel` and `Relocation.evaluates_forward/backward`: useful
  address transport. They do not establish the pure interpretation or exclude
  pointer observations.

## Separate consequences and implementation readiness

After the bridge/no-reentry theorem, derive successful-cache stability and
successful write counts separately. In a pure run, allocation cannot reuse an
old address, later SRec closes only newly created group cells, and no reference
write is permitted. Together with no active reentry, a completed successful
write can therefore prevent later body entries at that address. Repeated body
exceptions may still be evaluated repeatedly, and separate delays still
allocate separate cells. Do not claim equal heaps/traces from equal values.

The first authorized slice is concrete enough: effect predicates, finite
values/descriptors, stable member/body-environment equations, and the two
recursive representation clients. It should make no primitive adequacy,
machine simulation, no-reentry or ticket-completion claim. Remaining work is
the pure transition and basis interpretation, persistent raw group provenance,
counted all-outcome decomposition, the simultaneous cache-validity/finite-run
bridge, explicit body-entry occurrence certificates, and the resulting actual
no-reentry/resource corollaries. The unrestricted effectful machine and its
existing reentrant examples remain intact.
