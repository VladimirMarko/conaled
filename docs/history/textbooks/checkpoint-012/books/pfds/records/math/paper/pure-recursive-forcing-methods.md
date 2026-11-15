# Pure self-forcing: proof-method investigation

Local ticket 10019 remains open. This is read-only method research, not a
formalization result or a change to the unrestricted machine. The obligation
comes from thesis Appendix A, printed p. 135 / PDF p. 147. It requires a proved
connection between an adequate pure domain and actual finite execution; a
nonreentrancy hypothesis cannot replace that connection.

## Primary sources inspected

Joachim Breitner's [2014 correctness paper](https://arxiv.org/abs/1405.3099)
reports a flaw in the original denotational correctness argument and two
repairs: explicit-stack operational semantics or a revised heap denotation.
This cautions against importing the original argument without checking its
heap-update invariant. The [AFP entry](https://isa-afp.org/entries/Launchbury.html)
provides Isabelle developments of correctness and adequacy. These are method
references, not Lean dependencies or evidence for our machine.

The inspected [Launchbury theory](https://isa-afp.org/browser_info/current/AFP/Launchbury/Launchbury.html)
uses a variable rule that removes the forced binding while evaluating its
expression and reinstalls its result afterward. That operational rule already
prevents a second lookup of the active binding. It differs from Appendix A,
which leaves the thunk available. A theorem about that rule alone therefore
does not settle the local obligation.

The [ResourcedAdequacy theory](https://isa-afp.org/browser_info/current/AFP/Launchbury/ResourcedAdequacy.html)
proves `add_BH`: under a finite-resource nonbottom hypothesis, deleting the
currently evaluated expression's binding preserves nonbottom evaluation.
Its argument uses the least demand, resource-restricted environments, and
heap fixed-point induction. The subsequent `resourced_adequacy` theorem
connects nonbottom resource semantics to the operational judgment. This is
a promising way to justify an auxiliary blackhole semantics rather than
assuming its equivalence to the source machine.

## Local proof obligations exposed by that approach

The intended pure domain must retain functions, finite data, recursive groups,
delays and forces, and enough primitives for the book's algorithms. Its
restriction must rule out mutable reference effects and observations of raw
allocation identities. Address-equivariance alone does not prohibit a
primitive that compares two addresses for identity. Exception behavior and
generative exception names also need an explicit decision and proof boundary.

A suitable semantic interpretation must account for finite captured and
recursive environments, private allocations, and completed cache writes. The
new address transport supplies an operational component, but its equal-count
simulation does not establish denotational adequacy or pure nonreentrancy.

An auxiliary evaluation with active thunks unavailable could support a
no-reentry theorem, but acceptance requires a bridge from the existing
machine's finite runs under the proved pure-domain invariant. The default
machine must remain unchanged, retaining the already checked effectful
reentrant examples. Counts for successful body evaluation and successful
memoization must be derived separately from the semantic bridge.

No method has yet been selected as a completed implementation. No source
coverage status, requirement, public theorem or acceptance result changes
on the basis of this investigation. Only links and this original method
analysis are preserved; no external paper or Isabelle source is vendored.

## Alternative constructive route to investigate

The following is original proof planning, not a result inferred from the AFP
formalization. A memory-free, non-memoizing interpretation could use the same
source Expr/Pattern syntax but represent a suspension as finite code, captured
environment and a finite recursive-binding component, analogous to the current
function-closure triple. Simultaneous recursion would place the original
creation environment in that third component rather than build cyclic Lean
values. Functions, data, branching, recursive groups and suspensions remain
available; purity must be a source/primitive restriction, not an assumption
that programs terminate or never force an active thunk.

An exact finite derivation in this interpretation could carry an unshared
evaluation count. Determinism would make both result and that count unique.
An evaluation of a suspension body containing a proper nested evaluation of
that identical body/environment would then contradict count uniqueness and
strict containment. This argument alone only proves the claim for the auxiliary
interpretation; it does not yet justify the heap machine.

The substantial bridge would attach an immutable pure suspension meaning to
each allocated address. A thunk cell must represent the corresponding body
and capture. A cached value must instead carry a finite pure evaluation witness
for that same meaning. A cache hit can be expanded by the retained witness,
and a successful cache write can construct its new witness from the body's
finite execution. Actual creation/closing must establish those meanings before
any recursive binding can be forced, then preserve them. The existing pending
Recursive proof is relevant to that obligation.

To infer absence of actual reentry, the bridge must preserve a raw body-entry
subderivation as a proper subderivation of the pure evaluation. Mere equality
of final values is too weak. Reentry of the same heap address must map to the
same pure body/environment throughout the enclosing evaluation; private fresh
allocations cannot silently change that identity. Cache expansion may add work,
so this auxiliary count must not be confused with machine transition counts
or the book's resource bounds.

This route would avoid importing a complete HOLCF model, but introduces serious
proof obligations of its own: simultaneous recursive capture, a stable store
representation through all pure transitions, deterministic exceptional/fault
behavior if retained, and a meaningful primitive law that excludes raw pointer
observations. None is discharged by this note. Before implementing another
semantic layer, compare it with the existing source-rule/continuation APIs and
exercise a representative mutually recursive suspension case. The explicit
effectful reentry examples must continue to lie outside the purity premise.

## Independent critique and finite group-descriptor repair

A separate read-only statement/design check found a concrete flaw in the naive
finite-triple proposal above. In `f () = force s; s = $(f ())`, interpreting the
raw function's recursive component pointwise would put the already-closed
meaning of s inside the group used to define that same meaning. This either
requires a cyclic Lean value or produces different nested environments on each
unrolling, invalidating the intended equal-input/count argument.

A proposed repair uses a finite GroupDescriptor containing only the original
source right-hand sides and the interpreted outer environment. It contains no
newly created member values. A members operation constructs each pure closure
or thunk with that same descriptor. Repeated unrolling then supplies the same
body environment literally. The raw closure's recursive component needs a
separate group-template representation witness from actual creation, rather
than ordinary pointwise value representation. The independent check found that
this repair handles the f/s example and the cached-recursive-closure example
below; it did not establish any Lean theorem.

Keep creation pending until the exact creation-only prefix and SRec closing
step establish the descriptor meanings, or compile those final meanings from
the entire group in advance with a separate pending-state invariant. Ordinary
cache validity cannot simply be assumed before closing. Group provenance must
survive later caching of its thunks; it must not require them to remain thunk
cells forever. Semantic-address-map extension must preserve earlier meanings.
The existing Static.HasType.recursive source rule supplies distinct binders
when that typing judgment is part of the pure domain; the unrestricted machine
still retains its effective-lookup semantics for raw duplicate bindings.

Cache validity may be established simultaneously with finite-run simulation by
induction on the actual derivation: obtain a pure body witness from the smaller
body run before recording it at the cache write. A cache hit can reuse that
already retained witness. Never assume terminating witnesses for every
unforced thunk, or use no-reentry to prove the very subderivation bridge meant
to establish it. The auxiliary derivation metric must give positive size to
every constructor so proper containment is strictly smaller.

Three proposed discriminating cases are the checked mutual f/s runtime case,
the nonterminating f/s group above, and
`s = $(fn b => if b then 7 else (force s) true)` evaluated by `(force s) false`.
The last has the independently expected type `s : Susp (Bool -> Int)` and
result7. Its first force caches a closure referring back to s; the later force
is a cache hit after completion, not active body reentry. It rules out a hidden
acyclic-cache assumption. This new example has not been implemented or checked.
These remain open design and proof obligations for10019, not accepted source
coverage or an alteration of the current effectful machine.

Purity must inspect patterns as well as expressions. A raw reference pattern
reads the shared cell and distinguishes an unforced thunk from a cached value.
Excluding reference allocation/read/write expressions alone misses that
observation in bind or clause patterns. Exclude reference patterns from the
pure syntax, or separately prove a store-kind typing invariant sufficient to
rule out this use; do not silently rely on the unrestricted extension's false
value-type preservation claim.
