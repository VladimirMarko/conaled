# Exact transport-spine normalization

Issue [#283](https://github.com/VladimirMarko/conaled/issues/283) tests a small
optimization of native witness-sensitive derivative states. The transformation
combines the outer sequence of `Parser.transport` nodes into one node. Its
certificate is the composed witness isomorphism, with the source and result
languages retained in the type. It does not compare arbitrary parser meanings
or decide equality of functions.

## Existing behavior and selected boundary

`Parser.derive` already recurses through union, scale and transport. Its transport
case preserves the wrapper and restricts its isomorphism to the consumed prefix;
it does not fuse adjacent transports. An atom derivative introduces a transport
around scale/epsilon, and epsilon introduces a transport around zero. These
intervening constructors matter: this experiment only packs the outer transport
spine, stopping at the first other constructor. It cannot simplify every
transport introduced by atom, concatenation or nullable star derivatives.

The [implementation](../../Applications/Languages/DerivativeNormalization.lean)
structurally traverses that finite spine. `Packed` stores its original source
language, unchanged base parser and composite `Iso` to the result language.
`pack_base` proves the base has no outer transport; `normalized_depth` proves
the normalized parser has exactly one. This is the chosen representation
invariant, not a canonical form for semantic parser equality. The bounded
certificate is the finite traversed spine itself. Shape inspection is decidable;
no witness-bearing states are identified merely because their Boolean tests
agree. There is no key table or interning operation.

`normalize_exact` uses #276's identity and fusion equations to prove exact
`Decision (P word)` equality at every word. `contextual` applies #276's existing
finite-context theorem, retaining its language indices and bounded observations.
The [checked examples](../../Examples/DerivativeNormalization.lean) include a
nonidentity Boolean witness toggle followed by a product-field exchange. After
derivation and normalization, the result remains `(unit, false)`. Another case
uses the earlier star/concatenation/depth-restriction context. The previously
established Boolean-valid merge selecting different nullable witnesses still
fails after normalization.

## Operational experiment

`deriveCounted` follows the native derivative branches and counts each recursive
derivative invocation, including the outer call. `deriveCounted_result` proves
that its resulting parser equals `Parser.derive` for every native parser and
input symbol. `runWork` executes these instrumented derivatives in sequence;
it does not infer work from the number of syntax nodes removed.

`packCounted` records one event per inspected spine/base node and one per
composition closure. Its result is proved equal to `pack`.
`normalizationWork` adds one event for the final transport constructor, with
proved total `2 * outerDepth + 2`. This measures visits, composition closures and wrapper
construction in one explicit unit-cost model. It excludes evaluation of the
composed witness functions, whose chain has not been removed. `nodes` counts
retained parser constructors, excluding closure environments and proof terms.
These are logical cost models, not measurements of Lean time or heap usage.

Both starting states below are actual results of `Parser.derive true`. The
useful state comes from eight identity transports around universal; the adverse
state comes from bare universal. A common initial derivative produces the state
before the comparison starts. It costs nine calls in the useful case and one in
the adverse case, equally for each route. Normalization then runs once before
the indicated continuation. The baseline performs unchanged native derivatives.

| Derivative state and continuation | Baseline derive calls | Normalization events | Normalized derive calls | Baseline / normalized retained nodes |
|---|---:|---:|---:|---:|
| Eight transports, twenty symbols | 180 | 18 | 40 | 9 / 2 |
| Eight transports, one symbol | 9 | 18 | 2 | 9 / 2 |
| Bare universal, twenty symbols | 20 | 2 | 40 | 1 / 2 |

All entries and the strict comparisons are kernel-checked examples in the
normal integrated build. The longer transported workload saves modeled work
(58 versus 180); the short continuation loses (20 versus 9). Packing a state
without a transport adds a wrapper and loses (42 versus 20). The uniform
one-wrapper representation makes this adverse case explicit. It is not a
recommendation to normalize every state unconditionally.

## Consequences and remaining work

Exact witness preservation permits a useful syntax traversal reduction here,
without Boolean erasure. It does not eliminate the original witness-map
composition chain. Fewer retained parser constructors therefore do not prove
lower total memory or faster end-to-end parsing. No benefit is claimed for
nullable evaluation, final witness computation or arbitrary workloads.

The native parser API is unchanged. This opt-in operation supplies neither
sharing nor a cache lifetime policy; those require separate state ownership and
reuse contracts. General state interning would need decidable keys with proved
exact witness compatibility, which this experiment does not provide. #276
continues to own the reusable rewrite/context laws. [#235](https://github.com/VladimirMarko/conaled/issues/235)
owns the remaining interface question of when a certificate-backed normal form
and its construction cost justify adoption. Any broader optimizer must recover
these exact decisions and account for closure work as well as syntax size.
