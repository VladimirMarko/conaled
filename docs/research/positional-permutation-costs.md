# Executed positional permutation costs

Issue #506 supplies the positional-selection part of #459 R7: actual measured
construction, exact ordered values, a fuel-free public executor, full-pair
adequate-fuel correspondence and complete inner-spine observation. Its growth
claims concern explicit source charges. First-equal removal and delayed
insertion remain separate work; #459 and #149 remain open.

## Sources and retained owners

The retained archive `docs/history/algorithm-design-haskell/checkpoint-233.zip`
has SHA256 `8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63`.
The following recovered files are under `project/adwh-lean/ADWH/Chapter02/`:

| File | SHA256 | Disposition |
| --- | --- | --- |
| `PermutationConstruction.lean` | `e1ee15e63282160fcd62a4e662f8e08aec53c7830c6fa3fa3b78fe83f30733f5` | Actual picks, callback-map/concat and adequate-fuel source execution retained through native operations. Public execution is now fuel-free and correspondence covers the entire pair. |
| `PermutationGrowth.lean` | `4f94b9a544b4508eaa6de1e46d3e08b912bfafb728a52dfbd56bed4be20f5453` | Construction bounds and shifted-factorial rejection retained with native finite sums, factorials and real-valued asymptotics. |
| `PermutationObservations.lean` | `94b631bcdd7668abaa117e1d2d91d3b7eec427497f7933a94e3501a82f3bc1d8` | Arbitrary complete-spine observer and positional composition retained. Its removal/insertion results remain outside this child. |
| `RemovalPermutationCosts.lean` | `3c1886fb82ddb27f728ab056310dfc8572567f4c937fcaa503f259d041423e75` | Varying callback reasoning informs the local adapter. Measured removal and erasure generation remain open. |
| `InsertionDemand.lean` | `3afb2552f449c9e140b4df4b679b48c365cbf43cf220e9ed1bb103e76ed77619` | Delayed construction, forcing and local sharing require a separate frozen demand contract. |
| `InsertionDemandGrowth.lean` | `67d1a2b7f68adb9a42bf8b74afa4693be07de83f8a9f28e5c102b1b84e025abd` | Delayed insertion growth remains dependent on its actual future execution/observation model. |
| `PermutationRationalBounds.lean` | `abf86d62c69e926cb409a3540208bb2f9e7538c0727b3d1db2bb61dab2413a05` | The positional rejection is expressed with native real-valued Big-O and its existing natural-coefficient characterization, covering every real comparison constant. No historical arithmetic wrapper is copied. |

These are source inspections, not a replay of archived proofs. Historical
checkpoint names do not dictate interfaces. The source's assertion about a
printed shifted-factorial estimate is not treated as verified book attribution;
printed-source coverage and licensing remain #149.

The unchanged [Occurrences](../../Applications/Sequences/Occurrences.lean) and
[Permutations](../../Applications/Sequences/Permutations.lean) own positional
choices, exact enumeration, independent `List.Perm` membership and factorial
length. The unchanged [pure examples](../../Examples/Permutations.lean) supply
the singleton/pair/triple equations reused in the new checked cases. The
resource layer does not become a dependency of these pure owners.

## Operations and charges

[PositionalPermutations](../../Applications/Resources/PositionalPermutations.lean)
uses native `Resources.Measured` and `bind`, `ListFusion.map`,
`ListFusion.concat1`, `ListAppend.weighted` through that concat, and
`ListExecution.foldl`. Its local `mapRun` executes a callback once at each
occurrence, records the callback's returned bill, adds two structural units per
outer cons and one terminal dispatch. `mapRun_native` proves exact full-pair
correspondence with `StructuredLinear.Costs.traverse` specialized to the
`outputWrite` coordinate, plus this structural tariff. The native traversal and
all structured-linear clients are unchanged. There is no new global traversal
owner or shared framework.

`concatMapRun` completes the callback map and then executes native concat on
the returned blocks. Native concat copies the left outer spines; it does not
charge complete traversal of each inner permutation. `picksRun` executes the
recursive positional choices and the native unit-price map. `generate` uses
those measured choices, recursive branch execution, native cons mapping and
map-then-concat. Attached membership witnesses justify decreasing lengths;
they impose no equality test on labels. These source charges do not count
Lean proof packaging, native allocation or elapsed time.

Let T(n) be the native finite sum of 1 through n. The checked identities are:

- Picks work is `3*T(n)+1`.
- C(0)=1.
- C(n+1)=(n+1)C(n)+5(n+1)!+3T(n+1)+5(n+1)+4.

`generate_work` derives this recurrence from the executed operations.
`generate_eq` combines it with the exact ordered pure enumeration. The recurrence
is not used as the executor's bill. `generateFuel_eq` proves equality of both
returned components for every fuel at least the input length, including excess
fuel. The public executor accepts no fuel; a checked zero-fuel singleton
counterexample explains the source interpreter's adequacy premise.

`observeSpines` runs an actual native inner length fold at every outer
occurrence. Its returned labels and line boundaries are unchanged. For arbitrary
`xss`, `observeSpines_eq` proves the complete pair
`(xss, xss.flatten.length + 3*xss.length + 1)`. Empty inner lists retain a terminal
fold charge. `flatten.length` specifies payload mass; no extra flatten pass is
executed. `observed` composes the generator and observer, with exact work
`C(n)+n*n!+3*n!+1`.

This observer counts constructors, not element evaluation or rendering. Its
charge differs from concat's `2*mass+2*outerLength+1` and #505's literal token
renderer. #505's insertion example observes already generated outputs; it does
not establish recursive generation costs.

## Growth and statement review

[PositionalPermutationGrowth](../../Applications/Resources/PositionalPermutationGrowth.lean)
proves `(5*n+1)*n! ≤ C(n) ≤ (20*n+1)*n!` for all natural n, then
`n*n! ≤ C(n) ≤ 21*n*n!` for n≥1. The complete observer has corresponding
bounds with upper coefficient 26. Native `Asymptotics.IsTheta Filter.atTop`
connects both actual execution costs to `n*n!`; input-family specializations
explicitly require length n. This premise has concrete witnesses, including
replicated Unit inputs, so duplicates do not make the claims vacuous.

`shifted_factorial_not_bigO` rejects an eventual upper bound of `(n+2)!` by
`n*n!` with arbitrary real coefficient, through the existing
`Resources.isBigO_natCast_iff` bridge. Transitivity gives the rejection for
construction and complete observation costs. This proves a model-relative
asymptotic obstruction, not an inference from small examples or a physical
runtime claim.

All generic execution/observation statements quantify arbitrary label types
and preserve occurrence order. No Nodup, decidable equality, canonicality or
nonempty premise is added to execution. Nonempty length appears only where
`n*n!` would otherwise vanish at n=0 while execution still has terminal work.
The work observation is Nat; equality of scalar totals does not establish
chronological trace equality or arbitrary fusion. Delayed forcing, memoization
and partial streams are not modeled by these finite executors.

The full-pair laws connect actual recursive output and bills. `generate_value`
uses the existing source equation, whose pure owner separately proves `List.Perm`
membership. `generate_length` reuses its factorial theorem, and
`generate_mass` derives complete payload mass from actual membership and lengths.
The observer's exact pair retains arbitrary nonuniform inner lengths and empty
payloads. The finite recurrence bounds are proved independently of particular
labels and transported through the execution equality.

## Checked cases and validation

[Examples.PositionalPermutations](../../Examples/PositionalPermutations.lean)
connects independently frozen values and charges through the public laws:

| Input | Construction | Complete construction plus observation |
| --- | ---: | ---: |
| `[]` | 1 | 5 |
| `[1]` | 18 | 23 |
| `[1,2]` | 69 | 80 |
| `[1,2,3]` | 274 | 311 |

The positional triple order is `[123,132,213,231,312,321]`, which differs from
insertion order. Repeated input `[1,1,2]` retains
`[112,121,112,121,211,211]` and construction 274. Function-valued labels are
checked by pointwise output observations without an equality instance.
`[[],[1,2],[]]` observes with charge 12 and retains both empty boundaries.
Varying callback bills on `[1,1,3]` retain repeated occurrences. Adequate and
excess fuel preserve the full result, while insufficient fuel does not.

The [runtime driver](../../scripts/PositionalPermutationsTest.lean) invokes the
actual public generator and observer, checks the literal fixtures, and compares
24 full pairs across six inputs and four adequate fuel choices. Its four-element
case has construction 1270 and combined work 1439. The initial missing-module
failure and empty-case green run are retained as development evidence; they
are not mathematical counterexamples. Focused compilation includes the connected
examples. Run inside the repository development shell:

```sh
lake build Examples.PositionalPermutations
lake env lean --run scripts/PositionalPermutationsTest.lean
```

The coordinator's immutable-candidate record owns the integrated guarded build,
exhaustive axiom audit and independent Standards/Spec acceptance. Focused checks
do not replace those gates. The public entrypoint imports the examples.

The accompanying edits reconcile only maintained family status and current
traversal guidance in the recovered handoff/research notes. Historical evidence
is preserved. Selected R1/R3/R5/R6 are accounted for; R2/R4 and removal/delayed
insertion residuals of R7 remain, alongside #149's wider obligations.
