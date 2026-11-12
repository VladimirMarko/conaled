# Executed first-equal-removal permutation costs

Issue #507 supplies the first-equal-removal part of #459 R7 after
[#506 positional execution](positional-permutation-costs.md). It executes removal
and recursive generation, preserves exact occurrence order, and derives finite
and asymptotic bounds from those operations. Delayed insertion and demand remain
open; this delivery does not complete R7, #459 or #149.

## Sources and retained interfaces

The archive `docs/history/algorithm-design-haskell/checkpoint-233.zip` has SHA256
`8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63`.
Its relevant recovered files are under `project/adwh-lean/ADWH/Chapter02/`:

| Source | SHA256 | Current disposition |
| --- | --- | --- |
| `RemovalPermutationCosts.lean` | `3c1886fb82ddb27f728ab056310dfc8572567f4c937fcaa503f259d041423e75` | Actual removal and varying recursive bills retained. Public generation is fuel-free; correspondence now covers the complete pair for all adequate fuel. |
| `PermutationObservations.lean` | `94b631bcdd7668abaa117e1d2d91d3b7eec427497f7933a94e3501a82f3bc1d8` | Removal composition reuses #506's complete inner-spine observer; insertion obligations remain separate. |
| `PermutationRationalBounds.lean` | `abf86d62c69e926cb409a3540208bb2f9e7538c0727b3d1db2bb61dab2413a05` | Native real-valued Big-O and the existing natural-coefficient bridge replace historical arithmetic wrappers. |

These are inspected source identities, not replayed historical proofs. Checkpoint
names do not dictate interfaces. Printed-book attribution and licensing remain
#149; the growth correction below concerns this declared source model.

The [pure permutation owner](../../Applications/Sequences/Permutations.lean)
retains `byErasure`, its ordered equation, independent `List.Perm` membership,
head law and missing-base counterexample. Its new `byErasure_length` proves
factorial output count without a Nodup premise or resource dependency.

[ErasurePermutations](../../Applications/Resources/ErasurePermutations.lean)
reuses `Resources.Measured`, bind, native cons map, and #506's `concatMapRun`,
congruence/attach bridges, constant-block length law and `observeSpines`.
`StructuredLinear.Costs.traverse` remains the shared varying-callback owner.
No new global callback interface is introduced. Positional execution and its
function-valued labels keep their existing equality-free APIs.

## Operations and exact bills

`removeRun` tests equality at each visited cons. Empty input costs one dispatch;
a successful comparison costs two units (dispatch and equality oracle); a failed
comparison copies that prefix cell after recursion and adds three units. It stops
at the first equal element. `removeRun_first` proves the complete returned pair
for a match after an arbitrary prefix containing no equal element: the prefix is
preserved, the first match is removed, and the bill is `3*prefix.length+2`.
`removeRun_absent` retains the input and bills `3*length+1`. Thus a successful
prefix of length k executes k+1 equality decisions; absence executes length
comparisons and a terminal dispatch. Later equal values are untouched.

Each equality decision is one oracle event. No bound is claimed for the internal
cost of an arbitrary `DecidableEq` implementation. Scalar charges do not measure
physical allocation, proof packaging, machine time or chronological traces.

`generate` visits each original input occurrence, executes its measured removal,
recurses on the returned shorter list, maps the chosen head onto every recursive
output, completes the measured callback map and then concatenates its blocks.
It has no fuel parameter. Membership witnesses and `removeRun_length` justify
termination. Empty input returns `[[]]` with bill 1.

`generate_value` proves exact ordered equality to `byErasure`.
`generateFuel_eq` proves equality of the entire measured pair for every fuel at
least the input length, including excess fuel. The bounded interpreter is a
source comparison; it does not replace public well-founded execution. Insufficient
fuel remains observable.

For nonempty input of length m, `generate_work_cons` proves:

```
work(xs) = sum (map (fun x => removeWork(x,xs) + work(erase xs x)) xs)
           + 5*m! + 5*m + 3
```

`subproblemWork` is that native occurrence-preserving map/sum, using actual
returned removal and recursive bills. There is no second callback-sum owner.
The recurrence is derived from execution, not substituted for it. Repeated
values retain repeated branches. Equal input lengths and even equal multisets
do not imply equal bills: [1,1,2] costs 243 while [1,2,1] costs 240.

Equal choices erase the same first equal occurrence, so exact enumeration can
differ from positional selection. On [1,2,1], erasure gives
[121,112,211,211,121,112]; positional selection gives
[121,112,211,211,112,121]. Both contain six occurrences. Equality of membership
would miss their ordered difference.

`observed` composes actual generation with #506's unchanged complete spine
observer. Every output has input length by the pure membership law; factorial
count therefore gives payload mass n*n!. `observed_eq` retains the exact ordered
values and adds `n*n!+3*n!+1`, including empty inner terminals. This is neither
label evaluation nor token rendering.

## Growth and statement review

[ErasurePermutationGrowth](../../Applications/Resources/ErasurePermutationGrowth.lean)
proves `(5*n+1)*n! ≤ work(xs) ≤ (20*n+1)*n!` at n=length xs from the exact
varying subproblem recurrence and removal bounds. For n≥1, coefficients 1 and 21
bound construction by n*n!; complete observation has upper coefficient 26.
The zero case remains explicit, since its terminal bill is nonzero while n*n!
is zero there.

`generate_theta` and `observed_theta` use native real-valued
`Asymptotics.IsTheta Filter.atTop` for any explicit input family of length n.
Replicated Unit and distinct `List.range` families demonstrate satisfiable
hypotheses. Duplicates require no special growth restriction. Transitivity with
#506's quantified shifted-factorial obstruction rejects `(n+2)! = O(cost)` for
both construction and complete observation, including arbitrary real comparison
constants. Finite fixtures are examples, not the basis of that rejection.

The execution theorems quantify arbitrary types with executable equality;
no Nodup, nonempty or canonical-representation premise is added to generation.
The no-equal-prefix premise in `removeRun_first` is exactly what makes the named
match first. `removeRun_absent` covers the complementary terminal behavior.
The decreasing-length proof uses actual measured remainder erasure, not an
unrelated list of the desired length. The adequate-fuel theorem compares both
values and bills, and the recurrence preserves input occurrences in its sum.

## Connected cases and validation

[Examples.ErasurePermutations](../../Examples/ErasurePermutations.lean) uses public
removal laws, the full-pair fuel bridge, value and observer laws, and growth
specializations. It retains duplicate enumeration, reordered-input cost
separation, positional-order separation, first/late/absent matches, inadequate
and excess fuel, empty generation and the missing-base distinction.

The [runtime driver](../../scripts/ErasurePermutationsTest.lean) executes both
public and bounded generators, checking five removal cases, nine generation and
complete-observation fixtures, thirty-six adequate/excess fuel pairs and three
separation checks. Its frozen expected bills are:

| Input | Construction | With complete spine observation |
| --- | ---: | ---: |
| [] | 1 | 5 |
| [1] | 16 | 21 |
| [1,2] | 62 | 73 |
| [1,1] | 59 | 70 |
| [1,2,3] | 249 | 286 |
| [1,1,2] | 243 | 280 |
| [1,2,1] | 240 | 277 |
| [1,1,1] | 231 | 268 |
| [1,2,3,4] | 1165 | 1334 |

The expected fixtures were computed independently during preparation from the
frozen removal/map/concat convention. Development logs retain setup and proof
failures; a missing object or blocked shell is not a mathematical counterexample.
Run focused checks inside the development shell:

```sh
lake build Examples.ErasurePermutations
lake env lean --run scripts/ErasurePermutationsTest.lean
```

The coordinator's immutable candidate record owns integrated guarded compilation,
exhaustive axiom auditing and independent Standards/Spec acceptance. Focused
checks do not replace those gates. The maintained ADWH status notes record this
selected removal delivery while preserving delayed insertion, R2/R4 and #149's
wider obligations.
