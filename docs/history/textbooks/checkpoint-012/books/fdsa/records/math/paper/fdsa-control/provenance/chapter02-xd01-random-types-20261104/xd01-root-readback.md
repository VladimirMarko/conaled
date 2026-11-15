# Difference-list costs: complete source and elaborated-type readback

Recorded 4 November 2026 by root, within the existing XD01 implementation/review loop.

**All 72 public declarations assessed, with zero concrete source/statement findings.**
Root read the complete 42-declaration resource source and 30-declaration example source,
all 72 explicit elaborated types, and each compiler-correction diff. This is an
implementation statement assessment, not an independent final review or acceptance.

## Exact candidates and closed evidence

The corrected minimal author candidate is 52722e3ee481167e99b8f6c0b2417df7fb7615d8.
Both Lean files are byte-identical in central checked candidate
dfaf68114d1dda4e15628c94c3d988c3f5457c49. Their identities are recorded below.
The two original independent source assessments concern original 62809ced; their
completed analysis and findings are retained, but they do not approve this successor.
Both axes still need the full-scope correction/integration and terminal-gate continuation.

The corrected four-target focused attempt 4 exited 0 in 9.201865451 seconds, with
clean unchanged HEAD. Its closed log has 4186 bytes and SHA256
514c8e71be97d10be7bb0c181e2dc3605423186b0adbfc085c122f63bee0896a.
The 134-declaration explicit inspection exited 0 in 13.325960255 seconds at the same
clean immutable candidate. Complete log 123793 bytes, SHA256
5027831298792411bde1622e6ad00aef816a0f0f41c97e372139eb8a47afe182.
Both secured native records are retained. This XD01 section contains 72 declarations,
36180 bytes, SHA256 987e4a4cd89fcaa821e0e8b628dcd6947d4571f39f737ad4f8b05573a2e2830e.
The inventory matches every output heading, with explicit arguments, full names
and visible universes. The other 62 declarations belong to the separate random-pivot
assessment. These are focused public-declaration counts, not exhaustive audit counts.

## Meaning, assumptions and implementation correspondence

Payloads remain arbitrary Type u. No order, equality, inhabitance, finiteness or
nonempty-output class was inferred. Rep quantifies over every supplied suffix;
AppCost is a separate all-suffix contract. Composition actually feeds g's returned
value to f. Creation captures the supplied callbacks and never pays for their
application or their earlier creation. buildFrom reuses the existing workload
executor, and build includes the one initial identity creation. Proof-only
normalization did not alter these operations, contracts or observations.

The tariff counts unfolded callback-invocation occurrences. It is not a claim
about compiler allocation, machine time, memoization or the number of distinct
shared descriptions. The doubled family makes this boundary explicit: linear
creation can yield exponential application work. Value equality with Batteries
DList append and fused push transports only values. Arbitrary extensionally valid
callbacks do not obtain an application bound from output length. The padded
empty-prefix family supplies a constructive counterexample for every affine bound.

All existing example conclusions were retained. General laws are consumed by
the concrete and polymorphic clients; the examples do not merely substitute an
independent evaluator. The source-scanner operational continuation remains separate:
it must relate its actual singleton-seeded callback history to prefix length and
include scanner/control/direct-constructor charges under its fixed tariff.

## Exact source identities

| Source | Lines | Bytes | SHA256 |
| --- | ---: | ---: | --- |
| `Applications/Resources/DifferenceListCosts.lean` | 222 | 10061 | `f99420b831dff2d0f5fcc3dac1001937942b87c78b710b79f94fa941ab972b01` |
| `Examples/DifferenceListCosts.lean` | 234 | 9299 | `df9936f23d5e60afd562b921d5b4ab0075fa58e7c91efcf92eddc33aa4d5e1a1` |

## Every resource declaration: 42 of 42

Each row was compared with its complete source/proof and explicit elaborated type; no finding was identified. Names have prefix `Resources.DifferenceListCosts`.

| Declaration | Assessment |
| --- | --- |
| `Builder` | Alias to an ordinary suffix callback returning the existing Measured list/Nat pair; arbitrary payload universe, no extra carrier or class. |
| `Rep` | Universal all-suffix ordered-prefix contract, independent of the supplied suffix and separate from every cost premise. |
| `AppCost` | All-suffix exact Nat application contract; no value representation or output-size implication is assumed. |
| `empty` | Charged value identity with one callback-entry observation. |
| `singleton` | One supplied payload is prepended; its charged entry covers the modelled local operation. |
| `compose` | Runs g first, passes its actual output to f, then charges the composition entry; no unrelated output is substituted. |
| `empty_apply` | Whole pair is (suffix,1) for every suffix, including uninhabited payload types. |
| `singleton_apply` | Whole pair is (a::suffix,1), with only the supplied element required. |
| `empty_rep` | The charged identity represents the empty prefix for every suffix. |
| `empty_appCost` | The identity application count is exactly1 for every suffix. |
| `singleton_rep` | The supplied singleton callback represents [a]. |
| `singleton_appCost` | Singleton application count is exactly1, with no suffix traversal charge. |
| `compose_value` | The value projection is f applied to the actual value returned by g. |
| `compose_cost` | Exact count is g(suffix).cost + f(g(suffix).value).cost +1; dependent callback input is preserved. |
| `compose_rep` | Two all-suffix value contracts imply prefixF++prefixG in that order; explicit witnesses and append associativity discharge the proof. |
| `compose_appCost` | Separate all-suffix contracts k and l imply k+l+1; the proof specializes f at the actual g output. |
| `createEmpty` | One closure-creation charge captures identity without applying it. |
| `createSingleton` | One closure-creation charge captures its supplied payload without applying to a suffix. |
| `createCompose` | One local creation charge captures the supplied f and g references without invoking or reconstructing either. |
| `createEmpty_eq` | Exact returned callback and creation count1. |
| `createSingleton_eq` | Exact singleton callback and creation count1. |
| `createCompose_eq` | Exact composed callback and creation count1, independent of application work or represented lengths. |
| `pushRun` | Actual bind creates singleton and then composition using the supplied seed callback. |
| `pushRun_eq` | The callback is compose f (singleton a), with creation count2. |
| `pushRun_rep` | Preserves the existing prefix and appends exactly the supplied element; no cost contract is required. |
| `pushRun_appCost` | The actual returned callback has uniform application weight k+2, independently of a Rep hypothesis. |
| `buildFrom` | Runs the existing push workload from an already supplied seed; seed creation and generic traversal overhead remain outside this observation. |
| `buildFrom_nil` | Returns the unchanged supplied callback and count0. |
| `buildFrom_cons` | Recurses on the callback actually returned by the first push, retaining its count2. |
| `buildFrom_cost` | Construction is exactly2*length items for every supplied callback; it never invokes that callback. |
| `buildFrom_rep` | The returned callback represents pref++items under only the supplied seed Rep contract. |
| `buildFrom_appCost` | The returned callback has all-suffix count k+2*length items; the corrected induction normalizes the same successor arithmetic. |
| `build` | Includes exactly one initial identity creation before the existing push execution. |
| `build_cost` | Exact construction count2*n+1, including n=0. |
| `build_rep` | Represents precisely items, with no payload typeclass or list-order requirement. |
| `build_appCost` | Every suffix application costs2*n+1; this is a property of this construction, not arbitrary represented callbacks. |
| `toDList` | Uses the actual callback value and its all-suffix Rep witness to construct the existing Batteries DList; no cost is transported. |
| `toDList_apply` | DList application returns exactly the callback value at the same supplied suffix. |
| `toList_toDList` | Empty-suffix materialization returns the represented prefix. |
| `toDList_eq_ofList` | Equality in Batteries DList is an extensional value correspondence, not equal construction or application cost. |
| `toDList_compose` | The erased actual composition equals ordered DList append of the erased inputs. |
| `toDList_pushRun` | The erased actual returned push callback equals Batteries fused push as a value; its different execution tariff is not equated. |

## Every connected example declaration: 30 of 30

Each row was compared with its complete source/proof and explicit elaborated type; no finding was identified. Names have prefix `Examples.DifferenceListCosts`.

| Declaration | Assessment |
| --- | --- |
| `ordered_composition` | Public Rep and AppCost composition laws give ([1,2,9],3); order and count are independently observed. |
| `standard_composition_value` | Arbitrary valid callbacks connect the composition result to existing DList append, preserving prefix order. |
| `expensive_capture` | For arbitrary p,q, creating a composition costs1 while its application costs p+q+1; the callbacks are concrete supplied measured identities. |
| `materialize` | Actual build result is invoked once at the supplied suffix through bind. |
| `materialize_eq` | Public construction, Rep and AppCost laws give (items++suffix,4*n+2) for every payload type and suffix. |
| `construction_application_split` | Separately exposes the two exact counts2*n+1; neither is inferred from value equality. |
| `materializeTwice` | One construction followed by two actual invocations at independently supplied suffixes; returned lists remain separate. |
| `materializeTwice_eq` | Public laws give both ordered values and total6*n+3, including the zero-item case. |
| `duplicate_values` | The actual three-item client preserves both copies of3 and yields [3,1,3,9] at count14. |
| `duplicate_values_twice` | Both different suffixes survive, with count21 after one construction and two applications. |
| `empty_payload_boundary` | Empty payload type requires no inhabitant: one materialization costs2 and two cost3. |
| `singleton_boundary` | A supplied singleton plus any suffix yields a::suffix at count6. |
| `extendSingleton` | Uses an already supplied singleton seed; that seed creation is deliberately outside the client boundary. |
| `extendSingleton_eq` | Public seed build laws give ((a::items)++suffix,4*n+1); source use must separately include actual initial creation. |
| `fused_push_value` | The actual explicit-model callback and Batteries fused push return the same list; no cost correspondence is asserted. |
| `identity_value_cost` | Composing on the right with charged identity preserves values but adds exactly2 callback entries. |
| `padded` | A finite history grows by composing charged identity while retaining empty represented output. |
| `padded_rep` | Every such history represents []; uses the public representation composition law. |
| `padded_appCost` | Every suffix costs2*n+1; the result follows the actual composition recurrence. |
| `padded_empty_value` | All histories erase to the same empty DList materialization. |
| `no_bound_from_output_length` | For every affine constants K,B an explicit history n=B+1 exceeds K*0+B; the premise is nonvacuous even for Empty. |
| `doubled` | One captured callback is used twice by each new composition; description sharing does not memoize later invocation. |
| `doubled_creation` | Exactly n+1 creation events, including the initial identity. |
| `doubled_rep` | All doubled callbacks still represent the empty prefix. |
| `doubled_application_add_one` | Actual invocation count plus1 equals2^(n+1), with induction specialized to the actual inner output and arbitrary suffix. |
| `doubled_appCost` | The exact all-suffix count is2^(n+1)-1; the preceding equation justifies Nat subtraction at n=0 and beyond. |
| `materializeDoubled` | The callback returned by actual shared construction is applied once to the supplied suffix. |
| `materializeDoubled_eq` | Value is the original suffix and total creation/application count is n+2^(n+1). |
| `four_shared_closure_extensions` | Concrete n=4 uses public laws: creation5, invocation31, value[9]. |
| `four_shared_closure_extensions_materialized` | The connected client combines those observations into exact total36. |

## Findings and remaining gates

XD01-DOC-001 remains fixed in the retained original provenance correction and
independently assessed source reports. Compiler findings XD01-ELAB-001/002/003
are preserved with their actual failures and proof/binder corrections. Explicit
bare reserved binders were renamed without changing quantifier meaning; one
arithmetic step and explicit representation witness applications repaired proof
elaboration. The successful focused/type results now cover those exact bytes.

Root's attempt 2 invocation incorrectly supplied literal HEAD to a recorder
requiring a full SHA; the unchanged guard rejected it before a compiler launched.
Attempt 3 included a nonexistent Sorting target for the random module; its actual
aggregate exit 1 remains recorded, despite successful requested XD01 builds and
random example build. The corrected exact-target attempt 4 passed. Neither
bookkeeping error was treated as a mathematical failure or bypassed guard.

No new source/statement finding remains from this 72-declaration assessment.
Whole-candidate integrated validation, exhaustive proof audit, exact minimal
integration conflict review, both independent full-scope review outcomes and
immediate qualified candidate verification still precede acceptance. The accepted
Chapter 1 ref and pending exact foundation candidate remain unchanged.
