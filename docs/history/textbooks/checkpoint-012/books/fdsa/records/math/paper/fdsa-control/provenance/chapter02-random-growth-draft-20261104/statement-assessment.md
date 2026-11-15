# RandomQuickSortGrowth: complete source statement assessment

Status: uncompiled source draft on fixed base
`c0440a99c2a503b7816a44367f7e4168378dbbf1`. This author assessment is
neither a compiler/type-inspection result nor an independent Standards or Spec
review. The parent owns all compilation, complete validation and acceptance.

The approved plan is the complete 393-line
`chapter02-random-growth-preparation-20261104/plan.md`, SHA-256
`8f9b2e960eda6e1563786f7941b412bd23f1390d40244b23c292cbed2ec83b96`.
The coordinator's full plan assessment found no mathematical issue and released
exactly two new source files. The author-start and alignment records identify
the fixed base and unchanged source dependencies. Rank and numerical modules
were still under first central compilation when the release was issued; no
dependency compiler/acceptance result is inferred here.

## Complete source scope

| File | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `Applications/Resources/RandomQuickSortGrowth.lean` | 203 | 9896 | `2b8bf7b4820790edaaa5726efb8e8bd8bccd3a30cb30388148d95bba00e63674` |
| `Examples/RandomQuickSortGrowth.lean` | 215 | 9959 | `2d173d7572ae76395c3779c216ea43d21719ff1774f6a7f21c68a5677b511a16` |

I read every declaration, every proof body and all 418 source lines. There are
17 public resource theorems and 14 public example theorems, with no private
declarations. The full source statements, namespaces, imports, line locations
and file hashes are in the adjacent `source-inventory.json`; that inventory is
source extraction only. Complete elaborated statements remain to be inspected
after the root's focused compilation.

The resource imports exactly the actual rank module, the separate numerical
solver and the inspected filter-atTop/Tendsto API. The example imports only the
new resource. Both files retain `autoImplicit false` and `warningAsError true`.
No existing source, root import/map, pin, linter configuration or cost definition
is changed. No build, cache operation or child agent was started.

## Resource claims: intended versus actual source

In the following table, T and F denote the existing actual `exerciseMean` and
`literalMean`; they are mathematical abbreviations in this report, not new Lean
definitions. The input comparator is exactly
`fun a b => decide (key a < key b)`. Input theorems retain independent
`α : Type u`, `κ : Type v`, only `[LinearOrder κ]`, and local
`hd : (xs.map key).Nodup`. Family indexing adds independent `ι : Type w`.

| Public resource theorem | Source contract and proof assessment |
| --- | --- |
| `sizeMean_eq_closedForm` | For every Nat n, the actual canonical mean equals the existing numerical closed form. The proof applies `QuickSortMean.eq_closedForm` with actual `sizeMean_zero` and `sizeMean_recurrence`, not new hypotheses. |
| `sizeMean_eq_harmonic` | Expands that exact equality to `8*(n+1)*H_n-12*n+1` in Real. Zero is included. Definitional unfolding of the existing closed form supplies the bridge. |
| `exerciseMean_eq_closedForm` | For arbitrary mapped-key-distinct xs, actual T equals `closedForm xs.length`. It composes the already derived actual input-to-size equality with the canonical solver result. |
| `exerciseMean_eq_harmonic` | The same actual input equality displays the harmonic expression explicitly. It retains the exact key predicate and original input; no sorted or resampled input is introduced. |
| `literalMean_harmonic_comparison` | The harmonic expression is ≤ actual F and F is ≤ twice the whole expression. The proof rewrites actual T in the existing same-run mean comparison. It does not assign F an exact harmonic formula. |
| `exerciseMean_le_log` | For length at least one, T ≤ `16*n*(1+log n)`. The proof rewrites to the closed form and applies its exact numerical inequality. |
| `literalMean_le_log` | Under the same hypotheses, F ≤ `32*n*(1+log n)`. Same-run F≤2T, positive multiplication by two and ring normalization preserve the actual append observation. |
| `exerciseMean_le_nlog` | For length at least two, T ≤ `16*(1+1/log 2)*(n*log n)`. The domain excludes the positive zero/one tariffs. |
| `literalMean_le_nlog` | For length at least two, F ≤ `32*(1+1/log 2)*(n*log n)`. The doubled constant follows from the actual same-run comparison, with no extra distributional premise. |
| `exerciseMean_le_nlogb` | For length at least two, T ≤ `32*(n*Real.logb 2 n)`. This is a real binary logarithm, not a rounded integer logarithm. |
| `literalMean_le_nlogb` | For length at least two, F ≤ `64*(n*Real.logb 2 n)`. It uses the actual append-inclusive F and the proven factor-two bound. |
| `sizeMean_isBigO_log` | Standard `Asymptotics.IsBigO Filter.atTop` for the actual canonical size sequence against real `n*log n`. Function extensionality rewrites it to the independently proved numerical bound after the actual recurrence connection. |
| `sizeMean_isBigO_logb` | The corresponding standard binary-log bound for actual `sizeMean`. The proof does not postulate any recurrence or introduce a new asymptotic predicate. |
| `exerciseMean_family_isBigO_log` | Arbitrary filter l and actual lists xs, eventual mapped-key distinctness and Tendsto actual lengths atTop imply Big-O of their actual T against their actual lengths times natural log. Explicit constant `16*(1+1/log 2)`; eventual length ≥2, actual mean nonnegativity and log nonnegativity remove the norms. |
| `literalMean_family_isBigO_log` | The same arbitrary-family contract for actual F with constant `32*(1+1/log 2)`. No payload measurability/finite enumeration or integrability of a family of payload-valued variables is required. |
| `exerciseMean_family_isBigO_logb` | Arbitrary-family binary-log version with constant 32. The denominator uses `(xs i).length`, not an unidentified or assumed-equal family index. |
| `literalMean_family_isBigO_logb` | Arbitrary-family binary-log version with constant 64, using actual F nonnegativity and the previously proved scalar literal bound. |

The 17 public resource contracts match the approved plan. No new public
recurrence hypothesis, payload instance, distinct-input averaging assumption,
sampler or alternative cost law occurs in these statements. There are no
private proof claims hidden from this assessment. The four arbitrary-filter
proofs are parallel norm-bound derivations from the inspected standard
`Asymptotics.isBigO_iff` interface. Their concrete Nat examples use atTop and
unbounded sizes; the general filter statement does not require an unnecessary
nonempty-filter premise.

## Example claims: complete assessment

| Public example theorem | Source contract, independent expectation and proof assessment |
| --- | --- |
| `empty_payload_means` | Actual Empty-payload input has exercise/literal means 1 and its exercise mean equals the displayed H_0 expression. The new input harmonic theorem is used with a constant Nat key; no pivot or default payload is constructed. |
| `singleton_payload_means` | Arbitrary payload/key types yield actual means 5 and 8 and literal sandwich `5 ≤ F ≤ 10`. The existing exact singleton mean laws discharge the consequential base case. |
| `empty_log_boundary` | For every real constant C, both actual positive empty means fail `C*(0*logb 2 0)`. No positivity restriction on C is needed because the right side is zero. |
| `singleton_log_boundary` | For every C, both actual singleton means fail `C*(1*logb 2 1)`. Arbitrary key/payload types remain independent. |
| `two_distinct_harmonic` | Actual reversed two-key input has T=13, `13 ≤ F ≤ 26`, and scalar upper bounds T≤64/F≤128. The new harmonic/sandwich and binary scalar theorems are all consumed. Loose literal bounds are not claimed equal to F. |
| `three_reordered_harmonic` | Actual `[2,0,1]` has T=71/3 and F between 71/3 and142/3. The expected T agrees with the earlier actual 21/25 distribution, but this proof checks the newly connected harmonic interface and mapped-key premise. |
| `four_tagged_harmonic` | Keys `[3,1,0,2]` with arbitrary payload tags have T=109/3 and F between109/3 and218/3. Mapped-key Nodup reduces only the Nat keys; no equality or order on tags enters the proof. |
| `five_sizeMean` | Canonical actual sizeMean5=253/5. The proof reduces the new actual harmonic theorem with the pinned rational harmonic successor law; the expected fraction was fixed independently. |
| `arbitrary_length_indexed_growth` | Arbitrary xs : Nat→Listα, key distinctness and exact length n give both actual binary-log Big-O statements in n. Tendsto length is proved by equality with id and the general family theorem is specialized. No hidden enumeration of payloads is needed. |
| `function_tagged_family_growth` | Full payloads are Nat paired with arbitrary Nat→Nat functions, selected by an arbitrary two-index tag family. Mapping the key projection returns List.range n, so only key Nodup and length are needed. The actual T and F both retain genuine Big-O conclusions. |
| `shifted_range_family_growth` | Actual input `List.range (n+2)` has bounds written in n+2. The proof derives Tendsto of actual lengths from eventual n≥b; it never replaces that length by n. |
| `equal_key_three_not_harmonic` | Distinct raw payloads `[0,1,2]` mapped to constant key7 have non-Nodup keys. The corresponding all-false actual comparator has T=25, different from the distinct-key harmonic expression71/3. All four facts occur in the public conjunction. |
| `equal_key_family_means` | Arbitrary tags under the constant-key/all-false comparator retain exact actual quadratic T=`2*n²+2*n+1` and F=`2*n²+5*n+1`. These are existing actual all-false theorems specialized without an extra universe or payload-instance restriction. |
| `equal_key_binary_bounds_fail` | Raw List.range256 is Nodup; constant-key actual T=131585 and F=132353. `Real.logb 2 256=8` is derived from the pinned power/self laws. Thus fixed distinct-key right sides65536 and131072 are strictly too small. It does not assert non-Big-O of a whole family from one finite counterexample. |

All 14 planned examples are present. The expected harmonic values were fixed
before proof: H_2=3/2, H_3=11/6, H_4=25/12, H_5=137/60, giving T=13,
71/3,109/3,253/5. The size256 calculation uses only actual constant-key mean
theorems and arithmetic/logarithm identities, not recursive evaluation of 256
random-pivot calls. Independent arithmetic is evidence for intended statements,
not a Lean compiler result.

## Boundaries and outstanding checks

The harmonic equality is for the Exercise 2.4 observation: actual empty cost1
and nonempty local filter/call toll4n−1. The append-inclusive observation charges
the existing two right-associated appends and is compared through the same
joint execution. The proof does not introduce an exact append expectation
formula. It does not charge uniform sampling implementation, random bits,
indexing/lookup/removal, allocation or physical runtime beyond the specified
call model.

The original algorithm still chooses fresh uniform occurrence indices at each
nonempty call and recursively binds its actual erased/filtered children. No
deduplicated pivot set, child-input resampling or unproved priority coupling is
introduced. The separate deterministic first-pivot average over uniformly
permuted input remains a distinct mandatory C02-024 obligation.

All existing rank, mean and numerical source identities, `lean-toolchain`,
`lake-manifest.json` and `AGENTS.md` were checked unchanged against
`author-start.json`. This preserves the official Lean/Lake4.35.0 profile, exact
Mathlib pin and disclosed native adapter. Nix alone is waived. The accepted
Chapter1 state is unchanged; no acceptance is claimed for the inherited
foundation candidate or any Chapter2 draft.

The author found no concrete mathematical source-contract discrepancy after
the complete readback. The source remains uncompiled. Possible elaboration,
simplification or linter findings must be recorded from the root's actual
focused result and repaired without weakening any statement. The parent must
inspect all31 full elaborated public types, run applicable complete candidate
check/audit gates, retain independent Standards/Spec reviews and perform the
immediate candidate verification before an accepted integration. Earlier
compiler failures and their terminal statuses remain preserved in their own
records; this source assessment supersedes none of them.
