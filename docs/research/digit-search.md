# First-hit inspection and the finite decimal mean

[#478](https://github.com/VladimirMarko/conaled/issues/478) connects actual
left-to-right search to a complete finite-uniform decimal population.
[DigitSearch](../../Applications/Resources/DigitSearch.lean) uses existing
measured pairs, native List.findIdx?, native List.pi and SquareKit.FiniteSums.
The [frozen contract](digit-search-contract.md) and
[independent fixtures](../../Examples/DigitSearchContract.lean) preceded
implementation. No probability or resource hierarchy was added.

## Executed first hits

`search` returns Option Nat and charges one unit per inspected element, with
zero on empty exhaustion. It stops at the first success and requires no equality
instance on the element type. `search_value` identifies its result with native
findIdx?. `first_spec` says the index is in range, succeeds, and every earlier
position fails; `none_spec` says every element fails. `search_work` gives i+1
at a hit and length at failure. `work_le` and `work_pos` preserve the empty and
nonempty boundaries. The signed -1 sentinel belongs only to `signedPosition`,
with `signed_failure` as its exact presentation theorem.

`first_hit_suffix` quantifies over every suffix after an independently supplied
failing prefix and successful element. The executor returns the prefix length
and costs that length+1 regardless of that suffix. `work_eq_takeWhile` proves
equality with existing ListFusion.takeWhile at dispatch0/cells0/tests1 for the
negated predicate. The returned values differ, but their inspected positions
agree. No uncharged prefix materialization implements search.

## Ordered population and actual uniform sum

Digits are Fin10, ordered by finRange10, with success at value≥5. `words` decodes
native List.pi over finRange n into ordinary lists. Private decoding lemmas
handle finite-position bookkeeping; no second public enumeration framework or
recursive word generator is introduced. `words_zero` and `words_succ` prove the
literal head-major enumeration: the zero population is `[[]]`, and each next
population iterates digits outside the prior words. `words_spec`, `words_nodup`
and `words_length` prove completeness, uniqueness and cardinality10^n.

`functions` exposes that same native product as total functions Fin n→Fin10.
`words_functions` is equality with their List.ofFn decoding. `functions_nodup`
and `functions_complete` identify the function population with Finset.univ.
Thus `totalCost_functions` and `expected_functions` equate the actual list sums
with finite-uniform function sums, including the singleton empty function.

`totalCost` sums actual `search` work over words; `expected` divides that sum by
the rational population cardinality. Neither is defined by its closed formula.
`sum_cons_cost` retains the search cost on rejected tails. `totalCost_step`
derives T(n+1)=10^(n+1)+5*Tn, and `totalCost_exact` gives
Tn+2*5^n=2*10^n. Denominator positivity holds even at zero. These imply
E(n)=2−2/2^n=2*(1−(1/2)^n).

`expected_error` retains the exact error2/2^n; `expected_lt_two` proves strict
finite inequality. For the existing weighted half sum Hn over Ico1(n+1),
`weighted_difference` proves E(n)−Hn=n/2^n. The weighted series and the finite
mean are therefore different. `expected_modulus` reuses the existing explicit
ceiling modulus and the comparison Hn≤E(n)<2. It gives strict positive error
below any positive rational epsilon at every index past that threshold.
`expected_tendsto` uses the existing rational epsilon/topology equivalence,
without a second convergence definition.

## Checked callers and rejecting cases

[The public client](../../Examples/DigitSearch.lean) applies the universal
first-hit and no-hit laws to [0,4,8,9]→(some2,3) and [0,4,3]→(none,3).
A duplicate leading hit ignores an arbitrary suffix. Best/worst families and
the native takeWhile work comparison exercise the generic interface.

The literal successor theorem recovers the frozen length-two product. Its first
words are [0,0],[0,1], and positions9/10 are [0,9],[1,0]. Direct List.sections
starts [0,0],[1,0], so it is rejected as this ordered presentation. This is an
order distinction; permutation alone need not change a uniform mean.

Among the100 length-two words,50 hit at the first position,25 at the second,
and25 fail. The latter two groups both cost2, yielding total150 and mean3/2.
The client connects that total and mean to the native function population.
At n=1 the mean is1, differing from the weighted sum1/2 and from the limit2.
At n=0 the population contains one empty word, total0, denominator1 and mean0.
These checks retain terminal failures and distinguish finite means from limits.

Population construction is not charged as searching one word. The one-unit
predicate price is a selected inspection model, not physical runtime. Results
concern the finite-uniform decimal population, not arbitrary distributions,
infinite random streams or varying predicate costs.

## Source dispositions and limits

Primary recovered member: project/adwh-lean/ADWH/Chapter02/DigitSearch.lean in
[checkpoint-233.zip](../history/algorithm-design-haskell/checkpoint-233.zip),
SHA-256 d3a9d4930bf0dba58c40244449e1dfeca8c18949a49e7ff261adc857e83be0f4.
Its search, total-cost decomposition and finite-mean proof arguments informed
this native implementation.

| Recovered declarations | Native coverage |
| --- | --- |
| search/search_value, search_first_spec/search_none_spec | Actual `search`, `search_value`, `first_spec`, `none_spec` |
| search_work/search_work_le/search_work_pos | `search_work`, `work_le`, `work_pos` |
| signedPosition/signedPosition_failure | Presentation `signedPosition`, `signed_failure` |
| digits/digits_complete/digits_nodup | Native finRange and corresponding coverage |
| words/words_spec/words_nodup/words_length | Native List.pi decoding, literal successor and corresponding theorems |
| totalCost/sum_cons_cost/totalCost_step/totalCost_exact | Actual total and corresponding decomposition/exact identity |
| expected/expected_uniform | Population-cardinality definition, `expected_functions` and `totalCost_functions` |
| ten_power_product/expected_scaled | Native field/power algebra inside `expected_closed`, without wrapper copies |
| expected_closed/expected_probability_form | `expected_closed`, `expected_probability` |
| expected_lt_two/weightedHalf_le_expected/expected_limit | Strict bound, stronger `weighted_difference`, comparison, native modulus and Tendsto |
| search_no_hit_cost/worst_case/best_case | `no_hit` and importing `worst`/`best` families |
| printed_finite_average_false and concrete examples | Checked finite mean correction, boundaries and executed callers |

The correction is proved for the defined finite experiment. The recovered
source attributes the discrepant calculation to Exercise2.13; this task did
not newly inspect the printed chapter or certify its wording. Printed coverage
and licensing remain #149. This accounts for selected R5 mathematics and
supports parent reconciliation; it does not close #459 or Chapter2. The five
design investigations and other residual families remain separate.
