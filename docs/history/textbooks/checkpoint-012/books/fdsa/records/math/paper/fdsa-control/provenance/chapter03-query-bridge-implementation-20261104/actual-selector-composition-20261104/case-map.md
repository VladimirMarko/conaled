# Connected case handoff

All cases are source-only pending root's focused compile. The independently expected calculations were recorded before author source in design-and-expected-cases.md.

| Case | Source declarations | Main connections |
| --- | --- | --- |
| Arbitrary acquired list and actual worker | acquired_worker_execution | observedSelect_total, acquired, on_acquired, work_acquisition |
| Empty, all ranks and tariffs | empty_run; empty_every_work | observedSelect_run, actual selectRun_nil, determinism; no Fin0 rank asserted |
| Singleton | singleton_run; singleton_every_work | actual selectRun_small and measured insertion/lookup; actual frontend and determinism |
| Concrete [8,3,5] | concrete_run; concrete_value_run; concrete_every_work | actual helper calls16, frontend run, value-view correspondence, tariff2 total22 and tariff0 total16 |
| Duplicate [4,4,4] | duplicate_run; duplicate_every_work | actual helper calls14, three real reads, tariff2 total20; correctness not restricted to distinct data |
| Invalid rank3, length3 | invalid_every_work | actual invalid guard cost5 plus query work6; total11 |
| Cutoff20 | cutoff_twenty_run | actual small worker result/cost73, combined93 |
| First nested size21 | first_recursive_run | actual run; occurrence rank10; checked actual cost<=F with F21=1419, total<=1440 |
| All valid inputs / competitor nonvacuity | total_correct_value_view; any_valid_input_contract | Total + all-input Selects, actual some/default proof, paid lower/upper bounds |
| Earlier pairMinimum competitor | pair_minimum_comparison | exists_uniform_optimality, existing pairMinimum_total/correct; supplies both executions/equal answers |

The core uniform affine/linear and family-IsBigO claims consume the checked actual worker bounds. Their constants precede all data. The final comparison pays selection and proves a uniform factor relative to positive-price coordinate queries on distinct valid-rank inputs. No newly measured physical time or arbitrary source tariff is claimed.
