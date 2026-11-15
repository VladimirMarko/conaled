# Natural-operation examples correction 2 — complete actual diagnostic readback

Base `c7aa6fa810af070434155ece48b92470ca4a91ec`. The complete 352-line original examples file, all 18 exact example diagnostics and the complete proof-only diff were read. The saved actual live-log observation is for central `c0440a99c2a503b7816a44367f7e4168378dbbf1`. Its 32,431-byte prefix has SHA-256 `b45bded7778156f7829c4fc80e374276edcc9252ea433f848dbb89ac58239126`. At observation there is no terminal result: this record makes no aggregate exit/pass inference. The same fixed prefix explicitly records the corrected core built in 138 seconds; examples did not build.

All 43 theorem headers, propositions, hypotheses and expected values are byte-identical to the parent. Fourteen theorem proof bodies change to address the 18 diagnostics (the odd-runs and tie-boundary proofs contain multiple failed local steps). The complete 63-declaration core is byte-identical; all 106 source contracts/cases remain. No linter setting, resource tariff, source algorithm, dispatch domain, value law or mathematical assumption changes.

| Finding | Source case / old line | Actual issue and exact proof-only correction |
| --- | --- | --- |
| `NOPS-C02-01` | `descending_two` / 63 | Add explicit [natLT] unfolding to the existing simpa. The comparator is definitionally the same strict Nat comparator; statements/counts remain unchanged. |
| `NOPS-C02-02` | `descending_three` / 66 | Add explicit [natLT] unfolding to the existing simpa. The comparator is definitionally the same strict Nat comparator; statements/counts remain unchanged. |
| `NOPS-C02-03` | `descending_two_execution` / 71 | Add explicit [natLT] unfolding to the existing simpa. The comparator is definitionally the same strict Nat comparator; statements/counts remain unchanged. |
| `NOPS-C02-04` | `descending_three_execution` / 77 | Add explicit [natLT] unfolding to the existing simpa. The comparator is definitionally the same strict Nat comparator; statements/counts remain unchanged. |
| `NOPS-C02-05` | `three_boundary_worker` / 91 | After the existing actual worker/scanner rewrite, close the displayed concrete pair projections, cons and Nat numeral equality with rfl. The actual execution theorem remains the first proof step. |
| `NOPS-C02-06` | `three_boundary` / 96 | After the existing actual worker/scanner rewrite, close the displayed concrete pair projections, cons and Nat numeral equality with rfl. The actual execution theorem remains the first proof step. |
| `NOPS-C02-07` | `restart_worker` / 102 | After the existing actual worker/scanner rewrite, close the displayed concrete pair projections, cons and Nat numeral equality with rfl. The actual execution theorem remains the first proof step. |
| `NOPS-C02-08` | `restart_boundary` / 110 | After the existing actual worker/scanner rewrite, close the displayed concrete pair projections, cons and Nat numeral equality with rfl. The actual execution theorem remains the first proof step. |
| `NOPS-C02-09` | `odd_runs` / 119 | After the existing actual worker/scanner rewrite, close the displayed concrete pair projections, cons and Nat numeral equality with rfl. The actual execution theorem remains the first proof step. |
| `NOPS-C02-10` | `odd_runs` / 123 | After the existing actual worker/scanner rewrite, close the displayed concrete pair projections, cons and Nat numeral equality with rfl. The actual execution theorem remains the first proof step. |
| `NOPS-C02-11` | `odd_runs` / 129 | After the existing actual worker/scanner rewrite, close the displayed concrete pair projections, cons and Nat numeral equality with rfl. The actual execution theorem remains the first proof step. |
| `NOPS-C02-12` | `odd_runs` / 118 | After the existing actual worker/scanner rewrite, close the displayed concrete pair projections, cons and Nat numeral equality with rfl. The actual execution theorem remains the first proof step. |
| `NOPS-C02-13` | `weak_descent_with_ties` / 147 | After the existing actual worker/scanner rewrite, close the displayed concrete pair projections, cons and Nat numeral equality with rfl. The actual execution theorem remains the first proof step. |
| `NOPS-C02-14` | `weak_descent_with_ties` / 143 | After the existing actual worker/scanner rewrite, close the displayed concrete pair projections, cons and Nat numeral equality with rfl. The actual execution theorem remains the first proof step. |
| `NOPS-C02-15` | `arbitrary_builder_restart` / 176 | After the existing actual worker/scanner rewrite, close the displayed concrete pair projections, cons and Nat numeral equality with rfl. The actual execution theorem remains the first proof step. |
| `NOPS-C02-16` | `padded_worker` / 277 | Close the explicit remaining [[] ++ [a]] = [[a]] value goal with rfl after padded_rep. No work equation or Rep premise changes. |
| `NOPS-C02-17` | `repeated_payload_exact` / 323 | Prove the closed Boolean identity decide ((0 : Nat) < 0) = false by decide, and include it in the existing simp-only transport. No hypothesis or comparator behavior changes. |
| `NOPS-C02-18` | `ascending_range_exact` / 333 | Add natLT to the existing simp-only source-theorem specialization; id and range-length normalization remain. |

## Statement and case assessment

The four descending examples retain scanner6/9 and complete execution7/10. Explicit
natLT unfolding aligns the source theorem with the unchanged example comparator.
The restart examples retain worker7/scanner10 for [3,1,2], worker12/scanner15 for
[1,3,2,4], and the odd three-run sequence8/11/16/19. The tie boundary retains
worker8/scanner11 and both tagged equal-key occurrences. The arbitrary composed
builder restart remains14. Each added rfl closes the concrete residual goal after
the existing actual branch theorem; it does not replace the connection with a
separate abstract count or a changed expectation.

The padded callback retains its arbitrary empty-prefix Rep and worker work2*n+4;
only nil append in its value projection is normalized. The repeated payload family
keeps n≥2 and total6*n-4, with the existing key-zero source specialization; its
closed comparator is explicitly equated with false. The ascending range family
keeps n≥2 and the same6*n-4 count, with explicit natLT unfolding. All other source
lines outside these proof deltas are retained, including unbounded supplied work,
sharing5/31/36, arbitrary payload correctness and distinct comparison/operation
observations. No claim of machine time or full multirun operational merge is added.

`git diff --check` exited0. No compiler, cache, central checkout, child agent or
uniform-input source was touched. The uniform candidate remains clean and frozen
at9d5dcd2cfbd6fc5df572234a85bf4957d0c32a21. The next immutable build, all actual type
inspection, independent review and complete acceptance gates remain with root.
