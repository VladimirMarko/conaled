# Random quicksort rank and actual size mean: complete author source assessment

## Boundary and evidence

This is the author assessment of the two released new source files. It is
source-level preparation for root's exclusive compiler run, explicit type
inspection, complete-candidate validation and independent review. **Neither
new file has been compiled.** No checked theorem, focused pass, chapter
coverage closure or acceptance is claimed here.

The reviewed 399-line plan and zero-finding root assessment are preserved in
`../chapter02-random-rank-preparation-20261104/`. The original implementation
start at 19879f2, priority mean correction to 1f315fdb, checkpoint0090 hold,
and resumed source release are recorded separately. The source parent for
this rank slice is `1f315fdbb40288d99921164bb3fd8afcbd756e58`. The rank work
adds only `Applications/Resources/RandomQuickSortRank.lean` and
`Examples/RandomQuickSortRank.lean`; no existing source or pin changes.

The new resource is 393 lines/19,615 bytes, SHA-256
`22960885c968620b957e7e2381baa8b887d9dc80a54fb72fe9644c3ace2890b4`.
The new examples are 151 lines/6,427 bytes, SHA-256
`a0f5fbd6b3d41cad08193a371228bede1b869a773608b21906e85f2848d747bf`.
All source lines and proof bodies were read back, including all **30 public
declarations and seven private helpers**. The adjacent inventory fixes each
source name, statement, line and file identity; it is not an elaborated-type
dump. The second key type is named `ν` in actual Lean source because the
pinned parser reserves `λ` as a lambda introducer. This preserves the plan's
four independent universes and changes no mathematical requirement.

The initial random run/law pair retains its earlier exact focused pass and
complete 62-name source/type readback. The actual-mean dependency at 1f315fdb
has reported individual core and example build milestones in the still-running
central attempt 4 at e4965499; at this assessment root has supplied no terminal
aggregate or complete mean-type inspection pass. All earlier closed failed outcomes,
including cast repair's attempt 3, remain preserved. In particular a downstream
example job labelled `Ran` has never been treated as a pass.

## Every public resource declaration

All names in this table are in `Resources.RandomQuickSort`.

| Declaration | Intended and actual source contract | Assessment |
| --- | --- | --- |
| `occurrenceRank` | The inverse of `Tuple.sort` on the finite tuple `i ↦ key xs[i]`, an `Equiv.Perm (Fin xs.length)`. | It reindexes existing occurrences and is not a random execution or pivot choice. It is defined for empty and repeated-key lists. Only the key type has a `LinearOrder`; payload/key universes are independent. |
| `occurrenceRank_lt_iff` | Under `(xs.map key).Nodup`, rank order between two actual valid indices is equivalent to strict order of their selected keys. | The mapped-key hypothesis is explicit. Injectivity is derived only on this finite occurrence tuple, not postulated globally for `key`. The proof upgrades the actual sorted tuple's monotonicity and uses its inverse laws. |
| `left_length_eq_rank` | The length of the actual strict filter of `xs.eraseIdx i.val` equals the selected occurrence rank's Nat value. | The statement contains the actual selected `xs[i.val]`, exact indexed removal and strict Boolean predicate. The filtered permutation of `pivot :: remainder` removes only the strict-failing selected pivot, so occurrences and source filter values are retained. |
| `right_length_eq_rank` | The actual complementary filter has length `xs.length - 1 - rank.val`, under mapped-key Nodup. | It uses the existing complementary partition length theorem and valid indexed deletion length, not a new partition implementation. Natural subtraction is justified by the exact length sum. Equal keys are excluded by the explicit hypothesis. |
| `child_keys_nodup` | Both actual filtered child lists, after mapping the same `key`, are Nodup. | The conclusion is the precise induction premise needed for each recursive input. The proof maps actual sublist relations, requiring no payload equality and no global key injectivity. |
| `left_length_law` | The actual left-length observation of `uniformIndex tail.length` equals the Nat-value pushforward of that same uniform index distribution. | It proves uniform key rank for the actual occurrence choice, with mapped-key Nodup. Fin permutation invariance is proved first; the Nat law is obtained by map composition. No finite-target PMF lemma is applied to arbitrary payloads or to Nat. |
| `exerciseMean_eq_of_length_eq` | Inputs of equal lengths and distinct mapped keys have equal actual exercise means, with unrelated payload types, unrelated linearly ordered key types, and four independent source universes. | The proof strongly inducts on the common actual length. Root indices are paired by their actual rank permutations and `finCongr`; the actual left/right children have equal sizes and inherited distinctness, so smaller actual means agree. The only mean recursion used is the existing actual `exerciseMean_cons`. |
| `sizeMean` | `exerciseMean (fun a b : Nat => decide (a < b)) (List.range n)`. | This is definitionally an actual recursive execution mean on a concrete canonical input. No separately stipulated numerical recurrence or probability distribution is introduced. |
| `exerciseMean_eq_sizeMean` | Every actual distinct-key input's exercise mean equals `sizeMean xs.length`. | It instantiates the proved cross-input equality with `List.range`, its actual length and its actual Nodup. It does not assume size invariance or use a harmonic formula. |
| `sizeMean_zero` | The canonical actual mean at zero is one. | It uses the actual empty-input mean and the empty range. No empty uniform sampler or division by zero is introduced. |
| `sizeMean_succ` | `sizeMean (m+1) = (2 / ((m+1 : Nat) : Real)) * Σ i : Fin (m+1), sizeMean i.val + ((4*m+3 : Nat) : Real)`. | It follows the actual child-mean rewrite, proved rank sizes, root-index reindexing and `Fin.revPerm` reversal. The source toll remains the cast of the natural observation. It is then instantiated on the actual nonempty canonical range. |
| `sizeMean_recurrence` | For `0<n`, `sizeMean n = (2/(n:Real))*Σ k∈range n,sizeMean k + 4*(n:Real)-1`. | It is a proved interface conversion from the successor theorem: finite-index sum to range sum, explicit positivity case split and justified Nat casts. The zero equation stays separate. This matches the harmonic owner's requested interface without importing that owner's module. |

## Every private resource helper

| Helper | Source proof role and boundary |
| --- | --- |
| `filter_length_eq_card_indices` | Identifies the length of an arbitrary Boolean list filter with the cardinality of its actual satisfying occurrence indices. It represents the list as a map of `finRange`, uses the returned filtered list, then finite-set cardinality on Fin. It does not deduplicate payloads. |
| `strict_filter_length_eq_rank` | The actual rank permutation maps the strict-below-pivot index filter onto the finite interval below the selected rank. The image equality, permutation injectivity and `Fin.card_Iio` prove the count. Mapped-key Nodup is retained. |
| `filtered_remainder_keys_nodup` | Maps the filter/eraseIdx sublist relation by the supplied key and inherits its Nodup. The generic helper needs no order or valid-index assumption; it proves only sublist preservation. |
| `filtered_remainder_length_lt` | Uses a valid `Fin xs.length`, exact `length_eraseIdx_add_one` and `length_filter_le` to prove a strict child-size bound. No unavailable private proof from the earlier random core is imported. |
| `uniformIndex_map_perm` | Every output of a finite permutation has the unique preimage `σ.symm r`. The actual PMF map mass therefore equals the original uniform mass, using `PMF.map_apply`, inverse laws and the single-term tsum. It asserts no conditional child-input law or priority coupling. |
| `sum_rank_children` | A finite real sum over an arbitrary rank permutation is reindexed by `Equiv.sum_comp`; reversal uses the actual `Fin.revPerm` Nat value and checked Nat subtraction. It proves a finite algebra identity for an arbitrary sequence and supplies no premise about execution costs. |
| `exerciseMean_cons_size_formula` | Applies the proved actual mean-to-size bridge to each actual child, using inherited distinctness. It then rewrites the actual bind-mean equation by actual rank sizes and the finite rank-sum identity. Its positive denominator and exact local toll are inherited from the successor input length. |

## Every public example declaration

All names in this table are in `Examples.RandomQuickSortRank`.

| Declaration | Consequential case and independent expected result |
| --- | --- |
| `empty_rank` | The empty occurrence permutation is the identity on Fin 0, for arbitrary payload/key universes; its proof eliminates the impossible index. No payload default is requested. |
| `empty_uninhabited_mean` | An actual `List Empty` computation has the canonical zero mean. Both are one. |
| `singleton_rank` | The sole occurrence has rank zero, for arbitrary payload/key universes. Fin's actual bound proves the value. |
| `sizeMean_one` | The canonical mean is five, transported from the earlier actual singleton theorem. Independent arithmetic is `1+1+3`. |
| `sizeMean_two` | The canonical mean is 13, transported from the earlier actual two-key PMF mean. Both pivot ranks give `1+5+7`. |
| `sizeMean_three` | The canonical mean is 71/3, transported from the earlier actual 21/25 cost law's mean: one middle rank contributes 21 and two endpoint ranks contribute 25. |
| `three_occurrence_ranks` | On `[2,0,1]`, the original-index ranks are `[2,0,1]`. It computes the actual strict-filter lengths and uses the proved rank correspondence, avoiding evaluation of the abstract tuple permutation. |
| `three_middle_children` | Actual removal of index 2 from `[2,0,1]` and the actual pivot 1 filters produce `[0]` and `[2]`. It checks returned lists, not only lengths. |
| `three_left_size_law` | The same nonidentity occurrence/rank example has the proved uniform Nat rank pushforward. The source sampler is still `uniformIndex 2`. |
| `three_reordered_exercise_mean` | The actual reordered input `[2,0,1]` has mean71/3 by the new source-connected size bridge, agreeing with the independent 25,25,21 branch calculation. |
| `sizeMean_four` | The positive-size range-sum recurrence yields 109/3 using earlier actual means at 0–3. The independent branch calculation gives extreme-rank conditional means 119/3, internal-rank means 33, and their uniform average 109/3. |
| `four_occurrence_ranks` | On `[3,1,0,2]`, the original-index ranks equal `[3,1,0,2]`, again through actual strict-filter counts. |
| `four_selected_children` | Selecting index 3 (pivot 2) returns actual left input `[1,0]` and right input `[3]`. The unsorted left input order is preserved; it is not silently replaced by a sorted or resampled child. |
| `four_reordered_exercise_mean` | The actual fixed input `[3,1,0,2]` has mean 109/3, with no input permutation distribution premise. |
| `distinct_tags_repeated_keys` | The three payload records `[(1,false),(1,true),(2,false)]` are Nodup, while their mapped keys are not. Thus payload distinctness does not satisfy the mathematical domain. |
| `repeated_key_rank_is_not_left_size` | On those same tags, the second equal-key occurrence has tuple-sort tie position 1, while its actual strict-left child has length 0. Monotonicity of the key tuple determines the tie permutation; the rank-size theorem is deliberately unavailable because its key-Nodup hypothesis fails. |
| `equal_keys_keep_quadratic_mean` | Three equal keys retain actual mean 25, which differs from the distinct-key sizeMean 3=71/3. This connects the domain counterexample to the actual previously measured mean, not just to rank bookkeeping. |
| `tagged_inputs_equal_mean` | A client on `κ×τ` and `ν×υ` with unrelated key types and unrestricted tag universes applies the four-universe bridge. Only mapped-key Nodup, key orders and equal lengths are premises; payload finiteness/equality/measurability/inhabitation remain absent. |

## Mathematical correspondence and remaining validation risk

The three substantive connections have explicit proofs in source. First,
selected occurrence to rank uses the actual key tuple and exact finite
permutation. Second, rank to recursive size uses actual indexed removal and
both returned filters, with inherited hypotheses. Third, means are compared
by pairing actual equal-rank pivots and smaller executed inputs, before the
canonical size mean and its recurrence are introduced. No execution mean
recurrence is assumed, and no numerical check supplies a general premise.

The four-universe induction compares means, not full output/joint-run laws.
It does not assert uniform child input order or introduce a conditional
resampling step. The uniform left-length law is a pushforward of the actual
occurrence distribution. Repeated keys keep multiplicity in the unchanged
run and are excluded only where the rank/count proof needs distinct keys.

The metric is unchanged: local nonempty toll 4*m+3, empty cost 1, and actual
returned recursion/filter observations. Appends, sampling, lookup/removal
and random-bit qualifications remain those of the prior source. The new
size recurrence concerns the exercise observation only. The existing literal
mean comparison is not used here to imply an unproved runtime bound.

There is no concrete mathematical/source-contract finding after this author
readback. Elaboration, tactic compatibility, imports, generated theorem
names, linting and the actual implicit argument/universe output still require
root's compiler and complete explicit type inspection. All 30 public and
seven private contracts remain uncompiled. No speculative gate suppression,
axiom, `sorry`, `admit`, unsafe proof, `native_decide` or dependency change was
introduced; the source token check is only supplementary evidence, not an
axiom audit.

The actual harmonic identity, logarithmic/Big-O bounds, final connection to
the separate numerical solver, the separate uniform-input first-pivot mean,
and pivot implementation overhead qualifications remain mandatory. All
complete immutable-candidate validation/audit, independent Standards/Spec
review, and immediate candidate verification gates remain in force. This
source slice supplies no foundation or Chapter 2 acceptance.
