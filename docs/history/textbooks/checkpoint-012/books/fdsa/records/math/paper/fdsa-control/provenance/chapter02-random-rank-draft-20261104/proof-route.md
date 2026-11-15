# Rank implementation proof route at checkpoint 0090

Status: source implementation released, but paused for priority mean compiler
corrections and the checkpoint before either new rank Lean file was created.
This is an implementation note, not Lean code or a proof result. The full
399-line reviewed plan and zero-finding root assessment remain authoritative.
Current clean author base is1f315fdbb40288d99921164bb3fd8afcbd756e58.

## Small exact correspondence lemmas

Define occurrenceRank as inverse Tuple.sort of the finite occurrence-key tuple.
For its order iff, let f i := key xs[i.val]. Obtain Injective f from
List.nodup_ofFn and List.ofFn_getElem_eq_map applied to mapped-key Nodup.
Tuple.monotone_sort combined with injectivity of f and the sorting permutation
is strictly monotone. Change the target to inverse-sort ranks versus f-values;
use StrictMono.lt_iff_lt at the two inverse images, with only comp_apply and
Equiv.apply_symm_apply simplification. This avoids payload instances.

For the general filter length/cardinality helper, let f be the actual list
getElem function and prove (List.finRange xs.length).map f = xs using
List.ofFn_eq_map and List.ofFn_getElem. Transport filter length using congrArg,
then List.filter_map and List.length_map. Convert the filtered finRange length
to its toFinset.card with Nodup.filter and List.toFinset_card_of_nodup, then
List.toFinset_filter and List.toFinset_finRange. This operates on Fin equality
only. For strict below-pivot count, prove the rank image of the finite index
filter equals Finset.Iio rank; use card_image_of_injective and Fin.card_Iio.

Actual left length follows by filtering the explicitly typed permutation
`(xs[i.val] :: xs.eraseIdx i.val).Perm xs` from
List.getElem_cons_eraseIdx_perm i.isLt. The selected pivot fails its own strict
comparison, so the filtered permutation's length equality removes its head.
Right length follows from this left count, QuickSort.partition_lengths, and
an explicitly typed List.length_eraseIdx_add_one equation. Each child's
mapped-key Nodup follows from filter_sublist.trans eraseIdx_sublist, mapped
by key, then List.Nodup.sublist. No actual child is resampled or reordered.

The existing core filter_eraseIdx_length_lt helper is private. Use a new
private proof from length_filter_le and the explicit erased-length equation.
The public predicates remain exact inline eraseIdx/filter expressions.

## Uniform map and actual mean induction

For a private uniformIndex_map_perm lemma, PMF.ext and PMF.map_apply reduce
to the sum over actual preimages. For each output r prove
`r = sigma j iff j = sigma.symm r` via sigma.injective and inverse laws.
Then `simp only [that_iff, tsum_ite_eq, uniformIndex_apply]` yields the mass.
The public left-length law rewrites the actual length function to rank.val,
then uses inverse PMF.map_comp and this finite permutation law. Do not invoke
map_ofFintype with target Nat; map the proved Fin rank law by Fin.val instead.

The four-universe equal-length theorem should use an explicit local auxiliary
strong induction, avoiding recursive theorem termination elaboration:

  aux : forall n (us : List alpha) (vs : List beta),
    us.length = n -> (us.map key1).Nodup -> (vs.map key2).Nodup ->
    us.length = vs.length -> exerciseMean cmp1 us = exerciseMean cmp2 vs

Use Nat.strong_induction_on n, quantify both lists in the induction property,
and case split them. The mismatched nil/cons cases contradict equal length.
For two cons lists, define their actual left/right input functions and rank
permutations rho1/rho2. The root bijection is
`(rho1.trans (finCongr hlen)).trans rho2.symm`.
For its rank-value identity, change to rho2 (rho2.symm (finCongr hlen (rho1 i))),
rewrite apply_symm_apply, then rfl. This explicit change avoids dependent
rewrite problems. Exact left child lengths match by the two rank lemmas;
right lengths match by the same value equality and parent length equality.
Natural arithmetic can handle the latter without rewriting dependent Fin
index types. Apply the smaller-size induction hypothesis separately to the
actual child pair using inherited mapped-key Nodup and the proved strict
length bound. Reindex the actual root mean sums with Fintype.sum_equiv.
Only after that sum equality rewrite the common tail lengths in denominators
and tolls. The actual exerciseMean_cons is the only recurrence used here.

## Size recurrence and checked API refinements

Define sizeMean as the actual Nat.lt Boolean-comparator mean on List.range n.
The general bridge compares to that list using List.nodup_range, map_id and
length_range. Apply the bridge to actual children of exerciseMean_cons, use
the proved sizes, then Equiv.sum_comp for ranks and Fin.revPerm for reversal.
Pinned Fin.val_rev is `(Fin.rev i).val = n - (i.val + 1)`, not a theorem named
rev_val. At n=m+1 normalize with Nat.succ_sub_succ_eq_sub (or an explicit
Nat equality), rather than assuming a definitional m-i identity.
Fin.revPerm is in Mathlib.Data.Fin.Rev and publicly imports Fin.SuccPred,
which contains finCongr and finCongr_apply_coe.

The finite rank-child sum becomes twice the sum over all ranks. Rewrite
`div_eq_mul_inv` and use real ring arithmetic for the factor. The actual
nonempty toll remains the cast of Nat (4*m+3). The positive-size wrapper uses
Fin.sum_univ_eq_sum_range from Mathlib.Data.Fintype.BigOperators and justified
Nat-to-real cast normalization. The observed mean compiler errors show two
specific disciplines: parenthesize additive finite-sum bodies; stage toReal
and Nat.cast_ofNat rewrites when necessary, retaining all finiteness premises.

No harmonic solver import is needed for these actual recurrence proofs. The
quicksort author owns the generic harmonic module and agrees on the exact
range-sum interface. Full example and per-claim assessment work remains to be
written with the source. All cases and validation restrictions remain those
of the reviewed plan. Resume only after root releases checkpoint0090 hold.
