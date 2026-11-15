# Rank example proof correction — root source assessment

The current core at6f3e010 compiled individually in live focused7 at immutable
central5398db7. The example module emitted exactly two complete diagnostics,
preserved here from the fixed partial log. The aggregate run is still live;
no terminal success or acceptance is claimed.

Root read all151 lines of the original example file, both complete diagnostics,
and the exact two-block correction. All18 public theorem headers are byte-identical.
The core's19 named declarations consist of12 public and7 private helpers; those
core bytes do not change. The combined rank public inventory remains30 names.

1. singleton_rank: the actual Fin index type reduces to Fin1. Use the official
Lean4.35.0 Init/Data/Fin/Lemmas.lean theorem Fin.fin_one_eq_zero, whose proof is
Subsingleton.elim. This proves the same actual occurrenceRank value equals zero
for arbitrary payload and key universes, with the same LinearOrder key instance.
No payload inhabitance/equality or altered rank algorithm is introduced. The
failed omega attempt treated an unsimplified Fin-zero coercion/length as unknown.
2. repeated_key_rank_is_not_left_size: after the established sorted tuple equals
Equiv.refl, rfl closes exactly the emitted residual inverse-identity value goal.
The second repeated-key position remains1 while the actual strict-left child is
empty. Its separate finite child decision and all duplicate-key limitations stay.

All other statements/proofs remain unchanged: empty/uninhabited means, exact
small-size means, nonidentity occurrence ranks, original child orders, four-key
mean109/3, equal-key quadratic25, and unrelated key/payload universe transport.
No definitions, instances, imports, policy, linter settings or source requirements
change. No compiler/build/cache command was run in this source-only worktree.
The successor needs actual compiler/type/full-scope independent evidence and all
acceptance gates. Root's author assessment is not an independent review axis.
