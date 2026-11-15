# C03-RANDOM-MEAN-ELAB-001: narrow expectation-proof correction

Candidate `ffc6707febff782a386615a20a0ef3dee9112b2d`, tree `f20948aca2572981349a02b6ded4d258690454b0`, parent `f76bc53339e172a179560654b181040a7313506d`.
Branch `work/fdsa-ch03-random-selection`; clean worktree.
Commit `fix(selection): elaborate actual run expectations (#174)`.
This correction is **uncompiled**. Root remains the sole compiler owner.

## Actual failed evidence retained

The first mean pair check closed with actual exit1 at the parent: owned67278,
terminal `41a139`, root closure `38bff2`. The complete closed log and closure
were read in `88143f`. The outer log is 9,295 bytes, SHA-256
`f579f7c48fdeb0c1d7a33247a4c8a8f3dbcf6c39b81fdd34fd970e8b54783705`.
All14 attempt records and all64 previous author records are bound unchanged.
This failure establishes no successful mean-pair, type, audit or chapter gate.
Do not poll the closed session again.

## Exact bounded correction

Only `Applications/Resources/RandomSelectionMean.lean` changes: six insertions
and six deletions in five proof bodies.

1. `workExpectation_cons`: remove the redundant `dsimp only` that actually
   reported no progress. The conditional bind/map/pure proof is otherwise intact.
2. `scanExpectation_eq_workExpectation`: explicitly unfold the existing
   `workExpectation` at the final definitional equality.
3. `sourceExpectation_eq_workExpectation`: the same definitional closure for
   the existing source marginal.
4. `scanExpectation_nil`: supply the existing payload type explicitly when
   invoking `workExpectation_nil`. The logged original line251 belongs to this
   empty-scan lemma; `scanExpectation_cons` is unchanged.
5. `sourceMean_comparison`: give the finite numeral two an explicitly typed
   `ENNReal.ofNat_ne_top` witness, then use that exact witness in the finite
   addition and `toReal_add` specialization. Neither coefficient9 nor offset2
   nor any finiteness premise/conclusion is changed.

All108 public headers and13 authored private helper headers/bodies are
preserved. All definitions, imports, universes, options and cost observations
are unchanged. The other five source files are byte-identical, including all
original four sources and every mean example. The whole original statement and
case review is retained in `precommit-assessment.json`, together with exact
new-file headers and the five local proof assessments. Empty and invalid worker
ranks, uniform occurrence multiplicity, actual selected-child semantics, and
scan/source coupling remain explicit.

## Root-only validation input

```text
lake build Applications.Resources.RandomSelectionMean Examples.RandomSelectionMean
```

`Statements108-mean-correction1.lean` is byte-identical to the previous complete
explicit-@ input, with all108 targets and full-printing options. Its SHA-256 is
`a323a5014823dfdacd05249b5829b83d51eb2741cd8964601d02ba6aecb9f46e`. The companion preparation JSON binds it to this exact
candidate/tree and all six source blobs. It is prepared only; no author type
program execution occurred.

Actual precommit preservation/whitespace checks exited0 in `4af8ed`; actual
staging, staged whitespace check and commit exited0 in `bf382c`. These are
source-record checks, not Lean or proof-audit results. The new core SHA-256 is
`292fb4151665a701435ae6456a038b8a5a0b45c11326e16459617b0308c60aa4`.

No finding closure or independent-review outcome is asserted. The full
candidate check, proof audit, both axes and immediate verification remain
root-owned gates. The fixed whole-task review base remains
`2da5708478a1d943a9214b5b386ec2db16cd9eca`.

## Hold and remaining mathematical scope

All six sources and own provenance are held until root supplies an actual
terminal or explicitly releases work. No new probability source was written.
The actual chosen-child3/4 drift, E[W]<=4n, exact natural-w tail, worst-case
families and remaining pivot policies still require proof; their constants and
quantifiers have not changed. The inaccessible-Karp-primary-source limitation
is retained, without invented attribution.
