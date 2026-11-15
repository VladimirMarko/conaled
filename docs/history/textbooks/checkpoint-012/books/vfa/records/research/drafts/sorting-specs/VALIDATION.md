# Staging validation record

Date: 2026-11-02. All compiler commands were run from
`/workspace/scratch/0c54f2db1fdf/conaled` using its pinned Nix shell and cached
Lean 4.35.0 / Batteries dependencies. They requested no project build and no
`.olean` or `.ilean` output. Source writes were confined to this staging folder.

Environment prefix used for each compiler invocation:

```bash
export PATH=/root/.nix-profile/bin:$PATH
export NIX_CONFIG='build-users-group =
experimental-features = nix-command flakes'
export LEAN_NUM_THREADS=1
```

The approved escalated execution mode was used because the execution sandbox
cannot see the installed Nix profile; this follows `work-state/environment.md`.
No cache repair, dependency update, or `lake build` was requested.

## Investigation commands

The temporary signature-probe command was:

```bash
nix develop --command lake env lean /workspace/scratch/0c54f2db1fdf/work-state/staging/sorting-specs/Inspect.lean
```

1. With imports `Mathlib.Data.List.Sort` and `Mathlib.Data.List.Count`, it exited
   1 before elaborating declarations because
   `conaled/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Order/Fin/Basic.olean`
   was absent. This was an import-availability problem, not a mathematical gap.
2. Narrowing imports to `Batteries.Data.List.Lemmas`, `.Pairwise` and `.Perm`
   successfully displayed the needed signatures. The command exited 1 because
   three speculative queries named absent identifiers:
   `List.getElem?_eq_some`, `List.getD_eq_getElem`, and
   `List.exists_cons_append`. The displayed existing alternatives included
   `List.getElem?_eq_some_iff`, `List.getElem?_eq_getElem`,
   `List.pairwise_iff_getElem`, `List.isChain_iff_pairwise` and
   `List.perm_iff_count`. These unsuccessful name lookups do not concern the
   final draft's statements or proofs. The temporary probe file was removed.

No project outputs or dependency artifacts were generated to overcome the
first import failure. The final draft uses the already available lower-level
standard lemmas rather than reimplementing their theory.

## Substantive draft checks

Every substantive check used exactly:

```bash
nix develop --command lake env lean /workspace/scratch/0c54f2db1fdf/work-state/staging/sorting-specs/SortingSpecifications.lean
```

| Revision of the staging file | Result |
|---|---|
| First complete draft | Exit 1: the `Indexed` definition left i and j's types implicit, causing a stuck LT instance and cascading failures to unfold the invalid definition. No mathematical obligation was refuted. |
| Explicit Nat index binders plus direct getD bridge and connected clients | Exit 0; no diagnostics. |
| Final draft, adding the source query/value equality-orientation bridge `contents_cons_by_query` | **Exit 0; no diagnostics.** |

`set_option autoImplicit false` and `set_option warningAsError true` are enabled
in the final draft. It contains no admissions, application axioms, unsafe
declarations, or native-evaluation proof shortcuts. The source was also scanned
for those constructs. The final compiler invocation checks every definition,
theorem and example in the staging file.

Original checked draft SHA-256:
`2582dde9bc3c8621e4ddf8b6bbef6bafcebc0d4cc76820af70e870065aecc1a4`.

## Independent staging review correction

The independent staging reviewer found only SS-1, a comment that overstated
LawfulBEq as logically necessary for every permutation-characterizing Boolean
count vector. The source comment and README now state the proved sufficiency
claim. Definitions, theorem statements and proofs are unchanged. The exact
corrected file was checked with the same single-worker command above and exited
**0 with no diagnostics**; `review-correction.log` is empty as expected.

Current corrected `SortingSpecifications.lean` SHA-256:
`45546bba250cb8613ff0fa41143f63f1a3f81d271a0bdeafac1663343e15188c`.

See `../../reviews/sorting-spec-draft.md` for the independent staging review.
That review remains distinct from the chapter acceptance axes below.

This record does **not** report an integrated project build, exhaustive project
proof audit, independent Standards review, or independent Spec review. Those
remain required when root integrates a chapter's accepted changes.
