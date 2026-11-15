# Finite-search counting and checked frontier data

## Source identity and selected scope

- Snapshot: `adwh-checkpoint-335-compact-recovery`.
- Supplied archive SHA-256:
  `9e8bee022149e8456c9c4ab318f3be0d5d7f8361c25e7409cfe1c12bf8eb812c`.
- Retained payload member:
  `project/adwh-lean/ADWH/Chapter15/SearchCounting.lean`.
- Member SHA-256:
  `58865e1bb09be088984f4d84756e8c2311c16ba99b14e07fe0e8f9234df34cc8`.
- Source namespace: `ADWH.Chapter15.SearchCounting`.

The [declaration ledger](adwh-search-counting-provenance.tsv) accounts for all
nineteen named source declarations. This is a source-module reconstruction,
not a claim that all of Chapter 15 or the surrounding experimental artifacts
have been integrated. The original source requires only Std and uses Lean
4.35.0. The destination uses conaled's existing pinned toolchain and audit.

## Public interfaces and architectural placement

`SquareKit/FiniteSearch.lean` exposes the reusable mathematical operations and
their laws. `enumerate` gives the ordered endpoint occurrences after exactly
the supplied number of transitions. `count` computes their length without
constructing the complete endpoint list. A finite successor list is sufficient;
the state type itself need not be finite. A transition may revisit a state or
repeat it within the same list. Those occurrences remain distinct contributions.

`count_partition` splits an arbitrary depth into a frontier depth and residual
depth. `Tail` is an ordinary optional residual function. Its separate `Exact`
contract quantifies over every returned answer, and `countWith_eq_count` justifies
fallback to recursive counting when a backend declines. Neither raw operations
nor ordinary callers have to construct categorical wrappers.

The new `enumerate_map` and `count_map` transport this construction through a
decoder preserving successor lists. The law retains order and multiplicity;
injectivity, invertibility, a finite type instance, and decidable equality of
states are unnecessary. `Applications/Search/Counting.lean` packages the same
law in the existing `Squares.Rep`/`Squares.Square` interface. `countSquare` and
`countWithSquare` expose enumeration-length semantics and compose with ordinary
existing consumers. No new square, category, or representation hierarchy is
introduced. Existing `SquareKit.Iteration.UntilSpec` describes first-hit
iteration, and `SquareKit.FiniteUniverse` describes finite-type enumeration;
neither has this exact-depth occurrence contract.

`Applications/Checking/SearchCount.lean` retains the numerical proposal checker
and frontier certificate from the source. The new `Valid` predicate describes
each proposed entry using the independently enumerated residual answer list.
`verify_iff` connects the executable checker to that predicate; `verify_sound`
establishes the resulting total. `release` returns `none` on rejection and only
returns a sum after successful checking. `checkedTail` turns an arbitrary
producer's proposals into an exact optional backend using `release_sound`.
Its proof assumes nothing about the producer's answers.

## Checked uses and statement review

The cases in `Examples/SearchCounting.lean` were chosen before implementation:

| Case | Independent expectation | Public connection |
| --- | --- | --- |
| Binary word extension | Two choices at every step yield eight occurrences after three steps; two steps list `00, 01, 10, 11` in that order. | `count_map`, `enumerate_map`, `countSquare.commutes` and the all-depth `binary_count` specialization. |
| Word length decoder | Both extensions have the same length, so the abstract successor list has two identical entries. | The decoder law `binary_length` discharges the exact ordered-list premise. No injectivity premise is added. |
| Count observation | A positive count can feed a Boolean consumer. | `Squares.compose` and `Squares.exactSquare` construct `hasWordSquare`; its commuting theorem states the corresponding enumeration observation. |
| Duplicate graph edges | Edges `0 → [1,1,2]`, `1 → [3]`, others `[]` give endpoints `[3,3]` at depth two. | `count_eq_length` and `count_partition` recover count two and residual counts `[1,1,0]`. |
| Dead ends | Depth zero counts the start once; a positive depth at a dead end counts zero, and the graph is exhausted at depth three. | `count_eq_length` connects the cases to the endpoint specification. |
| Exact residual backend | A one-step backend returns the successor-list length and declines other depths. | `oneStepTail_exact` proves its contract and `countWithSquare` transports it. |
| Frontier data | The graph certificate at depth one has entries `[1,1,0]` and total two. | `verify_certificate`, `verify_sound`, `release_eq_some_iff`, and `release_sound` connect generation, checking, and the released answer. |
| Malformed frontier data | Wrong counts, missing entries, reordered unequal counts, and excessive depth are rejected. Some malformed proposals even have the right sum. | The concrete `release` and `checkCount` conclusions preserve their independently expected `none`/`false` results. |
| Untrusted backend producer | A producer proposing the constant `99` cannot change the graph's count of two. | `checkedTail_exact` discharges `countWith_eq_count` without any hypothesis about the producer. |

The generic statements quantify over all natural depths and all states. The
decoder law is required at each state, not assumed merely for the initial one.
Partitioning uses addition of depths, and certificate validation separately
checks the frontier-depth bound before using truncated natural subtraction.
The verifier checks the whole list, so a correct sum alone is insufficient.
Equal entries may of course be exchanged without changing that list; no stronger
claim about distinguishing identical numerical entries is made.

The backend proof requires `Exact` for the supplied backend; it is not a theorem
that arbitrary unchecked backends are correct. `checkedTail_exact` constructs
that proof for arbitrary certificate producers because rejected proposals
decline the query. No satisfiability or termination assumption is hidden: every
recursive search reduces the finite depth, and the checked word and graph
clients discharge their premises explicitly.

## Limits and validation

This is occurrence counting, not cardinality of distinct reachable states or
counting terminal states at all depths. `verify` recomputes each residual count;
accepting a certificate supplies logical reuse without a promised speedup.
There is no complexity model, allocation claim, benchmark, compiler correctness
claim, or modified-kernel dependency in this scope. The local development uses
no admission, new axiom, or native-evaluation proof shortcut.

The integration entrypoint is `Examples.SearchCounting`, covering the theory,
checker, adapter, and all cases. The encompassing integration imports it into
`SquareApplications` and performs the
repository's candidate build, exhaustive axiom audit, and independent Standards
and Spec review. Focused development commands are:

```sh
direnv exec . lake build SquareKit.FiniteSearch \
  Applications.Checking.SearchCount Applications.Search.Counting Examples.SearchCounting
```

These focused checks alone do not establish acceptance of the whole repository.
