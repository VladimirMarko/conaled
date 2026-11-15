# Selection: prospective recurrence, fuel, and cost lemma leads

Source-only preparation recorded 2026-11-04 while Preface/Perm validation is
pending. This supplements `../specs/1006-Selection.md`; it implements no Lean
algorithm or proof and changes no chapter order or acceptance gate. Selection
implementation remains blocked until BagPerm is accepted.

The exact VFA Selection source has SHA-256
`ff343099ae0fd551648a8fa2bf0adfe32bf5fb158389cee211ff8d1b32c28e11`.
Pinned API reads used the complete Lean 4.35.0 sources under `src/lean` in the
supplied kit's official distribution. The native advisor found the leads;
root directly inspected the declarations below before recording this note.

## Literal select permutation

Induct on the tail while generalizing the carried candidate: the false branch
changes that candidate. After destructing the recursive pair as `(y,r)`, the
source's true branch needs the permutation chain
`x :: h :: t ~ h :: x :: t ~ h :: y :: r ~ y :: h :: r`.
The false branch needs `x :: h :: t ~ x :: y :: r ~ y :: x :: r`.
These use `List.Perm.cons`, `List.Perm.swap`, and `List.Perm.trans` from
`Init/Data/List/Basic.lean`. `List.Perm.swap'` in `Init/Data/List/Perm.lean`
combines a swap with an arbitrary tail permutation. No payload equality or
order law is required for this permutation argument. This preserves the exact
remainder reconstruction; a minimum plus erase/filter is not the same recurrence.
`Prod.eta` in `Init/Core.lean` supplies `(p.1,p.2)=p` for the pair observation.

For minimum proofs, `Std.le_of_not_ge` in `Init/Data/Order/Lemmas.lean` states
`¬ b ≤ a → a ≤ b` under `LE` and `Std.Total` only. Instantiate with reversed
arguments for the source's false comparison branch. `Std.le_trans` separately
requires a transitive relation. Neither lemma introduces antisymmetry or payload
equality; retain the actual assumptions of each public result.

## Fuel as a prefix of independently defined well-founded execution

A useful proposed bridge is `F xs fuel = (W xs).take fuel`, using the plan's
names. First define `W` by the genuine list-length measure and prove its
one-step equations; it must not be an alias of the fuelled function. The
returned remainder-length theorem supplies the required decrease before this
bridge can be proved. A subsequent fuel induction, generalizing `xs`, can
unfold both equations and destruct the same select result.

Relevant pinned declarations are:

| Declaration | Source file relative to `src/lean` | Use |
| --- | --- | --- |
| `List.take_succ_cons` | `Init/Data/List/Basic.lean` | Positive fuel and nonempty well-founded result. |
| `List.length_take` | `Init/Data/List/Nat/TakeDrop.lean` | Output length is `min fuel (W xs).length`. |
| `List.take_of_length_le` | `Init/Data/List/TakeDrop.lean` | Sufficient fuel returns the whole result. |
| `List.take_length` | `Init/Data/List/TakeDrop.lean` | Exact-length fuel specialization. |

With independently proved length preservation for `W`, these lead to the
planned output-length formula, saturation, and equality with length-fuel `S`.
The bridge concerns executable comparison and recurrence only; ordering laws
are unnecessary for these value/fuel statements. The proposed proof has not
been elaborated or compiler checked.

## Comparison saturation does not imply complete output

The proposed instrumented count recurrence is `T(m+1,n+1)=m+T(m,n)`, with
zero count for empty input or zero fuel. The final singleton selection costs
zero comparisons. Thus the additional prospective arithmetic result
`T(n,n-1)=T(n,n)` would hold even though length-minus-one fuel omits the last
output element for nonempty input. For the retained five-element example,
fuel four would have ten comparisons and four output elements. This is a useful
future checked boundary case alongside fuel three (nine comparisons) and full
fuel (ten comparisons).

Derive the count statement from the actual measured recurrence and proven
remainder length, not from an extensionally equal library sort. Equality of
comparison counts is not evidence of sufficient fuel, full-input permutation,
physical allocation, or wall-clock equality. All claims proposed here remain
pending normal implementation, source-fidelity checking, integrated validation,
independent reviews, and the chapter acceptance checkpoint.
