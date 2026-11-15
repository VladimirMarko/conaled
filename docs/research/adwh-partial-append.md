# Partial-spine append and suffix visibility

This development adapts twelve append declarations from checkpoint 335 through
the existing partial-spine semantics. The operation composes arbitrary partial
or infinite observation ideals. Its public laws explain when a suffix becomes
visible, and the retained clients consume actual guarded and paused producer
observations through the existing first-output and function-valued truncation
interfaces.

## Existing owners

`SquareKit/PartialSpine/Append.lean` adds the operation and its laws to
`SquareKit.PartialSpine.Observations`. It imports the existing limits module and
defines just one new operation:

```lean
append xs ys = Observations.foldr Observations.cons ys xs
```

`Order.Ideal` owns the carrier, information order and principal embedding.
`CompletePartialOrder`, `ScottContinuous` and `IsLUB` retain their standard
Mathlib owners. The actual observation CPO, semantic cons, strict semantic fold,
generic ideal extension and fusion theorem are unchanged from the [directed-limit construction](adwh-directed-limits.md).
No additional domain, order, completion, continuity or fusion framework is
introduced. Labels have no order assumption.

The two continuity results reuse fold-input continuity and fold-seed continuity.
Both arguments range over all observation ideals. The constructor laws retain
bottom, known nil and semantic cons, and `append_right_nil` reuses the existing
constructor-fold identity. `append_ofList` refines ordinary finite `List`
append. The normal aggregate imports `Examples.PartialSpineAppend`, bringing
both new modules into the integrated build and proof-audit closure.

## An independent account of the finite boundary

The previously established `view` records an ordinary finite prefix and a
Boolean completed-end flag. The new principal refinement is:

```lean
append (Ideal.principal s) ys =
  (view s).1.foldr Observations.cons (if (view s).2 then ys else ⊥)
```

This follows from the existing finite fold's independent prefix/end equation,
after principal refinement of the semantic fold. The suffix is selected by the
end flag, independently of the append implementation's name or recursion.

| Left observation | Seed after the known labels | Consequence |
|---|---|---|
| Bottom | Bottom | A nonempty suffix remains invisible. |
| Known nil | The suffix | Every suffix observation is available. |
| Completed `ofList pre` | The suffix | Ordinary cons folding prepends `pre` to any suffix ideal. |
| Open `openPrefix pre` | Bottom | The result is the same principal open prefix for every suffix. |
| Infinite `stream sigma` | No completed end occurs | The result is the same stream for every suffix. |

`append_ofList_left` exposes the completed case with an arbitrary suffix.
`append_openPrefix` retains the entire open principal ideal:

```lean
append (Ideal.principal (openPrefix pre)) ys =
  Ideal.principal (openPrefix pre)
```

This is stronger than the source helper restricted to stream prefixes. Through
the existing `foldr_principal`, it supplies that helper for every ordinary
finite prefix. A known prefix is not completed by appending a suffix to its
unknown end.

`append_stream` applies left Scott continuity to the existing directed
least-upper-bound family of principal `openPrefix (sigma.take n)` observations.
Each member is fixed by `append_openPrefix`. Uniqueness of the least upper
bound then identifies the appended ideal with the independently defined
stream. This uses ordinary `Stream'.take` and the existing stream ideal; it
does not define a second stream semantics.

`append_ofList_stream` connects a completed prefix to Mathlib's standard
`Stream'.appendStream'`. Its cons case uses the semantic append equation and
the existing stream-cons theorem. This gives consumers an independent ordinary
stream whose finite observations can be calculated directly.

## Fold composition and associativity

For a CPO result, an arbitrary seed `e`, and Scott-continuous tail steps, the
public composition law is:

```lean
Observations.foldr f e (append xs ys) =
  Observations.foldr f (Observations.foldr f e ys) xs
```

Its proof uses the existing strict continuous fold-fusion theorem. The observer
is `Observations.foldr f e`; its bottom law supplies strictness, and its semantic
cons equation supplies commutation. The target seed is the interpreted suffix
`Observations.foldr f e ys`. It is not replaced by `e`.

The theorem retains the source's continuity premise on each tail step. A
monotone algebra already gives continuity in the input ideal, but that alone
does not supply every semantic cons equation. Associativity is the specialization
of this public fold/append law to semantic cons and the last suffix as seed.
It is therefore available for arbitrary partial or infinite operands.

Right Scott continuity does not imply right strictness. The retained example
appends bottom to a completed singleton. Its known head survives, yielding
`Observations.cons a bottom`, which is not bottom by the existing nonstrict-cons
theorem. Left strictness is a separate valid law.

## Connected producer and function consumers

`PartialSpineAppend.append_guarded` and `append_paused` connect the semantic
stream law to the actual producer observation API. Appending any suffix leaves
either observation ideal unchanged. Their all-cuts laws preserve equality of
the entire `Nat -> Observations` function, not merely one selected coordinate.

`counting_allCuts_and_deliveries` specializes these functions to the existing
counting coalgebra and retains the existing `Delivers` witnesses alongside
them. For a start `s` and prefix length `n`, guarded delivery has `n`
transitions; paused delivery has `2*n`. The concrete case starting at 4 retains
the prefix `[4,5,6]` and final state 7 after 3 or 6 transitions. The witnesses
describe the input producers. No transition count is assigned to the
noncomputable semantic append operation.

`first_append` consumes the public fold/append theorem with the continuous
tail-ignoring step `fun a _ => p a`. Its new seed is `first p ys`. A retained nil
case followed by paused counting from 4 consequently returns `p 4` through that
law. `counting_first` also shows directly that an infinite counting left input
returns its own first label after any suffix is appended.

The completed/open boundary is retained in a connected calculation:

| Left prefix followed by actual counting from 4 | Result of `allCuts ... 4` |
|---|---|
| Completed `[1,2]` | Principal open prefix `[1,2,4,5]` |
| Open `[1,2]` | Principal open prefix `[1,2]` |

The completed case uses `append_ofList_stream` and the existing `allCuts_stream`
consumer before calculating a standard stream prefix. The open case uses the
new general open-prefix law and the existing finite cut refinement. Both ends
remain unknown: a constructor budget of four does not invent a final nil.
The general open-prefix consumer quantifies over every budget and every suffix.

## Source correspondence and scope

The companion `adwh-partial-append-provenance.tsv` maps all twelve selected
source declarations exactly once. It preserves their original inventory
statements, locations, hashes and qualifications, then records actual owners
and adaptation decisions. The source is checkpoint 335's
`ADWH/Chapter01/InfiniteListFusion.lean`, SHA-256
`5361a0bafad1f966393222bb0ec0ee7d1aee15de123541c4899e14c467d3a4da`.
The supplied archive SHA-256 is
`9e8bee022149e8456c9c4ab318f3be0d5d7f8361c25e7409cfe1c12bf8eb812c`.
Standard owners refer to the repository's pinned Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

The selected rows are `append`, both one-sided continuity laws, `append_bottom`,
`append_nil`, `append_cons`, `append_right_nil`, `append_ofList`, `foldr_append`,
`append_assoc`, `consFold_streamPrefix`, and `append_stream`. The source prefix
helper maps to the stronger `append_openPrefix` plus existing principal-fold
refinement, rather than an additional source-shaped wrapper. The independent
view, arbitrary completed-prefix and ordinary-stream bridges strengthen the
retained client interface without selecting further source operators.

[Concat](adwh-partial-concat.md) and the other operator developments use this
append interface. Their source obligations are recorded in their own ledgers;
the append result alone does not establish chapter completion.

The model is a denotational account of finite observations over fixed labels.
It does not add an executable lazy-language evaluator, prove whole-language or
compiler adequacy, equate observation ideals with runtime costs, or make claims
about sharing, allocation or memory. A failed bounded producer search is still
not a proof of divergence. The excluded queens-16 numerical proof remains out
of scope. Focused elaboration and self statement inspection support development;
integrated build, exhaustive audit and independent review remain separate gates.
