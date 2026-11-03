# Occurrence cursors through indexed feedback

Issue [#219](https://github.com/VladimirMarko/conaled/issues/219) preserves a
selected occurrence while a feedback history grows. Forward storage appends each
new input; reverse storage prepends it. Both expose the same ordered history, but
their occurrence cursors evolve differently. The certificate is actual
`Fin history.length` data in `Type`, so two equal payloads can remain distinct
occurrences.

## A certificate over the original solution

[DependentFeedback](../../Applications/Progress/DependentFeedback.lean) takes an
existing initialized feedback machine `f`, a family `C : S → Type`, an initial
witness `c₀ : C f.initial`, and an operation

```text
advance : (a : A) → (s : S) → C s → C (f.step (a,s)).2
```

`lift` constructs the ordinary machine on `Sigma C`. It runs the original body
and advances the accompanying witness. `projection` uses existing
`Feedback.transport` to prove that its first component is the original recursive
state. `certificate` transports the actual second component along that equality,
with result type `C (state f input n)`. It does not choose a witness from a
proposition asserting existence.

`certificate_zero` and `certificate_step` establish the initialization and the
supplied dependent recurrence after this transport. `advance_cast` states the
cast/advance coherence used in the step equation.

For two machines, the reusable `transport` result accepts a base relation `R`, a
family relation `E : DependentSquares.TyRel R C D`, related initial witnesses,
ordinary input/output and state-step compatibility, and fiber-step compatibility.
The fiber law uses the same next-state relation proof as the ordinary step law.
The proof invokes existing feedback transport on `DependentSquares.extRel E` and
then `cast_related` to relate the actual certificate sections over both original
solutions. The only existential in its conclusion packages the base relation
proof in `Prop`; the two compared witnesses are the specified certificate
functions in `Type`.

This helper is restricted to the selected `Type`-level interfaces. It adds no
dependent-feedback syntax or new logical-relations fundamental theorem.

## Forward and reverse histories

[OccurrenceCursor](../../Applications/Progress/OccurrenceCursor.lean) supplies the
concrete client:

| Component | Forward representation | Reverse representation |
| --- | --- | --- |
| State update on input `a` | `s ++ [a]` | `a :: t` |
| Observable history | New forward state | Reverse of new stored state |
| Cursor family | `Fin s.length` | `Fin t.length` |
| Cursor update | Keep numeric index | Increment numeric index |

The base relation is `s = t.reverse`. The fiber relation is
`i.val + j.val + 1 = s.length`. `encode` uses `Fin.rev` and a length cast to
translate a forward cursor. `encode_advance` proves the actual square connecting
that translation with the two different cursor updates. Bounds and lengths are
proved from existing list/Fin facts; `lookup` uses the existing reverse lookup
lemma.

`cursors_related` instantiates the generic dependent transport at every input
stream and prefix length. `cursor_lookup` derives equality of the payloads
selected by those related cursors. `selected_value` separately proves that the
selected payload remains the initially chosen one at every prefix, using the
existing feedback transport again. Agreement between two stores therefore does
not stand in for retention of the original selection.

## Substitution and finite temporal certificates

The parameter context is `(inputStream, observationIndex)`. The two families
return cursors in the corresponding feedback states, and `forwardSection` and
`backwardSection` return their actual certificates. `sections_related` packages
the arbitrary-prefix theorem as `DependentSquares.TermRelated`.

The [checked uses](../../Examples/IndexedFeedback.lean) instantiate existing
`term_sub_related` for the nonidentity substitution that increments the
observation index. They also use identity and composition laws for substitution:
two successive increments observe index two when starting at zero. These are
changes of observation parameters, not a theorem about changing the operational
clock or preserving causality under arbitrary time maps.

`mapUntil` maps terminal certificates from the genuine evolving forward cursor
family to the reverse family. Waiting evidence is `PUnit`; the terminal evidence
is a cursor at the terminal index. `until_related` reuses `Until.Rel.map`, and
examples reuse map composition and horizon preservation. A two-wait witness
terminates at index two with the selected occurrence intact. This is a finite
observation certificate over an already defined solution; it proves no
scheduler fairness or eventual arrival.

## Independent cases and failures

The initial forward and reverse lists are both `[7,7]`. Selecting the first
forward occurrence gives cursor zero and reverse cursor one. After inputs
`[3,4]`, the checked states and cursors are:

```text
forward: [7,7,3,4], cursor 0
reverse: [4,3,7,7], cursor 3
```

Both select seven. The second equal occurrence instead has final cursors one and
two. Universal examples connect these observations to `cursors_related`,
`cursor_lookup`, `selected_value` and the explicit dependent recurrence equations.
The temporal example retains horizon two and reverse terminal cursor three.

Three negative cases expose separate obligations:

- No function of payload seven alone can reconstruct both distinct original
  `Fin 2` occurrences. Erasing occurrence identity loses information.
- An empty initial history has no `Fin 0` cursor. Initialization needs an actual
  selected position.
- Keeping the reverse index fixed breaks `encode_advance`. For the second
  occurrence, reverse index zero incorrectly selects newly prepended three;
  incrementing it correctly retains seven. The primary example's reverse index
  one would still select seven after one step, so payload equality alone would
  conceal that occurrence error.

The independently authored client mathematics consists of two history bodies,
two cursor advances, initial positions, the reversal relation, its step law and
the cursor compatibility/lookup proofs. Generic feedback lifting and transport,
dependent reindexing, temporal maps and horizon laws are reused. Remaining
obligations for a new client are its family, initial witness, advance operation,
base/fiber laws and any casts connecting its chosen indices. Ordinary Lean
callers can use lists, `Fin` and dependent pairs directly; no syntax wrapper is
required.

This bounded result contributes to [#36](https://github.com/VladimirMarko/conaled/issues/36)
and the [correspondence programme](correspondence-contracts-and-integration.md).
It does not complete #107/#108, smooth-model gates, a modal language, or a general
recursion theory. Existing STLC higher-order relational preservation remains
available independently.
