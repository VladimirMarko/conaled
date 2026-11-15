# Manual author outcome

E and W are checked in `attempts/Attempt03.lean`. Its immutable checked copy is
`attempts/checks/Attempt03/Source.lean`, with SHA-256
`71c66b1c663b17b09a13eeae8b2349179a0379ffbb8cf9a0ffd9628547df9e04`.
The final check exited 0 without diagnostics. All declarations are under
`ProofRequirementTrial.Manual`.

Start: 2026-11-04T20:41:09Z. The end timestamp below includes reading, authoring,
checks, and this report. Work stopped before the 20-minute cap.

## E requirements and interpretations

`ReversalRequirements m f` requires the binary law
`f (m x y) = m (f y) (f x)` for all inputs. `reverseBlocks` applies it twice,
using equality congruence for the second application. It concludes exactly
`f (m x (m y z)) = m (m (f z) (f y)) (f x)` for arbitrary `x`, `y`, and `z`.
The interface does not contain this three-block conclusion. No associativity,
unit, or involution is required by the changed proof.

The source's ambient law is `∀ t, t ++ [] = t`. Its proof body does not use it.
The body uses `List.reverse_reverse` twice, first backwards and then forwards,
and `List.reverse_append` twice, together with equality symmetry, congruence,
and transitivity. `OriginalReversalRequirements` records involution and the
binary reversal law. `reverseBlocks_original` replays every source step and
retains the unused ambient right-unit law as a separate argument. Removing
the two canceling steps yields the weaker generic proof. Both proofs have the
same three-block equality, with the same input and output parenthesization.

The list interpretation proves the binary obligation with
`List.reverse_append`; its replay additionally uses `List.reverse_reverse`
and `List.append_nil`. The Boolean interpretation proves the binary obligation
by the four Boolean cases. Its involution and right-unit obligations follow
by reduction and Boolean cases. Both final interpretation theorems call the
weaker generic theorem, and both original-dependency replays also check.

The retained applications use these interpretation theorems: all-empty lists
give `[]`; inputs `[1,2]`, `[3]`, `[4,5]` give `[5,4,3,2,1]`; Boolean inputs
`true`, `false`, `true` give `false`.

`bad_target_failure` checks the requested counterexample at `true`, `false`,
`false`. Its two sides reduce to `true` and `false`. The missing interface
obligation is binary reversal: at `true`, `false`, its two sides already
differ. `bad_requirements_impossible` derives rejection from that failed law.

## W requirements, selection, and erasure

`RightUnit m e` names the source dependency `∀ x, m x e = x`.
`selected_original` replays the source construction, using the symmetric
right-unit equation under `congrArg observe`. Its projection theorem is
reflexivity, as in `Source.selected_value`.

`ObservedRightUnit m e observe` weakens the law to
`∀ x, observe (m x e) = observe x`. It is a law on the supplied operations;
it does not assume a selected subtype value or its projection theorem.
`observedRightUnit_of_rightUnit` proves the weakening. `selected` packages
the supplied `x` with the symmetric observed equation. `selected_value`
proves that its first projection is exactly `x` for every input. The carrier
and observation type are independent universe-polymorphic types.

Both models prove right-unit laws and obtain the observed laws through the
generic weakening theorem. `selectedList` and `selectedBool` call the generic
construction; their projection theorems call its generic projection theorem.
The applications retain `[]`, `[1,2]`, and `true` as values.
`selected_agrees_original` checks equality of the whole subtype values after
weakening. The list original replay equals `Source.selected`; the final list
specialization also equals `Source.selected` as subtype data, using subtype
extensionality and the generic projection result. The Boolean original replay
retains its projection too.

For `Nat.add`, unit `1`, observation `id`, and input `0`, `natAlternative`
is the witness `1`. `nat_witness_exists` proves the fiber inhabited, while
`nat_selection_impossible` proves that no member has first projection `0`.
`nat_observed_right_unit_missing` rejects the required observed unit law at
zero, where it would assert `1 = 0`.

For list input `[1]`, `listAlternative` is `[2]` in exactly the same subtype
as `selectedList [1]`. Their lengths meet the same condition; their first
projections differ. `erased_witnesses_equal` checks equality of their
`Nonempty` erasures. `no_recovery_from_nonempty` rules out any function of
that erased evidence which recovers every original witness's first projection.
The contradiction uses both different witnesses and proof irrelevance of the
erased inputs. It does not claim that no witness can be chosen from an
inhabited fiber; it rejects preserving every original choice.

## Statement review

The universal E results quantify over arbitrary operations and then every
triple; they retain exact Lean equality and the required parenthesization.
Their binary-law assumptions are inhabited by both requested models. The
original replay preserves source dependencies while the changed proof removes
only canceled steps. The negative target violates a stated obligation and the
requested conclusion on the fixed concrete inputs.

The W construction quantifies over arbitrary carrier and observation types,
operations, law evidence, and each supplied input. It returns subtype data,
retains the given input, and uses equality of observations with the specified
`m x e`. All generic comparisons and source recovery concern subtype values,
not only propositions of existence. The natural-number negative example
separates inhabitance from selecting a specified input. The list erasure
counterexample fixes one common fiber and quantifies over all its witnesses,
so differing observation fibers cannot explain the contradiction. The
noninjective list observation supplies two distinct valid values.

No new axioms, placeholders, or native-evaluation shortcuts occur in the
successful artifact. Exhaustive repository axiom auditing and independent
review remain with the coordinator under the frozen conduct rules.

## Checks, failure, and assistance

| Attempt | Scope | UTC check start | UTC check finish | Exit |
| --- | --- | --- | --- | --- |
| 01 | E complete | 20:42:06.718880 | 20:42:33.272134 | 0 |
| 02 | E and W | 20:43:21.532331 | 20:43:22.530905 | 1 |
| 03 | E and W repaired | 20:43:38.187014 | 20:43:39.446901 | 0 |

All checks occurred on 2026-11-04. Attempt 01 emitted syntax and proposition
style warnings. Attempt 02 adopted the new structure syntax and changed the
four proposition-valued model declarations from `def` to `theorem`. Its only
failure was `Trans Eq Eq` synthesis in the chained proof of
`selectedList_eq_source`. Attempt 03 replaced that chain with `Subtype.ext`
and `selectedList_value`; it changed no statement or expected result. This
was an elaboration repair, not evidence of a false mathematical claim.

Every checked source and raw compiler diagnostic remains in its numbered
check directory with exact command, source hash, UTC start/end, and exit code.
`AttemptNN.wrapper.log` also retains raw outer-command output.
`commands.txt` is the authored plain command transcript. No shell/setup
failure occurred. No raw agent session export was available or fabricated.

The author used the frozen conduct, tasks, public support, route prompt,
manifest, wrapper, and guidance. No dependency ledger was supplied. There was
no prior exposure to task design, private solutions, #286's argument, or other
author attempts in this fresh context. The supplied guidance and tasks name
prior issues; those references were not followed. No external source, other
author, nested agent, or mathematical assistance was used. The inherited
session identifies the author as Codex based on GPT-6; it exposes no precise
model identifier or reasoning setting. Hidden serving revision, effective
token usage, and price are unavailable. The pinned toolchain is Lean 4.35.0
with Mathlib v4.35.0, as supplied.

No author task or negative control remains incomplete. The intermediate
failure is retained as evidence and superseded by the checked artifact.

End UTC: 2026-11-04T20:44:57Z
