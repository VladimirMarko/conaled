# Assisted author outcome for #293

Both tasks are checked. The best source is `attempts/Attempt02.lean`, SHA-256
`555bfb48de9d38bc7f68dfbc7207d5e5f79f2d253b0cc2e69199d780aaf9b83a`.
Its immutable checked copy is `attempts/checks/Attempt02/Source.lean`.
All declarations are in `ProofRequirementTrial.Assisted`.

Start: 2026-11-04T20:41:18Z. End is recorded below after this report is written.
The cap was 2026-11-04T21:01:18Z. Task order was E, then W. No crossover,
external sources, other author attempts, private reference solutions, nested
agents or mathematical intervention beyond the supplied ledger were used.
Metadata and prior exposure are in `session-metadata.md`. Exact effective model
configuration, hidden serving revision, token use and price are unavailable.
The developer identity says Codex based on GPT-6; that does not identify the
serving revision or reasoning setting. No session-transcript export was exposed.

E uses `ReversesOperation m f`, the binary law
`∀ x y, f (m x y) = m (f y) (f x)`. The generic `reverseBlocks` applies that
law to `(x, m y z)` and `(y, z)`, using congruence and transitivity. Its conclusion
has exactly the requested right-nested input and left-nested output. It needs
neither a unit, associativity nor involutivity. The law is a useful local binary
requirement, not the requested three-input conclusion assumed as a field.
No claim of globally weakest requirements is made.

The source's ambient right-unit hypothesis is unused. Its body nevertheless
uses `List.reverse_reverse` twice, then `List.reverse_append` twice. The ledger
made that distinction explicit. `reverseBlocks_replay` retains the ambient law,
uses the involutive law in both cancelling congruence steps, and then reverses
the two operations. `list_replay` supplies `List.append_nil`,
`List.reverse_reverse` and the proved list reversal law. The changed generic
proof removes those first two steps; their endpoints were equal before the
remaining argument began. The replay and changed proof have literally the
same conclusion. The latter no longer takes the unit or involution assumptions.

`list_reverses` discharges the remaining law with `List.reverse_append`.
`bool_reverses` discharges it by the four Boolean cases. Both
`list_reverseBlocks` and `bool_reverseBlocks` invoke the generic theorem.
The retained applications use those specializations before reducing the final
concrete result: empty lists give `[]`; `[1,2]`, `[3]`, `[4,5]` give
`[5,4,3,2,1]`; `true`, `false`, `true` gives `false`.
`bad_conclusion` checks inequality for the requested Boolean negative input
`true,false,false`. `bad_obligation` rejects the proposed binary law at
`true,false`: its two sides reduce to `true` and `false`. Thus rejection is
both a failed interface obligation and a concrete failure of the conclusion.

W uses `RightUnit m e`, namely `∀ x, m x e = x`, with arbitrary types `A`, `B`
and observation `observe : A → B`. This is deliberately a sufficient carrier
law; it is stronger than preservation of the observation alone and is not
claimed necessary for every observation. It permits reuse for any observation
without an injectivity assumption. `select` follows the original dependency
pattern exactly: apply the unit law to `x`, take symmetry, apply congruence under
`observe`, and pair that proof with `x`. `select_value` is definitional equality.
The right-unit law assumes no subtype construction or projection theorem.

The W argument did not change its mathematical dependencies: `RightUnit`
replaces the concrete `List.append_nil` leaf, and `select` itself is the generic
source-body replay. `select_value` replays `Source.selected_value` by reduction.
The list target uses `List.append_nil`; the Boolean target uses its two cases.
`listSelected` and `boolSelected` call `select` with those obligation proofs.
Their projection theorems call `select_value`. Checked applications retain
`[]`, `[1,2]` and `true`. `listSelected_source` proves equality with
`Source.selected` as subtype data by `Subtype.ext` and the generic projection
theorem. This retains the selected value and does not replace the result by
mere existence.

For the Nat negative model, `natWitness` supplies the value `1`, proving that
the required subtype at `x=0` is inhabited. `nat_selection_impossible` proves
there is no inhabitant with first projection `0`, since its property would
force `0=1`. `nat_rightUnit_missing` rejects the proposed law at `0`;
`nat_observation_law_missing` also rejects its observation-level consequence.
These distinguish existence from the required selection.

For the successful list fiber at `[1]`, `alternative` selects `[2]`, whose
length is also one. `selected_alternative_differ` proves its first projection
differs from the generic selection `[1]`. `no_projection_recovery` proves the
general obstruction: all proofs of the same `Nonempty` proposition are equal,
so any function from that proposition returns the same output for both erased
witnesses. Requiring it to recover each original first projection contradicts
their inequality. `list_erasure_no_recovery` instantiates this theorem with the
two retained witnesses of the exact same subtype. It rejects recovery of every
original witness; it does not reject choosing some inhabitant.

Statement review covered every family of declarations and its concrete cases.
The E laws quantify over arbitrary pairs before the theorem quantifies over all
three inputs, with the requested parenthesization and ordinary Lean equality.
Both obligation predicates have checked target inhabitants. W quantifies over
arbitrary carrier and observation types, and its construction is available for
each supplied `x` after the shared right-unit law is provided. The subtype
predicate mentions that same `x`, and the first projection equals it.
The source equality is equality of subtype data; the differing-witness control
uses the same fixed fiber rather than unrelated propositions. The erasure
statement quantifies over every witness after choosing one recovery function,
which is the intended impossible order. No assumptions assert the requested
three-block theorem, selected subtype, projection theorem or erasure conclusion.
Concrete expected values and negative inputs remain those in the frozen tasks.

The prepared `dependency-ledger.md` was read before authoring and used to track
the opaque source leaves and the distinction between ambient and used
requirements. It is a manually prepared intervention, not extractor output.
No independent timing or causal benefit of that ledger can be inferred from
this one author run. The frozen example-driven-development, architectural,
language-direction, worked-example and writing guidance were read. General
Lean and mathematical knowledge supplied the interface choices and proofs.

Validation used the prescribed Nix/direnv wrapper and pinned Lean v4.35.0,
with the handoff's Mathlib v4.35.0 dependency. Both compiler checks exited 0
with empty Lean diagnostics. No failures or repairs occurred. Attempt01 is the
completed E artifact; Attempt02 retains E and adds W. Each invocation used a
fresh filename and has exact source bytes, source hash, inner command, UTC
start/end and exit status under `attempts/checks/Attempt01/` and
`attempts/checks/Attempt02/`. The plain authored command transcript is
`commands.txt`; it is not presented as a raw agent session export. Read/setup
commands also returned 0. There were no shell/setup failures requiring a
separate raw failure archive. The first combined guidance output was truncated;
narrower reads supplied the remaining material.

| Check | UTC start | UTC finish | Exit |
| --- | --- | --- | --- |
| Attempt01 | 2026-11-04T20:42:26.034880+00:00 | 2026-11-04T20:42:56.014001+00:00 | 0 |
| Attempt02 | 2026-11-04T20:43:34.656121+00:00 | 2026-11-04T20:43:35.814143+00:00 | 0 |

No formal task remains unfinished. The coordinator's independent recheck and
exhaustive axiom audit remain pending under the trial conduct. The author did
not access the repository audit entrypoint. There are no `sorry`, `admit`, new
axioms or native-evaluation shortcuts in the submitted source. No post-cap
repair was made.

Recorded UTC end: 2026-11-04T20:44:56.226719+00:00.
