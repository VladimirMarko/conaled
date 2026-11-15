# Combinatorial games and surreal numbers: source audit and integration plan

Research for [#442](https://github.com/VladimirMarko/conaled/issues/442),
2026-11-11. This is a source assessment and proposed acceptance contract, not
an adopted dependency, a formal implementation, or a successful Lean build.

Reuse `vihdzp/combinatorial-games`. Its sources already supply the ordered field
of surreals, real and ordinal embeddings, and infinite and infinitesimal examples
needed for the first milestone. Start compatibility work from the upstream
Lean 4.35 revision below; keep the local toolchain unchanged while testing its
Mathlib compatibility. The wider programme includes class-level mathematics,
normal forms and reusable interpretations. A small native integration does not
settle those interfaces. Dependency adoption remains pending owner discussion and
separate implementation authorization.

## Revisions, provenance and evidence boundary

| Source | Inspected revision and role |
|---|---|
| conaled | `1ecdea2376786920a043009a35712a5dec93723a`; Lean `v4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, from `lean-toolchain` and `lake-manifest.json`. |
| Upstream U | [`e8c95387dc4270cb965ef3c06c305a986691cec2`](https://github.com/vihdzp/combinatorial-games/tree/e8c95387dc4270cb965ef3c06c305a986691cec2); requested audit baseline, Lean `v4.36.0-rc2`, Mathlib `102de382a7e651ba15daa5e792b0fe2b872dbf8f`. |
| Compatibility candidate C | [`d949bd1fd3355d23175b8ed0834e0bb166e5fd3b`](https://github.com/vihdzp/combinatorial-games/tree/d949bd1fd3355d23175b8ed0834e0bb166e5fd3b), upstream's “update to 4.35” commit; Lean `v4.35.0`, Mathlib `089be84e24e41b7a26860084d1747195cf9299f3`. Matching Lean is established; compatibility with conaled's Mathlib is **unverified**. |

The two upstream checkouts, manifests, declaration searches and differences were
inspected directly. C and U both contain the first milestone APIs named below.
C precedes U's sign-expansion correspondence and later Hahn-series and nimber
extensions. Names such as C's `leftMoves_wpow` become U's `moves_left_wpow`;
do not combine files from the two revisions without an explicit adaptation.
Neither upstream nor conaled was compiled for this report. No cache result or
upstream README is being treated as a local build receipt.

[Upstream LICENSE][license] is Apache-2.0. Source headers preserve named authors,
including Violeta Hernández Palacios, Mario Carneiro, Kim Morrison, Aaron Liu
and the other contributors listed per file. The source is a maintained Lean
library, not a verbatim transcription of a book. Preserve its license, notices,
revision and changed-file provenance if adapting code. A dependency pin should
also record its complete resolved manifest in [SOURCES](../SOURCES.md), following
[ADR 0001](../adr/0001-modules-and-proof-dependencies.md).

Conway's [*On Numbers and Games*, 2001 publisher record][onag] supplies the
programme's reference (chapters 0–4 and 7–11). Its full text was not available
in this audit; no claim of checking its proofs is made. Schleicher–Stoll's
[version 2][ss], sections 2–4, was inspected for the mathematical distinctions:
set-sized options, proper-class collections, game equivalence, and short
numbers. Implementation claims below come from pinned code rather than either
book descriptions or upstream aspirations.

## Declaration-level coverage

Paths below are relative to `CombinatorialGames/` at U unless marked C.
“Implemented” means a definition or proof body is present in the inspected
source, not that this audit has compiled it.

| Area | Implemented APIs and assumptions | Boundary |
|---|---|---|
| Presentations | [Game/IGame][igame]: `IGame : Type (u + 1)`, `ofSets`, `moves`, `ofSetsRecOn`, `moveRecOn`. Its identity retains the actual left/right option sets. [Game/Functor][functor] implements this through `QPF.Fix GameFunctor`. | Well-founded play; options must be `Small.{u}`. Identical option sets and semantic equivalence are different relations. |
| Quotient and order | [Game/Basic][game]: `Game := Antisymmetrization IGame (· ≤ ·)`, `Game.mk_eq_mk`, `mk_add`, `mk_neg`, additive group instances. [Game/IGame][igame]: `zero_le`, `le_zero`, `zero_lf`, `lf_zero`, preorder and fuzziness. | Order is partial for games. `x ≈ y` means both inequalities; `x ‖ y` means neither. A quotient equality must not be used to identify option trees. |
| Outcomes | `IGame.zero_le : 0 ≤ x ↔ ∀ y ∈ xᴿ, 0 ⧏ y` and `le_zero : x ≤ 0 ↔ ∀ y ∈ xᴸ, y ⧏ 0`. These give recursive outcome reasoning. | The IGame documentation explicitly does not prove a separate strategy characterization. Four outcome classes are Left win, Right win, second-player win (`≈ 0`), first-player win (`‖ 0`). Proving an independent evaluator correct is additional work. Loopy-game outcomes are a separate theory. |
| Negation and disjunctive sum | `IGame.neg_ofSets` exchanges and negates options; `ofSets_add_ofSets` forms moves in either summand. `Game.mk_add` and `mk_neg` descend these operations. | `IGame` cancellation is up to `≈`; `Game` cancellation is equality. Multiplication does not in general descend to arbitrary game equivalence; see [Counterexamples/Multiplication][counter]. |
| Finite games | [Game/Classes][classes]: `Short` recursively requires finite move sets, `short_def`, `Short.finite_moves`. [Game/Birthday][birthday]: `short_iff_birthday_finite`, `birthdayFinset`, `mem_birthdayFinset`. | `Short` is a proposition, not an executable move enumeration. The semantic constructors are noncomputable. |
| Impartial games and nimbers | [Game/Classes][classes]: `Impartial`; [Grundy][grundy]: `grundy`, `nim_grundy_equiv`, `grundy_eq_zero_iff`, `grundy_add`, all with `[Impartial x]` and, for addition, `[Impartial y]`. [Nim][nim]: `moves_nim`, `nim_equiv_iff`. [Nimber/Field][nfield] has `Field Nimber`, characteristic two. [Algebraic][nalgebraic] has `_root_.IsAlgClosed Nimber`. | Nimber addition is nim addition, not surreal addition or ordinal addition. Finite heap labels must use the ordinal/nimber representation, not blindly a field natural cast (characteristic two). U's explicit `leastNoRoots_omega0` and `algClosure_zero` are `proof_wanted`, not proved formulas. |
| Numeric games | [Game/Classes][classes]: `Numeric.mk` requires every left option strictly below every right option and every option numeric. `Numeric.neg`, `.add`, `.not_fuzzy`; [Special][special]: `Numeric.half`, `not_numeric_star`. | Equivalent numeric values may have nonnumeric game presentations. Recognize the actual presentation or supply an appropriate representative; do not infer `Numeric` from arbitrary equivalence. |
| Surreal arithmetic | [Surreal/Basic][surreal]: `Surreal := Antisymmetrization (Subtype Numeric) (· ≤ ·)`, `mk`, `mk_eq_mk`, `LinearOrder`, `mk_add`, `mk_neg`. [Multiplication][mul] supplies commutative ring and `IsStrictOrderedRing`; [Division][div] supplies `Field Surreal`, `mk_inv`, `mk_div`. | Inverse congruence and multiplicative descent on IGame carry Numeric hypotheses. Inverse cancellation needs nonzero input; division by zero uses Lean's totalized field convention. The introductory phrase “complete ordered field” is not evidence of Dedekind completeness. |
| Reals and ordinals | [Real][real]: `Real.toIGame`, `Real.toSurreal`, `Real.toSurrealRingHom : ℝ →+*o Surreal`, `toSurreal_inv`, `toSurreal_div`. [Ordinal][ordinal]: `NatOrdinal.toSurreal : NatOrdinal ↪o Surreal`, `toSurreal_add`, `toSurreal_mul`, `toSurrealRingHom`. | `NatOrdinal` uses natural (Hessenberg) arithmetic. These are not preservation laws for ordinary noncommutative ordinal addition/multiplication. Every ordinal of the selected host universe is represented, not a single type containing ordinals of every Lean universe. |
| Birthdays | [Game/Birthday][birthday]: `IGame.birthday : IGame.{u} → NatOrdinal.{u}`, `birthday_lt_of_mem_moves`, `birthday_add`; `Game.birthday_mk_le`, `birthday_add_le`. [Surreal/Birthday/Basic][sbirthday] supplies quotient birthdays and bounds. | Presentation birthdays can exceed quotient birthdays. `Surreal.birthday_mul_le` and [Birthday/Dyadic][sdyadic]'s `Surreal.birthday_dyadic` remain `proof_wanted` at U. Real.lean's birthday-at-most-omega claim remains a TODO. |
| Canonical and normal forms | [Canonical][canonical]: `undominate_equiv (x) [Short x]`. [Dyadic][dyadic]: `toDyadic`, `equiv_toIGame_toDyadic`, arithmetic laws under `[Short x] [Numeric x]`. [SignExpansion/Surreal][sign] at U: `toSignExpansion`, `length_toSignExpansion`, `range_toSignExpansion = Set.ofPred SignExpansion.Small`. | Undomination is not a complete reversible-option canonicalization algorithm. U's sign correspondence is stronger than C's sign-expansion files. Do not promise it in C without a backport. |
| Infinite scale and series | [Pow][pow]: `wpow_pos`, `wpow_add`, `wpow_neg`, `mul_wpow_lt_wpow`, `wpow_lt_mul_wpow`; [Leading][leading] supplies leading-term theory. [HahnSeries/Basic][hahn]: `SurrealHahnSeries`, `mk`, field structure and `TermSeq.surrealHahnSeriesEquiv`. | The last equivalence relates ordinal-indexed term sequences to small-support Hahn series. It is **not** an ordered-field isomorphism `Surreal ≃+* SurrealHahnSeries`. That full normal-form interpretation remains missing in the inspected tree. |

Searches included `proof_wanted`, `sorry`, `axiom`, `lift`, and the declaration
names above. A `proof_wanted` is an outstanding statement, not usable evidence
of its payload. A source scan does not replace a transitive axiom audit of the
actual imported declarations.

## Universe and closure audit

`IGame.{u}`, `Game.{u}` and `Surreal.{u}` inhabit `Type (u + 1)`.
An option set `s : Set IGame.{u}` has a subtype of elements in that larger
universe, but `[Small.{u} s]` witnesses an equivalence with some `Type u`.
Thus constructors accept arbitrary `u`-small families, including infinite ones.
They do not accept an arbitrary large set merely because Lean spells it `Set`.
`GameFunctor`'s polynomial representation indexes each player's options by a
`Type u`; its `Shrink`/`equivShrink` use makes this boundary explicit. [Sources:
GameFunctor][functor], [IGame][igame].

For numbers, `Surreal.ofSets_eq_mk` additionally requires separation
`∀ a ∈ s, ∀ b ∈ t, a < b`. The constructor supplies a number between the
option sets; `lt_ofSets_of_mem_left` and `ofSets_lt_of_mem_right` prove the
comparison laws. Arithmetic and reciprocal remain in the same `Surreal.{u}`,
as do omega powers. This is closure under these operations and small separated
cuts, not closure under arbitrary large cuts or order completeness.
`Surreal.Cut` has a `CompleteLinearOrder` and two embeddings `leftSurreal` and
`rightSurreal`; it is a different carrier which also describes gaps. [Sources:
Surreal/Basic][surreal], [Division][div], [Pow][pow], [Cut][cut].

The classical collection of all games or all surreals is a proper class relative
to its set theory. The host's small/large distinction models a related size
boundary, but does not itself prove an interpretation of ZFC or a class theory.
A source language can quantify over the class of all numbers **inside a
represented setting**, even when the setting and its satisfaction relation are
host types. Such an internal account need not be finite or birthday-bounded.
Its quantifiers range over that setting's numbers, not automatically over the
union of all host universes. Establishing a comparison with native
`Surreal.{u}` requires a specified model, its set/class distinction, recursion
and collection principles, and a checked interpretation. The paper's
proper-class explanation is in [Schleicher–Stoll §2.3][ss].

No dedicated cross-universe `IGame.lift`, `Game.lift` or `Surreal.lift`, with
preservation/reflection laws, was found in U or C. `Quotient.lift`, order lifts
and cardinal/ordinal lifts in these files do not provide that API. There is a
useful existing construction: [GameGraph][graph] allows states `α : Type v`,
`u`-small option fibers, and a `GameGraph.WellFounded` proof; `toIGame` then
lands in `IGame.{u}`. Reinterpreting the graph of an existing IGame's moves in
a larger universe is a candidate lift construction. New proofs must establish
identity-option compatibility, order reflection, equivalence descent, numeric
preservation, arithmetic preservation and coherence of repeated lifts. A
universe-polymorphic declaration alone establishes none of these comparisons.

Birthday restrictions are separate. `IGame.small_setOfPred_birthday_lt` and
`small_setOfPred_birthday_le` prove smallness for a fixed ordinal bound.
`short_iff_birthday_finite` identifies finite birthdays with Short games.
Short numeric values are dyadic by `equiv_toIGame_toDyadic`; their arithmetic
forms a ring, not a field (the inverse of 3 is not dyadic). They contain neither
all reals nor infinite ordinals. A fixed birthday bound is not generally
closed under addition: already values born by day 1 contain 1 but not 1 + 1.
Field-closed ordinal stages require separate closure theorems and bounds;
none is inferred here from smallness. [Sources: Birthday][birthday],
[Dyadic][dyadic], [Schleicher–Stoll §3.2][ss].

### Evidence handed to #443

[#443](https://github.com/VladimirMarko/conaled/issues/443) owns source rules,
author corpus, diagnostics and the checking/interpretation contract. Its
initial investigation and native integration can proceed independently.

| Required mathematical capability | Existing evidence | Additional obligation for a class-theoretic frontend |
|---|---|---|
| Quantify over numbers and reason with arithmetic | `Surreal.{u}` and its ordered field instances; quotient induction `Surreal.ind`. | Interpret class quantifiers and equality in a named setting; prove the supported logic sound. No global class-model interpretation is supplied upstream. |
| Form a number from a set-sized separated cut | Small option sets, `Surreal.ofSets_eq_mk`, the two strict comparison laws. | Translate internal set-size evidence to the interpretation's smallness witness and preserve separation and cut meaning. An internal proper class is not automatically an admissible option set. |
| Change host size or interpretation | `GameGraph.toIGame` with independent state/option universes; small birthday stages. | Construct the lift/transport comparison and coherence above. Absorb routine lifts in implementation where possible; do not require authors to hand-insert them into every argument. |
| Extend normal forms | Omega-power order/arithmetic, leading terms, small-support Hahn carrier, U's sign correspondence. | Prove the absent full Hahn interpretation and its support/size compatibility before transporting a normal-form theorem. |

This inventory neither chooses #443's foundation nor imposes birthday bounds
on its internal class quantifiers. The distinction is semantic; frontend
notation alone cannot establish the missing interpretation theorems.

## First checked integration target

These are **proposed theorem statements**, not checked examples in this report.
Use C's `CombinatorialGames.Game.Special`, `Surreal.Division`, `Surreal.Pow`
and `Game.Graph` (or their transitive imports). Avoid importing the entire
upstream umbrella merely to obtain these APIs.

1. Define the presentation examples using `IGame` notation:
   `z = !{∅ | ∅}`, `o = !{{0} | ∅}`, `m = -o`,
   `h = IGame.half = !{{0} | {1}}`, `s = IGame.star = !{{0} | {0}}`.
   Prove `z = 0`, `o = 1`, `m = -1`, `Numeric z`, `Numeric o`,
   `Numeric m`, `Numeric h`, `0 < h`, `h < 1`, `h + h ≈ 1`,
   `s ‖ 0` and `¬ Numeric s`. APIs: `Numeric.zero`, `.one`, `.neg`,
   `Numeric.half`, `zero_lt_half`, `half_lt_one`,
   `half_add_half_equiv_one`, `star_fuzzy_zero`, `not_numeric_star`.
2. Check presentation/quotient boundaries with
   `Game.mk (-x) = -Game.mk x`, `Game.mk (x + y) = Game.mk x + Game.mk y`
   for arbitrary `x y : IGame.{u}` and
   `Surreal.mk (x + y) = Surreal.mk x + Surreal.mk y` under both Numeric
   hypotheses. Check `Surreal.mk 0 = 0`, `Surreal.mk 1 = 1`,
   `Surreal.mk (-1) = -1`, and `Surreal.mk IGame.half = (2 : Surreal)⁻¹`.
   The last is `IGame.mk_half` in Division.lean; preserve its namespace.
3. In `Surreal.{u}`, define `W = ω^ (1 : Surreal)` and
   `e = ω^ (-1 : Surreal)`. Prove `0 < W`, `0 < e`,
   `∀ r : ℝ, (r : Surreal) < W`,
   `∀ r : ℝ, 0 < r → e < (r : Surreal)`, and `W * e = 1`.
   `Surreal.wpow_pos` proves positivity;
   `Surreal.mul_wpow_lt_wpow r (show (0 : Surreal) < 1 from …)`
   and `wpow_zero` give the infinite comparison.
   `Surreal.wpow_lt_mul_wpow hr (show (-1 : Surreal) < 0 from …)`
   gives the infinitesimal comparison. `wpow_add`, or `wpow_neg` and
   nonzero cancellation, gives the product identity. These source APIs exist
   in both C and U. There is no missing mathematical prerequisite for these
   particular examples; dependency compatibility and local checked proofs
   remain to be established. They are transfinite examples, not a finite-only
   demonstration.

### A caller that reuses the mathematics

Add a reusable ordered-additive-group lemma, independently of game syntax:
for any `K` with `[AddCommGroup K] [PartialOrder K] [IsOrderedAddMonoid K]`,
and any `a b e : K`,

```text
0 < e → e < b - a → a < a + e ∧ a + e < b
```

Its assumptions expose the ordered addition used by the proof. Specialize it to surreals with `a = (r : Surreal)`,
`b = (s : Surreal)`, `r < s : ℝ`, and the `e` above, yielding
`r < r + e ∧ r + e < s`. Use `Real.toSurrealRingHom` to transport subtraction
and strict positivity, then the positive-real bound on `e`. Recover the same
result through numeric IGame representatives using `Surreal.mk_add`,
`mk_lt_mk`, and `mk_eq_mk`; this tests descent rather than introducing another
arithmetic implementation. A second specialization to rational inputs in `ℝ`
checks the reusable lemma's scope independently of surreal presentations.

This is mathematical reuse and remains noncomputable for arbitrary surreal
inputs. If executable finite play is desired next, define a finite move table
and a terminating Boolean winner evaluator independently; interpret it through
`GameGraph.toIGame`, prove `moves_toIGame` correspondence, and prove its two
starting-player results equivalent to `0 ≤ x` and `x ≤ 0` as appropriate for
second-player winning. Keep that new adequacy theorem separate from `game_cmp`,
which constructs proofs of comparisons and is not an extracted general game
solver. Neither transfinite evaluation nor strategies are supplied by the
ordered-field caller.

## Dependency strategy and validation tasks

Pinned Mathlib's [Hyperreal.lean][hyperreal] defines `Hyperreal` as
`Germ (hyperfilter ℕ) ℝ`, with ordered-field instances, `ofReal`, `omega`,
`epsilon`, `coe_lt_omega`, `epsilon_pos` and `inv_omega`. This is a different
construction and has no game presentation, birthday or all-ordinal embedding
contract. It can provide another specialization of this ordered-additive-group argument, but cannot
substitute for the surreal integration.

| Route | Recommendation and remaining evidence |
|---|---|
| Reuse C directly | First test on conaled's existing Lean/Mathlib pins. C's manifest has a different Mathlib commit, so dependency resolution must select and record one coherent version. The existing source is sufficient mathematically for the milestone. A same-Lean match is not a successful dependency test. |
| Scoped adaptation of C | Preferred fallback if direct reuse fails. Pin a fork or maintained patch series, retain provenance, and change only demonstrated Mathlib API incompatibilities in the transitive import closure. Report each required change and test both downstream callers and affected upstream modules. Do not copy an independent replacement surreal theory into conaled. |
| Upstream contribution | Contribute generally useful compatibility fixes, cross-universe maps and missing preservation theorems. Publication requires its own authorization; this report does not send a contribution. Local integration can use a pinned reviewed patch while upstream review proceeds. |
| Adopt U through a toolchain upgrade | Defer unless separately justified by necessary capability or failed scoped adaptation. U's extra normal-form work is not needed for the initial examples. A coordinated Lean/Mathlib upgrade affects the whole monorepo and cannot be justified merely by avoiding C inspection. |

The following tasks are dependency-ordered proposals under
[#441](https://github.com/VladimirMarko/conaled/issues/441); they are not new
tracker issues created by this report.

1. **Dependency compatibility, owner #441 integration successor.** Resolve C
   against current Mathlib in an isolated checkout. Record exact compiler,
   dependency revisions, imports, errors and any patch. Acceptance: the selected
   upstream import closure compiles with the single resolved Mathlib; no
   admission or unsupported axiom is used by the intended callers. If a pin
   changes, update manifest/provenance and run README's fresh project acceptance.
   Tooling changes additionally require `nix flake check` and shell smoke check.
2. **Native examples and caller, same owner, after task 1.** Add the examples
   and reusable lemma above with example-driven statement review. Put reusable
   mathematics in `SquareKit/` only where its assumptions justify reuse; domain
   adapters belong in `Applications/`, checked callers in `Examples/`. Import
   the public examples through `SquareApplications.lean`. Acceptance: all
   numbered statements, the generic caller and its specializations compile,
   star remains nonnumeric, and the public-entrypoint coverage check and
   exhaustive transitive axiom audit include the local adapters/callers.
   Run `./check.sh --candidate HEAD`, then `--verify-candidate HEAD`; dependency
   changes require the applicable `--fresh` mode. Independent Standards/Spec
   review remains required. Do not broaden the audit's allowed axiom set.
3. **Size transport, owner #441 with #443/#235, after task 1; can run beside
   task 2.** Prototype the graph-based universe map. Acceptance: explicit
   universe parameters, option-image theorem, injectivity/order reflection,
   quotient descent, numeric and arithmetic preservation, identity/composition
   coherence, and checked examples crossing two lifts. Failure must name the
   missing theorem or size hypothesis. Native integration does not wait for
   this task. Formal validation and review are the same as task 2.
4. **Class interpretation and normal-form continuation, owners #443 and #441
   respectively, coordinated by #235/#36/#8.** #443 consumes the preceding
   evidence and defines its own interpretation acceptance. #441 first checks
   current upstream for completed Hahn and birthday results before proposing
   contributions. Acceptance for normal forms must include an actual
   surreal/Hahn comparison, uniqueness and arithmetic/order preservation with
   support bounds, not just the existing TermSeq equivalence. These programmes
   remain open when the native milestone lands.

Open decisions are the tested dependency pin/patch (task 1), the exact lift
laws and interpretation relation (task 3 and #443), and which upstream
normal-form gaps merit the next contribution (task 4). This report changes no
ADR or library interface. Documentation validation consists of checking source
paths and declarations at both frozen revisions, checking the recorded pins
and local links, and `git diff --check`; it does not establish elaboration,
axiom dependencies or runtime behavior.

[license]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/LICENSE
[onag]: https://www.routledge.com/on-numbers-and-games/conway/p/book/9781568811277
[ss]: https://arxiv.org/html/math/0410026v2
[igame]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Game/IGame.lean
[functor]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Game/Functor.lean
[game]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Game/Basic.lean
[counter]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Counterexamples/Multiplication.lean
[classes]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Game/Classes.lean
[birthday]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Game/Birthday.lean
[grundy]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Game/Impartial/Grundy.lean
[nim]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Game/Specific/Nim.lean
[nfield]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Nimber/Field.lean
[nalgebraic]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Nimber/SimplestExtension/Algebraic.lean
[special]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Game/Special.lean
[surreal]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Surreal/Basic.lean
[mul]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Surreal/Multiplication.lean
[div]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Surreal/Division.lean
[real]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Surreal/Real.lean
[ordinal]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Surreal/Ordinal.lean
[sbirthday]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Surreal/Birthday/Basic.lean
[sdyadic]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Surreal/Birthday/Dyadic.lean
[canonical]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Game/Canonical.lean
[dyadic]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Surreal/Dyadic.lean
[sign]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/SignExpansion/Surreal.lean
[pow]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Surreal/Pow.lean
[leading]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Surreal/Leading.lean
[hahn]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Surreal/HahnSeries/Basic.lean
[cut]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Surreal/Cut.lean
[graph]: https://github.com/vihdzp/combinatorial-games/blob/e8c95387dc4270cb965ef3c06c305a986691cec2/CombinatorialGames/Game/Graph.lean
[hyperreal]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Real/Hyperreal.lean
