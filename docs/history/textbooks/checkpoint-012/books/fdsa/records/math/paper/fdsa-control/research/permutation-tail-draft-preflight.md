# Conditional-tail examples and documentation: bounded source preflight

Recorded 2026-11-02 by the separate `tail_examples_preflight` contributor.
This is a read-only statement/API assessment within the existing book
implementation loop. **No source-level finding was identified in the scoped
root-owned content below.** This is not final Standards or Spec review, a
compiled-example result, an axiom audit, or an acceptance decision.

## Scope and exact inputs

The development checkout is `conaled-permutation-tail`, with the root-recorded
starting commit `4bb13e44a6c7e3277b69cbac9fd9dd37cd7780f8`. No Git command was
used during this assessment. Ordinary file SHA-256 reads established these
input identities after the content inspection:

| File relative to that checkout | Bytes | SHA-256 |
|---|---:|---|
| `Examples/PermutationTail.lean` | 8,775 | `7470b1889baf878488eca8dad1240e1ca419a925b6f18f853a82eccd1178abfe` |
| `docs/research/fdsa-permutation-tail.md` | 10,367 | `34162854a3bfabbec1e87bea6111b4939495cc27eb9ee811758dceaeb62dc96f` |
| `docs/research/fdsa-reconstruction-map.md` | 18,893 | `f519e995709de1e147439ebfc5a903a9e753883b49fd82f02d5bd484619acb9f` |
| `SquareApplications.lean` | 8,392 | `7aedfca880167dc6a66e1b49b7ce1c5210c5f97ad090817061c5961c0b1aa321` |

The first two files were read in full. Review of the reconstruction map was
limited to its new **Shared conditional remaining orders (draft)** section;
review of the public root was limited to its new `Examples.PermutationTail`
import. Their full-file hashes identify the surrounding input, not a claim
to have reviewed all older contents anew.

Governing frozen requirements:
`../reviews/permutation-tail-requirements.md`, 12,866 bytes, SHA-256
`80323e579fe63419a10d7b26eb55f7ac540fea98a8a7c9c4efe36dce5f088b9c`.
The coordinated, not-yet-elaborated API orders were read from
`../reviews/permutation-tail-start.md`, 4,119 bytes, SHA-256
`7513827aea4d3596424833662104178101e8a73459b92a19613bd9bc39fa88bc`.
The independent expectation file was read, not rerun:
`permutation-tail-calculations.json`, SHA-256
`b614ea7eb98b3aaba5c15006a967e1d8da51fc373d5b963c99cdccce6b4632eb`.

The core `Applications/Probability/PermutationTail.lean` and
`Examples/PermutationTailBoundary.lean` were being authored separately and
are explicitly excluded from this assessment. Neither their changing proofs
nor their completed interfaces are approved here. The main example's new
calls were compared with the recorded interface agreement; root must still
check them against the completed core and compile the actual candidate.

Repository guidance read included AGENTS, architectural quality,
example-driven development, domain guidance, the glossary, ADR index and
ADRs 0001/0010. The assessment retains their separation of operations,
observations and laws and their requirement for eventual whole-candidate
verification and exhaustive audit. It starts no additional review loop.

## Main example: mathematical and connection assessment

The initial observation is exactly the earlier inverse-permutation/filter
operation on Fin4, positions `[0,1,2,3]`, and S=`{0,2,3}`. The old example's
`positions`, `selected`, `law`, completeness/Nodup facts and `observed_law`
were inspected. The new `observed_hasLaw` uses that actual map equality and
finite-source measurability; it does not posit the desired first conditional
tail law. Its local discrete measurable structures agree with the earlier
concrete setup.

| New declaration group | Connected public input and assessment |
|---|---|
| `first_mass` | Uses `head_mass_of_hasLaw` with the established whole-order HasLaw; a=0 is a member of the three-element subset, giving 1/3. |
| `afterFirst_eq_uniformOn` | Uses the actual global-uniform conditioning identity. It is not generalized incorrectly to an arbitrary environment measure. |
| `tail_hasLaw`, `tail_map` | Observe the actual tail under `afterFirst`; the generic HasLaw and global map interfaces both target the orders of S.erase0=`{2,3}`. |
| `tail_23_mass` | Uses the new universal conditional source-fiber theorem, then a supported concrete list premise and reciprocal-factorial arithmetic. |
| `tail_32_mass` | Uses the new conditional HasLaw, then the finite target measure to obtain the other supported tail's mass 1/2. |
| `repeated_tail_mass_zero` | Uses the same new universal fiber theorem with the unsupported list `[2,2]`. |
| `filtered_tail_hasLaw`, `filtered_tail_mass` | Apply the generic fixed-subset theorem to the actual tail filter with T=`{3}`; T is contained in S.erase0, and the sole output has mass one. |
| `filtered_tail_eq_projection` | Retains the head-event premise for its equality with the original same-sample T projection. It does not assert this equality outside that event. |
| `remaining_projection_map` | Uses the corresponding public conditional projection map for the same T and original sample. |
| `afterFirst_first_event_mass`, `environment_changed` | The proved positive finite 1/3 head mass justifies conditional self-mass one, and differing mass on the same event proves the two environment measures differ. |
| `second_head_mass`, `last_tail_hasLaw`, `last_tail_mass` | Reuse the actual tail's HasLaw under `afterFirst`, at current set `{2,3}` and member 2. The next event has mass 1/2; its further tail is `[3]` with conditional mass one. |

The saved first-stage enumeration has eight conditioning samples out of 24,
four for each tail `[2,3]` and `[3,2]`. Hence the second-head-2 event retains
half the first conditional mass, and all its further tails are `[3]`.
The source's two-step statements agree with these independent expectations.
No additional enumeration was necessary.

`afterSecond` is the actual nested measure
`afterFirst[|firstEvent tailOrder 2]`. The second call supplies `tail_hasLaw`
as its premise, not a fresh original-global-uniform premise. The full original
positions are reused for both calls, while only the selected finset shrinks.
No partial tail is treated as a complete enumeration of Fin4.

The fact that `tailOrder` may have a different support outside the first
conditioning event causes no mathematical mismatch: the law is under
`afterFirst`, and no pointwise support theorem for every original sample is
claimed. This is an appropriate use of the a.e. HasLaw interface. Neither
independence nor a complete history invariant is assumed by the examples.

## Pinned API inspection

The inspected Mathlib sources are from the existing pinned revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

- `Mathlib/Probability/HasLaw.lean` defines HasLaw with protected
  `aemeasurable` and `map_eq` fields. Its `HasLaw.measure_eq` takes a
  measurable output predicate event and transports its mass. The private
  example helper `mass_of_law` uses the singleton event in this way; it
  does not need finite Ω or a new source probability instance.
- `Mathlib/Probability/UniformOn.lean` exposes
  `uniformOn_apply_finset`, giving the intersection-cardinality ratio used
  by that helper. Membership of xs reduces the intersection to the
  singleton, and the old public `orders_card` supplies S.card factorial.
  The helper therefore extracts a mass from the new HasLaw conclusion,
  rather than proving the concrete tail probability independently of it.
- `Mathlib/Probability/ConditionalProbability.lean` gives
  `cond_apply_self` from nonzero finite event mass, exactly the two
  obligations supplied using `first_mass`. Its
  `cond_cond_eq_cond_inter` requires measurable events; the new examples
  avoid claiming such a generic transport by keeping nested conditioning
  explicit.
- The old `Examples.PermutationOrder.observed_law` has the source and target
  equality required by `observed_hasLaw`. The recorded new call orders
  match the uses in the main example at source level.

No readily identifiable API or argument-order error was found. This is not
an elaboration result. In particular, implicit measurable-space unification,
definitional unfolding of the concrete observation/measure aliases, tactic
normalization of ENNReal numerals and the final realized core signatures still
need the prohibited-at-present compiler run. They are ordinary outstanding
validation work, not findings established by this source-only assessment.

## Documentation and integration assessment

The new document consistently labels the work uncompiled and unaccepted.
It separates the event definition, on-event value bridges, generic observed
law and actual global-permutation specializations. It keeps the following
consequential distinctions explicit:

- The first key in a selected subset can differ from the global first key.
- A generic HasLaw supplies a.e. support; an outsider event can be nonempty
  but null. Literal empty-event claims are confined to the actual projection.
- Membership supplies positive conditioning mass. Empty and outsider events
  are not normalized into an arbitrary probability tail law.
- Remaining-set containment is stronger than merely excluding the revealed
  key; the documented Fin3 masses 1/3 and 2/3 agree with the frozen counterexample.
- List I is countable after the local finite enumeration, not generally a
  finite ambient output type. Source and output measurability requirements
  are kept distinct.
- A later history proof must connect its actual updates and all revealed
  information to the observed-law invariant. The two-step example does not
  close those source algorithm, coupling, termination, drift or cost obligations.

The main declarations named by the document are present and connected as
described. Statements about the separate boundary module and the core proof
route agree with the frozen requirements and mathematical preflights; their
implementation correspondence remains outside this report until those files
are complete and separately inspected.

The new reconstruction-map section accurately preserves the draft and
remaining-scope boundary. The new public root imports the main example,
which imports the core and the boundary module; this is the intended public
integration route. This inspection is not execution of the project's import
coverage check.

## Findings and limits

**No XU03-SP finding is opened by this scoped source assessment.** No
requirement or independent expectation was weakened or changed. No final
review finding is closed.

Only this report was written. No compiler, project hash helper, Git command,
cache, build configuration, active gate, repository source, tracker or
requirements were changed. No external source campaign or repeated finite
enumeration was performed. All acceptance gates, including compilation of
the completed candidate, the guarded full build, exhaustive proof audit,
both independent final axes and immediate candidate verification, remain
pending under the original workflow.
