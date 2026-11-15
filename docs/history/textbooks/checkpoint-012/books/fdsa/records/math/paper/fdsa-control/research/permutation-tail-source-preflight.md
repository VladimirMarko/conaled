# First revealed subset key: conditional remaining-order source preflight

Prepared 2026-11-02. **Bounded mathematical/source preparation only.** No new
scope is frozen and no implementation, chapter activation, validation or
acceptance is claimed. The parent reports the preceding whole-order draft
at `4bb13e44a6c7e3277b69cbac9fd9dd37cd7780f8`; this note does not validate it.

## 1. Smallest conditional target

Retain the original complete, Nodup `positions : List I`, ordinary finset S,
and one global uniform permutation law μ. Write
`R_S π := restrictedOrder positions S π`. Fix a member `a ∈ S` and define

\[
E_a=\{\pi:(R_S\pi).\mathrm{head?}=\mathrm{some}(a)\},\qquad
B=S\mathbin{\mathrm{erase}}a,\qquad \nu=\mu(\,\cdot\mid E_a).
\]

The actual observation is `(R_S π).tail`, not a newly sampled list. The
useful conclusions are

\[
\mu(E_a)=1/S.\mathrm{card},
\]

and, for every list xs,

\[
\nu\{\pi:(R_S\pi).\mathrm{tail}=xs\}=
\begin{cases}
1/(B.\mathrm{card})! & xs\in\mathrm{orders}(\mathrm{positions},B),\\
0 & \text{otherwise}.
\end{cases}
\]

A map corollary identifies this observed tail's distribution with the existing
uniform measure on those orders. The discrete source-event formulas need
measurable structure only on the permutation sample space; a List-valued
`Measure.map` additionally uses the explicit output measurable structure and
measurable singletons. As before, completeness supplies finiteness locally.
`head?` and `tail` require no default key or `Inhabited I` assumption.

Ordinary event conditioning is sufficient. The API contributor verified the
pinned `ProbabilityTheory.cond` route: conditioning `uniformOn Set.univ` on E
is `uniformOn E`. No conditional-distribution kernel or arbitrary choice of
versions on null fibers is needed. Under `a ∈ S`, the head mass is positive
and finite, so ν is a probability measure.

## 2. Direct proof from the whole-order law

For every list xs, the elementary list identity gives the exact event equality

\[
E_a\cap\{\pi:(R_S\pi).\mathrm{tail}=xs\}
=\{\pi:R_S\pi=a::xs\}.
\]

Under completeness, Nodup and membership, cons support is equivalent to
remaining support:

```text
a :: xs ∈ orders positions S ↔ xs ∈ orders positions (S.erase a).
```

The previous whole-output theorem therefore gives joint mass `1 / S.card!`
for every supported xs and zero otherwise. Summing the disjoint tail fibers
gives the head mass. If `b = B.card` and `m = S.card`, use `b + 1 = m` and
`m! = m * b!`; membership establishes `m > 0`, and every factorial is positive.
This avoids an unguarded natural-subtraction or zero-denominator step.
Dividing the joint masses by the head mass gives the conditional formula.

On E, the actual tail equals `restrictedOrder positions B π`: Nodup means
there is only one occurrence of a to remove. This equality holds **on the
conditioning event**, not globally. Outside E, `List.tail` removes whichever
key is first, while erasing a may remove a later key. Conditional support on
E makes the on-event equality sufficient for equality of the observed laws.

The event is “a is first in S”, not “a is first globally”. When S is proper,
outside keys may precede a. Nor is the observed tail the global list's tail.

## 3. A small remaining-subset corollary

Recommend retaining a fixed `T ⊆ B` corollary if the unit is intended to serve
its first quicksort/selection clients. It adds a direct use of existing value
and measure composition, not a new random-execution framework. T may be a
function of the fixed revealed a and fixed input data; it must not depend on
additional unrevealed random information.

Let `f π = restrictedOrder positions B π` and `g xs = xs.filter membership_T`.
The conditional tail result and its on-event value bridge give

\[
\nu.\mathrm{map}(f)
=\mathrm{uniformOn}(\mathrm{orders}(\mathrm{positions},B))
=\mu.\mathrm{map}(f),
\]

where the second equality is the prior unconditional whole-order law.
Map both sides through g. The existing deterministic nested-filter theorem,
using `T ⊆ B`, identifies `g ∘ f` with `restrictedOrder positions T` on
**every** sample. The previous whole-order theorem then gives the conditional
uniform order on T. This also describes filtering the actual tail to T on E.

Every application retains the **original complete positions**. On E, the
observed tail enumerates only B, as does `positions.filter membership_B`.
Both omit a, and for proper S also omit outside keys. They cannot discharge
the old theorem's whole-universe completeness premise. Equality of the
existing pushed-forward laws avoids that invalid substitution and avoids
introducing a subtype enumeration just for this corollary.

Containment is consequential. On Fin3, condition on 0 first in S=`{0,1}`.
The allowed global orders are `012`, `021`, `201`. For T=`{1,2}`, which excludes
0 but is not contained in B, the conditional orders `[1,2]` and `[2,1]` have
probabilities 1/3 and 2/3. Merely excluding the exposed key is insufficient.
No claim about arbitrary outside restrictions or joint independence follows.

## 4. Connected arithmetic and zero-event boundaries

The saved exact expectations are
[permutation-tail-calculations.json](permutation-tail-calculations.json),
SHA-256 `b614ea7eb98b3aaba5c15006a967e1d8da51fc373d5b963c99cdccce6b4632eb`.
They enumerate only the concrete Fin4 and Fin3 cases below; this source
assessment does not rerun them or treat them as Lean validation.

For positions `[0,1,2,3]`, S=`{0,2,3}` and a=0, eight of 24 samples satisfy E:

| Observation | Global count | Joint mass with E | Conditional mass |
|---|---:|---:|---:|
| Actual tail `[2,3]` | 4 | 1/6 | 1/2 |
| Actual tail `[3,2]` | 4 | 1/6 | 1/2 |

Thus the head-event mass is 1/3. Only six samples have global first key 0;
`[1,0,2,3]` is a pointwise witness satisfying E with global first key 1.
For the four fixed subsets of B=`{2,3}`, empty and singleton restrictions have
their unique order with conditional mass one; the full pair has its two
orders with mass one-half.

For S=`{2}` and a=2, E is the whole sample space, the tail is `[]`, and its
conditional mass is one. For empty S, the output has `head? = none` on every
sample: the none event has mass one, whereas each some-a event is empty.
An outsider a likewise has an empty head event. Under the ordinary conditioning
convention, conditioning these null events yields the **zero measure**, not
a normalized uniform tail law. Membership must therefore not be dropped.
An empty index universe has the normalized identity-permutation law and the
empty observation, but provides no member a to instantiate the positive-head
statement. No distinguished empty-case key is introduced.

## 5. Precise source benefit and remaining work

The existing [probability source preflight](probability-source-preflight.md),
[quicksort plan](quicksort-average-proof-plan.md) and
[whole-order note](permutation-order-source-preflight.md) retain primary-source
pins and exact chapter scopes. The parallel API assessment is
[permutation-tail-api-preflight.md](permutation-tail-api-preflight.md).
No source inventory is revised here.

For **C02-024**, the head/tail law supplies the basic decomposition of a
uniform distinct-key order after a specified pivot. The fixed-T corollary
supplies the separate lower/upper filtered-order marginals for that pivot.
This matches the role of `random_permutation_of_set` in the saved AFP
`Quick_Sort_Average_Case.thy`. Its stronger `partition_random_permutations`
pair-law step is not automatically proved here. Expected sums can use the
marginals without independence; actual recursive cost observations, the
source tariff and equivalence to fresh randomized occurrence choices remain.

For **C03-059–077**, index **occurrences**, so equal payload values still have
different indices. Given a fixed active set and a specified pivot occurrence,
when selection continues its retained strict partition is a fixed subset of
`S.erase a`, determined by the data, pivot and requested rank. The corollary preserves its random priority
order. Revealing only a repeated value is a different conditioning event,
possibly merging several occurrence cases. The actual selection list/value
and rank bridges, uniform sampling given the entire execution history,
coupling to fresh choices, work/drift and tail bounds remain separate. The
zero-based occurrence/rank versus existing one-based selection API distinction
also remains unchanged.

This one-step fixed-subset theorem does not itself prove a history invariant
for adaptive active sets. Such a client must establish its current conditional
law and the information revealed at each step. The proposed tail and fixed-T
results are bounded support for that work, not an algorithm or cost theorem.

Only this requested note was written. No compiler, Git command, project hash
helper, cache, gate, repository source, ticket, requirement or acceptance state
was changed.

## 6. Append-only assessment: an observed-law premise for successive reveals

Added at root's request before scope freeze. The original 8,947-byte assessment
above is preserved byte-for-byte at SHA-256
`15a60420d81d93bcf610b6ab14b918847cdb474480565e1e6a8c09965dd1287b`.
No additional enumeration or implementation was performed.

### The generalization is mathematically sufficient

Let Ω be an arbitrary measurable environment, μ its measure, and
`Y : Ω → List I` the actual current-order observation. Retain the existing
complete/Nodup positions and define
`ηS := uniformOn (orders positions S : Set (List I))`. Assume the existing
`HasLaw Y ηS μ`: it supplies `AEMeasurable Y μ` and `μ.map Y = ηS`.
This specifies the whole observed-list distribution, not merely a head marginal.
It requires no finite environment or assertion that μ is a uniform global
permutation law. The normalized finite target implies source normalization;
Mathlib's `HasLaw.isProbabilityMeasure` already expresses that consequence.

For the measurable list event `H_a = {xs | xs.head? = some a}`, put
`E_a = Y ⁻¹' H_a`. Ordinary conditioning satisfies

\[
(\mu[\mid E_a]).\mathrm{map}(Y)
=(\mu.\mathrm{map}(Y))[\mid H_a]
=\eta_S[\mid H_a].
\]

The pinned `Measure.restrict_map_of_aemeasurable` handles the possibly only
null-measurable preimage E. Together with map/scalar compatibility and the
mapped event mass, it proves this transport without demanding globally
measurable Y. Conditioning is absolutely continuous with respect to μ, so
Y remains a.e. measurable under the conditional measure. Transport itself
needs no positive-event premise; positivity is needed for the resulting
conditional probability interpretation and follows from `a ∈ S`.

The canonical cons/tail calculation from §2 now transfers through Y. Thus the
head has mass `1 / S.card`, and the **actual** observation `fun ω => (Y ω).tail`
has law ηB under `μ[|E_a]`, for `B = S.erase a`. This is a meaningful
one-step conclusion from an unconditioned whole-order law, not an assumption
of the desired conditional tail law. The original global-permutation result
remains a concrete specialization: XU02 supplies its `HasLaw` premise.

### Filtering the actual conditional tail

For fixed `T ⊆ B`, prove once that the ordinary filter maps ηB to ηT, using
the original complete-position XU02 experiment and its nested-filter theorem
as in §3. Then `HasLaw.fun_comp` combines that canonical filter law with the
conditional tail law. The conclusion concerns

```text
fun ω => ((Y ω).tail).filter membership_T
```

under the same conditioned environment. It does not require a new finite
source carrier, incomplete tail enumeration, or claim that the current μ
is still uniform. The actual global specialization recovers the corresponding
erased-set projection only on the head event. Arbitrary Y has no global π
projection to substitute silently.

### Null sets and the precise history-induction boundary

Under `HasLaw` alone, Y has valid support **almost everywhere**; it can return
an invalid list on a null set. Consequently, an outsider head event has mass
zero but need not be literally empty. The pointwise emptiness assertions in
the original assessment concern its actual projection `R_S`; they are not
assertions about every generic Y. Null conditioning still gives the zero
measure. No pointwise Nodup/support guarantee for all Ω is inferred.

For a fixed positive-probability history h, an appropriate induction hypothesis
is `HasLaw Y_h ηS_h μ_h`, where μ_h is the actual environment conditioned on
that history and S_h is fixed by the history. The generic theorem supplies
the next head mass and the next filtered-tail law. The client must still:

- establish the initial observed law;
- identify the actual program update with that tail/filter observation,
  pointwise on the event or almost everywhere under the conditional measure;
- show the next retained set is determined by the revealed data and is a
  subset of the current set with its exposed occurrence erased;
- justify the history events and successive-conditioning identity, rather
  than silently discard additional branch observations or random information.

In particular, `HasLaw` supplies only a.e. measurability. The inspected
`cond_cond_eq_cond_inter` API requires measurable history events; a generic
client must prove those or provide the appropriate null-measurable/a.e.
transport. The finite permutation examples have measurable events directly.
Full arbitrary-history, joint-independence, algorithm-coupling and cost proofs
remain separate obligations.

The proposed second reveal makes the generalization useful without claiming
a full history theorem. In the Fin4 case, ν conditions the selected first key
to 0, so ν(E0)=1 while μ(E0)=1/3: the environment measure has changed. Its
observed tail nevertheless has uniform law on `{2,3}`. Applying the same
observed-law theorem again to exposed key 2 gives next-event probability 1/2
and subsequent tail `[3]` with conditional mass one. These values follow from
the retained first-stage tail counts; no new enumeration was needed.

This assessment checked the existing pinned source for `HasLaw`, its
normalization/composition results, `restrict_map_of_aemeasurable`, and ordinary
conditioning in Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.
The exact API routes are coordinated with `permutation-tail-api-preflight.md`.
This append authorizes no code, freezes no scope, and supplies no validation
or acceptance evidence.

