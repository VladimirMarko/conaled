# Uniform-ranking preceding count: bounded source preflight

Prepared 2026-11-02. **Mathematical/source preparation only: no frozen scope,
implementation, validation, final review or chapter acceptance.** This note
coordinates with `permutation-expectation-api-preflight.md`. It extends the
already queued expectation discussion in `finite-ranking-source-preflight.md`
and `finite-ranking-api-preflight.md`; existing chapter obligations are unchanged.

## 1. Exact observation and mean

Let I be finite, P linearly ordered, and `priority : I → P` fixed and
injective. Give the finite permutation sample space measurable singletons
and use the existing law `μ = uniformOn (Set.univ : Set (Equiv.Perm I))`.
Fix `S : Finset I` before sampling. Write N = `Nat.card I` and s = `S.card`.
For a sampled key-to-priority-label permutation π, observe the actual count

\[
B_S(\pi)=\operatorname{Set.ncard}
 \{b:I\mid \forall a\in S,\;priority(\pi b)<priority(\pi a)\}.
\]

The intended theorem is

\[
\boxed{\mathbb E_\mu B_S=\frac{N-s}{s+1}}.
\]

It holds **including S=∅ and I=Empty**. The quotient is in ENNReal or Real
after casting; it is not natural-number division. Since s≤N, natural
subtraction in the numerator agrees with the corresponding real difference.
The denominator s+1 is positive and finite. No order or measurable structure
on I, or measurable/finite structure on P, is required by the mathematics.
The measurable permutation sample space is still explicit. A proof-local
Fintype enumeration suffices; no new carrier, sampler or global instance is
needed. The definition itself only needs the strict relation on P; finite
I, a linear order and injectivity belong to the expectation theorem. The
deterministic count bound below needs only a preorder on P and finite I,
since its proof uses the failed self-comparison rather than injectivity.

### Proof through the existing minimum-event theorem

For b∈S the strict-before predicate is false, because it includes the
self-comparison. For b∉S its event is exactly

`PermutationMinimum.minimumEvent priority (insert b S) b`.

In one direction strict comparisons imply non-strict minima, including
the reflexive comparison with b. In the other direction, equality with
any a∈S would imply πb=πa by injectivity of priority and then b=a by
injectivity of π, contradicting b∉S. This strict/non-strict bridge is an
essential use of injectivity, not a change of the minimum-event definition.

Pointwise B is the finite sum of these indicators over the N−s outsiders.
The existing `uniformOn_minimumEvent` assigns every summand expectation
1/(s+1). Finite integral linearity gives the displayed formula without any
independence premise. The deterministic bound

\[
0\le B_S(\pi)\le N-s
\]

also follows because no member of S contributes. It justifies finite
expectation and real integrability directly. The actual count/indicator
identity and event equivalence must be proved; replacing B with a separately
defined sum having the desired mean would omit its observation connection.

## 2. Ordinal bridge, with the nonempty premise retained

Supply `rank : I ≃ Fin U` and use `priority = rank`. For hS:S.Nonempty let

\[
m_\pi=\min\{rank(\pi a):a\in S\}\in\mathrm{Fin}(U).
\]

The composed equivalence `rank ∘ π` maps the strict-before set bijectively
onto the initial segment of Fin U strictly below mπ. Consequently

\[
B_S(\pi)=m_\pi.\mathrm{val},\qquad
T_S(\pi):=B_S(\pi)+1=m_\pi.\mathrm{val}+1.
\]

This connects an ordinary count to the **actual minimum of the finite
image**, with a proof of nonemptiness supplied to `Finset.min'`. It needs
no default key or empty-set minimum. The rank equivalence gives N=U, and
finite expectation plus the mean-count result yields

\[
\boxed{\mathbb E_\mu T_S=\frac{U+1}{s+1}}.
\]

Here rank gives zero-based global positions; T is one-based. There is no
requirement that rank respect the keys' search order. For a general ordered
priority target, B+1 is still the ordinal position among the finite set of
assigned priorities when S is nonempty. It is **not their raw numeric
minimum**. Connecting an arbitrary priority assignment to a particular
enumeration or numeric rank additionally requires an order-preserving
bridge; an arbitrary enumeration does not provide that bridge.

The arithmetic identity E(B+1)=(N+1)/(s+1) remains true for empty S, but then
B+1=N+1 is a sentinel beyond all available positions. It must not be
presented as the position of a nonexistent first member. A nonempty-S
ordinal theorem keeps this semantic boundary visible.

## 3. Independent examples and exceptional cases

The following expectations reuse `finite-ranking-calculations.json`.
That file already exhaustively checked the finite count identity through
universe size six. No enumeration was repeated for this task. Its exact
arithmetic is independent evidence for later connected examples, not Lean
validation.

| Universe and fixed S | Saved law of B | E B | Ordinal interpretation |
|---|---|---:|---|
| Empty universe, S=∅ | 0 with mass 1 | 0 | No first member; B+1=1 is only a sentinel. The permutation law is still normalized. |
| Fin3, S=∅ | 3 with mass 1 | 3 | No first member; B+1=4 is only a sentinel. |
| Fin3, S={0} | 0, 1, 2 each with mass 1/3 | 1 | First position has mean 2. Being first within a singleton does not mean being globally first. |
| Fin3, S={0,1} | 0 with mass 2/3; 1 with mass 1/3 | 1/3 | Actual first position has mean 4/3. |
| Fin3, S=univ | 0 with mass 1 | 0 | Actual first position is always 1. |
| Fin4, S={0,3} | 0 with mass 1/2; 1 with mass 1/3; 2 with mass 1/6 | 2/3 | Actual first position has mean 5/3. |

These cover empty, singleton, proper and full subsets, plus an empty index
universe. In general a singleton has mean count (N−1)/2; a nonempty full
subset has count zero and first position one. The full subset of an empty
universe belongs to the empty case, not the nonempty full-set interpretation.

The saved numeric-priority counterexample uses Fin3, S={0,1}, and labels
100+10j. Its expected raw minimum is 310/3, whereas the ordinal expectation
is 4/3. Changing gaps or translating priorities leaves B unchanged and
changes the raw mean. For a connected example, define M to be the **actual
minimum of the finite image** of S under `a ↦ 100 + 10 * (rank (π a)).val`.
Prove pointwise that this positive affine map preserves the minimum, hence
M=100+10·mπ.val=100+10·B, and only then compute the real expectation of the
cast of M as 310/3. Merely naming 100+10·B the raw minimum would omit the
value bridge. This one concrete observation fits the unit's boundary
examples; no general numeric-priority expectation theorem is required.
The existing negative/gappy Int priority example is another permissible
specialization after its ordering bridge, not a different random model,
and need not be added as an additional formal example here.

Two small premise checks require no new enumeration:

- In the existing two-key constant-tie setup, take a singleton S. Every
  strict-before comparison fails, so B=0, while the proposed formula would
  give 1/2. The injectivity hypothesis is necessary. Taking S=univ instead
  would hide this defect, because both counts are then zero.
- With Fin3 choose S after sampling to be the singleton containing the
  globally first key. Its cardinality is always one, but B is always zero,
  rather than the fixed-singleton mean one. Fixed cardinality does not
  replace the fixed-subset premise.

Useful connected formal examples should invoke the generic count theorem
and rank bridge on these observations. A second arithmetic derivation alone
would not show that the new public statements are usable.

## 4. Exact source benefit and retained limits

The already pinned Blelloch–Ferizovic–Sun paper, *Joinable Parallel Balanced
Binary Trees*, p.7:25, uses the expected global priority position of a pivot
treap's root in the union analysis. Re-reading that page confirms that the
position estimate feeds an expected-depth/logarithmic-concavity step. The
present result supplies precisely the fixed-set positional estimate after
the separate canonical-treap root/minimum bridge.

For fixed operand key sets A,B, let U=|A∪B| and s=|A|>0. Shared keys have
shared priorities. If |B|≤s, then U≤s+|B|≤2s, so

\[
\mathbb E T_A=\frac{U+1}{s+1}
\le\frac{2s+1}{s+1}<2.
\]

This entails the paper's looser bound by two, including overlapping
operands; there is no need to duplicate shared keys or replace U by a
disjoint-union sample. The paper expresses a coarser size-ratio estimate,
not the exact formula above. Its priority vocabulary must continue to be
translated consistently to the chosen smaller-is-earlier convention.

This supports C10-115's shared ranking model and one estimate needed for
**C10-117**. It does not discharge C10-117's actual join/split work relation,
conditional depth estimate, Jensen hypotheses, rank-cluster continuation
or weighted charging. In particular:

- Recursive sets can depend on the revealed priorities. An unconditional
  result for fixed S does not establish their conditional law or mean.
- The existing one-step conditional remaining-order draft proves its
  specified observed-list law. It does not make the entire conditioned
  global ranking uniform or automatically supply a global-position mean.
- Overlapping operand restrictions remain correlated. No independence is
  used in the indicator sum, and none is supplied by the final scalar mean.
- A bound on E[d] does not permit factoring E[dZ] into E[d]E[Z]. The saved
  correlated-weight counterexample and the open conditional/charging bridge
  in `probability-source-preflight.md` remain unchanged.

The earlier source notes already map minimum and restriction laws to
Chapter 2. This expected global position is not the requested order
statistic or pivot-relative key rank in Chapter 3. No new quicksort or
selection work theorem follows from this scalar mean alone.

## 5. Bounded-unit recommendation and provenance

One small unit can reasonably contain: the actual Nat-valued count; its
pointwise bound and minimum-event indicator connection; its ENNReal mean;
an explicitly justified real-expectation corollary; and the nonempty rank
image/minimum bridge with the corresponding ordinal mean. These are
successive views of one finite observation, not separate probability
frameworks. Finite measurability/integrability and finite casts must be
proved before using a totalized real integral or ENNReal-to-Real transport.
Architecture owns the exact pinned API choice. Full distributions, tails,
adaptive histories, arbitrary conditional charging and algorithm work
remain outside this proposed unit; their existing chapter obligations stay
queued. No scope is frozen by this recommendation.

Saved evidence used:

- `finite-ranking-source-preflight.md`, SHA-256
  `a67ce7f338587b1cf719c47e200fde4fff948647f67d04571e5b209a68a738f9`;
  `finite-ranking-api-preflight.md`, SHA-256
  `97da582310e190ab7036817ee42e746ee3f14a4a6ed44b690b449d86748ef6dc`.
- `finite-ranking-calculations.json`, SHA-256
  `36f853f68d0f0713581aea33e7c91187a003f99bb7386ff5ba509e52964c1949`.
- `chapter10-obligations.md`, C10-112–118, and
  `probability-source-preflight.md`, §3.3 and §5. No inventory was edited.
- FDSA July 27, 2026, Chapter Notes p.125;
  <https://fdsa-book.net/functional_data_structures_algorithms.pdf>, SHA-256
  `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
- Blelloch–Ferizovic–Sun, DOI <https://doi.org/10.1145/3512769>, saved
  CC-BY-4.0 author PDF
  <https://www.cs.ucr.edu/~yihans/papers/TOPC/joinable.pdf>, SHA-256
  `c39df24da9ffdd1027777c26a8ef0330d73e8f8b2282c5accb4c090b2b0f3057`.
  Only its already retained root-position argument on p.7:25 was re-read.

Only this requested research note was written. No compiler, project hash
helper, Git mutation, repository source, ticket, requirements, cache,
gate or acceptance action was taken; no new source retrieval or enumeration
campaign was performed.

## 6. Bounded follow-up: conditional placement and priority premises

This append preserves the preceding assessment verbatim (its SHA-256 before
this append was
`6eb258cb80175f510f267d5e8a9dd54c116b1e2ced3cff10dfa44920f5604ef2`).
It records two source-level clarifications requested before any scope freeze.

### Same singleton-order law, different global count mean

Take I=Fin3, identity rank, S={1}, and the original uniform global law μ.
Let E be the event that key 0 is first **globally**, and ν=μ conditioned
on E. Its mass under μ is 1/3. The conditional remaining-order law gives:

| Actual global order under ν | Conditional mass | Actual B for S={1} |
|---|---:|---:|
| [0,1,2] | 1/2 | 1 |
| [0,2,1] | 1/2 | 2 |

Thus Eν[B]=3/2, while the unconditional fixed-subset formula gives
Eμ[B]=(3−1)/(1+1)=1. This calculation needs no new enumeration: the two
tails [1,2] and [2,1] and their masses are the full-subset instance of
the existing XU03 conditional tail statement. The pointwise connection
from those actual global orders to B must still be proved in a formal
example; already exposed key 0 counts as a global predecessor.

Under **both** μ and ν, the restricted order of S is identically [1].
Consequently it has the same uniform singleton-order `HasLaw` under both
measures, despite the different count means. A law of the relative order
inside S alone loses placement among the outside keys. It therefore cannot
transport this global before-count mean. This is compatible with XU03's
observed-law result and precisely delineates its information content.

Recommend this as one bounded cross-unit formal boundary, in place of a
larger new nonuniform-law example. It can reuse XU03's actual conditional
tail masses, a count-value bridge on E, and finite expectation; the
conditioning event is positive, so ν is a probability measure. It does
not require a new conditional framework or a general adaptive-set theorem.

### Clarification of the optional negative/gappy Int example

Section 3's phrase about specialization after an ordering bridge should
be read only as a qualification of a **specific numeric rank or minimum
interpretation**. Applying the count-mean theorem itself to the existing
injective Int priority assignment needs only its already established
injectivity (and the theorem's ordinary finite-law/order hypotheses).
It needs no monotonicity with respect to index order and no separately
chosen sorted enumeration. An ordering bridge is required when identifying
B with a particular numeric rank or deriving the value of an actual
numeric minimum, as in the concrete 100+10j example. No additional gappy
Int formal example is recommended for this unit.
