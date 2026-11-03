# Multimodal organization for processing and feedback clocks

**Recommendation:** retain explicit adapters for the current processing-to-batch
interaction. The dependent and temporal libraries already share its structural
proofs. A multimodal presentation is mathematically plausible, but this consumer
does not yet justify implementing its additional context/model machinery.
This research-only assessment addresses
[#221](https://github.com/VladimirMarko/conaled/issues/221), using the accepted
feedback, reactive-contract and indexed-cursor experiments. It adds no Lean
implementation, runtime or universal mode theory.

## What the primary sources establish

In MTT, a small strict 2-category supplies modes, modalities and transformations.
Its semantic context structure is contravariant in both dimensions. Suitably
functorial dependent right adjoints provide models; ordinary adjunctions alone
are not the complete model data. The guarded instance separately chooses a
presheaf model and adds Löb induction. Its later operation has a special initial
stage and restriction maps, unlike arbitrary natural-number-indexed families.
See Gratzer–Kavvos–Nuyts–Birkedal, [*Multimodal Dependent Type Theory*, author's
PDF, §§2, 5.1, 7.1–7.2, 9.1–9.2, printed pp. 4–10, 20, 35–39, 44–46](https://www.danielgratzer.com/papers/journal-multimodal-dependent-type-theory.pdf).

Lively RaTT distinguishes temporal next from guarded later. Equating them lets
guarded recursion construct an endlessly waiting inhabitant of an intended
terminating until type. Its directional inclusion avoids that construction;
it does not supply arbitrary external source progress. See Bahr–Graulund–Møgelberg,
[*Diamonds Are Not Forever*, §1.1, printed pp. 2:2–2:4](https://bahr.io/pubs/files/bahr21popl1-paper.pdf).

The clock/family constructions below are this assessment's mathematical
proposal, not claims that either paper formalizes this repository's APIs.
Existing checked results and unformalized adapter obligations are distinguished.

## One consumer with two uses

Fix `β : Type` and a finite processing trace
`q : List (Option (List β))`. Let `N = q.length` and define, on boundaries
`0 ≤ n ≤ N`,

```text
c(n) = (FRPSpec.Feedback.completed (q.take n)).length
δ(n) = 0 if q[n] = none, 1 if q[n] = some batch    (n < N)
c(0) = 0;  c(n+1) = c(n) + δ(n)
```

The clock counts emissions **before position n**. Consuming an emission at
position `n` advances the boundary to `n+1`. A completed empty batch has `δ=1`.
The successor equation is an elementary finite-list derivation, not a new Lean
theorem in this assessment. `completed_append`, `consume`, `agreement` and
`tick_count` already expose the relevant behavior in
[FRP.Feedback](../../Applications/FRP/Feedback.lean).

For a stream-based comparison, supply `a : Progress.Stream (List β)` and the
bounded compatibility obligation

```text
∀ n ≤ N, completed (q.take n) = Progress.prefixOf a (c(n)).
```

This is not a canonical infinite filtering operation. A finite completed list
can be extended by empty batches to witness compatibility, because the stream's
alphabet is `List β`; the extension beyond `c(N)` has no operational meaning.
An arbitrary element alphabet would require an extension value or a finite-only
interface. No producer of infinitely many actual deliveries is inferred.

**Use A: occurrence certificates.** Instantiate
[OccurrenceCursor](../../Applications/Progress/OccurrenceCursor.lean) with scalar
alphabet `α = List β`. Its histories are lists of batches. A cursor identifies a
**batch occurrence**, not an element of the flattened payload. For initialized
forward/reverse histories `s₀ = reverse t₀` and related initial cursors, write

```text
F(k) = Fin (state (forward s₀) a k).length
G(k) = Fin (state (backward t₀) a k).length
eₖ : F(k) → G(k)                         -- existing encode
u(k) : F(k), v(k) : G(k)                 -- actual certificate sections
```

The existing `cursors_related` and `encode_unique` identify `eₖ(u(k))` with
`v(k)`. The proposed processing observation is `u(c(n)) : F(c(n))`, compared
with `v(c(n)) : G(c(n))`. Concretely this is `tmSub` along
`σ(n) = (a,c(n))`, not a new dependent-feedback language.

**Use B: history and tick accounting.** The
[reactive history consumer](../../Applications/FRP/ReactiveContracts.lean) appends
the batch's payload to a flattened history and increments its tick counter once.
Its empty-delivery behavior differs from payload growth: `some []` advances the
counter while leaving flattened history unchanged. `consume`/`agreement` and
`tick_count` already connect actual optional inputs to batch execution. The same
clock identifies when this update happens. Its payload correctness still comes
from broker honesty, not from a clock equation.

For the actual `emptyQuery` fixture, the first two emissions are
`[none, some []]`: registration at position zero, delivery at position one.
Thus `c(0)=0`, `c(1)=0`, `c(2)=1`. Use A with initial batch histories
`[[7],[7]]` retains first forward cursor zero and moves reverse cursor one to
two after consumption. Use B initialized at `(2,[8])` becomes `(3,[8])`.
The latter and the source emissions are already checked in
[Examples.ReactiveContracts](../../Examples/ReactiveContracts.lean); the nested
batch-cursor specialization and combined clock adapter are paper calculations,
not newly checked examples. In the delayed fixture, emission position five
corresponds to batch position zero and after-consumption clock `c(6)=1`.

## The explicit adapter's required laws

Let `P = Fin (N+1)` and `B = Fin (c(N)+1)`. Monotonicity of completion count
makes `c : P → B` well-defined. Restrict `F` and `G` to `B`, viewing finite
indices as naturals. Families live in `Type` and morphisms are
pointwise functions. Pullback has exact endpoints

```text
c* : (B → Type) → (P → Type)
c* X n = X (c n)
(c* f) n = f (c n).
```

For the actual section context, `σ : P → Stream (List β) × Nat` additionally
supplies `a`. Existing `tySub`, `tmSub`, their identity/composition laws and
`term_sub_related` in [Dependent](../../Dependent.lean) apply directly.

The substantive new adapter obligations would be:

1. Prove the clock successor equation and finite compatibility. At an emitting
   position, compatibility must identify `a(c(n))` with the actual emitted batch.
2. Connect execution at the processing boundary to batch execution at `c(n)`.
   Reuse `agreement` and finite execution/stream comparison; do not assume the
   state equality merely because tick counts agree.
3. Define processing cursor advance as identity on `none`, or the existing
   batch advance on `some batch`, with casts justified by the clock equation.
   If these advances are `L_F(n)` and `L_G(n)`, require
   `e_{c(n+1)} ∘ L_F(n) = L_G(n) ∘ e_{c(n)}`. The stuttering case is identity;
   the emitting case uses `encode_advance` and input compatibility.

Pointwise encoding commutes with pullback, and pulling back twice equals pulling
back along the composed index map. These are substitution laws. They do not
justify a successor equation for the clock. The state/witness connection reuses
[DependentFeedback](../../Applications/Progress/DependentFeedback.lean), including
its explicit `advance_cast` and `certificate_step` laws.

For a further interpretation `J`, require a specified comparison between
`J(c*X)` and the target clock's pullback of `J(X)`, with term, substitution,
identity and composition coherence. If its carrier equality is only an
isomorphism, retain that isomorphism and its naturality. This is a requirement,
not supplied automatically by renaming an adapter a modality. Existing
[STLCNaturality](../../SquareKit/STLCNaturality.lean) similarly requires `MapLaws`,
`Preserves` and congruence; dependent sheaf interpretation already retains an
explicit substitution isomorphism in
[ordinary_term_substitution](../../SquareKit/Internal/DependentSheafComparison.lean).
Neither is a ready-made interpretation of this clock.

## A precise modal candidate, and what it would add

For this **fixed** clock, consider modes whose context categories are the ordinary
discrete family categories `Fam(P)` and `Fam(B)`, equivalently slices of sets.
This is a proposed semantic setting, not the guarded presheaf setting. On objects,
ordinary fiber adjoints to pullback have the following forms:

```text
Fiber(k) = {n : P // c(n)=k}
(Σc X)(k) = Σ n : Fiber(k), X(n.val)
(Πc X)(k) = (n : Fiber(k)) → X(n.val)
Σc ⊣ c* ⊣ Πc.
```

These are mathematical family constructions; no Lean adjunction or MTT model is
added here. Empty fibers give an empty sum and a singleton product. The candidate
right-modality `μ : P-mode → B-mode` would have context lock `c*` and right-adjoint
type behavior based on `Πc`. The unit has direction `Y → Πc(c*Y)` in `Fam(B)`;
the counit has direction `c*(Πc X) → X` in `Fam(P)`. Their triangle equations,
identity/composition comparisons for multiple clocks, and coherent dependent
lifting are additional obligations. The consumer presently uses pullback, not
fiberwise universal quantification.

One could instead present `c*` itself as right modality to `Σc`. That changes the
lock data and its coherence obligations; it is not free notation for the first
presentation. A full account must choose the dependent context/type/term model,
its modal rules and comparison transformations. The local
[GeometricMorphism](../../SquareKit/Internal/GeometricMorphism.lean) already keeps
adjunction and left-exactness evidence separate, but an instance of that record
alone is not an implemented MTT model.

Changing the trace changes `c`. A runtime would need compatible models/adapters
across trace extension, or a parameterized treatment of traces, rather than one
fixed clock silently covering all executions. Reindexing changes of base must
include their commuting squares; fiber-adjoint base-change comparisons require
the appropriate pullback squares. Arbitrary clock changes are insufficient.

## Negative interaction: stuttering does not commute with next

Work on boundaries with `n < N` and `c(n) < c(N)`, so both successor
observations exist. For a batch family `X`, define
next observations by `D_B X(k)=X(k+1)` and `D_P Y(n)=Y(n+1)` wherever those indices
are in range. Then

```text
D_P(c*X)(n) = X(c(n+1))
c*(D_B X)(n) = X(c(n)+1).
```

They agree at emissions. At stuttering positions they compare `X(k)` and
`X(k+1)`. For arbitrary families there is no uniform map in either direction:
choose one fiber empty and the other singleton. This disproves unconditional
next commutation, not the existence of a valid multimodal model for the clock.
For arbitrary contexts with restriction maps, available transformations would
instead depend on those extra maps and their direction.

The existing [Until.map and Until.Rel](../../SquareKit/Temporal/Relations.lean)
retain the same starting index, every wait and the horizon. They cannot be used
as if they compressed processing positions into batch positions. In the actual
empty fixture, a response certificate starting at processing position zero
waits once before emission at one, while the corresponding batch emission is at
zero. For an **after-update** cursor family with an additional requirement
`c(n)=1`, the earliest processing terminal boundary is two; the batch terminal
boundary is one. The two certificates have horizons two and one. A compression
adapter could retain a separate clock correspondence, but could not claim the
existing same-horizon relation unchanged. These finite counterexamples are paper
derivations from the checked emission fixture.

`Occurrence.later` is ordinary observation-index substitution. Neither that map,
these `D` operations, nor initialized total feedback constitutes a guarded
fixed-point modality. Source honesty and fairness remain the separate premises
of `eventual_update`; none is manufactured by an adjunction or clock comparison.

## Accounting and runtime decision

| Obligation | Explicit adapters | Multimodal presentation for these uses |
| --- | --- | --- |
| Honest actual emissions; `none` versus `some []` | Existing broker/feedback laws plus concrete clock connection | Same mathematical obligation |
| Retained batch occurrence and changed reverse index | Existing fiber/step/lookup proofs | Same client mathematics |
| Family substitution, related sections, composition | Existing `tmSub`/`term_sub_related`/`extRel` | Could package their use; no demonstrated removal of a duplicated induction |
| Finite terminal witness and horizon | Existing Until maps at a common index; new clock relation if compressing | Still needs the differing-horizon contract |
| Modes, locks, modal transformations and interpretation | No additional global interface | New model/coherence work before its notation is justified |

The two clients share clock bookkeeping but have different observations:
occurrence identity in a history of batches versus tick count and flattened
payload history. Their mathematical obligations persist under either notation.
This assessment found no repeated fundamental proof that an MTT layer would
currently eliminate. That is a consumer-specific engineering judgment, not a
claim against multimodal organization in general.

For [#31](https://github.com/VladimirMarko/conaled/issues/31) and the eventual
reactive target, preserve both processing progress and completed-batch count,
plus the actual emission and retained state. Put the finite clock/execution
comparison at their adapter boundary if both clients become runtime consumers.
Do not require an infinite filtered stream, guarded calculus, new kernel axiom
or mandatory source syntax before implementing the retained-state engine.
Keep physical/event time distinct, and retain source and scheduling assumptions.

No standalone MTT implementation follow-up is justified now. The bounded future
work, if the runtime consumes this comparison, is exactly the clock successor,
execution agreement and cursor-advance square above, with empty/delayed/stalled
cases and an explicitly changed horizon relation. This report has **not**
delivered that formal adapter. Revisit a shared modal presentation when further
independent consumers repeat these same clock/model coherence obligations. The
other correspondence routes, #36's existing model work, resource instrumentation
and broader #200 agenda remain active.
