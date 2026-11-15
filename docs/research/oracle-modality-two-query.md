# Two oracle requirements in a persistent truth model

Issue [#501](https://github.com/VladimirMarko/conaled/issues/501) delivers a bounded representation of the least-modality construction for two constant query names. It proves the return/query closure, its least-forcing property, and its interpretation by persistent propositions and actual answer sheaves. The public four-world example has two requirements: one query layer cannot establish their conjunction, but two layers can. The same answer object has local inhabitants and no global internal section.

The public entrypoint is [Examples/OracleModalities.lean](../../Examples/OracleModalities.lean). This is a native algebraic theorem plus a represented propositional fragment. It is not an interpretation of all CIC, arbitrary dependent query objects, or the paper's full oracle-sheafification.

## Primary source and foundations

The selected results are Proposition 6 and the constant-two-query case of Proposition 17 in [Ahman and Bauer, *Sheaves as oracle computations*, v2, 28 April 2026](https://arxiv.org/html/2602.22135v2). Sections 2–4 distinguish impredicative, proof-irrelevant propositions from answer types. Theorem 15 uses a preorder reflection of container morphisms. Theorem 19 requires unique choice in its converse; section 4.1 separately discusses conditional quotient-inductive sheafification. Section 4.2 distinguishes ordinary answer trees from their propositional truncations.

The inspected HTML has SHA-256 `66072221005b27e3898189684256e0b306a98cf89667725522487fe2c546d919`. The [linked software artifact](https://doi.org/10.5281/zenodo.19858008) was inaccessible during this study. No software revision, license, Rocq replay, copied source, or verified inter-prover translation is claimed.

The native development uses ordinary types, set lattices, proof irrelevance, extensionality, and the existing sheaf library. It adds no resizing or conditional quotient-inductive axiom. Existing classical mathematical infrastructure remains part of the external metatheory. None of it is used to replace the represented implication with classical implication. A native excluded-middle oracle would already have all its answers in classical Lean; the checked non-Boolean model below avoids that collapse.

## Independent closure and least forcing

[OracleModality.lean](../../SquareKit/OracleModality.lean) works over an arbitrary Heyting algebra `H`. It uses Mathlib's actual `Nucleus H`, whose laws include finite-meet preservation, inflation, and idempotence. For truth values `p`, `q`, a desired result `s`, and an approximation `t`, the definitions are:

```text
openNucleus p s = p ⇨ s
step p q s t = s ⊔ (p ⇨ t) ⊔ (q ⇨ t)
oracle p q s = (p ⊓ q) ⇨ s
```

`step` expresses returning `s` or proceeding from either query answer. The formula for `oracle` is specified before proving its connection to those rules. `two_steps` proves that applying `step` twice, starting at `s`, gives exactly `oracle p q s`. `step_fixed` proves closure under further queries. `least_prefixed` proves minimality among all truth values that admit return and both query continuations. Thus the formula does not acquire its intended interpretation merely by storing a correctness field.

`least_forcing` establishes, for any nucleus `j`,

```text
openNucleus (p ⊓ q) ≤ j  ↔  j p = ⊤ ∧ j q = ⊤.
```

Its proof uses actual finite-meet preservation and the implication adjunction. This is the bounded least-modality result. `join_characterization` gives the least upper bound of the two one-query nuclei. Separately, `open_comp` and `open_commute` prove that these particular nuclei compose to that join. They do not assert that arbitrary nuclei commute or that arbitrary composition is idempotent.

The conjunction formula is justified here because there are two fixed query names, and the proof exhibits two query layers. It is not generalized to infinite or dependent query families, nor used to identify all oracle modalities with open modalities.

## Persistent truth and its non-Boolean client

[OracleModalityKripke.lean](../../SquareKit/OracleModalityKripke.lean) represents truth values on a preorder `W` as `LowerSet (OrderDual W)`. These are upward-persistent sets of worlds, ordered by inclusion. This choice matters: Mathlib's `UpperSet` uses reverse inclusion.

The independently defined `implication U V` contains `w` exactly when every future world `v ≥ w` in `U` is in `V`. `implication_adjunction` proves its deduction law; `implication_eq_himp` identifies it with the native Heyting operation. `mem_himp` is the resulting future-stage interpretation theorem. The model therefore uses persistent implication, not pointwise implication on Boolean membership tests.

The public worlds are pairs of Booleans ordered coordinatewise. The root is `(false,false)`, the two middle worlds are `(true,false)` and `(false,true)`, and the tip is `(true,true)`. Proposition `p` requires the first coordinate true; `q` requires the second. Both are persistent, proper, and locally inhabited. Their conjunction holds only at the tip.

The checked cases establish:

- `openNucleus p p = ⊤` while `p ≠ ⊤`: the modality is not identity.
- `openNucleus p ⊥ = ⊥`: it is not indiscriminate forcing.
- `p ⇨ q = q` and `q ⇨ p = p`: one requirement cannot discharge the other.
- One query layer for `p ⊓ q` gives `p ⊔ q`, which omits the root; two layers give `⊤` through `two_steps`.
- The internal negation of `p` is bottom, so `p ⊔ ¬p ≠ ⊤`. The represented logic is non-Boolean even though Lean can classically decide external propositions about its sets.

These examples establish nonempty local answers and distinguish one query from two. They consume the generic implication and closure theorems rather than replacing those theorems with a finite truth table.

## The same propositions as actual answer sheaves

[OracleModalitySections.lean](../../SquareKit/OracleModalitySections.lean) constructs a site whose category is `OrderDual W`, with the bottom Grothendieck topology. Its sheaves are presheaves. At each world, `answers U` has carrier `PLift (w ∈ U)`. Its transition maps transport proofs along persistence; no field supplies an oracle answer. `answer_support` identifies the object's actual local inhabitance with `U`.

The representation is checked beyond membership:

- `hom_iff` identifies existence of an actual sheaf map `answers U ⟶ answers V` with entailment `U ≤ V`.
- `productIso` identifies the actual product of answer sheaves with the answer sheaf of conjunction.
- `parameterized_implication` identifies maps `answers R × answers U ⟶ answers V` with `R ≤ U ⇨ V`.

These results supply entailment, conjunction, and implication for the selected persistent propositional fragment. They do not claim a classifier for every universe of dependent predicates or a complete internal type-theoretic model.

The display `answers U ⟶ answers ⊤` forgets the answer. `term_iff` proves that this display has a section exactly when `U = ⊤`. `global_section_iff` then uses the existing `SquareKit.SheafSections.globalEquiv` to obtain the corresponding statement about global elements of the actual internal section object. The positive `topSection` uses the existing `name` construction, and `suppliedSection` exposes it publicly.

For `p ⊓ q`, `localJointAnswer` is an actual Type-valued answer at the tip. `modal_answer_without_section` combines modal validity with the absence of a global internal section of that very display. This is not an unrelated counterexample borrowed from another site. The answer types here are subsingleton because the chosen oracle is proposition-valued. Modal validity does not construct unmodalized global answers, and these results provide no extraction procedure for general data-bearing answer containers.

## Reuse and limits

Mathlib is pinned at `56a005855ea17e0b0958f73ec801ae140b0a1679`. The construction reuses its [nuclei](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Order/Nucleus.lean), [Heyting algebra](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Order/Heyting/Basic.lean), persistent set lattices, and ordinary sheaf category. The section bridge consumes [SheafSections.lean](../../SquareKit/SheafSections.lean), including its existing supported small-universe setup. No universe-resizing claim is needed.

The existing [Boolean lock fragment](../../SquareKit/Internal/ModalAccess/Fragment.lean) describes generated access judgments and keys. It is not the oracle return/query closure proved here. The existing [assembly category](../../SquareKit/Assembly.lean) supplies tracked maps; it does not by itself construct an effective topos, its full internal proposition object, or every Lawvere–Tierney topology. Those developments were inspected but are not silently promoted into a model of the paper's general construction.

The [oracle computation study](oracle-relative-computation.md) and [idealized target study](idealized-target-realizations.md) distinguish supplied programs from mathematical interpretations and uniform extraction. This delivery adds a different concrete distinction: modal truth versus a global section in a represented setting. It supplies no new machine-computability or physical impossibility result. No runtime oracle executor or physical device is claimed.

For #493, the demonstrated contract must retain which propositions are interpreted, how queries generate closure, which logical operations are represented, and whether the requested evidence is modal validity, a local answer, or a selected global section. The proved join/composition comparison has explicit hypotheses. These observations do not adopt a universal evidence interface or unblock #489.

## Validation

The focused target `direnv exec . lake build Examples.OracleModalities` checks all new definitions, generic theorems, representation laws, and public positive/separating cases. There is no runtime performance claim requiring a device or benchmark. Exact committed acceptance also requires the repository's full build, exhaustive axiom audit, and independent Standards and Spec reviews; those outcomes are recorded in the implementation handoff.
