# GitHub issue #458: Audit capability preservation in the recovered ADWH continuation

Source: https://github.com/VladimirMarko/conaled/issues/458
Retrieved: 2026-11-13 (UTC). Live issue snapshot; historical instructions are evidence, not active checkpoint commands.
Issue state at retrieval: closed. Updated: 2026-11-11T17:34:48Z.

## Issue body

Part of #149. Owner-qualified scope, 2026-11-11.

## Deciding criteria

1. Do not miss useful mathematics that has already been built.
2. Cover the materials of *Algorithm Design with Haskell*, with factual corrections.
3. Make the results useful to `conaled`.

Checkpoint 335 and the retired external continuation are evidence sources, not normative specifications. Historical acceptance labels, private task ordering and declaration counts do not decide completion. A faithful copy of an erroneous or unhelpfully specialized statement is not the objective. Preserve useful mathematical content through corrected statements, more general constructions and checked specializations where justified; document any deliberate replacement or exclusion and its effect on book coverage and repository use.

## Audit

Compare the recovered Chapter 1, Chapter 2 and generic-search selections with the book, factual corrections, built sources and current library. Use the existing provenance/correspondence ledgers in `docs/research/adwh-recovered-handoff.md`, `adwh-recovered-research.md`, `adwh-reconstruction-map.md` and `adwh-recovered-integration.md`. The recovered source was integrated at `1e7bee1e` and is published on master. Do not resume the private tracker or its process holds.

- Account for useful named declarations, anonymous examples, contexts and corrections as retained, generalized with checked specialization, replaced with proved correspondence, corrected, or explicitly scoped to a remaining issue. Explain deliberate exclusions using the three deciding criteria. Reconcile existing records rather than duplicating a full inventory.
- Check book coverage and mathematical truth independently of checkpoint parity. Cite the relevant book passage and correction where a source statement is incomplete or wrong. Do not silently weaken a claim to obtain a proof.
- Compare domains, assumptions, quantifier order, computational witnesses, partiality, ordered occurrences/ties, arbitrary initial states, pricing generality, exact versus bounded costs, demand and uniformity wherever useful content depends on them. Erased observations do not establish retention of richer data.
- Inspect elaborated types at coercion boundaries. Retain discriminating boundary/negative examples; finite examples do not replace symbolic asymptotic counterexamples.
- Check current shared owners and later local implementations before adding machinery. For retained/generalized capabilities identify an actual or concrete prospective `conaled` consumer, reusable interface or useful mathematical role. A blanket architecture migration is not required.
- Fix or scope each substantive gap with an owner, observable result and validation obligation. #459 owns the remaining Chapter 2 contracts; it must use these same criteria, not reimplement satisfied historical prerequisites. Formal changes require statement review, checked cases, applicable build/audit and independent review.
- Update the maintained coverage map and #149 with exact audited scope, useful recovered mathematics, factual corrections, integration/reuse findings and remaining obligations. Compilation or source completion labels alone do not establish whole-chapter coverage.

The separate queens/kernel work remains under #137. This audit does not assert a known ADWH witness-erasure defect; the Felix finding motivated a useful audit criterion. It does not require preserving every historical formulation or treating checkpoint 335 as mathematical authority.


## Comment 6802827095

Source: https://github.com/VladimirMarko/conaled/issues/458#issuecomment-6802827095

The selected recovered Chapter 1/2/search audit is complete under the owner's criteria: useful built mathematics, book coverage with factual corrections, and usefulness to conaled. Checkpoint335 remains evidence only. Correspondence ledgers and exact official code-archive paths are reconciled; Timing/Amortized already completed under #173 is not a prerequisite. Seven remaining packages R1–R7 are scoped to #459. Full printed chapters were unavailable, so this is not new whole-book certification; #149 retains evidence/provenance ownership. See the ADWH reconstruction and recovered-integration reports.

Integrated and published on `master` in `924542a1cdab7a3637a14fb9c61945b41fea77e4`. Final independent Standards and Spec reviews passed against original wave base `3c064b11a5812e38c317601473e6897f65ce2a32`. The exact combined candidate passed `./check.sh --candidate HEAD` (all 2,737 modules, exhaustive audit limited to `propext`, `Classical.choice`, `Quot.sound`) and `./check.sh --verify-candidate HEAD`. This combined check was guarded incremental; #7's required fresh validation was separately completed at `c866972a59c72dba3707c6389f7528394280062e`, before the added #440/#444 sources received their full integrated checks.

