# Issue 317 framework source check

Research helper `/root/sigma_research`, 2026-11-05. Continuation of the assigned implementation loop. No tracker operations, commits, source edits or independent review.

Primary sources opened and inspected directly:

- https://arxiv.org/html/2009.05539v1: BHL Definitions 5.1, 5.6–5.7, 5.11–5.12, 6.14–6.20; Proposition 6.21; Theorem 5.22; Corollary 5.24; inversion discussion and Appendix A scope.
- https://arxiv.org/html/2112.00539v1: Haselwarter–Bauer Definitions 2.16, 2.18, 2.20; instantiation and finitary boundary/congruence discussion.
- https://arxiv.org/html/1411.1736v2: Lumsdaine–Warren Theorem 3.4.1 and §4.1, including Heuristic 4.1.1's explicit type-equality exclusion.

The checked facts agree with the preparation's central boundary. The final report keeps source summaries short and derives an original obligation map for the selected example. It does not repeat the preparation's proposed conventional primitive signature as if it were the actual Lean implementation. Actual source uses sigma/pack/unpack, explicit context/substitution objects and untyped Horn equality; conventional Σ/pair/split binder rules are an explanatory presentation requiring an unproved adequacy bridge.

Full stable comprehension-isomorphism design selects both inverse laws up front. Dependent split's type uses pack ∘ unpack = id. Therefore adding a derived uniqueness schema later is a valid law extension over this model class, not evidence for beta-only-to-eta all-model expansion.

Report is in `/tmp/conaled-314-320/317/docs/research/dependent-constructor-admission.md`. Its final evidence inventory remains pending implementation. The helper will inspect actual declarations and validation evidence before reporting completion.

Final clarification from direct theorem inspection: Haselwarter–Bauer 3.18 is a raw-theory presuppositivity theorem with explicit well-formed metavariable and variable contexts, not a theorem requiring finitariness as its stated hypothesis. The report records this distinction. Their 3.8 substitution result is also raw-theory scoped; 3.13 needs derivable instantiations, 3.17 additionally needs well-formed contexts, and economical congruence 3.22 uses finitariness.

Draft handoff: source research and conceptual report are complete. Implementation evidence is deliberately pending. No claim of checked positive/negative cases, candidate acceptance, or independent review appears in the draft. Parent requested release of the helper slot; reactivate this helper after source modules and checked cases stabilize for final factual reconciliation.
