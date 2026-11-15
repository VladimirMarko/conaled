# Narrow quantified-binder correction assessment

Role: implementation author in the existing whole-Chapter-3 loop. This is not an independent review or a passing compiler/type result.

The complete failed attempt1 is preserved. Its five diagnostics name proof binders inside the conclusions of exists_uniform_competitor_bound and exists_uniform_optimality. Those bound names have no dependent occurrence later in their propositions; the proof terms still need and use all five hypotheses after their explicit intro commands. This correction changes only the proposition-local labels to the conventional underscore-prefixed names. It does not alter a linter option or remove a binder.

| Proposition | Raw binder-name changes | Preserved domains/order |
| --- | --- | --- |
| exists_uniform_competitor_bound | distinct → _distinct; correct → _correct | K first, then c/m, valid k:Fin m, input, Nodup(ofFn input), next, Selects next k, both traces/outputs, positive tariff and both actual runs, then the paid comparison |
| exists_uniform_optimality | distinct → _distinct; total → _total; correct → _correct | K first, then c/m, valid k:Fin m, input, Nodup(ofFn input), next, Total next, Selects next k, positive tariff, then witnesses for both actual runs, equal optional answer, lower query charge and paid comparison |

The raw source headers of these two propositions change by five added underscores. Normalizing exactly those five binder labels reproduces the original source byte-for-byte. Their quantifier order, domain types, dependencies, hypotheses and conclusions are unchanged. The proof bodies—including the introduction and later use of distinct, total and correct—are byte-identical.

All remaining44 public headers and the one private helper header are byte-identical; all47 declaration bodies are byte-identical. All three computational definitions (observedSelect, work, selectedValue) are byte-identical. The complete Examples.CoordinateSelection source, all16 cases and their independently expected mathematics are byte-identical. All six older query sources and eleven exact donor dependencies are byte-identical, for18 untouched source files besides the one corrected core.

In particular, this preserves the actual acquired-list/worker observation equality, paid selector calls, fixed-default0 some proof on valid ranks, all-input correctness including duplicates, uniform constants before data, Nodup/valid-rank competitor domain, positive query tariff, empty/invalid extension and every real-execution witness. There is no weakened hypothesis, new assumption, admission, option suppression or change of tariff.

The complete47-row preservation record includes exact corrected source headers and per-body hashes. The existing declaration/private/case inventories remain the source of their unchanged full scope; a corrected inventory is saved additively. Candidate-bound46 and337 explicit-@ input copies retain every original check and all six printer options; only their binding comment identifies the successor. Original inputs and all failed evidence remain immutable.

The examples have not compiled. Neither an absence of further diagnostics in the blocked attempt nor this lexical/source assessment is evidence of their success. The successor needs root's new serial focused attempt; actual printed statements, full candidate check/audit, both independent review axes, immediate verification and all83 obligations remain unchanged completion gates.
