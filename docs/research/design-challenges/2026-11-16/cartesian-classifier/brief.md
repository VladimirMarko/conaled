# Design challenge: Cartesian classification beyond vertex local systems

## Decision and requested capability

Assess [the original proposal](proposal.md) as a proposed research completion of
GitHub issue #602. The user asks to pursue the construction now, alongside
#601's separate bounded Lean formalization. The decision is whether to retain,
revise or reject this declared-domain classifier/decoder/ua construction and
its comparison on the accepted finite overlap. No adoption verdict is assumed.

The required outcome starts from arbitrary small Cartesian diagonal-Kan
families in a declared domain, preserves nontrivial higher data, and includes
the exact #600 Bool/Fin3 controls and selected-square comparison. An external
model existence theorem alone is insufficient. A genuine separating obstruction
with a concrete next construction is permitted by the issue; a missing proof
is not an obstruction.

## Inputs and pinned scope

- Repository `/home/vlad/Code/conaled`, starting revision
  `7406fbe2aceba3693856cc6998aae613011df1f5`.
- Read full issue via `gh issue view 602 --repo VladimirMarko/conaled --json body`.
- Read AGENTS.md, `docs/agents/architectural-quality.md`, domain guidance and
  applicable language-direction planning/adoption criteria.
- Accepted reports `docs/research/cartesian-filling-recomputation.md` and
  `docs/research/second-cubical-witness-preservation.md` establish the bounded
  route and original selected witnesses. Inspect the named local source when
  checking claims; do not use a concurrent #601 edit as previously checked proof.
- Candidate manuscript [the original proposal](proposal.md) is uncommitted research.
- Primary external PDF downloaded from
  https://www.cs.cmu.edu/~rwh/papers/uniform/uniform.pdf, SHA-256
  `ea235cf09eae29d3859f31976bc43a939a6565410ff4117addb99d0602c213a3`.
  Its §§2.7, 2.11–2.12 and 3.2 are construction dependencies, not a proof of the
  candidate's new overlap comparison. Fetch primary sources as useful.

The candidate chooses Cof=all sieves in a classical metatheory and Type u
fibers/Type(u+1) codes. This is an explicit stronger input filling requirement
than #600's finite formula cofibrations. No claim that every formula-only Kan
family admits the extra filler is made. The candidate supplies represented
classification, an instantiated aligned Glue construction, universe composition,
ua, a finite comparison through the common nerve, and a Z/2 higher consumer.
The cross-model comparison is a span with a native relative witness in RU and
another in U, each retaining its complete selected square. There is no proposed
global RU→U map. Judge whether this meets the requested overlap contract.

## Three independent perspectives

1. Contract and foundations. Verify the declared domain, sizes, Cof hypotheses,
   represented classification and strict record-level Glue alignment. Does ua
   follow from the identified source construction without assuming the desired
   result? Check endpoint/diagonal overlaps and the finite relative witnesses.
2. Implementation and use. Inspect usable local primitives and the exact finite
   clients. Determine which pieces can be reused and which are genuinely new.
   Check the higher Z/2 consumer all the way to its separating observation and
   whether the common-nerve span preserves the original selected data.
3. Alternatives and generality. Examine the all-sieve restriction and compare
   finite face/diagonal cofibrations, groupoid-only classifiers, or stronger
   cross-model bridges where consequential. Look for unintended models or
   evidence that the candidate's apparent generality loses a required client.

These lenses cover distinct failure modes; cross-cutting findings are welcome.
Use separate report paths `/tmp/conaled-602/challenge-foundations.md`,
`challenge-use.md`, and `generality.md`. Do not read other lens drafts
or coordinate conclusions before saving the initial report. Root will preserve
initial reports, reconcile findings and decide publication through the
implementation review workflow.

## Permitted work and report

Read-only repository investigation, primary-source checks and isolated scratch
experiments under `/tmp/conaled-602` are allowed. Do not edit repository files,
commit, push, alter tracker state, run a full build or spawn further agents.
#601 owns concurrent Lean work. If proof checks are useful, coordinate a
focused isolated scratch check through root.

Return a recommendation, strongest retaining evidence, concrete defects/risks/
unanswered questions with supporting locations, smallest useful correction,
and a discriminating test where evidence is insufficient. Distinguish inspected
Lean code, external mathematical proofs, candidate new derivations and executed
checks. State exposure and validation limits. Report whether the actual issue
acceptance is met and why; do not replace it with a weaker target silently.
