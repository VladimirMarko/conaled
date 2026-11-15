# Settings and semantic interfaces: research and checked boundary

The [#337–#342 orchestration](https://github.com/VladimirMarko/conaled/issues/235)
started from `b8731310f05efdac29f994706fbc1f32eb77de20`, which already contained
the completed #339 specification-transport experiment. This report connects
the subsequent results and keeps their evidential limits explicit.

## Results and use

| Issue | Delivered evidence | Consequence |
|---|---|---|
| [#337](https://github.com/VladimirMarko/conaled/issues/337) | [Indexed partial computation](context-dependent-partial-computation.md): paper approximants, selected certificates, repeated reindexing, conditional SDT comparison and failure controls. | Derive preservation of the selected solution under the stated strictness/continuity or SDT hypotheses. Existence of some solution does not suffice. |
| [#338](https://github.com/VladimirMarko/conaled/issues/338) | [Joint conversion](joint-conversion-extensions.md): paper arithmetic packages, independent selected dependent meaning, joint rewrite analysis and a nonconfluent-union control. | Semantic validity and operational admission are separate obligations. Compare explicit equality certificates with a conversion procedure on a stated fragment. |
| [#339](https://github.com/VladimirMarko/conaled/issues/339) | Earlier [checked same-signature transport](compositional-specification-experiment.md). | Reuse local rule certificates for existing clients; no general reverse translation or executable translator follows. |
| [#340](https://github.com/VladimirMarko/conaled/issues/340) | [Institutions assessment](institutions-as-interfaces.md): primary proof-sensitive frameworks, worked logic change, composition, rejected translation and three client families. | Investigate broad specification/interpretation organization with distinct satisfaction, proof, dependency and computation capabilities. No universal combined record is adopted. |
| [#341](https://github.com/VladimirMarko/conaled/issues/341) | [Checked semantic-client boundary](semantic-client-boundaries.md): exact squares descend to handles; arbitrary pure handle clients respect equal meanings; selected parses remain distinct. | An opt-in boundary is available for exact set-level clients. Raw representations remain available for compiler work. Relational and higher meanings retain their own contracts. |
| [#342](https://github.com/VladimirMarko/conaled/issues/342) | [Dependent-framework comparison](dependent-calculus-frameworks.md): independent fragments, paper translations and selected client, source hypothesis map and separating model. | Compare direct BHL theory-map machinery with an HB boundary-layer adaptation before deciding on an engine adapter or replacement. |

The new formal implementation is #341. The new constructions in #337, #338,
#340 and #342 are paper arguments supported by primary sources and independent
review. They are not new Lean theorems. Each report distinguishes earlier
checked library results from its proposed implementation work.

## Architectural conclusions

Equality and pair laws remain part of each mathematical specification. Local
representations can differ if their interpretation meets that specification.
The checked boundary identifies redundant flags without identifying different
specified parses. This is compatible with construction and observation: the
specification determines which observations must be retained, and local
preservation proofs derive correctness for composed constructions.

Ordinary satisfaction records truth. The institution literature also offers
proof-sensitive organization, so the comparison cannot end with the claim that
institutions necessarily erase witnesses. The unresolved design choice is how
much common structure helps these clients while retaining selected proofs,
dependent substitution and computation contracts. The #340 comparison supplies
concrete diagrams and tests for that decision.

The #341 quotient is one exact, set-level implementation of a semantic-client
boundary. It is not the proposed universal institution interface. Many-valued
relations need not induce the equivalence relation used there, and higher
identity data needs its own preservation evidence. Existing relational squares,
indexed interfaces and witness bridges remain valid alternatives.

The dependent-framework study similarly separates generic structural theorems
from their admissibility hypotheses. BHL also supplies syntax-template theory
maps, primitive-rule certificates and functorial derivation transport; this
existing source construction should inform a Lean implementation rather than
be treated as missing mathematics. A theory presentation must supply the
appropriate ordered boundary evidence. Such evidence can remove repeated
structural proofs; it does not manufacture a model or identify incompatible
pair contracts. The conversion study reinforces this separation: valid equations
do not by themselves determine a terminating, confluent checking strategy.

## Owned next experiments

The reports give bounded acceptance tests for the next implementation choices:

- Under #289/#235, formalize indexed partial certificates and selected least
  fixed-point transport; assess a concrete SDT provider separately against its
  additional hypotheses.
- Under #288, compare proof-producing conversion for the frozen joint packages
  with explicit equality transport, including the nonconfluent-union control.
- Under #290/#235, test an evidence-sensitive institution/computation interface
  on the report's actual logic change and selected clients before deciding its
  breadth of use.
- Under #289/#290, compare direct BHL implementation with an HB boundary-layer
  adaptation using independently specified fragments, derived structural
  results and the failed-extension control before deciding whether to adapt
  or replace the existing representation.

These are scoped follow-up proposals, not claims that their implementations
were completed here. The executable proof translator remains separately
[recorded on #339](https://github.com/VladimirMarko/conaled/issues/339#issuecomment-6702431657)
and owned by #290, deferred until a concrete compilation consumer supplies its
requirements. This orchestration does not resume #107 or prepare #108's
independent task.

Agent productivity is sufficient for the MVP. These results compare obligations
and establish bounded mathematical capabilities; they do not measure a broad
productivity advantage or runtime improvement. Independent review records and
candidate build/audit evidence are retained by the orchestration and linked
from its tracker completion record.
