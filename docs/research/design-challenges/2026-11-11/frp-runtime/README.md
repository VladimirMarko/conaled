# FRP runtime design challenge

This investigation challenges the proposed hybrid FRP runtime, its staged
implementation route, policy-directed realization choice and live backend
migration. It assesses architecture and evidence; it does not implement a
runtime or change the tracked acceptance criteria.

The source baseline is
[`1ecdea2376786920a043009a35712a5dec93723a`](https://github.com/VladimirMarko/conaled/tree/1ecdea2376786920a043009a35712a5dec93723a).
The [shared brief](brief.md) specifies the question, constraints, evidence and
three complementary perspectives. The [neutral candidate packet](packet.txt)
contains the exact proposal text supplied to the judges. It is preserved as
plain text: its relative links refer to the original document location,
`docs/research/frp-runtime-direction.md`, in the pinned source tree.

The judges received fresh contexts and a source archive without Git metadata.
Prior owner disposition and coordinator endorsements were removed from the
candidate packet; its technical scopes and proposed sequence were retained.
The [sanitization record](sanitization.json) identifies the source and packet
hashes. Judges were instructed not to read the original checkout, history,
project issue discussions or one another's drafts. They could inspect the
pinned code and external primary literature. This controls supplied context;
it is not evidence of model diversity or a guarantee against shared assumptions.

The brief's `/tmp/conaled-frp-design-evidence` paths identify the original task
location. Repository-relative paths and line numbers in the initial reports
refer to the pinned source archive. The publication preserves those reports
verbatim. The manifest records their hashes and any separately saved experiments
or clarification supplements. The synthesis is a separate coordinator analysis.

The three design judgments are distinct from the independent Standards and Spec
review used to publish this evidence. No runtime measurement, Lean compilation,
or implementation acceptance follows merely from a favorable recommendation.
