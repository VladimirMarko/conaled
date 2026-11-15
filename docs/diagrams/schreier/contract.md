# Finite labelled diagram contract

Issue #466. Frozen before implementing the exporter or renderer.

Vertices are indexed by an explicit equivalence `Fin n ≃ X`. Generator indices
are `Fin m`, mapped to group values by a function which need not be injective.
Export exactly one row per vertex/index pair, in vertex-major order. Each row
has a stable `source:generator` ID, source, target, generator index and group
label. The decoded target must be that label acting on the decoded source.
Every original labelled Schreier edge between decoded vertices must have its
row, retaining its generator index. Prove the comparison to the existing
forward-edge interpretation. Distinct indices remain separate even when their
group values coincide. No synthetic inverse edges are exported.

The executable seam is JSON: a list of diagrams, each with `name`, `vertices`,
`generators` and `edges`. Vertices have numeric `id` and display `label`;
generators have numeric `id` and observed group `label`; edges have string `id`,
numeric `source`, `target`, `generator`, and observed group `label`.
Group observations in these fixtures are faithful: cyclic residues are numbers,
and permutations are their three images. Display strings are never identities.

The renderer seam is a JSON-file-to-SVG-file command. Preserve every edge,
including loops and parallel edges, give it its ID and a directed arrowhead,
and escape text. Repeated runs on identical input must be byte-identical.
Geometric layout is outside the theorem and needs separate visual inspection.

Independent calculations:

- C3, additive residues written multiplicatively, generator 1: 0→1→2→0.
  The regular action has trivial stabilizers and this generator generates C3.
- Natural S3: generator indices 0 and 2 both denote (01), index 1 denotes (12).
  Image arrays are [1,0,2], [0,2,1], [1,0,2]. From 0 the chronological trace
  0 then 1 reaches 2; Mathlib's written-order path reaches 1. Generator (01)
  fixes 2 and (12) fixes 0. All nine rows must survive, including duplicate labels.
- Trivial S3 action on Unit with the same generators: three loops, of which two
  have equal group values but distinct indices; (01) and (12) remain distinct
  interpreted arrows despite having the same endpoints.
- Generation is stated per example. Reuse the existing nonempty proper-subgroup
  control to show why a generator drawing alone does not imply full coverage.

The fixtures specify mathematical expectations independently of serialization.
A new exporter and its public edge correspondence are missing at this baseline;
existing Schreier results already prove the chronological convention and proper
subgroup control. Those results should be consumed, not reproved independently.
