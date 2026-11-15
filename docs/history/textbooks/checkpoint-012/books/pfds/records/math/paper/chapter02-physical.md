# Physical ordered insertion: expectations and statement review

Chapter2 requirements version1, base82501d108f33c62d21b5e0d0f7d2376b902d8d49.
This is implementation evidence, not final Standards or Spec approval.

## Independent cases

Allocate leaf1 at address0, leaf5 at address1, then root3 at address2. The
observed ordered tree has three nodes. Inserting2 follows left then right:
three element comparisons, three structural visits (including the empty
endpoint), one new leaf and two copied ancestors. The new frontier is6.
The root's right child must remain address1. Every previously observed version
remains representable in the extended heap, in particular the original root2.

Baseline insertion of1 takes three comparisons and two visits. The equal
subtree returns unchanged, but its ancestor3 is copied, so exactly one cell is
allocated at address3 and the final root differs from the old address2. A
value-only identity theorem would miss this distinction. The optimized worker
must discharge the separate zero-allocation/original-root duplicate contract.

Existing pure insertion could calculate these values, but no public theorem
connected that pure result to an actual heap traversal and retained off-path
addresses. The missing connection motivated Path/Rebuilds and Ordered, without
changing the independent expected values to fit compilation.

## Claims and boundaries

- searchPathBy selects only by the supplied key. The generic form is shared
  by set insertion and map binding; no payload order is needed for the latter.
- Rebuilds records copied ancestor labels and exact untouched child roots.
  Its empty-path constructor leaves the modified focus unconstrained; it
  does not itself claim freshness or preservation of that focus's children.
  Allocation/fresh-frontier claims belong to the execution theorem. Map
  overwrite requires a separate endpoint property, owned by the map worker.
- off_path compares addresses reached in the same final heap. follow_mono
  separately transports successful old-heap observations. Together these
  give actual root identity, not merely equality of unfolded trees.
- insertRunFuel follows heap references and allocates after successful
  recursive return. Its independent profile uses pure member comparison
  count, search-path length plus one visit, and path length plus one cell
  exactly when the directed search misses. It is valid even for unordered
  represented trees; global set membership additionally requires Ordered.
- Frontier fuel is sufficient because Represents includes backward child
  references. Invalid roots or insufficient caller-supplied fuel remain
  optional failures. The valid-input theorem proves success rather than
  assuming success as a premise.
- Comparisons, structural visits and cells are three separate natural-number
  measures. No Lean runtime allocation, machine time or space lower bound is
  inferred from the model.
- insertSquare uses the existing representation/optionalRepresentation and
  Relational.RelSquare. optionalRootValueSquare composes while preserving the
  distinction between traversal failure and an observed empty tree. The
  ordered-set corollary combines physical execution, old-version retention,
  independent Contains semantics and the strict all-descendant invariant.

## Compilation state

Path including generic searchPathBy compiled at17de2f7. Baseline Ordered's
first corrections concern definitional tuple projections and allocation-root
normalization; no public statement or expected result changed. Candidate
8eaa9c2 contains the complete physical baseline and relational observations;
focused compilation is still running. Whole-chapter validation, audit and
independent reviews remain pending.

Focused update: all baseline insertion, generic optional observation, integer
traversal and connected cases compiled at ebdeec2,669jobs. See
validation/chapter02-integer-ordered-focused-r9.json and matching frozen log.
The final case correction unfolds Diverges explicitly because that recursive
proposition has no synthesized Decidable instance; it does not change the
expected shared right-root identity. The generic optionalRootValueSquare was
moved into SharedTree.Observation unchanged for use by optimized adapters.
Preparatory gap CH02-PRE-001 separately adds explicit duplicate terminal-root
identity; the existing Rebuilds statement was not weakened or overclaimed.
