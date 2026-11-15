# Conditional treap work: separate bounded mathematical check

Recorded 2026-11-02. Contributor: `/root/tail_examples_preflight`.
Inspected `../research/treap-conditional-work-preflight.md`, 25,523 bytes,
SHA-256 `99e7c6128c5a941d0dbef0b473c0f4f27e73d8f75b69aa64d347937dd4b2dcc1`.
Root transcribed this assessment from the contributor's completed response.
It arrived after checkpoint 0026 was captured and is not inside that archive.

## Result

No concrete mathematical error or missing probabilistic premise was found.
In particular, this bounded reading found no hidden dependence or indexing
failure in the fixed-key history partition or weighted layer assembly.
This is an assessment of a proof plan, not completed Lean coverage, an
independent final review or a chapter-acceptance result.

For each fixed key `v` in the pivot set A, its exact proper-ancestor sequence
followed by the current root v gives a finite partition of the sample space.
Every positive-probability atom determines the interval, K, its weight, the
parent's weight, rank-root eligibility and the nonnegative charge Z. The event
reveals successive minima along the search path to v, without revealing the
remaining descendant order. After the forced root v, the chosen child
therefore retains the uniform conditional order required by the induction.

The constant nine is valid: charge the forced root by one, then apply the
window-chain bound to its determined child, obtaining
`1 + 8*x_child/W <= 9`. Rank-root eligibility and Z are fixed on each history
atom, so the weighted inequality follows without an independence premise.
Summing over the fixed set A accounts for random rank-root membership.

The coverage argument also holds. Assigning a node to its highest ancestor
in the same integer layer gives a partition. Every resulting component is
contained in its root's relative rank window, and its descendant charges do
not exceed the root's charge. At any fixed layer, the roots are ancestor-free;
their pivot subtrees and decomposed-key intervals are disjoint. Consequently
the three bounds on the active-root count and the later concavity/geometric
sum apply pointwise. The substitution of an upper bound for that count uses
the valid monotonicity of `s * log_2(1 + b/s)` for positive b and s.

The contributor additionally checked:

- Both counterfamilies have the stated effect and arithmetic, including the
  strict-larger-pivot-subtree conditional-position example.
- The two-color search domination needs only each color's conditional
  uniform relative order. Uniformity of their merged order is not assumed.
- The actual left-maximum extraction and reconstruction in Figures 11 and
  13 of the retained `book-source/joinable-2022.pdf` agree with the proposed
  `join2` work analysis. The contributor inspected the retained source
  figures directly.
- A common conditional logarithmic charge suffices for the planned
  expectation assembly; it does not imply that each actual local `join2`
  is bounded by its actual local split.

## Limits and retained obligations

Canonical-tree uniqueness/search characterization, actual recursion/interval
correspondence, precise conditional history laws, primitive-work recurrences,
component coverage and book/paper execution-cost correspondence remain
explicit future formal obligations. The chapter and C10-117 are still queued
and open. The report does not refute the total expected-work theorem or
certify every literal intermediate claim in the source.

The contributor wrote or modified no files and performed no compiler,
checker, project hash helper, enumeration, cache/configuration, Git/ref or
remote operation. The old Chapter 1 validation continued unchanged.
