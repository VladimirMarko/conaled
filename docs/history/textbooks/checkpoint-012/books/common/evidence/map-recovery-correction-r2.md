# Map recovery: correction after focused round 2

Root's focused command on candidate `d59b8053…` completed with exit 1 in
7.42 seconds. The actual log remains `intake/maps-focused-r2.log`. All new
library modules compiled; the sole remaining failure was the `decide` proof of
`Examples.TextbookMaps.invalid_tree_boundary`, because the compound proposition
containing `OrderedBy` had no synthesized Decidable instance.

The correction changes only that proof. The malformed tree and all three parts
of the statement remain unchanged. The two lookup observations are proved by
reduction. If the tree were ordered, the existing public `lookup_correct`
theorem would identify those observations, yielding `none = some "hidden"`.
Constructor disjointness disproves the invariant. This directly connects the
negative example to the invariant-dependent public contract.

The author inspected `OrderedTree.All`, `OrderedTree.OrderedBy` and
`OrderedMap.lookup_correct`. No classical decision procedure, new instance,
warning suppression or weakened hypothesis was introduced. The previous
handoff, both failed logs and the first correction note remain unchanged.
Source writes are paused for root's next focused check. No compiler or Git
operation was run by this author, and no new compiler success is claimed.
