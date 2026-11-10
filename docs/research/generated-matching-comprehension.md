# Matching comprehension closure

This is an active #445 implementation record. General dependent comprehension
closure remains in progress.

`CechMatchingComprehensionProducts` constructs the product of two arbitrary
matching diagrams and an equivalence from their matching groupoid product.
It preserves both local objects, both overlap isomorphisms and both components
of every local arrow. No global extension or effectivity is assumed. Constant
non-discrete fibers specialize through the independently proved constant
diagram equivalence. This supplies product closure, including the base-binder
case when its parameter diagram is identified with the relevant product.

`CechMatchingComprehensionRebase` transports an independently supplied datum
along any selected isomorphism of its local representative. Diagonal and triple
laws follow by naturality and cancellation. The resulting matching isomorphism
has exactly the supplied local arrow. This is preparation for normalizing
relative matching fibers, not an assumption that matching objects extend.

`Examples.CechMatchingComprehension` checks both components of arbitrary
product arrows, retains a nonidentity integer loop vertically over arbitrary
base matching data, and recovers the selected local arrow of rebasing. Statement
review checks arbitrary datum quantifiers and preserves arrow data rather than
using object equality as a substitute. Both modules and examples pass focused
Lean checks at the repository defaults. Full dependent fiber identification,
set and identity cases, integrated audit and independent reviews remain open.
