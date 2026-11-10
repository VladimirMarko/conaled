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

The relative-fiber checkpoint adds a total diagram and strict projection built
from three groupoid families, six natural restriction maps and the five total
restriction equations. These hypotheses contain no matching equivalence or
extension operation. A relative object explicitly retains its local fiber,
actual overlap, diagonal and cocycle equations, and equality with the supplied
base overlap. Its groupoid arrows are actual matching arrows with vertical
local action. Reconstruction and extraction recover total matching data.

Transport along a base matching arrow uses the local family's own action and
transports the overlap by the canonical Grothendieck isomorphism. The checked
`transport_localFiber` theorem identifies this action exactly. The relative
transport functor laws and equivalence from its total category to total
matching data remain open; object transport alone does not establish closure.
