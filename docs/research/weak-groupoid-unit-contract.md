# Weak groupoid-unit construction contract

Frozen for #448 before proof development. Base is accepted integration ff63e506.

I is the codiscrete category on Bool with constructor false. For arbitrary
groupoids E,V and functor p:E→V, supplied lifting data select an actual target
and arrow above every arrow out of p(e), with identity normalization. No
composition law for these choices is assumed. No derivation of choices from
mere isofibration existence is claimed.

For every groupoid Γ, motive c:Γ×I→V and branch d:Γ→E with the exact equation
d followed by p = constructor followed by c, construct a whole functor j.
It must satisfy j followed by p = c and constructor followed by j = d.
Use lift conjugation on arrows; object agreement is insufficient. Keeping p
and lift choices fixed, arbitrary precomposition of c/d must preserve j as
equality of whole functors, also after two substitutions.

Construct the strict parameter groupoid P of pairs (a:I→V,e:E) with equality
p(e)=a(false), and arrow pairs (η,h) satisfying the transported equality
p(h)=η(false). This is not an isocomma groupoid. Evaluation and projection
provide a generic motive/branch. Currying gives a bijective representation of
motive/branch functors; prove both inverse equalities and substitution
naturality on full functors. Applying the same lift formula generically must
construct J and agree exactly with the direct j after instantiation.

The C2 motive must distinguish two fillers by an arrow although their object
maps coincide. A branch-fixing motive automorphism swaps them. A normalized
choice sending forward to 1 and backward to 0 fails composition, whereas
conjugation repairs it. These are counterexamples to stronger claims, not to
existence of the desired stable construction. Positive examples must consume
universal beta, arrow-composition and repeated-substitution theorems.

Both routes and their exact comparison are acceptance. No equality is weakened
to natural isomorphism. No general LF/isofibration framework or project-wide
local-universes adoption is required. Primary source conditions remain those
recorded for arXiv:1411.1736v2; full LF and arithmetic of universes are not new
Lean claims in this bounded construction.
