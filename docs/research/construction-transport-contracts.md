# Frozen practical construction contracts (#461)

Frozen before abstraction design at accepted revision
`924542a1cdab7a3637a14fb9c61945b41fea77e4`.

The compiler client is the existing bound-square list program in
`Examples/RecursiveCompilation.lean`. For every finite integer list `xs`, its
ordinary compilation returns the sum of the squares. Its counted compilation
returns that value paired with `1 + 3 * xs.length`, using the existing primitive
charges and one visit per cell. On `[2,-1,3]` the pair is `(14,10)`.
Source execution visits exactly `xs.length` cells. Preserve the source syntax,
existing compilation and fusion theorems, and value erasure. Resource
reweighting must act on actual transitions, including the visit charge.
These are executable finite computations and modeled charges, not Lean time
or allocation measurements. Equality observes both components when cost is
claimed; value-only fusion does not promise equal cost.

The feedback client is the independently defined natural triangular stream in
`Examples/GuardedStreamCompiler.lean`: coordinate zero is zero, and coordinate
`n+1` is `n+1` plus coordinate `n`. Its compiled stream must agree at every
coordinate, including coordinate four equal to ten. Retain the selected stream
and its feedback equation. Guardedness must justify equality of the outputs of
all admitted witnesses. Test coefficient interpretations through residues
modulo four and modulo two, with their pointwise stream observations. Recover
the native stream before quotienting; do not promise inversion of a lossy map.
This is denotational feedback with finite coordinate evaluation, not a service
scheduler or an external delivery/productivity guarantee.

Both direct baselines already exist and will be consumed through their public
theorems. The new investigation must identify proof work removed beyond those
native routes. A shared interface is optional: retain both contracts and a
checked separating obstruction if diagonal representation is inappropriate.
Target coverage experiments must retain #444's omitted-code counterexample
and include an inhabited positive case for the proposed weaker certificate.
