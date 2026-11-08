# Cut-observer continuity and uniform extension: historical proof proposal

This source-checked proof proposal refines the missing continuity obligation in
the [iteration roadmap](internal-sdt-iteration-roadmap.md) for
[#388](https://github.com/VladimirMarko/conaled/issues/388). It was prepared against
accepted P0/P1 code at `7a4bddcff3741741efda1dcb518ef86b81697c18`. The derivations
below were unformalized at that point. [P4 now implements them](internal-complete-certificate-family.md),
including concrete all-context N/LN completeness and the uniform extension compiler.
The proposal is retained to explain the proof choices and source boundary.

A direct recursion-theorem argument appears to supply both required semantic lemmas. A separate explicit search supplies the uniform extension tracker. The proof below uses the concrete finite/full cut realizers; it does not import an internal Eff theorem or assume continuity for arbitrary assemblies.

## Source and accepted assumptions

Primary source: van Oosten–Simpson, *Axioms and (counter)examples in synthetic domain theory*, APAL 104 (2000), 233–278, [publisher PDF](https://www.pure.ed.ac.uk/ws/portalfiles/portal/12306183/1_s2.0_S0168007200000142_main.pdf), DOI 10.1016/S0168-0072(00)00014-2. Retained PDF SHA-256: `066a36aa48fc38b5105637e8b77ef0b34de9e61751010492b922946b1ce9c2e2`. The source locators below were checked against that PDF.

Source locators: p.266 describes F by finite/full r.e. cuts; p.268 identifies I with finite cuts. Theorem 3.3, pp.268–269, uses a Rice–Shapiro-style monotonicity argument and the recursion theorem for a different target I₀, and explicitly obtains extension trackers recursively from source trackers. Definition 1.11, p.244, requires exponential restriction invertibility. Its general internal theorems are not transferred here. The following specialized LN argument is the present proposed derivation, not an attribution to Theorem 3.3.

Actual P0: `SquareKit/Assembly.lean` defines trackers on every realizer, products by pairing, `Hom.has_code`, and `encoded Nat`. `SquareKit/AssemblyLift.lean` defines `run e = (ofNat Code e).eval 0`; an LN realizer is a program diverging for `none` and returning the encoded value for `some v`. P1 `SquareKit/AssemblyPartialMap.lean` has saturated admissibility on every realizer. Its classifier is compatible with this lift; classification alone proves none of the continuity claims here.

Write `W(e)={k | eval (ofNat Code e) k is defined}` and `Cut(e,n)` for `W(e)=[0,n)`. Write `Full(e)` for `W(e)=N`. The #387 objects must realize n by **all** cut indices, with arbitrary returned values, and infinity by all full indices. Adding known finite bounds, restricting to canonical indices, or changing saturation would require rechecking these proofs. Construct a computable canonical index C(n) with domain `[0,n)` and output zero. [The #387 implementation](internal-cut-iteration.md) now constructs these cut objects, the computable canonical indices and their universal properties. P4 now supplies checked continuity and concrete completeness; the derivation below records its original proof plan.

## Observer interface

For f:Γ×I→LN with tracker code p, define the partial recursive observer

`q(p,r,e) = eval p (pair r e) >>= run`.

For every γ, every realizer r of γ, and every `Cut(e,n)`, tracking and single-valued partial evaluation give

`v ∈ q(p,r,e) ↔ f(γ,n)=some v`.

The same statement applies to h:Γ×F→LN on full indices and h(γ,∞). In particular a bottom output makes the observer undefined. No behavior is required on nonrealizing indices. Nat encodings should be retained explicitly in Lean until simp establishes the identity encoding. Fix γ,r for the next two lemmas; the observer remains recursive as a function of e.

## Lemma A: flat monotonicity on cuts

Proposed statement: if a partial recursive q has the observer contract for a finite-cut function f, then `n≤m` and `f(n)=some v` imply `f(m)=some v`. If its contract includes full indices, also `f(n)=some v → f(∞)=some v`.

For finite m use `Code.fixed_point₂` to construct an index E whose evaluation on k does this:

1. If k<n, return zero.
2. Otherwise, if k<m, wait for q(E); return zero exactly when its result is v, and diverge for any other result.
3. Otherwise diverge.

Thus W(E) is `[0,n)` if q(E) does not return v, and `[0,m)` if it does. In the first case E realizes n, whose observer contract forces q(E) to return v, a contradiction. Therefore it returns v, E realizes m, and the contract gives the conclusion. For the upper endpoint infinity, remove the `k<m` guard. Both possible domains remain legitimate finite/full cuts. The proof never applies extensionality to a malformed index.

Partial equality tests above are performed only after the observer terminates. There is no decision procedure for its divergence. Classical case distinction is used in the proof of domains, not in the program.

## Lemma B: finite witness for a defined value at infinity

Proposed statement: if q tracks a flat-valued function h on finite/full cuts and `h(∞)=some v`, then `∃n, h(n)=some v`.

Choose code Q computing the observer q on numeric indices. By `Code.fixed_point₂`, construct E with

`eval E k = if evaln k Q (encode E) = some v then diverge else return zero`.

The conditional is a total decidable bounded-computation test. If q(E) does not return v, soundness of `evaln` says every test is negative. Hence W(E)=N, and the observer contract at infinity forces q(E)=v, a contradiction. So q(E) returns v. Completeness of `evaln` supplies a bound at which v appears; let B be the least such bound. By minimality below B and `evaln_mono` above B, W(E) is exactly `[0,B)`. The observer contract now yields `h(B)=some v`.

This is the finite-observation lemma required for LN, with no appeal to the total-predicate version of Rice. `evaln` bounds all numbers encountered, not elapsed machine steps; only monotonicity, soundness, completeness, and computability are used. The self-referential input `encode E` can be larger than B candidates; the bound theorem merely delays the first successful bound and does not invalidate the initial-segment argument.

Together A and B give the exact graph equation

`h(∞)=some v ↔ ∃n, h(n)=some v`.

## Uniform extension program

For a source tracker p and context realizer r, define a partial recursive search S(p,r,e). Dovetail over natural tuples (n,s,t), using total bounded tests:

- n=0 is accessible without evaluating e;
- for n>0, accessibility requires `evaln s (ofNat Code e) (n-1)` to be some value;
- `evaln t Q(p,r) C(n)` must return some v, where Q(p,r) is a computably generated code for `q(p,r,·)`.

Return v from the first successful tuple. Implement the tuple scan with `Partrec.rfindOpt` and primitive-recursive decoding. Do not scan n by sequentially waiting for each computation. A successful tuple search gives

`v ∈ S(p,r,e) ↔ ∃n, accessible(e,n) ∧ f(γ,n)=some v`

on valid r,e. For the reverse implication, the witness tuple exists by `evaln_complete`; whichever earlier successful tuple the scan selects has the same value by Lemma A, comparing its n with the witness's n. This compatibility step is required to prove the equation.

For a finite cut of length N, accessible n are exactly n≤N. Lemma A and the witness n=N give S=f(γ,N), including N=0. For a full cut, every n is accessible, so S returns precisely a value occurring at some finite n. Such a value is unique by Lemma A.

Define the underlying extension at infinity to be that unique value when it exists, and none otherwise. Classical existence/choice can define this carrier function, but the tracker is independently explicit: emit the code for the zero-input program running S(p,r,e). Code generation is total and computable in p,r,e by s-m-n/currying. It returns a valid LN realizer even when the embedded search diverges. Running the search before returning its code would fail to track bottom and must be avoided.

This supplies an extension for every Γ using one tracker accepting the pair (r,e). Its semantic value is independent of the chosen realizer r because the graph equation is stated in terms of f(γ,n). For any competing tracked extension, Lemmas A and B force the same graph at infinity, while restriction forces equality on finite cuts. Apply `Hom.ext` for uniqueness. No global inhabitance of Γ is assumed: use `Γ.inhabited γ` only inside the pointwise uniqueness proof.

## N and exponential restriction

For f:Γ×I→N, compose with the lift unit and apply Lemma A starting at n=0. Each fiber is constant. Extend by `H(γ,t)=f(γ,0)`, tracked by evaluating p on `pair r C(0)` and ignoring the cut realizer. Any competing extension is constant on each fiber, including infinity, by Lemma A for finite-to-full cuts. This proves all-context N completeness without needing Lemma B.

For LN, the construction above proves all-context restriction bijectivity. Once genuine function assemblies and curry/uncurry exist, the exponential restriction iso follows categorically: take Γ=X^I, extend the evaluation arrow Γ×I→X to Γ×F→X, and transpose to obtain the inverse. The two inverse equations follow from extension and uniqueness (or the all-context/Yoneda argument). This uses an admitted arrow as inverse, not a separately chosen family of underlying extensions.

A stronger useful implementation lemma is that p↦the extension-tracker code is computable. The algorithm above has this form: compile a fixed universal observer/search template and curry its p,r,e parameters. `exists_code` may select the code of that fixed template once; it must not select a new opaque code noncomputably for each p. For function-assembly realizers, p is the supplied numeric tracker, so correctness is conditional on its tracking contract and code generation must work for every p without testing validity. The self-reference witnesses from A/B occur only in proofs; their choice does not enter the extension algorithm.

## Mathlib inventory and implementation order

Pinned Mathlib revision: `56a005855ea17e0b0958f73ec801ae140b0a1679`.

- [`Computability/PartrecCode.lean`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/PartrecCode.lean): `fixed_point₂` at line1040 has the needed self-referential partial-recursive function form. `evaln_mono`609, `evaln_sound`650, `evaln_complete`703, and `primrec_evaln`939 supply Lemma B and search. `eval_part`1012 gives universal evaluation; `exists_code`531 and `primrec₂_curry`/`smn` support the fixed-template compiler. These signatures were inspected in the accepted checkout.
- [`Computability/Partrec.lean`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/Partrec.lean): composition/bind, divergent partial function, conditional recursive programs, and `rfindOpt` supply program closure.
- [`Computability/Halting.lean`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/Halting.lean): `ComputablePred.rice` concerns total computable semantic predicates. No use of it or an assumed Rice–Shapiro theorem is needed for these proposed proofs.

Suggested implementation order: observer flattening; canonical cuts; Lemma A; Lemma B; tuple search graph and computable compiler; all-context N/LN completeness; function assemblies and exponential equivalence (function assemblies can be developed earlier independently). Each should have statement review and checked concrete specializations. Useful cases are a constant defined map, constant bottom, and the threshold map that stays bottom below a chosen finite length and returns a fixed value from that length onward. The last checks the accessibility off-by-one and extension at infinity.

## Remaining scope and risks

No unresolved mathematical contradiction was found in this derivation. Its status is an author-checked proof plan, not kernel validation. The two self-reference programs, the exact search graph, and the computable compiler are still substantive formal work. Preserve the all-realizer contracts and never treat bounded simulation as a decision procedure for divergence. P1 saturation is compatible with these arguments but does not replace them.

The specialized route is now [implemented in P4](internal-complete-certificate-family.md),
along with exponential/retract closure, uniform bound filtering, the fixed
subassemblies and certificate comparison. P3 has separate checked initiality
and finality proofs. These constructions establish neither every slice's
completeness nor general complete-implies-well-complete, and they do not complete
#371. P5 still owns the concrete state algebra and selected client comparison.
