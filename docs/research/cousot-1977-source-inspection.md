# Cousot and Cousot 1977: source inspection

This note records a bounded inspection of Patrick Cousot and Radhia Cousot,
[*Abstract Interpretation: A Unified Lattice Model for Static Analysis of
Programs by Construction or Approximation of Fixpoints*][paper], POPL 1977,
pp. 238–252. It supplies primary-source evidence for the abstract-interpretation
entry and experiment D5 in [the external comparison](external-language-comparison.md).
Page references below use the printed pagination. The distributed PDF has a
cover sheet, so printed p. 238 is PDF page 2.

A separate [corrected transcription](../references/cousot-1977/README.md) now
preserves §§5–9 and Appendix 12, with the original scan, diagram crops and
explicit uncertainty notes. This inspection note remains a mathematical reading.

## Reading method and limits

Inspected 2026-11-04. The 16-page source PDF has SHA-256
`5d2956eed13b2d40f6e15c2087fb870c3dea54a332fe46ee07cea608ca417238`.

The supplied scan was rendered as page images. OCR served only to locate
passages; the retained formulas, inequality directions, hypotheses and example
values below were checked against those images. Inspection covered §§5–9,
especially pp. 241–248, and the relevant appendix statements and proofs on
pp. 251–252. This is a reading of selected arguments, not a complete proof audit,
verified transcription or Lean formalization.

The scan needs visual checking because overbars distinguish abstract from
concrete objects, tildes lift operations to vectors, and faint inequality signs
carry the soundness direction. The widening symbol resembles a join in OCR;
the interval example uses an empty interval notation that OCR can lose.
Two-column text and diagrams also defeat a simple linear reading. In particular,
the p. 242 diagram depicts an inequality between outputs, not an equality of
the two computation paths. No OCR text or reconstructed diagram is treated as
an authoritative replacement for the scan. [Source: pp. 242, 246–247.][paper]

## Abstraction assumptions and fixed-point soundness

Section 5 uses a complete context lattice and an order-preserving interpretation
of primitive instructions. These induce an order-preserving functional on
context vectors, with program properties obtained from solutions of its
fixed-point equations. Section 5.2 separates the order, forward/backward
equations and choice of extreme solution; these choices should not be collapsed
into a universal forward least-fixed-point reading. [Source: p. 241.][paper]

For clarity, write `C` for the concrete lattice, `A` for the abstract lattice,
`F` and `F#` for their vector functionals, and use `alpha` and `gamma` also for
their pointwise lifts. This is normalized notation, not a transcription.
Section 6 requires:

- Monotone maps `alpha : C → A` and `gamma : A → C`.
- `alpha(gamma(a)) = a` for every abstract element.
- `c ≤ gamma(alpha(c))` for every concrete element.
- Local transfer soundness, equivalently expressed as
  `alpha(F(c)) ≤ F#(alpha(c))` or `F(gamma(a)) ≤ gamma(F#(a))`
  after lifting the primitive-instruction conditions to vectors.

The equality on abstract elements matters: the paper assumes a retraction,
stronger than the two inequalities of a general Galois connection. An
implementation following this statement must supply that hypothesis or prove
a suitably generalized theorem. Appendix L2 proves the two transfer conditions
equivalent under the stated hypotheses. Its first direction substitutes
`gamma(a)`, uses the retraction and monotonicity of `gamma`, then concrete
extensivity. The reverse direction substitutes `alpha(c)` and uses monotonicity
of `F` and `alpha` with the same identities. These steps were read in the scan.
[Source: §6.1–6.5, p. 242; H1–H3 and L2, p. 251.][paper]

The appendix gives soundness for both greatest and least fixed points. In the
normalized notation, the least-fixed-point conclusion is
`alpha(lfp F) ≤ lfp F#` and `lfp F ≤ gamma(lfp F#)`.
The greatest-fixed-point conclusion has the corresponding inequalities.
T1's displayed proof uses the greatest-fixed-point induction principle L3,
then monotonicity of `gamma` and extensivity; T2 is obtained there by duality.
The existence and induction results are attributed to earlier fixed-point
theory, not reproved in full. Neither conclusion asserts equality or reflection
of arbitrary abstract facts back to exact concrete behavior.
[Source: L1/L3, p. 251; T1/T2, p. 252.][paper]

Section 8 separates existence from computation. Directed-supremum continuity
supports the Kleene least-fixed-point limit; finite termination needs a further
reason, such as a finite ascending chain. Monotonicity alone does not justify
terminating iteration at the exact least fixed point. [Source: §8.1–8.2,
p. 244; H4/L4, p. 252.][paper]

## Widening, termination and precision

Section 9.1.1 supplies an increasing approximation procedure. While its current
value `S` fails `F#(S) ≤ S`, its next value must dominate both `S` and `F#(S)`;
a separate hypothesis excludes an infinite strictly increasing generated
sequence. The displayed proof establishes strict progress until stabilization.
At stabilization, `F#(S) ≤ S`; the least-fixed-point characterization then yields
`lfp F# ≤ S`. Soundness follows through the earlier abstraction result. Thus a
finite stopping result can bound the exact solution without being that solution.
[Source: p. 245.][paper]

Section 9.1.3 constructs this procedure using widening. The operator must
upper-bound both inputs and satisfy its stated sequence-termination condition.
Widening is placed on arcs meeting every dependency cycle. The proof uses the
finite arc set, coverage of cycles, and widening's termination property to
exclude endless strict growth; its other part establishes domination of the
ordinary transfer. An upper-bound operation alone does not supply this argument.
[Source: p. 246.][paper]

The interval example starts with `x := 1`, tests `x ≤ 100`, and increments on
the true branch. Widening sends the growing upper endpoint to infinity; the
reported exit approximation is `[101, +∞]`. The paper explicitly identifies
the information loss and observes that tests filter intervals. This supplies
a concrete sound-but-imprecise case, without importing a claim of exact
evaluation. Section 9.3 then discusses decreasing refinement: its proof keeps
iterates above the least fixed point, with separate conditions ensuring finite
termination. It does not promise that narrowing recovers the least fixed point
in general. [Source: §§9.2–9.3.2, pp. 247–248.][paper]

## Consequence for experiment D5

The following is a proposed acceptance refinement, not a result of this
repository. Compare the routes on the same ordered domains and transfer
functional. State whether the chosen abstraction satisfies the paper's
retraction assumption. Prove local soundness and its fixed-point consequence
separately from the termination of an approximation procedure. Include a
sound imprecise result, and distinguish the inequalities that establish its
safety from any equality asserting precision. If widening is used, retain its
termination obligation and cycle-placement condition rather than treating it
as an arbitrary join.

This paper supplies evidence for that approximation test. It does not establish
the separate probability-mass and graded-composition contracts in D5, nor any
measured author-effort advantage for a Lean interface. The abstract-interpretation
entry can now cite selected proof inspection; broader claims about the whole
paper, all its diagrams or implementation adequacy remain outside this note.

[paper]: https://www.di.ens.fr/~cousot/COUSOTpapers/publications.www/CousotCousot-POPL-77-ACM-p238--252-1977.pdf
