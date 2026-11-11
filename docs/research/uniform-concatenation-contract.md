# Native uniform-concatenation consumer contract

Frozen for #468 before theorem development, at accepted f69f87a4.

Input is a finite ordered list of blocks of arbitrary element type. Right and
left append association must both produce the ordinary flattened list. A full
right fold of that list supplies the independent consumer meaning, for arbitrary
combining function, seed and nonnegative declared combining price c. The left
producer may also start with an arbitrary accumulator; its prefix-copy work
must retain that accumulator's length.

Existing dispatch/copy prices are one each. An append of a left list of length
k costs 2*k+1. Each block traversal adds one; the final outer test adds one.
The consumer costs (1+c)*N+1 for N flattened elements, added to the producer.
For m equal-length n blocks, right producer work is 2*m*n+2*m+1. Left producer
work plus m*n is m*m*n+2*m+1; an initial accumulator of length k adds 2*m*k.
These equations describe executions; they must not replace them.

The full pipelines therefore cost (3+c)*m*n+2*m+2 and
(m*m+c*m)*n+2*m+2. Both parameter bounds must have constants independent of m
and n, with explicit nondegenerate domains. Existing fold/concat fusion should
be consumed in one comparison without redoing its proof.

The order-sensitive case [[1,2],[3,4]] folded by cons must produce [1,2,3,4].
At c=1, right producer work is 13 and left work is 9; the full consumer adds 9,
so pipeline bills are 22 and 18. A general theorem connection is missing even
though these finite reductions can already be computed. Three blocks of size
two tie at producer work 19. Zero blocks cost one; m empty blocks cost 2*m+1.
A single left block costs three even for unbounded payload size, but its full
fold consumer must still pay for all payload elements.

Nonuniform length patterns [1,3] and [3,1] have equal count/mass but left bills
7 and 11. They must remain a counterexample to discarding the uniform premise
or the ordered prefix-length observation. No strict finite improvement or
physical runtime claim follows from asymptotic bounds.

This task retains useful source mathematics and its corrected boundary cases.
The source is evidence rather than authority. Full printed-book evidence and
licensing remain with #149; other R1 and #459 families remain unfinished.
