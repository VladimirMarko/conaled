# ADR 0006 — Reified typed stack code with an explicit tail contract

**Status:** Accepted.

## Context

The stack-machine calculation specifies a program as acting on the top value
and preserving an arbitrary tail. Rank-polymorphic Haskell code motivates a
parametricity argument; Lean's type system alone is not that argument.

## Decision

Represent instructions and sequences with both accumulator and stack-effect
indices. `PUSH` and `POP` move product components between accumulator and
stack. Compile pairing through duplication and sequentialized product
operations, with right-to-left evaluation as in the source calculation.

A `StackMachine.Certified` arrow carries reified code and a proof for **every**
tail: executing the code yields `(spec x, tail)`. Its operations construct
code and proofs together. Instantiate the existing first-order compiler and
prove `compile_correct` for all terms, contexts, environments, and tails.
`compileSquare` exposes the corresponding square that forgets the stack tail;
the stronger tail-preservation theorem remains separately available.

## Alternatives

* Wrap an arbitrary host function in a single opaque instruction: would prove
  a specification without calculating a useful stack implementation.
* Prove only an empty-tail example: would not establish compositional stack
  discipline when one subprogram saves values across another.
* Claim full closure conversion from the draft: its closed-category and
  branching sections are incomplete; the implemented instruction language is
  the completed first-order fragment.

## Consequences

Generated code can be inspected and interpreted without its semantic
function. There is no host-language reflection, parser, assembler, register
allocator, or machine-code emission. The typed sequence prevents stack
underflow and mismatched stack effects. `run_append`, `push_pop`, and
`swap_swap` justify composition and representative local peephole rewrites.

## Sources

* Elliott, [Calculating compilers categorically](https://conal.net/papers/calculating-compilers-categorically/ccc.pdf), July 2018 draft, §§1–2 and Appendix A.
* Elliott, [Compiling gracefully](https://raw.githubusercontent.com/conal/talk-2020-calculating-compilers-categorically/master/compiling-gracefully.lhs), 2020 talk, explicit stack operations and programs.
