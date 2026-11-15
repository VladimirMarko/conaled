# Chapter 1 research inventory

Source: *Functional Data Structures and Algorithms: A Proof Assistant Approach*,
version of July 27, 2026, Chapter 1, printed pages 1–10. Edition, URLs, digest,
and exact source hyperlinks are recorded in `source-inventory.json`.

This inventory distinguishes mathematical obligations from language conventions
and informal implementation discussion. It is not a claim of completed coverage.

## 1.1 Programs

Map Isabelle's terminating algebraic datatypes, recursive functions, pattern
matching, `let`, `if`, and `case` to Lean. Lean's own total-definition checking
should be used; no second programming language needs to be invented solely to
reproduce the exposition. The chapter deliberately does not formalize compiler
or programming-language semantics.

## 1.2 Types

Record the correspondence for Bool, Nat, Int, Real, sets, lists, options, pairs,
Unit, function types, and function update. A small checked compatibility surface
can expose the equations actually used later. Reuse the established libraries
instead of duplicating their foundations.

The pattern-matching examples include the recurrence `fib (n+2) = fib (n+1) +
fib n` and an alias-pattern example. These illustrate syntax, not newly
specified algorithms (in particular the Fibonacci base cases are not given).
Do not silently invent such a specification and call it a book requirement.

The numeric-coercion discussion distinguishes additive natural-to-real coercion
from truncated natural subtraction. Document the mismatch and retain explicit
side conditions where subtraction is transported. Multiset operations introduced
are empty, membership, singleton insertion, sum, cardinality, list conversion,
underlying set, map, filter, and value sum.

## 1.3 Notation

Record correspondence of implication, list length, multiplication/exponentiation,
successor notation, and set comprehension. The book smooths over differences
between its mathematical typography and Isabelle syntax.

## 1.4 Proofs

The worked theorem is associativity of list append, proved structurally. Its
definition has the usual two nil/cons equations. Reuse Lean's append and prove
or explicitly reference the kernel-checked theorem as the coverage witness.

### 1.4.1 Computation induction

Euclid's example is `gcd m n = if n = 0 then m else gcd n (m % n)`.
The exact stated induction principle is:

```text
(forall m n, (n != 0 -> P n (m % n)) -> P m n) -> forall m n, P m n.
```

Its proof must rely on the strict decrease of the second argument in the
recursive branch. The general terminating-function induction scheme is explained
metamathematically, including branch conditions. A Lean well-founded recursion
explanation plus the concrete Euclid principle witnesses that discussion.

## 1.5 Running time

The chapter counts non-primitive function calls, not machine instructions or Lean
runtime. The recursive-equation translation adds one for entering a recursive
user function; primitives, constructors, and variable lookups cost zero. Costs
of nested argument expressions are added. `if` and `case` count the discriminator
and only the selected branch; `let` counts the bound expression and its body.
Nonrecursive functions can be inlined without an extra one. Higher-order cases
are referred to Appendix B.1.

The source explicitly says the translations E and T are not functions in the
logic. A reusable costed-computation interface may formalize their algebra, but
must not be presented as an automatic source-to-cost compiler without a proof of
that stronger claim. No end-to-end compiler/hardware cost soundness is offered
by the book, and the Lean adaptation should retain that boundary.

Required concrete definitions and results:

1. `appendTime [] ys = 1`.
2. `appendTime (x :: xs) ys = appendTime xs ys + 1`.
3. `appendTime xs ys = xs.length + 1`.
4. Naive `rev [] = []`; `rev (x :: xs) = rev xs ++ [x]` (Appendix A).
5. `reverseTime [] = 1`.
6. `reverseTime (x :: xs) = reverseTime xs + appendTime (rev xs) [x] + 1`.
7. `reverseTime xs <= (xs.length + 1)^2`.
8. The unnumbered exercise asking for the exact formula has solution
   `reverseTime xs = (xs.length + 1) * (xs.length + 2) / 2`; use natural division
   or the equivalent doubled identity and prove divisibility/parity if needed.
9. `itrev [] ys = ys`; `itrev (x :: xs) ys = itrev xs (x :: ys)`.
10. `itrev xs ys = rev xs ++ ys`.
11. `rev xs = itrev xs []`.
12. `itrevTime [] ys = 1` and
    `itrevTime (x :: xs) ys = itrevTime xs (x :: ys) + 1`.
13. `itrevTime xs ys = xs.length + 1`.

Append associativity and length/reversal helper lemmas should reuse the standard
library when their statements coincide. The cost recurrence belongs to the
naive reverse even if the standard library's `List.reverse` implementation is
optimized; distinguish extensional result equality from algorithm identity.

### Source irregularity to handle explicitly

The worked translation on printed page 7 seems to insert a final `+1` in a line
labelled T of an append expression even though the same page says constructor
costs are zero. The subsequent displayed append-time equations are unambiguous
and consistent with the entry-call convention, so treat these equations as the
formal target and document any correction if reproducing the metatranslation.

### 1.5.2–1.5.3

These sections discuss a conditional cost model and the preference for explicit
bounds over asymptotic machinery. They contain no additional algorithm theorem
requiring a new proof. They must still be accounted for in the chapter coverage
matrix. Do not elevate the informal RAM/finite-word discussion into an axiom
asserting actual machine running time.

## Source-code provenance

Chapter 1 has no direct Isabelle theory hyperlink. The first such link is the
Chapter 2 `Sorting` theory. The full source-link table is in the JSON inventory.
The Isabelle source mirror is pinned there and its BSD-3-Clause license is
preserved as `ISABELLE-COPYRIGHT`. Later AFP sources require per-entry license
inspection. This directory's full book PDF and extracted text are research
inputs; code deliverables should include provenance and original Lean work.
