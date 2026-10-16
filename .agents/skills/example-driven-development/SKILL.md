---
name: example-driven-development
description: Develop Lean definitions and theorems through checked specializations and applications. Use when adding or changing formal claims, demonstrating how abstract results apply, or reviewing whether a formal statement captures its intended mathematics. Use TDD for executable behavior that needs runtime tests.
---

# Example-driven development

Grow the theory and its checked uses together, one case at a time. A proof
establishes a formal claim under its assumptions; examples and statement review
help check that this is the claim we intended. They do not establish that human
intent has been captured exhaustively.

Read the repository's domain guidance, glossary if present, and relevant ADRs.
Use the existing public interfaces and module layout to choose where cases
belong. In this repository, `Examples` also contains universal cross-application
theorems; its name alone is not a placement rule.

## Vocabulary

- **Specialization:** instantiate a general result at more specific types,
  structures, parameters, or hypotheses. It can remain abstract or noncomputable.
- **Application:** use a result, possibly with other results, to derive a further
  claim.
- **Worked example:** explain a selected case and its expected mathematics, with
  a checked connection to the general result.
- **Statement review:** compare a formal claim and its assumptions with the
  intended mathematics.

## The loop

1. **Choose a case.** State the intended mathematics and select a specialization
   or application that would demonstrate it. Identify the public definitions and
   results it should use, reusing interfaces agreed in the task or architecture.
   Resolve consequential ambiguity with the user; routine case selection needs
   no additional approval. Write the expected conclusion from a worked
   calculation, specification, or independent mathematical account.
2. **Expose the obligation.** Express that conclusion as a Lean proposition.
   Identify what is missing: a definition, a general result, suitable hypotheses,
   or the connection to the case. An unsolved goal in a scratch file can make the
   gap visible; record the relevant failure before proceeding. An unrelated
   syntax or import error is not evidence of a mathematical gap. If existing
   results suffice, use them without manufacturing a failure.
   A case may already be provable by reduction while its connection to the
   intended public theorem is missing. Record that as a missing connection,
   not as evidence that the proposition cannot yet be proved.
3. **Connect the case.** Develop enough of the general theory to discharge the
   obligation through the intended public results. Prove the case's hypotheses
   for its chosen instance. Use intermediate specializations when jumping
   straight to concrete data would hide the mathematics. Inspect the derivation:
   an independent proof of the expected result alone does not exercise the new
   theorem. Automation is welcome when its connection to that theorem is clear.
4. **Review the statement.** Apply the checks below to the changed claims and
   the case. If the case exposes a mistaken statement, correct the theory and
   explain the correction; preserve the independently justified expectation.
   Change that expectation only for a mathematical reason, not to obtain green.
5. **Retain and continue.** Place the checked case in the appropriate module and
   include it in the normal build and proof audit. Remove scratch obligations and
   placeholders from completed work. Choose the next case from what this one
   revealed, rather than writing a batch against an imagined interface.

Green means the case is proved through the public result with its assumptions
established, statement review is complete, and the required checks pass.
`sorry`, `admit`, or a new axiom standing in for the obligation is not green.

Read [worked-example.md](worked-example.md) when first applying this loop or
when the distinction between an expected result and its connection is unclear.

## Statement review

For each new or changed formal claim, compare the intended claim with the actual
statement. Inspect elaborated types or explicit arguments when notation,
inference, coercions, or instances could conceal the difference. Check:

- Quantifier order, types, domains, and the scope of implicit parameters.
- Hypotheses: are they justified in the intended uses, satisfiable, and weaker
  than simply assuming the desired conclusion?
- The conclusion: which equality, relation, direction, or notion of correctness
  is proved? Does it cover the intended inputs and edge cases?
- Definitions used in the statement: do their semantics match the explanation,
  or does the claim merely repeat a definition that could itself be wrong?

Use a meaningful instance to expose vacuity when relevant. A theorem whose
premise cannot hold says nothing about usable inputs. Examples complement the
universal proofs and existing axiom audit; they do not replace either.

## Keep the evidence useful

Choose cases for what they reveal: intended use, a consequential edge case, or
composition with another result. Existing cases can cover helper lemmas; there
is no quota per declaration. For proof-only refactoring, retain existing cases
and check that the public statements and assumptions remain the same.

Consume public definitions and theorem statements so cases survive changes to
proof construction. Avoid inspecting private lemmas, proof syntax, or source
text to establish correctness. A proof by `rfl` can be appropriate; its value
depends on whether the independently stated claim checks the intended meaning.
A claim equating a definition to itself provides no such evidence.

Use executable TDD where runtime behavior needs testing, such as integration
outside the proved model. Documentation or accounting file presence is not a
mathematical case; validate such artifacts directly when the task requires it.

For implementation handoffs and `code-review`, report the intended claims,
retained cases and public results they use, statement-review findings, and
build/audit results, including any checks that could not run. Supply this
through the existing task or review report; no separate accounting file is
required. This evidence supports both the full and lightweight implementation
workflows without replacing their review and correction stages.
