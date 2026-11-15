# Stable address meanings and recursive templates

Local10019, requirements version1. Root implementation on purity-foundation;
fixed enclosing review base b422800fb5b6dc1253823057c0ea71644274d77c.

## Intended contract and design

The immutable semantic world reuses Durability.Heap and Extends. An address
denotes finite source code, an interpreted capture and an optional recursive
group descriptor. Mutable heap writes never change that meaning. Structural
value/environment/optional-value relations preserve constructors and names;
addresses consult the world. They do not assert source typing, purity,
termination, uniqueness of every possible closure interpretation or cache
validity.

The raw third component of a recursive closure is its original creation
template, not an environment of already-closed member values. GroupMembersRep
records those original function closures and delayed-address meanings in
reversed creation order. No requirement says those cells must still be thunks.
The public GroupRep.unroll and bodyEnvironment laws connect actual Rec to the
finite group descriptor; all structural relations survive immutable world
extension. There is no acyclicity premise or eager body-result witness.

## Connected examples and statement review

Examples.SuspensionPureRepresentation connects the public template/unrolling
laws to a mutually dependent function and suspension. It retains the raw
template in the represented recursive function, then uses GroupRep.mono to
transport the same environment across a fresh unrelated world entry. A missing
world entry cannot represent an address. A separate delayed function returns
an ordinary closure capturing the same suspension address; this demonstrates
that cyclic references in source memory do not require cyclic Lean values.

Statement review checked the indexed constructor shapes, reversed-list order,
shadowing-preserving environment relation, actual Core.Env.rec expansion and
optional descriptor distinction. Empty recursive templates can have multiple
closure views; functionality is deliberately not claimed. Distinct allocated
addresses may have equal meanings. Cache-result agreement must later follow
from evaluation uniqueness for a fixed meaning, not injectivity of this world.

## Focused evidence

- r1: exit1, unchanged inputs. The direct mutually recursive proof definitions
  did not satisfy Lean's structural-recursion elaborator, and EnvRep.names had
  an underconstrained List.cons head. Definitions and other proofs elaborated.
- r2: core GREEN in7.4s after using the generated mutual induction principle
  and explicitly binding the name. The concrete absent-address example then
  failed dependent elimination. No public statement or expected result changed.
- r3: complete target GREEN,630jobs, exit0, unchanged input hashes. The absent
  address contradiction is proved for a generic semantic value before its
  concrete instantiation. The connected example compiled in2.3s.

All three JSON/log pairs are preserved in session/validation with stem
suspension-pure-representation-rN. No proof limits or linters were relaxed;
no admissions, axioms or native evaluation shortcuts were added. Focused
evidence does not replace the enclosing exact candidate build/audit/reviews.

## Remaining obligations

Actual creation/closing and cache-cell validity are separate modules under
development. A full finite-run bridge additionally needs hereditary code-domain
preservation, primitive compatibility and occurrence preservation. These
representation results alone do not establish the thesis's no-finite-pure-
self-forcing statement or any once-only execution/resource consequence.
