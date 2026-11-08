# Classical control, a delivery pole and selected finite search

For [#378](https://github.com/VladimirMarko/conaled/issues/378), the construction
below warrants a bounded implementation of a control machine and its finite
search specialization. A predecessor-closed delivery pole validates implication
and Peirce control. It is nonempty, proper and coherent for an explicitly
restricted proof-like class. A separate invariant proves that the search returns
the first even entry, and a closure-to-frame simulation retains its certificate.
The pole alone admits later even entries. These are paper proofs, with finite
fixture checks, not checked Lean theorems or a full implementation of Krivine's
realizability algebra.

The [earlier proposal](deferred-traditions-reassessment.md) is now resolved at
this scope. Control supplies an operational interpretation of a classical
principle and an alternative implementation of finite search. It adds no
computability to this search problem; a direct recursive search has the same
selected result without the logical interpretation or continuation machinery.
Neither capability needs an adapter to the current engine as an entry condition.

## Source map and independently chosen boundary

Jean-Louis Krivine, [*Realizability algebras: a program to well order R*,
arXiv:1005.2395v4](https://arxiv.org/pdf/1005.2395v4), published version,
retrieved 2026-11-08. The inspected PDF has SHA-256
`84677db217259cdc1a2a84049511fb04ae08b875e235030785060bf4a7940796`.

| Borrowed ingredient | Exact source |
|---|---|
| Application, push, capture, continuation reinstatement and predecessor closure | §1, p. 3 |
| Restricted proof-like syntax | §1, p. 4: closed combinator terms |
| Implication orthogonality and substitution adequacy | §1, p. 7, Theorem 1.3 |
| Continuation lemma and Peirce | §1, p. 8, Lemma 1.5 and Proposition 1.6 |

Our machine uses primitive lambda abstraction instead of the paper's combinator
translation. The proof-like class is correspondingly closed lambda/application/
`cc` terms. We rederive the needed fragment below; we do not claim to replay the
paper's full algebra, quantifiers or arithmetic storage theorems. Output,
finite-list scanning, certificate decoding, the chosen pole and the representation
comparison are this report's construction. The source's full model hypotheses
are not assumptions of this bounded propositional construction.

## Independent result and certificate meaning

Fix a finite list `L : List Nat`. Positions start at zero. An output record is
raw data, independently validated by the following predicates:

```text
Found(j,n,h,O):
  j < length L; L[j] = n; n = 2*h;
  length O = j; for each i < j, L[i] = 2*O[i] + 1.
None(O):
  length O = length L; for each i < length L, L[i] = 2*O[i] + 1.
```

Call this predicate `First(L,z)`. Thus `O` is a list of oddness witnesses for
all earlier positions, not merely a claim that some earlier entries are odd.
The independent observation is the output tag, position, numeral, evenness
witness and ordered oddness witnesses. For natural numbers these witnesses are
unique when valid. If `Found(j,...)` and `Found(k,...)` both satisfy `First`,
then `j<k` contradicts oddness of `L[j]` in the second certificate, and similarly
for `k<j`. Thus the selected record is unique. `None` excludes every `Found`.

The weaker predicate `Weak(L,Found(j,n,h,O))` checks only the first three
conditions. It ignores `O`; it is false for `None` and for internal values.
For `L0=[1,2,4]`, both `Found(1,2,1,[0])` and `Found(2,4,2,[])` satisfy `Weak`.
Only the first satisfies `First`. No pole or program defines these predicates.

## Machine, callbacks and proof-like terms

Core terms are variables, lambda abstraction, application and `cc`. Runtime
terms also include saved continuations `k_π`, `ret(v)`, `walk(k,L,j,O)`,
`test(k,L,j,O)`, `last(L,j,c,O)` and `stuck`. Values comprise the output records above and
internal `Odd(h)`. Terms in processes are closed; substitution avoids capture
and substitutes inside the continuation parameter of `walk` and `test`.

A stack has bottom `halt` or `out(L)` and finite cells of two kinds:
`arg(u,π)` and `cb(f,π)`. The latter stores a function closure. The only
permitted callback family is

```text
f[k,L,j,O](Odd(h)) = walk(k,L,j+1,O ++ [h])
f[k,L,j,O](other)  = stuck.
```

This is a function with captured environment `(k,L,j,O)`. Its return value is
a term; the stack tail is retained by the callback application rule. Core
terms and stacks can contain these closed runtime objects. Captured stacks
are immutable; reinstating one replaces the current stack in full. The machine
has states `t ⋆ π` and terminal `Deliver(L,v)`. Its reduction relation consists of the following rules
and the three last-policy rules specified in the negative control below:

```text
(t u) ⋆ π                     → t ⋆ arg(u,π)
(λx.t) ⋆ arg(u,π)             → t[u/x] ⋆ π
cc ⋆ arg(t,π)                 → t ⋆ arg(k_π,π)
k_π ⋆ arg(u,ρ)                → u ⋆ π
ret(v) ⋆ cb(f,π)              → f(v) ⋆ π
ret(v) ⋆ out(L)               → Deliver(L,v)
walk(k,L,j,O) ⋆ π             → test(k,L,j,O) ⋆ cb(f[k,L,j,O],π)   if j < |L|
walk(k,L,|L|,O) ⋆ π           → ret(None(O)) ⋆ π
test(k,L,j,O) ⋆ π             → ret(Odd(h)) ⋆ π                 if L[j]=2h+1
test(k,L,j,O) ⋆ π             → k ⋆ arg(ret(Found(j,L[j],h,O)),π) if L[j]=2h.
```

The last two rules require `j<|L|`. Natural parity has exactly one applicable
case. All other states are stuck, and delivered states have no successors.
There is no implicit output validation or arbitrary external callback.
At an even entry, the saved continuation discards the callback which would
otherwise process the rest of the list. That discarded remainder is part of
the representation comparison below.

The admitted proof-like terms `PL` are exactly closed terms generated by
variables, lambda, application and `cc`, with no literal saved continuations,
output, scanner or callback instructions. Runtime continuations may arise by
reduction. This restriction is part of the logical consistency claim. Search
programs use the extended runtime and are not in `PL`.

## Constructed pole, properness and coherence

Freeze `L0=[1,2,4]`. Let `Pgood` be the states reducing in finitely many steps
to `Deliver(L0,z)` with `Weak(L0,z)`. It includes terminal successes themselves.
This definition uses the independent weak result predicate; it does not assume
membership of the search program. If `s→s'` and `s'∈Pgood`, concatenate that
step with the finite successful reduction, proving predecessor closure.

The state `ret(Found(1,2,1,[0])) ⋆ out(L0)` reduces in one step to an accepted
terminal, so the pole is nonempty. The terminal
`Deliver(L0,Found(0,1,0,[]))` fails `1=2*0` and has no successor, so is outside
the pole. The pole is therefore proper. A universal pole also satisfies
predecessor closure, but includes this invalid terminal and cannot express the
requested output discipline; reject it for this experiment.

Properness alone would not prove coherence. Here coherence means
`∀ t∈PL, ∃π, t⋆π ∉ Pgood`. The common witness stack is `halt`.
Define a runtime state to be output-free when it is built from pure core terms,
`halt`, argument cells and saved continuations recursively containing only such
objects. A source `t∈PL` on `halt` is output-free. Application and beta only
rearrange or substitute output-free objects. Capture saves an output-free
stack; reinstatement restores one. No other rule applies to these states.
Induction on the length of a reduction proves that no such state reaches a
`Deliver` state, whether or not its execution terminates. Hence every `t∈PL`
has the stated rejecting stack. With falsity interpreted by all stacks, no
admitted proof-like term realizes falsity. This establishes consistency only
for the explicitly given proof-like fragment and typing rules below.

Search membership is a different theorem. Admitting arbitrary output primitives
as proof-like axioms would invalidate this proof's invariant; no consistency or
extraction claim for that larger proof language is made. Properness and this
restricted coherence do not establish correctness of arithmetic decoding.

## Implicational adequacy, including Peirce

The following argument works for any predecessor-closed pole `P` on this
machine, including `Pgood`. Assign to each propositional atom `A` a set of
stacks `||A||`. Recursively set

```text
|A|       = {t closed | ∀π∈||A||, t⋆π∈P}
||A → B|| = {arg(u,π) | u∈|A| and π∈||B||}.
```

For an arrow, the falsity-set clause uses only smaller formulas; `|A|` is the
orthogonal of the resulting `||A||`. If falsity is used, set `||⊥||` to
all stacks. This is an orthogonality interpretation, not a decoding function
from realizers to arithmetic witnesses.

Use the variable, implication-introduction and application typing rules for
lambda terms, plus `cc : ((A→B)→A)→A` for any formulas `A,B`. First verify this
control rule. Given `π∈||A||`, the term `k_π` belongs to `|A→B|`: for every
`u∈|A|` and `ρ∈||B||`, its process steps to `u⋆π∈P`, so predecessor closure
applies. Now let `f∈|(A→B)→A|`. The process

```text
cc ⋆ arg(f,π) → f ⋆ arg(k_π,π)
```

lies in `P`, since the right side tests `f` against a stack in
`||(A→B)→A||`. This proves Peirce for arbitrary `A,B` and pole, including the
control case needed by adequacy. It does not require `B` to have a realizer.

For a derivation `Γ ⊢ t:C` in these four rules and a closing substitution `σ`
with `σ(x)∈|Γ(x)|`, prove `tσ∈|C|` by induction on the derivation:

- A variable uses the substitution hypothesis.
- For application `s u:B`, the induction hypotheses give `sσ∈|A→B|` and
  `uσ∈|A|`. At any `π∈||B||`, the application step reaches
  `sσ⋆arg(uσ,π)∈P`; predecessor closure gives the result.
- For abstraction `λx.s:A→B`, test any `u∈|A|` and `π∈||B||`. Beta reaches
  `s(σ[x:=u])⋆π`, which lies in `P` by the extended substitution hypothesis.
- For `cc`, use the control calculation just proved.

Thus any closed proof of falsity would yield a term in `PL` realizing falsity,
contradicting coherence for `Pgood`. This is a bounded consistency conclusion.
No runtime `walk` typing axiom occurs in the induction. The search below uses
the same capture/reinstatement rules, but its certificate theorem follows from
a traversal invariant, not from the adequacy theorem or a claimed extraction of
an arithmetic proof.

## Captured search and its complete result

Define the closed runtime program

```text
Search(L) := cc (λk. walk(k,L,0,[])).
```

Run it on `out(L)`. Application, capture and beta take three steps to
`walk(k_out(L),L,0,[]) ⋆ out(L)`. At a scan boundary maintain

```text
0 ≤ j ≤ |L|;
length O = j;
∀i<j, L[i] = 2*O[i]+1;
k = k_out(L); the stack is out(L).
```

At `j<|L|`, the machine pushes a callback for the remaining traversal. If the
entry is odd `2h+1`, `test` returns `Odd(h)`, the callback consumes it, and the
next boundary has `j+1,O++[h]`. Its new oddness equation is exactly the parity
check; prior equations are unchanged. If the entry is even `2h`, `test` passes
`Found(j,L[j],h,O)` to the captured continuation. Reinstatement discards the
pending callback, then output delivers the record. The invariant proves all
conditions of `First`. At `j=|L|`, exhaustion returns `None(O)` and the same
invariant proves its full no-witness certificate.

For `L0`, after the three initialization steps the execution is:

```text
walk(k,L0,0,[]) ⋆ out(L0)
→ test(k,L0,0,[]) ⋆ cb(f[k,L0,0,[]],out(L0))
→ ret(Odd(0)) ⋆ cb(f[k,L0,0,[]],out(L0))
→ walk(k,L0,1,[0]) ⋆ out(L0)
→ test(k,L0,1,[0]) ⋆ cb(f[k,L0,1,[0]],out(L0))
→ k ⋆ arg(ret(Found(1,2,1,[0])),cb(f[k,L0,1,[0]],out(L0)))
→ ret(Found(1,2,1,[0])) ⋆ out(L0)
→ Deliver(L0,Found(1,2,1,[0])).
```

Here `k=k_out(L0)`. The callback that would continue at position 2 is discarded,
so `4` is not visited. The delivered record is `Weak`, proving actual membership
of this program in `Pgood` by this reduction, without assuming it.

Each odd visit uses three steps and decreases `|L|-j` at the next boundary.
An even visit uses four steps including delivery; exhaustion uses two. Therefore
there are `3j+7` steps when the first even entry is at position `j`, and `3|L|+5`
steps for all-odd input. These counts treat arithmetic and list operations as
single primitive actions and are not wall-clock or allocation bounds. They
prove termination only for this finite-input program, not normalization of the
untyped control machine.

For `[1,3,5]`, the returned record is `None([0,1,2])`; for `[]`, `None([])`.
These are correct full results but lie outside the fixed `Pgood`, which is a
successful-witness pole for `L0`. One may define a pole for each input with the
same weak predicate; it is empty on all-odd lists. That does not undermine the
separate total-search theorem, and no nonemptiness claim is made for those poles.

## Closure continuation to explicit frame simulation

Replace source callback functions with a target frame datatype:

```text
FrameStack ::= halt | out(L) | arg(u,π) | Next(k,L,j,O,π).
```

The target retains the core application/beta/control rules and `test` rules.
Its `walk` rule pushes `Next(k,L,j,O,π)`. Its return rule is

```text
ret(Odd(h)) ⋆ Next(k,L,j,O,π) → walk(k,L,j+1,O++[h]) ⋆ π.
```

Other values at `Next` go to `stuck⋆π`, matching the source callback's second
case. Source callbacks are actual functions accepting a value; target frames
are tagged data interpreted by a dispatcher. This removes function-valued
continuations from the scanner. It is not a relabelling of the source runtime
constructor: the correspondence uses the callback's pointwise behavior.

Define a representation relation `R` by structural clauses: identical natural
and certificate data; related core term constructors; related stack bottoms and
argument cells; `k_π R k_π'` whenever their saved stacks are related; and

```text
cb(f[k,L,j,O],π) R Next(k',L,j,O,π')  if k R k' and π R π'.
```

Only the generated callback family is admitted. An arbitrary host function
requires another code tag and a new pointwise equation. Relate `walk`/`test`
parameters componentwise and deliveries by identical `(L,v)`. For substitution,
structural induction on a core term gives `tσ R t'σ'` whenever the term and
substitution components are related; runtime payloads remain closed data.

Whenever a member of a related pair takes a step in this fragment, the other
has a matching step to a related state:

| Source step | Matching target step and obligation |
|---|---|
| Application/beta | Corresponding term/argument cells; use substitution lemma |
| Capture | Save related whole stacks, then push related saved-continuation terms |
| Reinstatement | Restore the related saved stacks and discard the current stacks on both sides |
| Walk, nonempty | Function closure becomes `Next` with the same captured environment and tail |
| Test, odd/even | Identical parity branch and identical raw certificate data |
| Callback return | Evaluate the displayed function equation; target dispatcher builds the related next walk |
| Exhaustion/output | Identical `None` witnesses or identical terminal output |

This proves a step-for-step simulation, and also its reverse on the generated
source/target states by the same cases. Terminal observations agree. In particular,
at the even branch the source pending function and target `Next` frame both
represent the unvisited suffix starting at `j+1`; capture reinstates their
saved `out(L)` stack, discarding that remainder. The `R` clause includes `j,O,L`
and the tail, so preserving only the selected numeral could not substitute for
this relation. Full certificate meaning survives because the terminal data and
independent `First` predicate are unchanged. The result applies to the specified
callback family, not arbitrary higher-order continuation compilation.

## Weak pole and changed-policy negative controls

The terminal `Deliver(L0,Found(2,4,2,[]))` belongs to `Pgood` by zero steps.
It fails `First` because its prefix certificate has the wrong length; no valid
prefix certificate can exist because `L0[1]=2` is even. Thus even a nonempty,
proper, coherent pole does not imply first-result selection.

For a policy change, use the additional runtime instruction `last(L,j,c,O)`,
where `c` is either absent or an even candidate `(j,n,h)`. Its rules are:

```text
last(L,j,c,O) ⋆ π → last(L,j+1,c,O++[h]) ⋆ π      if j<|L| and L[j]=2h+1
last(L,j,c,O) ⋆ π → last(L,j+1,(j,L[j],h),O) ⋆ π if j<|L| and L[j]=2h
last(L,|L|,c,O) ⋆ π → ret(finish(c,O)) ⋆ π
finish(absent,O)=None(O); finish((j,n,h),O)=Found(j,n,h,[]).
```

These rules complete the frozen machine; `last` is excluded from `PL` and from
the first-search representation simulation. Its initial state is
`last(L,0,absent,[]) ⋆ out(L)`. The index increases once per entry, so it
terminates. On `L0`, its successive candidates are absent, `(1,2,1)` and
`(2,4,2)`, followed by delivery of `Found(2,4,2,[])`. Its execution is in `Pgood`
but disagrees with the first policy's position, numeral and certificate meaning.
If no candidate exists, every entry was odd and `None(O)` has a valid full
certificate. The extended rules do not affect the coherence proof because an
output-free process cannot create `last`.

The representation simulation does not apply to this policy change: replacing
an even-branch escape by a continuing scan changes the transition rule and
violates its matching-step case. Changing continuation representation and
changing selection policy are separate operations with different contracts.

## Finite validation and proof boundary

An executable fixture model evaluated both the function-callback machine and
explicit-frame machine on every list of length 0 through 5 with entries 0
through 4: `1+5+25+125+625+3125=3906` inputs. It checked related states at each
step, equality with direct search, full certificates and the stated step counts.
The explicit `[1,2,4]`, all-odd and empty cases, last-policy rejection, invalid
terminal and callback equations also passed. The orchestration evidence retains
the script and output. These finite checks do not certify general substitution,
adequacy, coherence or simulation; those are the paper arguments above, awaiting
formalization. No Lean build or proof audit is claimed for this report.

## Direct search comparison and next implementation

A direct recursion checks the head, returns it if even, otherwise recursively
searches the tail and shifts a found index by one while prepending the head's
oddness witness. Its base case returns `None([])`. Induction on the list proves
`First`; the uniqueness proof above equates its record with `Search(L)`.
Both inspect exactly the prefix through the first even entry, or the whole
list if none exists. Neither needs excluded middle for arbitrary propositions:
parity is decidable. The direct route needs neither a pole nor a saved continuation.

| Capability/obligation | Direct recursion | Control/pole route |
|---|---|---|
| Full selected finite result | List induction and prefix certificate | Scan invariant, escape correctness, prefix certificate |
| Classical principle as an instruction | Not supplied | Peirce's realizer and implicational adequacy |
| Search termination | Decreasing tail | Decreasing boundary measure plus administrative steps |
| Change continuation representation | No captured continuation to translate | Pointwise closure equation and saved-stack simulation |
| Coherent logical interpretation | Not a claim of the search function | Output-free invariant for the restricted proof-like class |

Control gives a reusable escape implementation and a classical logical
interpretation. The search fixture does not show extra expressiveness, less
author work or better performance. Excluding runtime instructions from the
proof-like class is a deliberate boundary, not a proof that extended-language
arithmetic programs are extracted correctly. A future extraction theorem would
need logical specifications and adequacy cases for those primitives, plus an
observation theorem relating the chosen formula interpretation to `First`.

The local baseline is `be1dfca1f57a950950a4e77d81f9fed5140161ee`.
The [#296 handler study](effectful-witness-interpretation.md) compares state and
exception policies, and the [omitted-traditions record](omitted-semantic-traditions.md)
left a classical pole open. Neither is treated as this construction's checked
implementation. The result contributes independent scope under #290/#196,
coordinated with #235, and requires no change to existing handler contracts.

Create a bounded implementation successor with these acceptance criteria:

1. Define the lambda/control machine, raw result decoder and restricted
   proof-like class. Prove implicational substitution adequacy and Peirce for
   any predecessor-closed pole; do not postulate program membership.
2. Construct `Pgood` for `[1,2,4]`; prove closure, nonemptiness, properness and
   restricted coherence. Check the invalid terminal and universal-pole control.
3. Implement finite search and prove the full `First` invariant, termination
   and equality with direct recursion. Check multiple witnesses, all-odd input,
   empty input and a match at position zero.
4. Define function callbacks and explicit `Next` frames separately. Prove the
   related-state simulation, including substitution, saved stacks, discarded
   suffix and complete output certificate. Restrict callbacks to this family.
5. Check the later-even weak-pole witness and changed last-witness policy.
   Retain the boundary between logical adequacy and runtime correctness.
6. Perform example-driven statement review, integrated build and exhaustive
   proof audit, without new kernel axioms, and independent Standards/Spec review.

No general normalization, full classical arithmetic extraction, arbitrary
callback compiler or migration is a prerequisite. Extending the proof-like
class or changing the observation contract needs a new scoped proof; #235 owns
coordination if such an extension is pursued. #107 stays paused and #108's
held-out theorem stays unselected. The enclosing orchestration owns review and
successor publication; neither is claimed complete by this report.
