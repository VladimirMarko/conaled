# Proof-derived requirements and declared theories

For [#286](https://github.com/VladimirMarko/conaled/issues/286), the worked
comparison supports extraction as an authoring aid inside a theory presentation.
It recovers usable sufficient laws from the frozen concrete arguments without
rebuilding their inference trees. Naming those laws, choosing the abstraction
boundary and certifying interpretations remain mathematical work. A declared
theory exposes the same obligations once its author has identified them.
Neither route infers a universal weakest requirement language.

This is a paper derivation, not a Lean importer, an MMT implementation or an
independent author trial. The [fixture](proof-requirement-comparison/fixture.md)
was committed at `782f4bd` before route adaptation. It fixes the source terms,
logic, two intended targets and observations. Only documentation changes here;
existing direct Lean clients and independent denotational contracts remain the
reference for future implementations.

## Source results and what this comparison adds

The primary fulltexts were inspected on 2026-11-04:

- Johnsen–Lüth, [*Theorem Reuse by Proof Term Transformation*](https://ebjohnsen.org/publication/04-tphols/04-tphols.pdf),
  TPHOLs 2004 author PDF, 16 pages, §§2.1–2.4 and §3, printed pp. 2–6.
  Their staged method exposes theorem assumptions, replaces function symbols,
  then abstracts types. Symbol abstraction needs higher-order variables; type
  abstraction needs type variables and exposure of type-specific rules.
  Substitution avoids capture. Their Isabelle implementation checks transformed
  terms by replay. Their discussion of normalization concerns applicability
  conditions of supplied proofs; it is not a universal proposition minimizer.
- Farmer–Guttman–Thayer, [*Little Theories*](https://imps.mcmaster.ca/doc/little-theories.pdf),
  author manuscript dated 15 October 1992, 19 pages, §§1.1–1.2 and §2.
  Theories separate mathematical assumptions; interpretations reuse theorems
  after translated axioms and logic-specific obligations are proved. This
  supplies the organizational comparison, not a theorem that arbitrary equality
  or selected witness observations can be changed freely. We do not adopt
  IMPS's classical logic for the constructive target.
- Rabe–Kohlhase, [*A Scalable Module System*](https://www.kwarc.info/people/frabe/Research/mmt.pdf),
  preprint dated 17 December 2012, 95 pages, §7.2, Definitions 30/32 and
  Theorem 34, printed pp. 60–64. Definition 30 requires equality respecting
  normalization, equivalence/congruence and context conversion, and preservation
  of typing/equality by flat assignments satisfying declaration types and
  definitions, including meta-theories. Definition 32 requires totality of the
  metamorphism and nonfiltering of undefined constants. Defined constants may
  be filtered if normalization expands them. Under a fixed regular foundation,
  Theorem 34 gives composition and, for total morphisms, typing/equality
  preservation. Partial axiom assignments do not certify theorem transport.

The derivations below are new worked instances in the explicitly fixed fragment.
They establish their displayed judgments directly; they do not extend any source
paper's transformation theorem to arbitrary native Lean proofs. No proof-object
identity between original and transformed derivations is asserted.

## Exposing the concrete proof's requirements

Write `m(a,b)` for the abstract binary operation and `u` for its unit candidate.
The dependency ledger is scoped to the opaque lemma boundary fixed in the
fixture. Fully unfolding arithmetic proofs would be a different experiment.

| Artifact | Mathematical leaves | Object-language rules used | Host/metalevel work |
|---|---|---|---|
| Eproof | `ruN`, `raN` | Universal elimination/introduction, equality congruence and transitivity | Typed capture-avoiding replacement, lambda binding |
| Wproof | `ruN` | Universal elimination, symmetry; data-pair introduction and function abstraction | Preserve the data judgment and pair projections |
| Estrong before simplification | `ruN`, `raN`, `em Q` | E rules plus disjunction elimination | Retain both branch binders and the decision proof |
| Ambient unused `em` | None in Eproof/Wproof | None | Availability alone adds no premise |

There are no hidden arithmetic reductions in these proof bodies. The arithmetic
lemmas are leaves whose full universally closed statements become hypotheses.
Equality remains the base logic's equality with the same congruence rules; it
is not replaced by an arbitrary relation.

### Stage 1: turn leaves into parameters

Replace each occurrence of `ruN` by a fresh proof variable r and `raN` by a.
Universal introduction in their statements ensures that `r z`, `r x` and
`a x y z` are well-scoped. Implication introduction gives these actual proof
terms at the concrete type:

```text
EN := λr:(∀t:ℕ. t+0=t). λa:(∀s t v:ℕ. (s+t)+v=s+(t+v)).
        λx y z. trans (cong (λt. (x+y)+t) (r z)) (a x y z)
WN := λr:(∀t:ℕ. t+0=t). λx. (x, sym (r x))
```

The final codomains are respectively E and W from the fixture. Substituting
`ruN` and `raN` beta-reduces to the original bodies. This step provides a
replayable proof, beyond a list of reachable declarations.

### Stages 2 and 3: symbols, then carrier

First replace `+` and `0` everywhere, including in leaf types and intermediate
judgments, by fresh parameters `m:ℕ→ℕ→ℕ` and `u:ℕ`. Then replace the carrier
ℕ by a type parameter A. In this fragment A is schematic, so no object-language
universe axiom is being added. The resulting terms are:

```text
R(A,m,u) := ∀t:A. m(t,u)=t
S(A,m)   := ∀s t v:A. m(m(s,t),v)=m(s,m(t,v))

Eabs := λA m u. λr:R(A,m,u). λa:S(A,m). λx y z.
          trans (cong (λt. m(m(x,y),t)) (r z)) (a x y z)

Wabs := λA m u. λr:R(A,m,u). λx.
          (x, sym (r x))
```

For replay, in context `A,m,u,r,a,x,y,z`:

1. `r z : m(z,u)=z` by universal elimination.
2. Congruence under `λt. m(m(x,y),t)` gives
   `m(m(x,y),m(z,u))=m(m(x,y),z)`.
3. `a x y z : m(m(x,y),z)=m(x,m(y,z))`.
4. Transitivity composes exactly the matching middle term. Discharge x,y,z,
   then a,r and the schematic operation/type parameters.

For W, `r x : m(x,u)=x`; symmetry gives `x=m(x,u)`.
Pair introduction gives `(x,sym(r x)):Σy:A. y=m(x,u)`.
Its first projection reduces to x by the specified beta equation. Discharging
x and r gives Wabs. The existential shadow follows by existential introduction,
but that logical judgment alone does not supply the pair observation.

The declarations must be ordered `A`, then `m,u`, then `r,a`, then the client
variables. R and S are abbreviations, not new axioms. Renaming a bound `t`
before a replacement avoids capture; the replacement parameters must be fresh
and independent of the local x,y,z. Bound proof variables in the strong proof
are local to their branches. This is simultaneous well-typed replacement of
whole terms and their types, not textual renaming.

Natural-number induction is not a rule in either body. If `raN` were unfolded,
its recursor, constructors and induction motive would have to be abstracted or
retained as explicit obligations before replacing ℕ. An arbitrary A does not
inherit induction. Nor does this calculation abstract dependent elimination,
quotient recursors, implicit coercions or universe constraints in Lean.
The data-pair rule is retained unchanged; its dependent family is explicitly
`λy. y=m(x,u)`. A different interpretation of dependent substitution requires
its own coherence proof, not an extra item in this leaf ledger.

## The same statement with a stronger proof

Unmodified extraction of Estrong gives the term Eabs wrapped in
`λd:Q∨¬Q. case d of inl q => e | inr n => e`, where e is its displayed
equality body. It therefore requires R, S and `Q∨¬Q`. Abstracting the entire
ambient `em` theorem instead gives the stronger sufficient schema
`∀Q. Q∨¬Q`; exposing its used instance first gives the narrower requirement.
The choice of leaf boundary changes sufficient requirements.

For the fixed intuitionistic target logic, an arbitrary proposition Q has no
such supplied proof. A two-world Kripke frame `w0 ≤ w1` with Q forced only at
w1 shows the missing obligation: w0 forces neither Q nor ¬Q, so does not force
their disjunction. Interpret the algebra at both worlds as the same L or B,
with identity transition; the algebra laws remain valid. Thus the algebra
assignments do not discharge this logical requirement. This is a failure of
the unsimplified proof's reuse in that logic, not a claim that boolean data
cannot be decidable.

A justified simplification is available here: both branch results are the same
well-typed term e, whose context excludes d,q,n. Replay e directly in the
smaller context. Weakening would insert it in either old branch, establishing
why deleting the whole case yields a proof of the same conclusion. This is a
change of proof; no definitional equality rule reducing a case on an unknown
decision is assumed. The simplified proof requires only R and S. W never used
the ambient principle. This separates unused availability, actual dependence,
and dispensability for the proposition. No general proof minimization follows.

## Discharging the two frozen target interpretations

Both routes use precisely these assignments and law proofs. Construction of
model laws may use the model's native induction or finite case analysis without
adding those principles to the client argument.

For L, define concatenation by `[]++v=v` and
`(h::t)++v=h::(t++v)`. Right unit rL is proved by induction on t:
`[]++[]=[]`; from `t++[]=t`, congruence under `h::` gives the cons case.
Associativity aL is proved by induction on the first list s: the empty case
reduces to `t++v=t++v`; the cons case follows by congruence under `h::` from
`(s++t)++v=s++(t++v)`. These prove the universally quantified R and S.

For B, define xor by `false xor b=b`, `true xor b=not b`, with
`not false=true` and `not true=false`. Right unit is the two cases
`false xor false=false` and `true xor false=true`. Associativity is the following
exhaustive computation; the final column is the result of each parenthesization:

| x | y | z | `(x xor y) xor z = x xor (y xor z)` |
|---|---|---|---|
| false | false | false | false = false |
| false | false | true | true = true |
| false | true | false | true = true |
| false | true | true | false = false |
| true | false | false | true = true |
| true | false | true | false = false |
| true | true | false | false = false |
| true | true | true | true = true |

Substitution in Eabs gives the actual target chains:

```text
L: (x++y)++(z++[]) = (x++y)++z = x++(y++z)
   first step: cong (λt. (x++y)++t) (rL z); second: aL x y z
B: (x xor y) xor (z xor false) = (x xor y) xor z = x xor (y xor z)
   first step: cong (λt. (x xor y) xor t) (rB z); second: aB x y z
```

Substitution in Wabs gives `(x,sym(rL x))` and `(x,sym(rB x))`, with respective
types `Σy. y=x++[]` and `Σy. y=x xor false`. Their first projections are exactly
x. For example the list x=`[0,1]` remains `[0,1]`; boolean x=true remains true.
No casts between lists and booleans or conversion of their equalities is used.
Each is an interpretation of the same schematic proof, not an isomorphism
between the two carriers.

### Missing law and failed view

Set A=ℕ, `m(a,b)=a∸b` (truncated subtraction), u=0. R holds, but S fails at
x=1,y=1,z=1: `(1∸1)∸1=0`, but
`1∸(1∸1)=1`. Thus no assignment to a can satisfy its universal type. E itself
fails at that tuple because `z∸0=z`. Wabs still works, with the selected
witness x. This separates failure of the E interface from the weaker W interface.

### Truth preservation without the selected observation

Let `q:List ℕ→Unit` be the constant map, with the unique unit operation on Unit.
It preserves concatenation and empty list, and maps equal lists to equal units.
Consequently E transports. The existential shadow of W is true for each source
x and true for its image `*`; sending any pair to the unit witness also preserves
that truth. Data transport with the explicitly weakened observation `q(x)` is
successful.

It does not preserve the frozen observation “recover the exact selected list.”
Pack the input with its output as
`D := Σx:List ℕ. Σy:List ℕ. y=x++[]`. The representation map sends every such
record to the single record in the analogous Unit type. The records at x=`[0]`
and x=`[1]` have different observed y, but identical images. If a recovery
function on represented records returned the original y for all D, it would
have to return both `[0]` and `[1]` at that one image, a contradiction.
At a fixed x retained externally, W can of course be regenerated from x; the
impossibility concerns recovery from the erased representation alone. A map
to mere existential truth forgets at least as much. This is the same observation
boundary discipline as the completed [FIFO experiment](abstract-fifo-client.md),
where public operation behavior did not determine a hidden layout observation.

## Declared interfaces and total MMT-style views

A manual author can declare the following interfaces before writing the argument:

```text
RightUnit:
  A : type
  m : A → A → A
  u : A
  r : ∀t:A. m(t,u)=t
RightUnitAssoc extends RightUnit:
  a : ∀s t v:A. m(m(s,t),v)=m(s,m(t,v))
```

The author writes the four-line equality derivation in RightUnitAssoc and the
pair derivation in RightUnit. These are exactly Eabs and Wabs with their leading
parameters supplied by the interface. The interface-first route has no separate
extraction pass, but the author must identify the laws before proving the generic
result. Declaring a full monoid would also work, at the cost of requiring an
unused left-unit law. Calling the interface RightUnitAssoc records the actual
laws without promising a canonical existing class.

For a paper MMT-style organization, use a common meta-theory NDData encoding the
fixture's logic and data judgments. RightUnit and RightUnitAssoc are theories
with the declarations above; `W` and `E` are defined declarations whose definiens
are the displayed proof bodies. `R`, `S`, and statement names are abbreviations
expanded before checking. There are no other primitive mathematical axioms in
these theories. The inclusion RightUnit→RightUnitAssoc assigns A,m,u,r to their
namesakes. For every declaration, the interpretation table is:

| Source declaration | View into natural-number source | Total view L | Total view B |
|---|---|---|---|
| A | ℕ | List ℕ | Bool |
| m | addition | concatenation | xor |
| u | 0 | [] | false |
| r, axiom proof | ruN | rL, induction derivation above | rB, two cases above |
| a, extra axiom proof | raN | aL, induction derivation above | aB, eight cases above |
| W, defined data term | `λx.(x,sym(ruN x))` | `λx.(x,sym(rL x))` | `λx.(x,sym(rB x))` |
| E, defined proof | Eproof | L chain above | B chain above |

The W row belongs already to RightUnit; a and E belong only to its extension.
The images of defined declarations are obtained by substitution into their
bodies and agree with the table by beta reduction. They are not additional
unproved model assumptions. If the physical syntax permits omission of an
assignment for a defined declaration, this expansion supplies its image; none
of A,m,u,r,a is omitted or filtered.

Both views have the identity metamorphism on NDData. Its primitive type/proof
judgments, arrow and binding constructors, equality and reflexivity/symmetry/
transitivity/congruence rules, implication and its rules, conjunction and its
rules, disjunction and its rules, falsity and its elimination rule, universal
quantification and its rules, existential proposition and its rules, and the
separate data-pair/projection constructors and beta equations all map to
themselves. This identity clause covers every base declaration; the example
neither reinterprets equality nor uses a partial meta-view. Here NDData is a
specified paper rule system, not a supplied executable MMT encoding.

To apply the cited general MMT transport theorem to an implementation, the
model builder must provide a foundation satisfying Definition 30, an adequate
encoding of this rule system, well-formed theories and views, and the totality
conditions of Definition 32, including the meta-view. Those obligations are
retained, not discharged by the label “MMT-style.” The explicit substitution
replays above establish the bounded example without pretending that this report
has implemented or verified that foundation. In particular the theorem does
not independently establish adequacy of data projections or a change of logic.

A proposed subtraction view assigning only A,m,u,r and leaving a unassigned is
partial. Its E image has an unsatisfied proof leaf at precisely the second
step. The displayed counterexample prevents completing a; mapping operation
names alone is not a certificate. A separate total view out of RightUnit is
valid for subtraction and transports W. Likewise an unsimplified strong theory
would extend RightUnitAssoc with `Q:Prop` and `d:Q∨¬Q`. L and B can assign Q to
an arbitrary chosen proposition P, but then owe `d:P∨¬P`; no such assignment
is available uniformly in the intended logic. Simplifying the proof permits
publishing E in the smaller theory, rather than silently dropping that axiom
from a purported total view.

## Author work and what was learned

The matched work is to reuse the frozen concrete arguments under the same L/B
interpretations and observations. This table records obligations visible in the
worked derivation, not timing or a human usability score.

| Work | Proof-derived route | Interface-first route | MMT-style organization |
|---|---|---|---|
| Argument author starts | Concrete Eproof/Wproof and chosen lemma leaves | Choose A,m,u and law statements | Choose or import RightUnit and its extension |
| Discover assumptions | Expose r/a, inspect strong-proof d, retain rule boundary | Identify R/S by reading or writing proof | Does not discover them automatically |
| Reuse argument | Replace leaves/symbols/types and replay existing tree | Write generic derivation once | Store derivation once in theory; substitute views |
| Public naming | Rename r/a as right-unit/associativity; separate W's smaller requirement | Name same laws in initial interface | Name declarations and select inclusion boundary |
| Model builder | Typed operations, rL/aL or rB/aB | Same | Same plus complete view and foundation integration |
| Syntax and registration | Proof variables, explicit binders and substitutions in paper | Interface fields and one specialization call | Theory/constant names, includes and view assignments |
| Casts in these cases | None | None | None; typed assignment substitutes carriers |
| Remaining logical obligation | Base rules; d if unsimplified | Base rules; avoid assuming d unnecessarily | Total identity meta-view; regular-foundation and encoding obligations |

The author-facing publication steps after extraction are concrete: choose the
opaque-lemma boundary; decide which type and symbols may vary; universally close
leaf formulas; replay; inspect stronger dependencies; choose whether to retain
them or change the proof; name R and S; split W from the associativity extension;
then supply or reuse the two typed interpretation packages. The names and split
are human mathematical decisions. The resulting artifact is smaller than a
full monoid interface, but no minimality is claimed. Even W's proposition has
the alternative witness `m(x,u)` by reflexivity with no R; that alternative
changes the frozen selected witness from x and is not the matched task.

The extraction route succeeds at preserving the given inference structure and
exposing a dispensable classical step. It does not spare the author the task of
recognizing right-unit and associativity or the model builder's proofs. For
these small examples, constructing the generic interface directly is equally
short. The fixture therefore gives no measured productivity advantage and no
reason to replace ordinary Lean theorem parameters with a mandatory theory
network. Total views add a useful organization/checking discipline once more
than one theorem or interpretation shares these laws.

## Prior results and bounded next scope

The completed [#248 investigation](recursive-argument-transport.md) and
[#252 implementation](recursive-fusion-implementation.md) already reuse a
recursive fusion proof in types and a nonconstant presheaf. Their source
`foldl_reachable` generalizes the accumulator during induction. The categorical
proof constructs algebra morphisms and uses list initiality and selected
exponentials; the implementations supply chosen products, coproducts and
Cartesian closure. Replacing the concrete induction's type name would neither
construct those morphisms nor justify the presheaf interpretation. The calibrated
extraction here stops at named law leaves for that reason. A future recursive
comparison must preserve the induction/initiality obligation and the accepted
full observation contracts, and account for any new proof design. #248/#252
are completed evidence, not tasks reopened by this report.

The completed [#210 study](abstract-fifo-client.md) distinguishes retained
operations from hidden observations; q above applies that discipline to the
selected witness. The completed [#249 study](toolkit-author-effectiveness.md)
and its [frozen protocol](../../experiments/toolkit-authoring/protocol.md)
provide the trial method if #235/#117 later commission an author comparison.
Such a trial needs a fresh frozen handoff with tasks, accessible interfaces,
reference solutions, author configuration, ordering/exposure, assistance and
attempt logs. This worked example is not that trial.

The decision for [#235](https://github.com/VladimirMarko/conaled/issues/235) is to
retain extraction as a complementary authoring service and stop before building
a native-proof importer or universal minimizer. If a concrete author need earns
an implementation, its exact first scope is an opt-in replayer for the displayed
many-sorted equational fragment: explicit leaf cut points, fresh operation/type
parameters, congruence/transitivity and universal binding, emitted named
requirements and total typed instantiations. Its acceptance cases are E in L/B,
the subtraction rejection, and the unsimplified/simplified classical detour.
The separate data-pair fragment must additionally preserve W's first projection
and reject erasure as exact-witness recovery. A scanner without the replayer
would not meet this scope. No implementation is authorized merely by this
recommendation, and #260 remains inactive.

Revise this scope if real examples produce opaque induction/representation
premises that are no easier to use than rewriting the proof. If dependent
substitution becomes the blocker, hand the concrete judgment and failed
substitution law to #107/#235 instead of advertising extraction as a repair.
Relational transfer, including the Trocq alternative inspected in the
[#280 comparison](external-discovery-280/assumptions-comparison.md), is relevant
when a representation relation is the actual obligation; it does not discover
R/S on this evidence. Nothing here mandates a common AST, adds kernel axioms,
or introduces global implicit subtyping.
