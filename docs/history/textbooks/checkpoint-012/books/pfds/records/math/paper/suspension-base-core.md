# Inherited 1990 Standard ML core audit for ticket 10014

## Status and exact source

Read-only audit against requirements/suspension-foundation.md version 1.
This report completes the inherited-rule source investigation. It does not
implement a complete Standard ML elaborator or establish type safety of
Okasaki's effectful suspension extension.

Primary source: the official SMLFamily reconstruction of Milner, Tofte and
Harper's 1990 Definition, https://smlfamily.github.io/sml90-defn.pdf, supplied
locally as research-pfds/source-assets/sml90-definition.pdf. Identity:
SHA256 2ad9e869db05f5a4316bc60b7170fb00789410436651c1a8f425a88098e8e9d1,
477208 bytes, 129 PDF pages. The PDF's TeX metadata dates its digital creation
to 2014-07-30; that is not a different semantic edition. The title names the
three 1990 authors, and the preface is dated August 1989. The official source
identity is also recorded in research/sml90-source-identity.json.

**Pagination matters.** In this reconstruction, PDF page n in the numbered
body carries printed page n-10. The thesis appendix cites pagination of the
original 1990 publication, not this reconstruction. Rule numbers and section
numbers, together with both locators below, identify the material reliably.
For example, original Rule 137 is at reconstruction PDF74/printed64 and
Rule 158 at PDF76/printed66. Do not apply the Okasaki PDF offset p+11 here.

Visually inspected inherited material includes:

- PDF15: type-variable lexical classes.
- PDF19-21: core grammar and syntactic restrictions.
- PDF31,34-37: semantic attributes, equality, schemes, explicit variable scope,
  non-expansiveness and closure.
- PDF39-46: expression, clause, binding and pattern typing, exception payload
  restrictions, and compiler warnings.
- PDF65-76: reduced syntax, state/value classes, finite closures, state and
  exception conventions, application, handlers, ordered alternatives,
  declarations, bindings and reference patterns.
- PDF97-99: initial static basis and exact ref/!/assignment/equality schemes.

Additional relevant pages were text-extracted; rendered source remains in
research-pfds/sml90, outside the deliverable. No source manuscript is copied
into the report or repository.

The companion suspension-foundation-inventory.md supplies the full book/thesis
extension inventory. This report replaces its open questions about the
inherited conventions with exact base-source findings.

## 1. Finite objects, environments and reduced syntax

### 1.1 What a closure actually contains

Figure 13 (PDF67/printed57) defines a closure as a finite triple:

    (match, creation environment, recursive variable environment)

It is not merely a function expression plus its lexical environment, and it
is not an infinite cyclic semantic value. The separate recursive environment
is essential to the finite interpretation of recursive functions.

The source state consists of finite memory plus a finite set of allocated
exception names. Before the suspension extension, memory maps addresses to
values. Appendix A adds expression/environment thunks as another memory-cell
case. Dynamic environments have structure, variable and exception-constructor
components; a core without modules may omit the structure component, but must
still distinguish the roles of variables and exception-constructor identifiers
in its source correspondence. [PDF66-67/printed56-57]

Map modification is **right-biased**: in f+g, g wins on its domain. Empty
components are injected when an environment component is added to a whole
environment. Thus captured environment plus recursive bindings, and matching
environment plus pattern bindings, have intentional shadowing order.
[Sections4.2-4.3, PDF32-34/printed22-24; Section6.3]

Exception values and raised exception packets are disjoint semantic classes,
even though a packet is structurally a tagged copy of an exception value.
FAIL is neither a value nor an exception: it is an internal pattern/match
outcome. These distinctions must survive the Lean representation.
[PDF65-67/printed55-57]

### 1.2 Why types are absent from the runtime syntax

Section6.1 erases explicit type ascriptions and exception payload type
annotations, removes type/datatype declarations, reduces abstype to its
executable declaration, and drops the type grammar from dynamic evaluation.
Thus root's separation of runtime Expr/Pattern from an external static
judgment is source-supported. It does not mean that any runtime syntax is
automatically well formed or well typed. [PDF65/printed55]

The selected core should retain the relevant syntactic restrictions: unique
bound variables within a pattern, unique record labels, no duplicate names
in a binding group, and the restricted recursive RHS forms. A source match
contains at least one rule. Empty clause lists can remain raw implementation
inputs, but need a validity boundary before being called source programs.
[Section2.9, PDF21 and continuation; grammar PDF20-21]

## 2. Rec and its interaction with SRec

Section6.6 (PDF68-69/printed58-59) defines Rec(VE) by exactly three properties:

1. Its domain is the domain of VE.
2. A nonclosure value at any binding is unchanged.
3. A closure (clauses,E,oldRecursive) becomes (clauses,E,VE), where VE is the
   **original complete input environment**.

The third component is replaced, not merged with the previous component.
The operation does not recursively traverse captured environments or arbitrary
nested values. It performs one finite unrolling.

Applying closure (clauses,E,VE) evaluates its match under E+Rec(VE), not E+VE.
The source invokes Rec at recursive value binding and at closure application.
This maintains finite semantic objects while allowing recursive computation.
[Section6.6 and Rules117,118,137]

Appendix A then modifies recursive binding as follows: evaluate the RHS group,
take VE'=Rec(VE), and return VE' with state SRec(VE',s). SRec changes the
captured environment of relevant thunk cells by adding VE'. It leaves the
memory domain and exception names unchanged. Functions in VE' keep the finite
Rec construction; suspension addresses remain ordinary values, so Rec itself
does not force or patch their contents.

The valid source binding forms explain why relevant address bindings hold
unforced thunks at this point: each suspended RHS creates its thunk but does
not run it. A bare alias or a reference-allocating RHS is not an additional
permitted recursive form. A generic SRec helper may need an explicit validity
predicate outside this concrete binding rule. Its law should not assume all
addresses anywhere in the environment graph denote thunks.

Root's current Syntax.lean has the required finite triple and an Env.rec that
maps each closure's third component to the original bindings. Its lookup_rec,
rec_domain, rec_closure and rec_address statements match these source clauses
at the interface level. This read-only comparison is not a compilation result.

## 3. State and exception conventions

### 3.1 State convention

Section6.7 (PDF69-70/printed59-60) restores omitted state arguments by threading
the result state of each premise into the next premise **from left to right**.
The conclusion receives the final premise's state. A rule with no judgment
premises preserves state, unless it explicitly gives a state change.
Side conditions remain side conditions.

This convention supplies evaluation order to rules whose printed forms look
pure. It covers record fields, operand evaluation, clause matching, alternative
selection and later value bindings. It must be expanded before translating
such rules into an evaluator.

### 3.2 Exception convention

For each premise position not already explicitly treating a packet, the
exception convention adds propagation of the first packet encountered after
the preceding premises. Later premises are not executed, and the conclusion
carries the state produced by the exceptional premise. It does not restore
the initial state.

**Rule119, the normal-result handler rule, is expressly excluded.** Otherwise
an exception from the protected expression would escape before the handler
could run. Rules120 and121 explicitly consume the packet from that expression.
A new packet from the handler's matching/body still propagates. [PDF70 footnote
and PDF72-73]

Applied to Appendix A's thunk rule, this means:

- An exceptional body stops before that frame's cache-write/match premise.
- Earlier body effects, including recursive successful memoization, survive.
- A normally returning body is written before the inner pattern runs.
- An exception from that inner pattern occurs after the successful write.
- FAIL is not a packet, so it follows the explicit failure rules rather than
  this exception convention.

The source convention already explains the required nonrollback behavior;
a separate transactional exception interpretation would contradict it.

### 3.3 Handlers and raising

| Rule | Exact inherited behavior |
|---|---|
| 119 | A normal protected result is returned unchanged; the handler is not run. |
| 120 | A raised exception value is matched in the handler's current lexical environment; a successful handler result is returned. |
| 121 | If handler matching returns FAIL, re-raise the original packet using the state after those failed matching attempts. |
| 122 | Evaluate the argument of raise first; a normal exception value is then packed. If evaluating that argument already raises, the convention propagates its packet. |

A successful pattern followed by a raising clause body does not make that
clause “fail to match”; it propagates the exception and skips later clauses.
Likewise an exception during a suspension pattern must not be converted to
FAIL. [PDF72-73/printed62-63]

## 4. Application, ordered matching and binding

### 4.1 Strict application

Operator and operand are evaluated in that order, both using the caller's
environment and successive states. A closure call then matches the operand
under the captured environment extended with Rec of the closure's recursive
environment. Exhausting that function's alternatives produces the predefined
Match packet, not FAIL as a public expression result. [Rules117-118, PDF72]

Constructors and exception constructors are first-class operator values:
ordinary constructor application pairs the tag with the evaluated argument;
exception-constructor application pairs a fresh/aliased exception identity
with its payload. Reference allocation is the separate ref case, after its
argument has been evaluated. Assignment evaluates the operator and its
two-field argument, updates the addressed cell, and returns the empty-record
unit value. [Rules112-115, PDF71-72]

The base reference rule chooses an address fresh in the memory resulting from
argument evaluation, not merely fresh in the state before evaluating the
argument. The source supplies no garbage-collection rule. [Rule114 comment]

The selected primitive interface may supply the meanings of basic values.
Ordinary source primitive typing and meanings must be explicit, with concrete
instances for clients. The source describes APPLY as returning a value or
packet and Appendix D gives exceptional primitive cases. The displayed
Rule116 on PDF72 writes only its normal value case; a claimed exact translation
of exceptional APPLY behavior must state its chosen bridge to that source
description rather than infer it from a state-rollback convention. The first
static counterexample can avoid this issue entirely by using a constant
integer-returning function instead of an arithmetic primitive.

### 4.2 Ordered alternatives and patterns

Rules124-128 (PDF73/printed63) try clauses in order. If the first pattern
succeeds, its bindings extend the clause environment and its RHS executes.
If it yields FAIL, the next alternative is tried against the same argument
value and matching environment, but the **latest state**. Pattern bindings
from a failed attempt are not exported to later clauses. State effects are
not bindings and are retained.

Pattern-row rules151-152 thread matching in source field order and short-circuit
on FAIL. They do not extend the matching environment with bindings from earlier
fields; they accumulate the output variable environment. This matters when
an exception-pattern identifier is an environment lookup: it uses the original
matching environment for that pattern, not a preceding field's newly bound
variable. [PDF76/printed66]

Reference patterns in original Rule158 explicitly preserve s because base
patterns cannot mutate it. Appendix A must change both the premise and
conclusion to the subpattern's final state. Other patterns/rows acquire state
threading through the existing convention once suspension patterns are added.
Record labels missing from a supposedly well-typed record, and reference
patterns applied to nonaddresses/unallocated addresses, have no corresponding
well-typed source rule; do not silently identify every such malformed input
with a source pattern mismatch.

Exception patterns look up the constructor identifier in the **current
matching environment** and compare the resulting exception identity. They
are not comparisons with the syntax name's numeric tag. Ordinary value
constructor tags, in contrast, denote themselves. Payload matching then uses
the same current environment. [Rules144-147,154-157, PDF75-76]

The reconstruction's displayed Rule126 omits v in its conclusion, while its
signature, both premises and the explanatory comment specify matching against
the same v. Record that presentation omission if transcribing the rule; do not
remove the argument from the core match relation.

### 4.3 Value bindings and declarations

Rules135-137 (PDF74/printed64) distinguish a binding group from sequential
declarations:

- Within pat=e and rest, evaluate e, match its pattern, then evaluate the
  remaining binding group using the original environment E and the updated
  state. The first group's new bindings are not in scope in the second RHS.
- A pattern FAIL raises Bind, with all evaluation/matching effects retained.
  Remaining group members do not run after that failure.
- On success, combine the groups' disjoint binding environments.
- Sequential declarations and a let body, unlike an and group, receive the
  environment produced by the preceding declaration.
- The recursive rule applies Rec to the completed binding environment; the
  suspension extension subsequently applies SRec to the state.

Exception binding Rule138 chooses a fresh identity outside the current ens,
adds it before evaluating later bindings, and returns the identifier-to-name
association. Rule139 aliases an existing exception identity without allocating
a new one. Selecting a numeric fresh-name policy is an implementation choice;
its initial invariant must reserve the exception identities already represented
by the selected basis, including Match and Bind. [PDF74; initial basis PDF100]

## 5. Exact 1990 static restrictions

### 5.1 Two independent type-variable attributes

A semantic type variable has an equality attribute and an imperative attribute.
They are independent. Source spelling uses initial primes for equality
variables, and one/two primes followed by an underscore for imperative
variables. The complement of imperative variables is the applicative class.
[Section2.4 PDF15/printed5; Section4.1 PDF31/printed21]

A type is imperative iff all its free type variables are imperative.
In particular, every closed type is imperative, including closed function
types. “Imperative” does not mean “a reference type” or “contains an effect.”
[Section4.4 PDF34/printed24]

A scheme's quantified variables retain both attributes. Instantiation of an
equality variable must give an equality type; instantiation of an imperative
variable must give an imperative type. Applicative variables have no extra
imperative restriction. Alpha-renaming of scheme binders preserves their
attributes. Do not confuse this with the separate convention that bound
variable attributes are irrelevant for type-function alpha-equivalence.
[Section4.5 PDF35/printed25]

### 5.2 Equality

Section4.4's equality cases are attributed variables, records whose fields
admit equality, named type applications whose name and arguments admit
equality, and **every reference type**, irrespective of its payload.

Functions do not admit equality. Appendix A additionally excludes every
suspension type. Consequently a reference to a suspension may admit equality
by address identity even though a suspension itself does not. A derived
equality checker that recursively requires an equality payload under ref
would be wrong.

The 1990 initial basis declares real an equality type (PDF97/printed87).
That fact differs from familiar later conventions and is another reason
not to call a modern type system the unchanged 1990 basis. The proposed
small core need not contain real.

### 5.3 Non-expansiveness and Clos

Section4.7 (PDF36/printed26) identifies variables, constructors and fn
expressions, possibly constrained by type expressions, as non-expansive,
with other forms expansive. Appendix A explicitly adds every dollar
expression, regardless of its body's effects. The runtime reduced syntax
has erased constraints; constructor expressions should be classified through
the source form represented, not by a general rule that all successful
runtime allocations count as values.

For each variable bound by its unique pat=e in valbind, Section4.8 defines
the quantified variables of its type tau as:

    non-expansive e: freeTypeVariables(tau) minus freeTypeVariables(C)
    expansive e:    freeApplicativeVariables(tau) minus freeTypeVariables(C)

**Expansive RHSs can still generalize applicative variables.** This is not
the blanket rule “generalize nothing unless the expression is a value.”
A closed identity application can retain applicative polymorphism even
though the application is expansive; a reference allocation's imperative
variable is withheld.

Rule17 elaborates the binding under C+U, closes its resulting monotypes
relative to C and valbind, and requires that the explicitly scoped U variables
do not remain free in the resulting schemes. Explicit type-variable scoping
is defined in Section4.6. The proposed core can state that its runtime syntax
has no explicit type ascriptions and therefore U is empty in its source
embedding, while still representing context-free variables precisely.
[PDF35-37,41-42]

Pattern bindings themselves are monotypes, not polymorphic schemes.
Recursive body uses are monomorphic: Rule27 elaborates the binding under
C+VE, and VE consists of the same monotypes assigned by the patterns.
Generalization happens at the surrounding value declaration, not at each
recursive use. [Rules26-27,35, PDF42,44]

### 5.4 Initial ref, read, assignment and exceptions

Figure23 (PDF98/printed88), visually checked, gives:

- ref: forall imperative alpha, alpha -> alpha ref.
- read (!): forall ordinary alpha, alpha ref -> alpha.
- assignment: forall ordinary alpha, alpha ref * alpha -> unit.
- equality: forall equality alpha, alpha * alpha -> bool.

The ref scheme is repeated in the constructor environment of Figure25
(PDF99/printed89). A core special form for reference allocation therefore
needs the corresponding imperative-payload condition. Closed integer,
Boolean and closed function payloads satisfy it.

Typing a reference pattern by the source's general constructor-pattern
Rule43 also uses the ref constructor scheme. A static fragment should retain
that distinction rather than assume the read operator and ref-constructor
pattern were given the same unconstrained scheme. The first explicit clients
use closed payload types, so their obligation is immediate.

Exception payload types must be imperative (Rule31, PDF43/printed33).
Exception environments contain monotypes, and exception declarations are
not closed into polymorphic schemes. Nullary newException in root's current
runtime syntax is a sufficient smaller fragment; payload exception types
may be supplied by a fixed signature without claiming the full declaration
grammar. [Rules21,31-32]

Exhaustiveness and irredundancy are compiler warning obligations, not rejection
of all nonexhaustive programs. This is necessary to retain Appendix A's
effectful-pattern counterexamples. [Section4.11 PDF46; Section6.5 PDF68]

## 6. SUSP-STAT-001: derived cached-polymorphic-reference counterexample

**Status:** source-derived suspected safety counterexample, not yet Lean
checked. The three decisive source facts have been visually verified:
1990 ref's imperative scheme, the Clos partition, and Appendix A's blanket
non-expansiveness of dollar expressions (thesis p132).

A list-free source candidate is:

    val s = $(ref (fn x => x))
    val ri : (int -> int) ref = force s
    val _ = ri := (fn x : int => 0)
    val rb : (bool -> bool) ref = force s
    val result : bool = (!rb) true

The type-ascription placement above is explanatory; the runtime core erases
it. The constant-zero replacement avoids any appeal to an unmodeled arithmetic
failure. An incrementing replacement is another useful client when a concrete
primitive interpretation is supplied.

Static derivation outline:

1. Let alpha be imperative. The identity function has type alpha -> alpha.
   That function type is imperative because alpha is its only free variable.
2. Instantiate ref at alpha -> alpha. The reference expression therefore
   has type (alpha -> alpha) ref.
3. Dollar gives ((alpha -> alpha) ref) susp and is non-expansive.
4. With alpha absent from the outside context, Clos quantifies alpha, even
   though it is imperative. The scheme of s is thus forall imperative alpha,
   ((alpha -> alpha) ref) susp.
5. Integer and Boolean are closed, hence imperative. Separate occurrences of
   s can instantiate alpha by int and bool, respectively.
6. The polymorphic derived force yields the two reference types shown above;
   source read/assignment schemes type the remaining operations.

Operational prediction:

- First force allocates the identity closure's reference and caches its address
  in s.
- Assignment replaces that reference cell by an integer-returning closure.
- Second force returns the same cached reference address.
- Applying its content to true returns integer 0 in the constant variant,
  despite the whole result's static Boolean type.

Thus preserving the published static rules should not be accompanied by a
blanket preservation/progress theorem for arbitrary effectful programs.
The first formal target should be the exact scheme/instantiation witness and
the actual machine run, followed by the precise negative safety conclusion
supported by the chosen type-of-value observation. The increment variant may
instead expose a primitive-domain fault; do not conflate that implementation
fault with an exception specified by Standard ML.

This finding is not authorization to change dollar generalization to a modern
value restriction or silently remove effects. A pure or otherwise constrained
algorithm client may prove its own safety/cache theorem under explicit
restrictions. The source-faithful static extension and those restricted
client guarantees are different deliverables.

## 7. Concrete core and proposed static API boundary

Root's inspected Syntax.lean provides atoms, expressions, patterns, finite
closures/environments, Rec, RecursiveRhs, derived force, and lazyFunction.
It is a suitable runtime fragment once a source-validity relation and the
typed operations below are stated. No edits to that file were made in this
audit.

A minimal static layer should provide:

1. **Attributed variables and types.** A TyVar records a stable name and its
   independent equality/imperative flags. Ty supports the atom types,
   variables, functions, references, suspensions and the selected fixed
   product/constructor types. A finite free-variable function and equality/
   imperative predicates have exact public characterizations.
2. **Schemes and instantiation.** A scheme has a finite set/list of attributed
   bound variables and a body. Substitution acts only on its bound variables;
   admissibility enforces both flags. Unbound variables are fixed.
3. **Context and generalization.** Include free variables of the environment
   and explicit ambient type variables. Generalize with precisely the
   Section4.8 partition, selected by the source non-expansiveness predicate.
   Provide membership laws showing that expansive RHSs still quantify fresh
   applicative variables and cannot quantify imperative ones.
4. **Patterns.** A judgment relates a pattern, input type and a finite
   monomorphic binding environment. Suspended patterns preserve those
   bindings and wrap the input type. Constructor and primitive signatures may
   be parameters; exception identifiers consult the current type environment
   as monomorphic exception constructors. Distinct bindings/record labels and
   nonempty clauses are validity obligations.
5. **Expressions and clauses.** Type strict application, functions, ordinary
   lets using exact Clos, references/read/assignment, suspension, ordered
   clauses and the selected exception fragment. Recursive bindings use
   monotypes inside their RHSs and the restricted function/delay forms.
   Do not introduce polymorphic recursion by storing arbitrary schemes in
   the recursive RHS context.
6. **Derived clients.** Prove force's type for every supported payload type;
   exhibit its general polymorphic scheme. Prove lazyFunction retains
   input -> suspended output, and give its syntactic delayed-match shape.
   The actual no-match-before-demand execution contract belongs to the
   machine/source correspondence, not merely to a typing theorem.

The first priority concrete client is SUSP-STAT-001's exact generalized
scheme and its int/bool instances. A second client must distinguish an
expansive identity application with applicative generalization from an
expansive reference allocation with withheld imperative generalization.
Equality clients should separate an equality payload, its forbidden
suspension equality, and the allowed equality of a reference to it.

### Hygiene and a subtle weakening obligation

Root's lazyFunction creates a fresh parameter and reuses the original clauses
inside a delayed function application. Its freshness condition must include
**exception identifiers in patterns**, which are environment lookups. Merely
collecting free Expr.variable occurrences is insufficient. A conservative set
of all names, including pattern binders, exception identifiers, recursive
binding names and newException binders, is acceptable and simpler; label it
“AllNames” or “AvoidsName,” not exact free variables.

For typing, fresh term names alone are not the whole weakening argument in a
polymorphic-let system: adding an unused environment binding may introduce free
type variables and hence change Clos's generalized set. A correct proof must
either preserve the context's free-type-variable set, use an explicit
fresh-type-variable/alpha-renaming lemma, or state a narrower typing-domain
hypothesis honestly. Do not prove lazyFunction typing by an invalid generic
weakening lemma that ignores generalization. Monomorphic clause cases supply
a useful initial specialization but are not a substitute for an announced
universal polymorphic-let theorem.

The function used to define force binds only its own local result variable;
strict evaluation of its argument occurs in the caller environment. Its fixed
internal variable name is therefore not the same capture concern as the
wrapper parameter inserted around arbitrary existing clauses.

## 8. Immediate handoff and acceptance boundary

The base conventions now support concrete implementation without inventing
full SML coverage. Root's finite closure triple/Rec design is confirmed.
The state machine must retain failed-match effects, handler-specific exception
behavior, generative exception identity and the distinction between an and
binding group and sequential declarations.

Only this report and permitted temporary research files were written.
No Lean source, references, tracker entries, entrypoint, or builds changed for
the audit. The subsequently authorized Static/Names implementation is a new
step within the existing ticket10014 implementation loop and must preserve
SUSP-STAT-001 until checked. Its source correspondence, concrete clients,
statement review, full exact-candidate validation and independent reviews
remain required; no Markdown derivation supplies an unverified code premise.

## Additional namespace check

The continuation of §2.4, physical PDF16 (printed6), was also visually checked.
The identifier spellings for variables and exception constructors initially
share lexical forms, but occurrences are classified from the scope of the
introducing declarations. A value declaration cannot shadow an active exception
constructor by introducing a variable with the same spelling: the purported
pattern binder is classified as the exception constructor. After this analysis,
the Definition assumes the identifier classes disjoint. A flat natural-number
runtime environment therefore needs a sorted-source embedding or a proved
separate-namespace encoding before it represents the source's `VE × EE`.
Arbitrary raw flat-name programs do not have that claim. The static fragment
records identifier status and forbids a variable pattern from changing an active
exception classification. A separate even-variable/odd-exception encoding is
owned by the root implementation. The cached-reference case uses no exception
constructor identifiers, independently of the reserved runtime Match/Bind
exception *identities*.
