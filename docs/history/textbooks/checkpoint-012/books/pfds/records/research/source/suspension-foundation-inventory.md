# Suspension foundation inventory for local ticket 10014

## Status and scope

This is a read-only source and architecture inventory, prepared on 2026-11-02.
It is not a formal implementation, a completed chapter, or a proof/audit result.
No Lean source, repository reference, entrypoint, tracker, or build configuration
was changed for this assignment. The existing ordered-tree implementation
branch remains intact.

The proposed foundation supports the union of book Chapter 4 and thesis
Chapter 2/Appendix A. Book Exercise 3.4(d) is a concrete earlier consumer of
demand and root-availability semantics, so this is a cross-cutting prerequisite,
not an authorization to start Chapter 3 or Chapter 4 implementation. Root must
approve the concrete scope and sequencing before formal work begins.

The main conclusion is that this extension needs **stateful, potentially
nonterminating evaluation and effectful pattern matching with an explicit
suspension identity**. A total function from a thunk to a value, ordinary
immutable-tree sharing, or a cached value equation alone cannot express the
source rules. Existing conaled evaluation, resource, and relational
constructions can supply the surrounding machinery; the missing part is the
source-specific suspension/core-language semantics and its correspondence.

## 1. Sources and inspection record

All page references below are printed page numbers. For both supplied PDFs,
printed page p is zero-based PDF page index p+11, or physical page p+12.

| Locator | Exact source | Inspected scope |
|---|---|---|
| B31-B38 | User-supplied published book, research-pfds/source-assets/okasaki-book-2003.pdf | Chapter 4, pp31-38, including Figure 4.1 p36, Exercises 4.1 p35 and 4.2 p37 |
| B20 | Same book | Exercise 3.4(c,d) and the source merge/makeT presentation, Figure 3.2 |
| T7-T12 | research-pfds/source-assets/okasaki-thesis-1996.pdf | Thesis Chapter 2, pp7-12, including Figure 2.1 p11 |
| A131-A136 | Same thesis | Entire Appendix A, all grammar, typing, state, forcing, reference-pattern, recursion and SRec rules |
| B212, T142 | The supplied sources' bibliographies | Text confirmation of the two different Standard ML Definition editions |

Every assigned chapter/appendix page and B20 was both text-extracted and
visually inspected, including all inference rules and boxed program figures.
B38 is blank. A136 contains only its running header and page number. Text
extraction corrupts some mathematical symbols and code tokens; the inventory
uses the rendered pages to resolve them. In particular, Exercise 4.2 says
O(n*k), not O(n-k).

Source identities:

- Book SHA256: b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41.
- Thesis SHA256: f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072.
- Thesis retrieval reference: https://www.cs.tufts.edu/~nr/cs257/archive/chris-okasaki/dissertation.pdf.

Research-only extracts and renders are in
research-pfds/suspension-foundation. Manuscripts and renders remain outside
the repository/checkpoint deliverable under ADR0001; this inventory retains
locators, identities, paraphrased contracts and original analysis.

**Version boundary.** Appendix A explicitly modifies Milner, Tofte and Harper,
The Definition of Standard ML, MIT Press, **1990** [MTH90], not the revised
definition. Book B31 cites Milner, Tofte, Harper and MacQueen, The Definition of
Standard ML (Revised), MIT Press, **1997** [MTHM97]; B34 refers readers to the
thesis for the formal dollar notation. These references were confirmed in
T142 and B212. No external Definition manuscript was downloaded or relied on
in this investigation. Appendix A is expressly a delta to its base Definition,
so its inherited rules, the exception convention, Rec, environment operations
and typing infrastructure are dependencies to identify in a later scope.
Substituting 1997 rule numbers or generalization rules silently would be wrong.

## 2. Complete syntax and static-semantics inventory

| ID | Source | Required change or distinction |
|---|---|---|
| SYN-1 | A131, Definition 2.1 | Reserve the dollar token; it is unavailable as an ordinary identifier. |
| SYN-2 | A131, Definition 2.8 and Appendix B | Add expression suspension, dollar followed by an expression, and suspension patterns, dollar followed by a pattern. Both productions have the lowest precedence in their alternative lists. |
| SYN-3 | B32; T7 | Dollar extends as far right as possible. Thus dollar applied to a function application encloses the application; dollar preceding addition encloses the addition. The analogous constructor pattern encloses its argument pattern. |
| SYN-4 | B32 | Bare dollar is not a valid expression and cannot be passed as an ordinary constructor function. The ordinary unary-datatype analogy on B31 is only an introduction to types/patterns, not the evaluation semantics. |
| SYN-5 | T7 | Suspension expressions may themselves be suspended. A double suspension has the iterated suspension type; forcing its outer layer does not automatically force its inner layer. |
| SYN-6 | B32; T8; A134 | Explicit force is derived by a one-clause function matching a suspension pattern and returning the bound value. It is useful but is not an additional primitive operation in Appendix A. |
| SYN-7 | B33 only | The book introduces the lazy annotation on function definitions as sugar delaying the pattern match and then forcing the selected right-hand side inside a new suspension. Thesis Chapter 2 instead writes the delayed case explicitly. |
| SYN-8 | A134, Definition 2.9 | Permit recursive value bindings whose right-hand side is a dollar expression, in addition to the base recursive forms. This is not an unrestricted relaxation to all recursive expressions. |
| STAT-1 | A132, Definition 4.4 | Suspension types do not admit equality, even when their result type admits equality. A forcing equality operator is described as a possible alternative, not part of the selected extension. |
| STAT-2 | A132, Definition 4.7 | Dollar expressions are non-expansive for the base static semantics. Runtime allocation does not make them reference-like for this classification. Do not silently replace this 1990 rule with a different edition's value-restriction account. |
| STAT-3 | A132, Definition 4.10 | An expression with type tau yields a suspended expression with type tau susp. The analogous pattern rule lifts a pattern of type tau to a pattern of type tau susp. Other static context and binding machinery comes from the base definition. |
| STAT-4 | A132, Appendix C | Add unary type constructor susp to the initial static type environment; mark it as not admitting equality. Add polymorphic force with type forall alpha, alpha susp -> alpha to the initial value environment. |
| STAT-5 | A132, Definition 4.11 | Exhaustiveness and redundancy reasoning must account for effects during suspension-pattern matching. Ordinary constructor coverage intuition is insufficient when references and suspensions interact. The source gives concrete counterexamples, detailed below. |

The book's lazy sugar is schematically:

    fun lazy f p = e
       expands to
    fun f x = $(case x of p => force e)

The premise for its advertised type preservation is that e already has a
suspension type. The extra force prevents introduction of another suspension
layer. A multi-clause function needs one delayed, ordered match over all its
clauses, not independent transformations that accidentally perform a match at
application time. Bound variables must be fresh during this translation.
Function arguments remain strict in the surrounding Standard ML language:
delaying the function body does not retroactively delay evaluation of arbitrary
caller argument expressions. [B33]

These syntax/static changes are obligations of ticket10014 even if a first
implementation starts with an explicitly typed core. Merely naming a Lean
type Susp or declaring every supplied expression well typed would not establish
the non-expansiveness, equality restriction, basis, or desugaring correspondence.

## 3. Exact dynamic order and outcome distinctions

### 3.1 Store, closure capture and allocation

Appendix A changes memory to a finite map from addresses to either ordinary
values or thunks. A thunk pairs the suspended expression with its **creation
environment**. Reference values and suspension values are both addresses.
Reference addresses contain values; a suspension address contains either its
unevaluated closure or a successfully computed value. The source relies on
static semantics to distinguish these uses. A tagged Lean memory-cell type is
a reasonable representation, but any additional address sorting must be
related explicitly to this shared-address source model. [A133]

Evaluating a dollar expression allocates a fresh address outside the current
memory domain, installs its expression/environment thunk, returns that
address, and does not evaluate the body. This rule does not prescribe a
particular fresh-address policy. A deterministic sequential allocator would
be a realization of the fresh-choice rule, not its literal identity. Other
state components are preserved by this allocation rule. [A133]

Identity matters: two creations of the same expression are two suspensions,
while aliases of one address share its cache. Nested dollar expressions are
also staged: allocating the outer thunk does not yet allocate/evaluate the
inner suspension expression in its body. [T7; inference from A133]

### 3.2 Forcing and matching rules in execution order

The following is a paraphrase using H for memory and rho for environments;
it is not a replacement for the base core-language rules.

1. **Memoized hit.** If H[a] contains value v, matching address a against a
   suspension pattern matches v against the inner pattern in the current
   matching environment and threads that match's final state. It does not
   reevaluate the old body. [A133]
2. **Unevaluated body, normal result.** If H[a] contains closure (e,rho0),
   evaluate e using rho0 and the current state. If this yields value v and
   state s1, first update a to v in s1. Only then match v against the inner
   pattern, using the caller's matching environment rho. Return the match's
   outcome and final state s2. The closure environment and pattern environment
   are intentionally different. [A133]
3. **Pattern mismatch after success.** Normal expression completion triggers
   memoization before matching, so an inner-pattern FAIL retains the new
   cache and any matching effects. It is not a failed thunk evaluation.
   Subsequent alternatives see the resulting state. [A133; A132 example]
4. **Exception during the body.** Propagate the exception and the state reached
   by the body under the base exception convention. That forcing frame does
   not perform its successful-value memoization update. This is not rollback,
   and it does not imply the target cell still contains the original thunk:
   recursive evaluation could already have changed it. [A134-A135]
5. **Exception after the body, during matching.** The successful body update
   has already occurred. Propagate the later pattern exception and its state;
   do not erase the memoization merely because the enclosing match failed
   exceptionally. Further recursive effects may also have modified memory.
   [A133 rules plus A134's exception convention]
6. **Reference pattern.** The modified base Rule 158 looks up the reference
   value, runs its atomic subpattern with state, and returns the resulting
   state. It must no longer be treated as a state-free match. [A133]

Pattern and pattern-row judgments gain an exceptional result in addition to
a successful variable environment and FAIL. FAIL, a raised exception packet,
and an absence of finite evaluation are different observations. In particular,
a finite search returning no answer is not an exception and is not proof of
divergence. The source's displayed signature abbreviations and detailed rules
must be interpreted together: the detailed rules explicitly thread state.
[A133]

The source does not cache raised exceptions. It mentions exception caching as
an alternative policy that would avoid repeating body effects, but does not
adopt it. The initial dynamic basis adds the derived force function. [A134]

### 3.3 Recursive suspensions

The modified Rule 137 has three stages:

1. Evaluate the value bindings, obtaining VE and state s1.
2. Apply the base function-recursion operation to obtain VE' = Rec(VE).
3. Return VE' and SRec(VE',s1).

SRec is a state update, not new allocation. Its required properties are:

- The exception-name component ens is unchanged.
- The memory domain is unchanged.
- At addresses outside the range of VE', memory is unchanged.
- At relevant addresses containing a thunk (e,rho), replace its environment by
  rho extended/overridden by VE', retaining e.
- The surrounding valid recursive-binding situation guarantees relevant
  address bindings still contain thunks: those suspensions have not yet been
  forced. This domain condition must not be generalized to arbitrary input
  states or arbitrary variable environments. [A134-A135]

The core's Rec operation still handles recursive functions; SRec is the
additional environment update for suspended recursive bindings. A later
formalization must either implement the needed base Rec fragment or expose
and discharge its exact interface assumptions. Replacing both operations by
an unproved general fixed-point axiom would not be acceptable.

These updates can create cycles through addresses. Consequently the
backwards-address/acyclic representation invariants of the existing immutable
list/tree libraries cannot be assumed for suspension environments.

A recursive body may reenter its own still-unevaluated suspension. An inner
evaluation can memoize a value, and the outer evaluation can later overwrite
it with a different value. The thesis explicitly permits this effectful case.
Its optional blackhole alternative detects circular evaluation and can enforce
single memoization; it is not the semantics being specified. [A135]

Coverage correction from a later paragraph-level audit: A135 additionally states
that self-forcing does not terminate without side effects. That substantive pure-
domain claim needs a proof; the unrestricted effectful examples do not establish
it. It is now explicit as TU.A.4.PURE/local10019, supporting Chapter4 and later
pure cache/resource clients. Complete AppendixA coverage requires both this
claim and the10014 extension obligations. A nonreentrancy premise alone must not
replace the promised purity-to-nontermination argument.

## 4. Examples, counterexamples and discriminating tests

The following cases should become checked public clients or source-facing
correspondence cases in a later implementation. Cases identified as derived
are analysis of the displayed rules, not additional examples printed by Okasaki.

| Case | Source/status | Required observable behavior |
|---|---|---|
| Expensive delayed computation | B32 | Creating the prime-computation suspension does not execute the computation; first demand executes it; a later demand of the same successful suspension uses its value. Treat primes as an opaque expensive body unless separately formalized. |
| Unused suspension | B32 | A local suspension that is never demanded does not execute its body. Allocation and body work must remain separate measures. |
| Nested suspension | T7 | The outer force yields an inner suspension address. Only a further force executes the underlying body. |
| Lexical capture | Derived from A133 | Create a thunk under x=1, later shadow x by 2, then force: its body uses the captured binding 1, while the receiving pattern uses the current match environment. |
| Shared versus repeated creation | Derived from A133 | Two aliases share one successful cache. Two independent dollar creations do not automatically share even if their bodies are textually equal. |
| Premature arithmetic forcing | B33 | The unannotated plus function with suspension patterns forces inputs when applied. The explicitly delayed case or lazy-annotated version waits until its result is demanded. |
| Premature take forcing | T8 | The tempting multi-clause take without an outer suspension demands its stream at application for the nonzero clauses; the delayed versions do not. The zero-count first clause is a separate case and need not demand the stream even in the eager variant. |
| Zero-count demand avoidance | B35/T8, derived stress case | Demanding take(0,s) produces an empty stream without forcing s, including when s would raise or fail to terminate if forced. |
| Successful body, failed pattern | A133, derived instance | A body increments a reference and returns 1; matching against suspended 0 fails, but the body result remains cached. A later suspended-variable pattern obtains 1 without another body increment. |
| Successful body, exceptional inner pattern | Derived from A133-A134 | A successful outer body returns a value whose later inner matching forces another exceptional suspension. The outer successful cache must already exist when the exception propagates. |
| Repeated body exception | A134, derived nonreentrant instance | A body increments a counter then raises; two attempts repeat the increment and exception. This concrete case keeps its thunk because it never reenters/mutates that target, not because all exceptional forcing preserves target cells. |
| Recursive environment update | A134 | A suspended recursive binding's closure can resolve the recursive bindings only after SRec. Include mutual function/suspension bindings and an unrelated thunk/reference to check the update footprint. |
| Inner memoization, outer success | A135, derived instance below | Two successful writes to one suspension may occur; the outer result wins. |
| Inner memoization, outer exception | A134-A135, derived instance below | The outer attempt raises, yet the suspension can already contain the inner successful value. A subsequent force can hit that value. |

### 4.1 The source's effectful-pattern counterexamples

A132 gives a three-clause function and a four-clause extension. Their clauses
test, in order:

1. reference currently true, with the other argument ignored;
2. reference currently false, with the other argument matched against
   suspended integer 0;
3. reference currently false, with the other argument ignored;
4. only in the second function: reference currently true, other argument ignored.

Apply these to an initially false reference r and a thunk whose body assigns
true to r and returns 1. Clause 1 fails. In clause 2 the reference test succeeds,
forcing changes r to true and caches 1, but the inner 0 pattern fails. Clause 3
now fails because r is true. The three-clause match is therefore non-exhaustive.
Clause 4 of the second function succeeds, so it is not redundant despite its
apparent overlap with clause 1. The failed clause has neither rolled back the
assignment nor discarded the successful memoization.

This is a strong acceptance example: a semantics that restarts every
alternative from the initial state, memoizes only after a successful whole
pattern, or erases FAIL/exception distinctions will give the wrong behavior.

### 4.2 Two recursive counterexamples to overstrong cache laws

The following schematic source programs use the permitted recursive
suspension binding and an ordinary reference. They are proposed test cases,
not claims of already checked Lean/SML executions.

**Overwrite after inner success.** Start with gate=false and bind a recursive
integer suspension whose body does:

    if gate then return 7
    else set gate=true; return force(self)+1

The first outer attempt enters the else branch. The inner attempt sees true,
returns 7 and memoizes 7. The outer attempt then returns 8 and memoizes 8 at the
same address. A later force returns 8. This refutes an unconditional theorem
that every suspension address is memoized at most once.

**Outer exception after inner success.** Use the same guard, but the else
branch forces self and then raises Boom instead of adding one. The inner
attempt memoizes 7. The outer attempt raises and performs no additional update.
The final target cell is nevertheless the memoized value 7, so a later force
can return 7 without raising. This refutes both blanket state rollback and the
claim that a failed forcing attempt always leaves its target as a thunk.

A no-reentrancy premise and explicit exception/effect assumptions can support
stronger cache bounds for the pure algorithm clients. Those are separate
hypotheses to prove for clients, not implicit changes to Appendix A.

### 4.3 The scope of force-after-delay equivalence

B33 and Exercise 4.1 use the law that force of a newly delayed expression has
the same meaning as that expression. At the Appendix A machine-state level,
the unoptimized left side also allocates a private suspension cell, may install
a cache value, and performs extra forcing/matching work. Therefore this law
must specify an appropriate observation: ordinary result/exception and visible
effects, possibly modulo fresh-address renaming and unreachable private cells.
It is not literal equality of complete memories or exact resource traces.

This distinction also applies to the two source drop implementations. Proving
their extensional or contextual result correspondence does not automatically
prove equal allocations, equal numbers of cache accesses, or identical
exception histories under an inadequately specified observation relation.

## 5. Book/thesis forcing-order and representation variants

### 5.1 Common stream model

A stream is a suspension of a StreamCell, whose cases are empty and
Cons(element,tailStream). Thus every cell is delayed and the tail is another
suspension. The element type itself is not automatically suspended. Producing
a Cons cell may compute its element and allocate a tail suspension, but need
not execute the tail body. Both sources expose StreamCell in the signature
to permit pattern matching, rather than presenting only opaque isEmpty/cons
operations. [B34-B36; T8-T11]

A suspension of an ordinary strict list is a different representation. Once
forced, its list-producing computation completes before the list value is
returned. A stream can return one cell with later work still suspended.
These are statements about the represented computation, not a guarantee that
every arbitrary stream body terminates quickly.

### 5.2 Operations and exact variant boundaries

| Operation | Thesis form and order | Book form and order | Correspondence obligation |
|---|---|---|---|
| Append of suspended lists | Delay the expression forcing both lists and appending them. | Same explicit form, plus an equivalent lazy-pattern presentation. | Monolithic demand: both argument results and the strict append complete before the result list is returned. |
| Stream append | One outer suspension enclosing case on the left stream. Empty-left branch forces the right stream; Cons branch returns a cell with suspended recursive append. | Lazy-annotated clauses. Empty-left returns the right suspension, but the sugar forces that selected result inside the outer suspension. | Same cell-demand order after desugaring; do not mistake the empty branch for leaving the first right cell unforced when the append result is demanded. |
| Take | Explicit delay enclosing the ordered case; returns cells, with recursion creating another suspension. | Lazy-annotated clauses returning suspensions. | Count 0 does not force input. A nonzero output demand forces the next input cell and postpones the recursive tail. Check the added force/delay pairs under a stated observation. |
| Drop | One delayed call of strict helper returning a StreamCell. Prose helper's zero case forces the residual stream; Figure 2.1 writes that force as a suspended-variable pattern. | Two forms: recursively lazy drop, and one lazy outer call with strict helper returning a Stream. The outer sugar then forces that helper result. | Producing the first result cell traverses the skipped cells and demands the residual first cell, unless the input ends first. The two book forms have different suspension overhead before optimization. |
| Reverse | Helper accumulator is a StreamCell, initially empty; each step forms a Cons whose tail is the suspension of the preceding accumulator cell; one outer suspension delays the traversal. | Helper accumulator is a Stream, initially suspended empty; each step allocates a suspended Cons; lazy outer wrapper forces the final accumulator. | Both traverse the entire input before producing the first result cell, but intermediate suspension placement and allocation are different. Do not identify heap graphs or exact costs without a separate correspondence. |

Sources: append B34/T9; take B35/T8; drop B35/T9-T11; reverse B35-B36/T10-T11.

Further source obligations and qualifications:

- The stream APIs use **int** for take/drop counts. The source code recognizes
  zero and otherwise decrements. If a first formal client restricts counts to
  naturals or nonnegative integers, record that domain explicitly. Negative
  counts on finite streams follow the code until the stream ends; on infinite
  streams the behavior differs between incremental take and monolithic drop.
  Do not silently introduce a fast negative-input rejection.
- Trivial suspension bodies contain only a bounded collection of constructors
  and variables. The book discusses creating them already memoized; the thesis
  likewise proposes that optimization. Their O(1) forcing claim assumes a
  fixed bounded body and an explicit unit-cost interpretation. Being syntactically
  free of function applications is not permission to call an unbounded input
  representation free.
- Pre-memoized creation is an optional optimization needing a value/observation
  refinement and a separate resource statement. It is not Appendix A's general
  suspension-allocation rule.
- Book Exercise 4.1 requires equivalence of its two drop versions via
  force-after-delay. Exercise 4.2 additionally requires insertion sort on
  streams and the prefix-extraction O(n*k) claim, with n the finite input
  length and k a valid requested prefix length. Empty/prefix-zero cases and
  construction versus demand costs must be stated; this inventory does not
  discharge either exercise.
- Thesis Figure 2.1 prints “sig” after the structure definition where a Standard
  ML structure body would use “struct”; the book figure uses struct. Preserve
  this as a source presentation discrepancy, not as a reason to implement an
  invalid module grammar. The thesis's withtype-in-signatures workaround is
  compiler/version context, not a new suspension semantic rule.
- Historical notes about Wadsworth, Vuillemin, streams without/with memoization,
  Michie's terminology, dynamic programming, path compression and early CAML
  give provenance. They are not requirements to formalize every cited result.
  T12 additionally contrasts constructor-level laziness with locally visible
  dollar notation. [B37; T10-T12]

## 6. Existing conaled constructions and their limits

The following source was inspected in main at commit
76d77a107deb37c30e0b061c30b03a3f8c6aa12c. No project build was run for this
read-only inventory. Findings refer to definitions actually read, not names
in historical proposals.

| Existing construction | Concrete reuse | Important limit |
|---|---|---|
| Applications/Progress/Evaluation.lean: Machine, Evaluates, Terminates, TotalOn | A source-specific small-step machine can use the existing independent finite-evaluation judgment and explicit termination domains. Return values may include the final store and either a value or raised exception. | Machine is deterministic and each supplied step costs one abstract transition. It does not prove the host implementation of that step constant-time or supply nondeterministic fresh-name equivalence. |
| Same file: search, search_sound, search_complete, searchSquare | Fuel search can be connected to finite derivations without confusing a missing answer with divergence. Reuse the existing set-valued admissible-result contract. | Fuel exhaustion is unknown, not a source exception, pattern FAIL, or proof of divergence. Do not replace recursive source behavior by an unqualified total force function. |
| Same file: sequential and sequential_evaluates | Reuse staged operational composition once an actual evaluator has its configurations and local steps. | The atomic step boundaries must expose the work relevant to root availability; hiding an entire force inside one step makes latency claims vacuous. |
| Applications/Progress/Streams.lean: Producer, Delivers, Productive, productive_of_next, Delivers.coherent | Finite demanded-prefix observations, silent internal work, and conditional productivity are available. | A suspension is not automatically productive. A guarded coalgebra with one output per step would assume away potentially unbounded thunk work. The heap/cache state must remain in the producer state. |
| Applications/Resources/Measured.lean: Measured, bind, reweight, erasureSquare | Use the existing value/ordered-observation pair and additive sequencing. Preserve final state and outcome even on failure. Product observations can separate allocations, force attempts, cache hits, body entries, successful writes and core work. | Value agreement does not imply resource agreement; same_value_different_cost is already explicit. No new cost monad or independent claimed-cost formula is needed. |
| Applications/Resources/Workload.lean: run, run_append, run_invariant, run_value_fusion | Run finite sequences of actual state transitions or repeated query actions and reuse the workload/fusion laws. | A step must really execute the relevant transition. This finite list runner alone cannot define general recursive forcing or prove infinite productivity. |
| Applications/Resources/Potential.lean: run_potential and run_potential_exact | Later amortized clients can reuse telescoping over the same state trajectory. | Appendix A's unrestricted effects/reentrancy do not supply a global at-most-once budget. Client-specific restrictions and actual resource events remain necessary. |
| Applications/Durability/Storage.lean: Heap, put | Reuse the simple address-indexed optional cell representation and point updates; add a finite-domain/frontier invariant if this is the chosen realization of source finite memory. | Extends preserves every old occupied cell literally. Thunk-to-value memoization and SRec closure changes violate it. It applies to fresh allocation only, not all evaluation transitions. |
| Applications/Sequences/SharedList/Basic.lean and Applications/Search/SharedTree/Basic.lean | Existing explicit allocation/count/observation separation is a useful precedent, and fresh-address reasoning can inform the new store layer. | Their cell types and backwards-reference Represents predicates describe acyclic immutable values. Recursive suspension environments can have cycles; no height_le_next bound on general forcing follows. Do not reuse their Store by an artificial payload encoding merely to avoid stating the correct mutable-cell contract. |
| SquareKit/Relations.lean: RelRep, RelSquare, compose | Connect an implementation to independent finite observations and compose forcing with an observer. Partial behavior can be represented by sets/relations or a proved finite-search interface. | A square has total functions at its two edges; it is not itself the definition of a possibly diverging evaluator. Use the existing relational/set-valued patterns rather than silently claiming total source evaluation. |
| SquareKit/InteractionContracts.lean: Safe, Stable, Refines, Run | If a later concurrent or environmental client needs it, use explicit behavior refinement and state invariance under specified interference. | No fairness is implicit. Its sequential interference rule models boundary interference unless the component relation itself exposes interruption; it does not manufacture a concurrent suspension protocol. |
| Applications/Resources/TreeFlattening/Cached.lean | Existing measured erasure theorems show how concrete costed traversals relate to independent value semantics. | This cached-tree module is not a thunk evaluator, a retained memoization interface or a suspension-identity law. |

A targeted search of public Applications and SquareKit Lean sources found no
existing suspension/thunk/blackhole evaluator. The broader repository search
also found a memo-table experiment in experiments/relative-graph; it is not an
accepted general source suspension layer. The research document
docs/research/elegant-memoization-fit.md itself distinguishes value tabulation,
retained caches, partiality and operational sharing, consistent with this
boundary.

The architectural consequence is to reuse the existing evaluation, observation,
resource and relation machinery while adding the missing domain semantics.
There is no evidence that a new generic execution framework is needed.
Conversely, pretending Extends or a total stream function is the needed
semantics would remove actual source behavior.

## 7. Viable minimal formalization boundary

This is a proposal for later scope approval, not an implementation decision.

### 7.1 Required semantic content

A viable core must make the following available, either as concrete syntax
with checked rules or as an explicitly specified base-core interface with a
realization that discharges its assumptions:

- Expressions, patterns and ordered match alternatives; variables, lexical
  environments, strict application and ordinary constructors/records needed
  for pairs, streams and the examples.
- Values, reference/suspension addresses, finite memory, exception packets and
  the exception-name state component. Success, pattern FAIL and raised
  exceptions carry the state reached by evaluation.
- Reference allocation/read/write and sequencing, because the appendix's own
  counterexamples and recursive overwrite case depend on observable effects.
- Function closures and the relevant base recursive-binding operation Rec,
  plus recursive suspension bindings and SRec. An acyclic-only thunk language
  does not cover A.4.
- Integer/Boolean/unit operations and branching sufficient to instantiate the
  source cases. Their primitive semantics/costs should be explicit parameters
  where appropriate, not a wholesale duplicate arithmetic library.
- Suspension expression and pattern forms, plus a derived force and the book's
  hygienic lazy-function translation.
- Typing judgments sufficient to state the unary suspension type, excluded
  equality, non-expansiveness, polymorphic force and preservation of the chosen
  source sugar. A later full base-language embedding may supply additional
  generalization details.

A small explicitly typed call-by-value core with this content is a realistic
first source realization. The work should be described as **the Appendix A
extension over the stated core fragment**, together with the relevant book
sugar, not full Standard ML. Modules, the complete initial basis, every
datatype elaboration feature and a production compiler need not be recreated
to state the extension boundary honestly. However, removing references,
exceptions or recursive suspensions from the supposedly complete Appendix A
contract would omit its decisive cases.

### 7.2 Execution and correspondence

Prefer a source-rule relation retaining memory, environment and outcome, with
an independent source-specific small-step implementation instantiated into
Progress.Machine. Configurations need continuation frames for forcing and
pattern matching so the order “body returns; write cache; match pattern” is
observable. A forcing frame must remember its address and continuation without
implicitly marking it Busy; automatic blackholing would change A.135.

An explicit deterministic address allocator can refine the source fresh-choice
relation. State the observation used for fresh names and private garbage.
Finite evaluation/search correspondence and trace/event erasure should precede
cost bounds. Divergence and stuck ill-typed inputs need distinct accounts;
a source exception must not be used as a catch-all for either.

At minimum, prove:

1. Creation is fresh, captures the correct environment, and executes no body.
2. Cache-hit evaluation skips the body but still performs the requested pattern.
3. Cache installation precedes the inner match; FAIL and exceptions preserve
   the appropriately threaded effects.
4. Exceptional body propagation performs no update at that forcing frame,
   while allowing recursive updates that have already happened.
5. SRec has the specified domain, exception-name and outside-footprint
   properties, and connects valid recursive bindings to resolvable closures.
6. Finite small-step runs correspond to the selected source rules and return
   the same visible outcomes under the chosen state relation.
7. Derived force and lazy-function sugar preserve the selected value/effect
   observations; resource differences remain separately stated.
8. The general laws are exercised by several independent clients: ordinary
   memoized forcing, source effectful-pattern counterexamples, recursive
   overwrite/outer-exception cases, and a shallow constructor/root observer.
   Stream algorithms will supply later clients after their chapter is active.

Operations, validity/typing laws, observations and resource bounds should remain
separate. Restricting to a pure, nonreentrant algorithm domain can then prove
stronger reuse properties as a specialization. Do not bake global totality or
single evaluation into the generic suspension interface.

### 7.3 Open base-definition dependency

Appendix A alone does not define all inherited judgments. Before a formal
translation claims conformance to its 1990 base, record precisely how the
selected core handles environment extension, Rec, ordered matching, reference
patterns, FAIL conversion into language exceptions, exception propagation and
polymorphic/non-expansive typing. If those inherited details require consulting
the Definition, use the exact 1990 edition from a primary/official source and
retain its bibliographic identity and locators. A 1997 port would require an
explicit correspondence or documented differences, not relabeling the appendix.
No external manuscript is required in deliverables.

## 8. Relevance to Exercise 3.4(d): root availability

B20 asks what the one-pass top-down weight-biased heap merge gains in lazy and
concurrent environments. This is an observation about **when a shallow result
becomes available**, so full-tree extensional equality is insufficient.

For two already available nonempty input roots with correct cached subtree
sizes, the top-down algorithm can select the smaller root key and decide
child placement before executing the recursive merge. For example, if the
first root is selected, the size of the recursive merge of its right child
with the other heap is the sum of their cached sizes. Comparing this known sum
with the retained left-child size decides whether to exchange the children.
The resulting total size is likewise known. The result root can therefore
contain the selected key, computed size and an address for the pending
recursive child. This is an inference from the weight invariant and 3.4(c),
not a concurrency theorem printed in the book.

The source bottom-up organization calls makeT on the recursive result. In a
strict interpretation the recursive call completes before makeT. In a lazy
interpretation, the helper's test of the recursively produced cached metadata
still demands enough of that recursive result to determine the choice. Merely
wrapping the whole old merge in one outer suspension does not establish the
top-down availability property.

A concrete later comparison should:

- Specify the translated lazy heap representation and keep the input-root/
  cached-metadata availability assumptions visible.
- Define independent root observations: empty/nonempty, root key, cached size,
  and child handles. These do not force either child.
- Exhibit an actual execution prefix producing that root before any execution
  of the deferred recursive child, and connect its later finite completion to
  the ordinary merge value/invariant.
- Contrast the dependency/order required by the bottom-up implementation on a
  family with longer recursive merge paths. A delayed child computation can
  distinguish the two observations even when both eventually produce the
  same finite heap.
- Count the relevant primitive events or explicit machine transitions. Any
  constant-cost first-root claim must specify the cost of key comparison,
  cached-size arithmetic, allocation and input-root reads; unbounded integer
  arithmetic is not automatically machine-constant.
- State a concurrent consequence as an allowed producer/consumer dependency or
  interleaving: an observer of the published root, or a consumer of an already
  retained branch, need not wait for the pending merge child. Observers needing
  that child may still block.

Appendix A is sequential. It does not specify scheduling, synchronization,
atomic publication, wait-free forcing, linearizability, memory ordering or a
cache race protocol. Thus the minimal prerequisite for 3.4(d) is a truthful
demand/availability relation and its execution witness, with explicit
interference assumptions if concurrency is modeled. A complete concurrent
Standard ML runtime is not implied by the exercise, and the appendix's rules
alone do not prove faster wall-clock execution or one body evaluation across
threads.

The same shallow-constructor observation will be reused for the first stream
cell, avoiding a heap-specific notion of “lazy” that cannot support Chapter 4.

## 9. Review and sequencing handoff

The assigned source inventory is complete. The concrete implementation scope
and its base-core boundary remain to be approved by root. This report does not
change ticket10014's status or claim an implementation gate has passed.

Important review traps to preserve:

1. Successful body memoization happens before matching, including a later FAIL.
2. A failing outer forcing frame does not imply rollback or an unchanged thunk.
3. SRec updates relevant captured environments while preserving memory domain
   and exception names; its input validity matters.
4. Reentrant effects can cause multiple writes and overwrite an inner result.
5. Optional blackholing, exception caching and pre-memoized trivial thunks are
   distinct policies/optimizations with separate proof obligations.
6. The book's lazy sugar is additional to the thesis and still runs in a strict
   surrounding language.
7. Observational force/delay equivalence is not exact heap/cost equality.
8. The stream variants require explicit correspondence, especially drop,
   reverse and integer-count domains.
9. Existing immutable heap extension and backwards-pointer invariants cannot
   be imposed on this source memory.
10. Root availability needs an actual demand/execution observation; value
    equality, a preassigned cost or an implicit scheduler cannot establish it.

A later formal candidate still requires connected examples, statement review,
public entrypoint/audit coverage, exact-candidate verification and the project's
independent reviews. None of those future gates is replaced by this inventory.
