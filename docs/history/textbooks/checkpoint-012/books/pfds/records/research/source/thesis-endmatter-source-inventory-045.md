# Thesis conclusions and endmatter: complete source inventory

Prepared 2026-11-04 UTC by `/root/thesis_bootstrapping_inventory`, as bounded
source preparation while the coordinator owns validation. The `045` suffix
is the reserved recovery-series label. This note supplies source accounting,
requirement reconciliation and proposed proof obligations. **Every proposed
formal obligation and example calculation remains unproved by this task.**
No implementation, test, independent formal review or acceptance is claimed.

## 1. Exact source and actual boundaries

The primary source is Chris Okasaki, *Purely Functional Data Structures*,
CMU-CS-96-177, September1996, at
`research-pfds/source-assets/okasaki-thesis-1996.pdf`. Its identity was
rechecked: **628,877 bytes; 162 PDF pages; SHA256
`f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072`**.
References `[T pN]` below identify printed Arabic page N of those bytes;
one-based PDF page is N+12.

Read all text on **printed127–150 / PDF139–162**, through the actual end of
the PDF. Rendered all24 pages. Visually inspected printed127–137,142,145–147
and150: all of Chapter9, the entire compact semantic appendix including its
blank final page, the relevant edition citation and the endmatter boundaries.
The remaining bibliography/index pages were text-read; their renders were
created but are not claimed as inspected merely because they exist.

| Actual component | Printed pages | PDF pages | Exact extent/disposition |
| --- | --- | --- | --- |
| Chapter9, Conclusions | 127–130 | 139–142 | §§9.1–9.4; four open-problem bullets; no new numbered theorem, exercise or algorithm listing. |
| AppendixA, The Definition of Lazy Evaluation in Standard ML | 131–135 | 143–147 | All syntax, static, dynamic and recursion changes, both effectful-pattern examples and the derived force function. |
| AppendixA trailing page | 136 | 148 | Running header/page number only. |
| Bibliography | 137–145 | 149–157 | All107 bibliographic entries and their backward page references. |
| Bibliography trailing page | 146 | 158 | Running header/page number only. |
| Index | 147–150 | 159–162 | All four pages contain index entries; printed150 is substantive and is the PDF's last page. |

The bracketed references to **AppendicesB, C and D** on thesis pp131–134
refer to appendices of the external Standard ML Definition. They are not
additional thesis appendices missing from this range. Likewise Figure13,
Figure23 and Rules137/158 are inherited Definition locators, not newly numbered
thesis figures or theorems. This thesis appendix is a semantic extension, not
a collection of Haskell algorithm listings.

Applied the PDF skill. Extraction used `/usr/bin/pdftotext -layout`, and
rendering `/usr/bin/pdftoppm -scale-to 1800 -png`. Reproducible intermediates
are under `research-pfds/thesis-endmatter-045/`: `endmatter-layout.txt`,
`p127.txt` through `p150.txt`, and `thesis-139.png` through `thesis-162.png`.
They are outside `session` and need not enter durability checkpoints. No
external paper or new source edition was retrieved. This pass makes no new
claim about book availability and does not inspect a book chapter or appendix.

## 2. Pending requirements checked and conflict result

Read the current `chapter02.md`, `suspension-foundation.md`,
`pure-recursive-forcing.md`, `pure-cache-counts.md`, `body-entry-counts.md`
and `shared-persistence.md` requirements. Reconciled the existing union records
and the `TU.A` / `TU.A.4.PURE` entries in `thesis-obligations.json` with the
primary appendix. Read the relevant semantic and example sections of
`suspension-foundation-inventory.md`, and targeted static-safety/generalization
passages of `suspension-base-core.md`, `suspension-static.md` and the retained
suspension Spec review. Those records were used to identify existing scope
and caveats, not to accept or independently validate their implementation.

**No new concrete semantic conflict with those pending requirements was
found.** The coordinator was informed during inspection. In particular, the
requirements already preserve the crucial distinctions below:

- A normal body result is cached before the requested inner pattern is matched.
- A body exception causes no successful write at that forcing frame, while
  preserving effects and any writes already performed by inner evaluations.
- Recursive self-entry and sequential exception retry are different phenomena.
- Successful-write uniqueness is distinct from body-entry uniqueness.
- The general semantics does not introduce blackholing or memoize exceptions.
- The pure self-entry claim requires actual source-domain restrictions and a
  finite-execution argument; it is not an assumed nonreentrancy predicate.
- Chapter2 immutable sharing laws are not imposed on mutable suspension cells.

One existing source caveat remains material. Thesis p132 declares every dollar
expression non-expansive, while p133 includes a broad reassurance about the
static semantics distinguishing reference and suspension uses. The retained
`SUSP-STAT-001` material studies a cached polymorphic-reference type mismatch
under the published extension and its inherited1990 rules. This pass does not
rederive or revalidate that candidate, and does not turn its narrower example
into a fresh proof about every possible address-kind invariant. It does mean
the source reassurance must not be promoted to an unproved universal
type-safety/preservation axiom. The pure-recursive requirements already
explicitly forbid that assumption. Preserving the published non-expansiveness
rule and proving restricted client guarantees are separate obligations.

The exact requirement snapshots read were:

| File under `session/requirements` | SHA256 |
| --- | --- |
| `chapter02.md` | `240b6bfec9f9e8599f1034abc309499928c8472edf76481b553ef99ce40ff944` |
| `suspension-foundation.md` | `56828fa549b0f96b76db9c2451b82106ea12cf4c6e15bd7cd0fc5ecdf3a98f3e` |
| `pure-recursive-forcing.md` | `57ddefb472b9393a3fe890f880ad4eb94893f5aa6bd8be912da2d7dfa4f4ec55` |
| `pure-cache-counts.md` | `fa5b5c01205aea18cc19aa53047cc7e0d57c0bb225534f0152bc04d7c87e569e` |
| `body-entry-counts.md` | `1483d8bfc4470c4aa700c809209b3083db89fa713def40821e1968d9e3ce2a58` |
| `shared-persistence.md` | `177e80e0beda3ec144279c104d2fa3b968e916b0104db7f2e5d3c7c81a4bec76` |

Relevant supporting record hashes are
`suspension-foundation-inventory.md`:
`a5b822225bb67978f5165442449949c49964fd1085b80bf800430df7a241732b`;
`suspension-base-core.md`:
`50f0e7871aa7c6081d6a608403fdc8855d052da1134d8cd94da794992395d457`;
`thesis-obligations.json`:
`d98a57b4aa508b2d2e40719e4e689ec15a7e5f67685b9029455c2e83d8b984ad`.
No requirement, source record, tracker or acceptance state was modified.

## 3. Chapter9: every conclusion and future-work statement

### 3.1 Summary and functional-programming conclusions, pp127–128

The opening paragraph summarizes the amortization framework of Chapter3,
scheduling of Chapter4, four design techniques in Chapters5–8 and sixteen
implementations. This is a backward reference to existing algorithm and
forward-table obligations, not sixteen new implementations or a certificate
that their formal proofs have been accepted. [T127]

The following distinctions retain the substantive content of §9.1:

| Source statement family | Required union disposition |
| --- | --- |
| Algorithm choice can limit functional-program performance despite compiler improvements; several thesis structures match imperative asymptotic bounds. | Link each actual algorithm/cost claim to its owning chapter and model. Do not infer an unrestricted performance theorem about languages or every imperative algorithm. |
| Design techniques help produce customized functional data structures. | Methodological conclusion; generic transformations still need their explicit premises and checked instances. |
| Extended amortized analysis helps estimate lazy-program cost, while lazy evaluation supports persistent amortized structures. | Link to the actual logical-history/debit theory and suspension semantics. Neither value equality nor a strict surrogate execution proves a lazy cost bound. |
| Amortized designs are described as simpler; the footnote notes that all but one implementation fit on one page. | Qualitative/presentation claim. Page count is not a formal complexity measure or a requirement to recreate every competing design. |
| Memoization overhead can hurt mostly single-threaded usage and help heavy persistent usage. | Empirical, workload-dependent source assessment. Preserve retained-version access and the chosen cost observer; do not claim a new benchmark or a parallel-runtime result. |
| A restricted lazy-versus-strict separation is attributed to [BJdM96], following [Pip96]. | External-result citation, not a supplied proof or an additional algorithm implementation. |
| The author proposes seeking a lazy amortized data structure asymptotically superior to every strict worst-case alternative, and reports knowing none at that time. | Historical research proposal. Do not solve it by assertion or turn the1996 report into a current universal statement. |

The text does not supply the external separation problem, its restrictive
model or a proof. It also does not make a source-level cost theorem alone
establish wall-clock superiority. [T127–128]

### 3.2 Persistent-data-structure conclusions, p128

Section9.2 summarizes memoization's role in reconciling amortization with
persistence and anticipates future applications. The mathematical content
belongs to the earlier persistent accounting and concrete implementations;
the prediction is historical context.

The section also recommends functional representations as a design medium
even for an eventual imperative implementation. It contrasts this route with
external persistence transformations [DSST89,Die89] and stresses combining
operations such as catenation. Preserve the relevance of multiple arguments,
retained versions and shared identity in the source-history model. The
paragraph does not provide a C compiler, a general translation proof, a
garbage-collection analysis, or the external transformations' algorithms.
Its comparative and priority language is not an unconditional theorem that
every functional representation handles every confluent operation efficiently.
[T128]

### 3.3 Programming-language recommendations, pp129–130

Section9.3 has five named discussion topics; all are retained:

1. **Order of evaluation.** Strict and lazy evaluation have complementary
   uses; the author recommends both in a general-purpose language and presents
   dollar notation as a lightweight addition to a strict language. This supports
   preserving exact forcing placement, not a theorem that strict evaluation
   cannot support amortization or that every lazy operation is efficient.
2. **Polymorphic recursion.** Nonuniform recursive types capture structural
   invariants that a uniform rewrite can lose. The recommendation is the
   Haskell1.3 policy of requiring explicit type signatures for polymorphic
   recursion. Preserve the earlier type/shape correspondence and generic
   representation obligations; this is not a supplied full inference algorithm
   or a statement about current language support.
3. **Higher-order recursive modules.** Generic heap bootstrapping motivates a
   module-to-module transformation instead of manual inlining for each instance.
   A constructor-class solution is attributed to private communication and
   [Jon95]. It is not listed here. The existing Chapter7 generic transformation
   and concrete realization remain separate obligations.
4. **Pattern matching and abstraction.** The source explains the attraction of
   exposed list representations and the potential cost of choosing them over
   suitable abstract structures. Views [Wad87,BC93,PPN96] are suggested as a
   reconciliation; dollar patterns are described as a special case. Preserve
   the actual dollar-pattern semantics. No general views implementation or
   universal linear-versus-exponential theorem is supplied. The remark about
   language support is historical, not a fresh survey.
5. **Implementation.** Efficient catenable lists are connected to sophisticated
   control structures [FWFD88], with a priority claim. This is motivation and
   an external application pointer, not a supplied continuation-calculus
   implementation or an extra formal algorithm to invent. [T129–130]

### 3.4 All four open problems, p130

These are explicitly questions in the source and remain classified as such.

| Question | Exact boundary to preserve |
| --- | --- |
| Appropriate empirical measurements for persistent structures | Older-version access must be represented in a relevant workload; the source does not supply a complete benchmark methodology or measured results here. |
| Strengthening the persistent physicist's method | The paragraph contrasts classical equivalence with an apparent persistent limitation and asks for improvement. Do not assert a proved strict separation of the two methods or an answer to the question. |
| A simpler catenable-deque implementation | The source compares its deque and list constructions and requests a simpler design. It supplies no replacement algorithm on this page. |
| Scheduling these catenable lists/deques | Schedule maintenance is said to appear to require more than O(1) time. This is neither a formal lower bound nor a supplied successful schedule. Binary/heap scheduling proofs do not automatically settle it. |

These questions and the §9.1 separation proposal are part of source accounting.
They do not create a requirement to resolve new research problems before
faithfully formalizing the supplied constructions. [T128,130]

## 4. AppendixA's base-definition boundary

The appendix expressly supplies changes to *The Definition of Standard ML*
by Milner, Tofte and Harper, **1990** [MTH90], whose bibliography entry is
printed142. It is designed to be read with that external definition. The
parenthesized page numbers in its paragraph headers refer to the Definition,
not to this thesis. [T131,142]

The existing `sml90-source-identity.json` identifies a separately researched
official reconstruction with SHA256
`2ad9e869db05f5a4316bc60b7170fb00789410436651c1a8f425a88098e8e9d1`.
This pass read that provenance record and the relevant inherited-core notes;
it did not freshly inspect or retrieve the external Definition. Therefore
this report directly confirms the thesis delta, not all inherited1990 rules
or any1997 correspondence.

The source assumes inherited environments and their extension operation,
ordinary values/closures, value bindings, Rec, ordered matching, records,
reference primitives, exception packets/name state, exception propagation and
typing/generalization infrastructure. A formalization must delimit a core
fragment or provide the additional inherited semantics. It cannot obtain full
Standard ML conformance from the five-page delta alone. This requirement is
already explicit in local10014.

There are seven displayed inference-rule instances in the appendix: two static
lifting rules, fresh suspension allocation, two forcing rules, modified
reference-pattern Rule158, and modified recursive-binding Rule137. The
pattern-result signatures, finite-memory definitions, four SRec clauses and
prose exception/recursion qualifications are additional semantic content,
not omitted because they are not inference bars.

## 5. A.1: complete syntax inventory, p131

| Definition locator printed by the thesis | Supplied change | Proposed obligation |
| --- | --- | --- |
| §2.1 Reserved Words, p3 | The dollar token is reserved and cannot itself be an identifier. | Preserve token classification, distinguishing the reserved token from an ordinary first-class constructor/function. Inherited lexical rules still govern other identifiers. |
| §2.8 Grammar, pp8–9 | Add `exp ::= $ exp` and `pat ::= $ pat`. | Supply both creation syntax and forcing-pattern syntax, with an actual operand phrase. |
| AppendixB Full Grammar, pp71–73 | Repeat both productions at the lowest precedence in their alternative lists. | Preserve scope and grouping. Dollar is not ordinary constructor application; a bare dollar is not a complete expression. |

The appendix does not add the book's lazy-function annotation here. That
additional sugar remains separately owned by the existing union foundation;
this inspection does not replace its hygienic, ordered delayed-matching
requirements. [T131; existing local10014 scope]

## 6. A.2: complete static inventory and both supplied examples

### 6.1 Type, equality, non-expansiveness and basis rules

All of the following appear on printed132:

| Definition locator | Supplied rule/change | Required qualification |
| --- | --- | --- |
| §4.4 Types and Type Functions, p18 | A type `tau susp` does not admit equality. | This remains true even if tau admits equality. Automatic forcing equality is described only as a reasonable alternative; it is not the chosen rule. |
| §4.7 Non-expansive Expressions, p20 | Every dollar expression is non-expansive. | This is a static classification despite runtime allocation. Preserve the1990 inherited generalization rules; do not silently impose a different value restriction or require a pure body. |
| §4.10 Inference Rules, pp24,29 | From an expression of type tau, infer its suspension has type `tau susp`. | Preserve the original context and underlying expression typing; do not declare arbitrary bodies well typed. |
| Same locator | Lift a pattern of type tau to a dollar pattern of type `tau susp`. | The base pattern/binding machinery remains necessary; the displayed abbreviation does not remove binding consistency or environment effects. |
| AppendixC Initial Static Basis, pp74–75 | Add unary `susp` to the initial type environment, not admitting equality. | Account for arity and equality metadata, not just a target-language type with a familiar name. |
| Same locator, Figure23 | Add `force : forall alpha, alpha susp -> alpha` to the initial value environment. | Prove the derived function's typing with its actual pattern and inherited polymorphism conditions. |

The remark proposing forcing equality is contextual variant accounting. It
does not specify how that alternative orders demands, handles exceptions or
divergence, or measures work. No complete alternative equality algorithm is
supplied and no such policy should enter the default realization. [T132]

### 6.2 Stateful exhaustiveness/redundancy examples

Under Definition§4.11, p30, the thesis gives **two complete function listings**.
They share the first three clauses; the second adds the fourth:

| Ordered clause | Pattern behavior | Body result |
| --- | --- | ---: |
| 1 | Reference currently contains true; ignore second component. | 0 |
| 2 | Reference currently contains false; force second component and match its result against0. | 1 |
| 3 | Reference currently contains false; ignore second component. | 2 |
| 4, only in the second listing | Reference currently contains true; ignore second component. | 3 |

The supplied input has an initially false reference r and a suspension whose
body assigns true to r and returns1. The required source calculation is:

1. Clause1 fails on the initially false reference without forcing the suspension.
2. Clause2's reference part succeeds. Forcing then assigns true, returns1 and
   caches that value. Matching1 against the inner0 fails.
3. Clause3 sees the changed reference, so it fails. The three-clause function
   is non-exhaustive on this input; the inherited function-match semantics
   determines its exceptional no-clause result.
4. In the four-clause listing, clause4 now succeeds and returns3. It is reachable
   despite its apparent syntactic overlap with clause1. [T132]

The match must preserve changed memory after FAIL, while discarding only the
failed clause's tentative bindings as required by the base matching rules.
Restarting each alternative from the original memory, caching only after
complete pattern success, or treating the second function's fourth clause as
redundant would change these examples. They are source semantic obligations,
not merely warnings in a convenient static checker.

The current requirements already demand actual execution of these two cases.
This pass did not run them or revalidate any retained implementation theorem.
The inherited notes identify the no-clause exception as Match; this inventory
does not claim a fresh inspection of that base Definition rule.

## 7. A.3: every dynamic rule and its execution order

### 7.1 Finite memory and suspension creation

Definition§6.3, p47/Figure13, is extended with thunks `(expression, environment)`
and finite memory from addresses to either values or thunks. References and
suspensions use the **same address/memory universe**: a reference cell contains
a value; a suspension cell can contain its captured thunk or a memoized value.
These are the source representation intentions, with the static-safety caveat
in §2 above. A target representation with tags or multiple maps needs a stated
relation to this shared-address model. [T133]

The creation rule at Definition§6.7, pp52,55,56 has one freshness premise:
the chosen address is outside the current memory domain. Its conclusion
returns that address and extends the state with the current expression and
current lexical environment. It **does not evaluate the expression**.

Proposed obligations are freshness, correct capture, unchanged old cells and
other state components, and no body event at creation. An allocation strategy
choosing a particular fresh address is a realization of the rule, not a rule
that the source itself selects consecutive addresses. Independent creations
remain different cells; aliases of one address share its eventual cache.
Creating an outer suspension does not execute an inner dollar expression in
its body. [T133]

### 7.2 Pattern and pattern-row outcomes

The source extends pattern and pattern-row result signatures to admit an
exception packet in addition to successful variable bindings and FAIL.
The abbreviated displayed signatures omit state parameters, but the actual
forcing/reference inference rules explicitly carry state. Read them together;
they do not license a state-free interpretation of effectful patterns.
[T133]

The inherited exception convention supplies propagation when a premise raises.
Do not interpret the absence of an explicit exceptional conclusion under each
displayed inference bar as a ban on that outcome. Match failure, a raised
packet, an unsupported/stuck raw configuration, and failure to find a finite
evaluation are different observations. Fuel exhaustion is not a source
exception or a proof of divergence; this is already required in local10014.

### 7.3 Cache-hit rule

If address a currently contains a value v, matching it against `$pat` matches
v against pat in the **current matching environment** and returns the inner
match's outcome and resulting state. No old body is evaluated or newly
memoized by that outer hit. [T133]

A hit does not imply the whole match is effect-free: pat may itself contain
reference or suspension patterns. It may fail, raise, or force another
suspension. Preserve its demanded computations and state changes. Distinguish
skipping the target's body from doing no work at all.

### 7.4 Unevaluated-body rule

If a contains thunk `(e,E_capture)`, the printed rule orders these actions:

1. Evaluate e in `E_capture` using the current state, obtaining normal value v
   and body-result state s1.
2. Write v at a **in s1**, retaining the other effects and allocations of the body.
3. Match v against pat in the caller's **current** matching environment,
   starting from that updated state.
4. Return the inner match's bindings/FAIL and resulting state; apply the
   exception convention if that later match raises. [T133]

The body and pattern environments are intentionally different. Installing
the value in the original pre-body state would discard actual effects.
Installing it after the inner match would incorrectly lose successful
memoization on pattern failure. The store update is not conditional on the
cell still being a thunk: reentrant evaluation may have written it already.
This last point is essential to the p135 overwrite remark.

After an inner FAIL or exception, the prior successful cache-write event is
not rolled back. That does not assert that arbitrary later matching effects
can never update the same cell again; the rule returns the state actually
reached. The requirements' retention language must be read as state threading,
not as a universal final-cell immutability theorem.

### 7.5 Modified reference-pattern Rule158

The rule looks up the reference value, matches that value against its atomic
subpattern with state, and returns the resulting state. The change explicitly
permits effects caused by matching. Nested patterns and failed alternatives
must therefore use the appropriate current state, not a pre-match snapshot.
Its base locator is Definition§6.7, p56. [T133]

### 7.6 Exceptional bodies, retries and the third code listing

The p134 remark uses the inherited exception convention: an exception escaping
a suspension body aborts that forcing frame before its normal cache-write
step. It does not memoize the exception as a successful value, and does not
roll back side effects. If the target remains a thunk, a later attempt can
evaluate it again and repeat effects. The next attempt need not have an
identical trace or outcome, because prior effects may change its inputs.

There are two essential qualifications:

- The body may already have triggered an inner successful write to the same
  address. Skipping the outer write does not restore the old thunk or remove
  that inner result.
- An exception during the inner pattern, after normal body completion, occurs
  **after** the cache write. It is not the earlier body-exception case.

An exception caught inside the body can still lead to a normal value and
successful memoization. An exception caught outside after the memoize frame
has unwound can permit a fresh attempt. This distinction is needed by the
conditional body-entry requirements. [T133–135]

Exception caching is discussed as a reasonable alternative, but is not adopted.
Changing to it would alter the retry/effect examples and require a separately
identified semantic policy and proofs.

The initial dynamic basis (Definition AppendixD, pp77,79) receives the third
and final code listing in this thesis appendix:

    fun force ($x) = x

This is a derived ordinary function using the suspension pattern, not an
additional primitive with independent operational rules. Its caller's argument
expression is still evaluated by the strict base language. Prove its value,
exception and state behavior through the supplied matching rules. A
force-after-delay equivalence needs an observation that accounts for the fresh
private suspension and extra work; it is not literal equality of all memory
or resource traces. [T134; existing foundation correspondence obligation]

## 8. A.4: restricted recursion, Rec/SRec and self-forcing

### 8.1 Recursive binding syntax and modified Rule137

Definition§2.9, p9, is relaxed specifically to allow a recursive value binding
whose right side has the form `var = $ exp`. It does not permit every possible
recursive expression. The inherited recursive function forms remain relevant.
[T134]

Modified Rule137, at Definition§6.7 p54, has these stages:

    evaluate valbind in (s,E) -> (VE,s1)
    VE1 = Rec(VE)
    s2 = SRec(VE1,s1)
    return (VE1,s2) for rec valbind

The original Rec operation for functions is still used; SRec is an additional
state operation for suspension environments. Preserve the order, mutual group
bindings and inherited context restrictions. Neither an unproved fixed-point
axiom nor an arbitrary cyclic heap substituted for the actual binding rule
supplies this correspondence.

### 8.2 All four SRec clauses and their domain

For SRec(VE,s), the source specifies:

| Clause | Exact obligation |
| --- | --- |
| Exception-name state | `ens` is unchanged. |
| Memory domain | The set of allocated addresses is unchanged. |
| Outside the binding range | If a is not in Ran(VE), its cell is unchanged. |
| Relevant thunk | If a is in Ran(VE) and its cell is `(e,E)`, replace that cell by `(e,E+VE)`. |

The affected range is the addresses that occur as bound values in VE, not
every address reachable through every closure or nested environment. The
body expression is unchanged; its captured environment is extended with the
recursive bindings. This is a mutation of existing thunk cells, not fresh
allocation. It can tie cycles through addresses, so immutable backward-pointer
or whole-memory `Extends` invariants do not apply to it. [T134]

The p135 paragraph supplies the domain justification for the missing case:
in the valid recursive-binding situation, an address in the range has not
already been forced and still contains a thunk. Prove this from the permitted
binding construction. Do not apply that premise to arbitrary externally
supplied environments and states. A total target operation may choose behavior
outside this domain, but source correspondence must identify the valid domain
rather than claiming the four clauses specify every raw input.

### 8.3 Effectful recursive reentry and overwrite

The p135 remark explicitly allows a body to force its own still-pending
suspension. An inner evaluation can return and write a value; the outer
evaluation can later overwrite it with a different result. The ordinary
successful-write rule performs that second write even though the inner force
has changed the cell. No implicit Busy/blackhole marker prevents it.

The previously recorded source-derived discriminator uses an initially false
reference gate. Its recursive body's false branch sets the gate true and
returns `force(self)+1`; its true branch returns7. The predicted sequence is
inner write7, outer write8, later hit8. A variant that forces self and then
raises instead of adding one retains the inner write7, adds no outer write,
and permits a later hit7. These are derived cases explaining the supplied
rules, not additional programs printed in this appendix or newly run tests.
[T133–135; retained foundation inventory]

The second case is especially important: an outer exceptional force does not
imply that the target is still a thunk. A blanket rollback or retry theorem
would contradict the rule ordering and this permitted reentrant behavior.

### 8.4 Pure self-entry claim and optional blackholing

The same paragraph states that self-forcing does not terminate without side
effects. This is a substantive qualitative source claim, already isolated as
`TU.A.4.PURE` /local10019. A suitable formulation excludes finite completion
after an **actual body entry at an already pending suspension address**, in a
properly delimited pure source domain.

The domain must constrain primitive behavior, references, exception/name
effects, captured environments and returned values sufficiently for the
argument. It must also support the intended recursive functional constructions.
Merely assuming nonreentry, excluding every recursive suspension syntactically,
or proving a literal-only toy calculus would not discharge the stated scope.
The theorem must use the actual evaluator/finite-execution relation; bounded
search failure is not a proof of nontermination. [T135; local10019]

This claim does **not** forbid sequential retry after a frame has unwound.
For example, in a context with a fixed exception packet, a delayed raising
body can be forced, handled outside, and forced again without a successful
write. Such a finite pure overall computation is compatible with the absence
of active self-reentry. This is why local10022 retains a separate no-unwind
premise for body-entry uniqueness.

Blackholing [Jon92] is mentioned as an optional technique to detect circular
suspensions and ensure a single memoization. It is not specified as the
default transition system; no detailed blackhole algorithm, exception choice,
concurrent protocol or proof is supplied. Preserve its alternative-policy
classification. Do not implement it silently to make an at-most-once theorem
easier. [T135]

## 9. Required observation distinctions and compatibility crosswalk

The following counts are proposed distinguishing expectations about source
body-entry and successful-write events, not fresh executions or validated
machine step counts from this task.

| Scenario at a named suspension address | Body entries / successful writes | Essential qualification |
| --- | --- | --- |
| Never forced | 0 /0 | Creation still allocates a thunk. |
| Ordinary successful first force followed by cache reuse | 1 /1 | Later inner pattern work is separate. |
| Two independent creations of identical code | One per demanded cell | Their addresses and caches remain distinct. |
| Body returns normally, requested inner pattern then FAILs | 1 /1 for that body | Failure does not undo the earlier cache write. |
| Body returns normally, later inner matching raises | Successful write has occurred | Propagate the later exception and state; account separately for nested bodies. |
| Nonreentrant raising body, handled outside and retried once | 2 /0 | The whole program may return normally; purity alone does not rule it out. |
| Exception caught inside body, which then returns normally | Can be 1 /1 | A blanket prohibition on exceptions is stronger than the needed no-unwind condition. |
| Effectful inner success followed by outer success | 2 /2 at the same address | Outer write can overwrite the inner value. |
| Effectful inner success followed by outer body exception | 2 /1 at the same address | Later force can hit the retained inner value. |
| Admitted pure actual self-body-entry | No finite completion under the intended theorem | A claim to prove, not an assumed generic machine rule. |

Successful-write uniqueness cannot alone prove unique body entry: aborted
attempts have no write. Unique body entry cannot by itself prove bounded work
inside the body. Fresh allocation, cache hits, forcing attempts, pattern work,
body entries, writes and primitive work are distinct observations. No abstract
debit label should identify unrelated fresh cells merely because their code
or eventual values agree.

| Current requirement family | Source reconciliation result |
| --- | --- |
| Chapter2 /10002 and shared immutable persistence /10013 | No new contradiction. These contracts concern their represented immutable lists/trees and actual sharing, not all AppendixA memory transitions. Fresh allocation can reuse heap-extension laws; memoization and SRec need their separate mutable contracts. |
| Suspension foundation /10014 §§1–2 | Syntax/static rules, captured thunks, shared address universe and freshness agree with pp131–133. Retain the exact inherited1990 boundary and known static-safety caveat. |
| /10014 §§3–5 | Separate stateful outcomes, pre-pattern cache write, frame-local exceptional unwinding, ordered alternatives and reference patterns agree with pp132–134. |
| /10014 §§6–9 | Restricted recursive bindings, Rec/SRec, effects, reentrant overwrite and derived force agree with pp134–135; finite correspondence and chosen observation remain necessary proofs. |
| Pure recursive forcing /10019 | Precisely owns the p135 qualitative pure-domain claim, without changing unrestricted effectful semantics. |
| Pure cache-write accounting /10020 | A separate consequence under finite admitted pure execution; the p135 effectful two-write case prevents a universal raw claim. This pass does not adopt a candidate's completion or acceptance status. |
| Conditional body-entry accounting /10022 | The extra actual no-memoize-unwind premise correctly distinguishes retry from self-reentry. Neither normal overall return nor successful-write uniqueness supplies it. |
| Persistent debit/source connection /TU.TRACE and owning algorithms | The appendix supplies execution distinctions, not the entire cost correspondence, body-work bound or every algorithm's debit account. |

These are source compatibility findings only. No candidate implementation was
audited or compiled here, and no requirement was weakened to match a convenient
model. The coordinator retains validation, review, implementation sequencing
and acceptance authority.

## 10. Bibliography: complete accounting without importing external work

All107 entries were read, including titles, source identities and backward
page references. The per-page accounting below records the complete span
without reproducing the bibliography as a second manuscript.

| Printed / PDF | Entries | First and last keys on that page |
| --- | ---: | --- |
| 137 /149 | 9 | Ada93 … BJdM96 |
| 138 /150 | 12 | Blu86 … CMP88 |
| 139 /151 | 11 | DGST88 … FSST86 |
| 140 /152 | 13 | FT87 … Hoo82 |
| 141 /153 | 13 | Hoo92a … Knu73 |
| 142 /154 | 13 | KT95 … Mye84 |
| 143 /155 | 12 | Oka95a … PPN96 |
| 144 /156 | 14 | Ram92 … Tar83 |
| 145 /157 | 10 | Tar85 … WV86 |
| 146 /158 | 0 | Header only. |

Bibliographic strings such as `AFM+95`, `H+92`, `P+96` and `W+90` can acquire
spaces in text extraction. They denote citation keys, not mathematical rules.
Historical URLs and labels such as "to appear" or "draft revision" are part
of the1996 source record, not fresh claims about present publication status.

The endmatter's directly relevant external dependencies/context are:

| Key and thesis bibliography page | Relevance and limit |
| --- | --- |
| MTH90, p142 | Milner/Tofte/Harper, *The Definition of Standard ML*, MIT Press1990. This is the semantic base named by AppendixA. Its inherited rules need the already delimited core correspondence; its citation does not silently request a full compiler or all language features. |
| Jon92, p141 | Richard Jones, *Tail recursion without space leaks*. Pointer for the optional blackhole technique, not supplied default suspension behavior. |
| BJdM96, p137; Pip96, p143 | Restricted lazy-versus-strict comparison cited in §9.1. No separation proof or new algorithm supplied in the thesis endmatter. |
| DSST89 and Die89, p139 | External persistence transformations discussed in §9.2. Preserve comparative context without importing their entire algorithms into the union ledger. |
| BO96, p138; Jon95, p141; MT94, p142 | Heap bootstrapping, constructor classes and higher-order functor context. The private-communication construction in §9.3 is not an included listing. |
| P+96, p143 | Haskell1.3 report used for the historical polymorphic-recursion recommendation. It is not the book's Haskell appendix and is not a fresh language-version recommendation. |
| Wad87, p145; BC93, p137; PPN96, p143 | Views and abstract-data-type pattern matching, cited as design alternatives. No complete views mechanism is supplied here. |
| FWFD88, p140 | Abstract continuations/control-structure application pointer. No new control-language implementation supplied. |
| KT95 /KT96a, p142 | Catenation comparisons; KT96a is explicitly listed as an August1996 draft revision of KT95. Their cited worst-case designs are not reproduced by the endmatter. |

The other entries similarly supply provenance/navigation for material owned
by the earlier chapters. Reading a citation entry does not mean its external
contents were inspected or its theorem proved. A cited paper can be a genuine
premise or further source for an explicitly identified sketch, but that must
be recorded by the owning construction rather than treating every title as
an automatically supplied algorithm obligation.

## 11. Index accounting and source limits

The entire index, pp147–150/PDF159–162, was text-read. Its first and last pages
were visually checked for actual boundaries and two-column layout. It contains
term, operation, structure/functor, signature, person and cross-reference
entries. No new code, inference rule, theorem, exercise or solved open problem
appears there.

Useful navigation checks include dollar notation's formal definition at131–135;
blackhole at135; exhaustive/irredundant patterns at132; exceptions at134;
recursive suspensions at134; empirical measurements/open problems at130;
polymorphic recursion and recursive modules at129; and the earlier algorithm
figures. Index page references are locators, not independent semantic premises
or a guarantee that every source occurrence is indexed.

The index retains both output-restricted deque locations (53 and115), the
input-restricted deque at115, the random-access queue remark at114, segmented
binomial material, and both catenable-deque functors. These support the existing
union navigation and the earlier source inventories; they do not merge those
distinct constructions or close any of their proofs.

The final page includes S–W entries, including scheduling, both skew structures,
streams, strict evaluation, structural abstraction/decomposition, suspensions,
unary/uniform representations, versions/views and worst-case benefits. It is
not a blank termination page. The PDF ends there; no further supplied appendix
or algorithm listing remains after this range.

## 12. Remaining proof obligations and frozen handoff

All supplied appendix rule groups have been accounted for above. The remaining
work is their actual formal realization, valid-domain/static correspondence,
execution and observation proofs, and the separately delimited pure/resource
consequences under the existing owners. In particular, preserve:

- Source syntax and the inherited1990 static semantics, including the known
  distinction between faithfully modeling the extension and proving safety.
- Fresh creation versus memoization versus SRec environment mutation.
- Captured body environment versus current matching environment.
- Normal body return before cache write before inner match; retained state on
  FAIL or exception; no rollback and no default exception caching.
- SRec's exact range/footprint and the valid-binding justification for unforced
  relevant cells; unrestricted reentrant effects and both overwrite cases.
- A proved pure-domain finite-self-entry result, separate successful-write and
  conditional body-entry laws, and actual body-work costs for later algorithms.
- The conclusions' historical/empirical judgments and open questions as such,
  without invented solutions or external algorithm imports.

No uninspected semantic subpart remains within the assigned thesis endmatter
range. That statement concerns **source reading**, not proof completion,
full-thesis implementation, book coverage or integration acceptance.

The only durable file authored in this task is
`session/research/thesis-endmatter-source-inventory-045.md`. The Chapter8
inventory remains immutable at SHA256
`ece3513b6c6f7fdb431a9507701e88e471fec3f1fbb422333c95cd3b4671967e`.
Final writing was held during checkpoint050 capture and released by the
coordinator afterwards. Intermediates remain outside `session`; the coordinator
owns checkpoint inclusion. No Lean/compiler/test, source/ref/runtime/controller,
requirements/tracker edit, process-control action or new agent was used.
All proposed proof obligations remain **unproved**.
