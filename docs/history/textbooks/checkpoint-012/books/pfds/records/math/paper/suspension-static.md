# Suspension static implementation record — local #10014

Status: this assigned implementation and its focused checks are complete.
Static, Names, Grammar and both client modules have passed. SUSP-STAT-001 is
now a checked counterexample in the encoded 1990 core with Appendix A's
extension: the exact shared Boolean-typed expression has a finite run returning
integer0. Parent owns integration, checkpoints, exact-candidate validation and
independent reviews; no project acceptance is claimed here.
This worker owns Static.lean, Names.lean, Grammar.lean and their two client
examples, plus this report. No Git index/ref/config changes are made by the worker.

## Source boundary and expected cases

The inherited-rule audit is `suspension-base-core.md`. This is a bounded 1990
core fragment plus the Appendix A extension, not a complete SML elaborator.
The book's derived lazy function is a separately identified addition. Type
variables have independent equality and imperative flags. All closed types
are imperative; references admit equality independently of payload, whereas
functions, exceptions and suspensions do not admit equality. Every suspension
expression is non-expansive. Expansive bindings still generalize fresh
applicative variables, so a modern blanket value restriction would change the
source rules.

The first client is SUSP-STAT-001: the exact public expression
`Examples.SuspensionMachine.cachedReference`, shared with the runtime worker.
Its delayed reference to an identity function is closed at a fresh imperative
variable. The two uses instantiate that variable by integer and Boolean types.
The assignment stores a constant integer-returning function, and the final
Boolean-typed expression returns integer zero in the operational witness.
Both derivation and run are now Lean checked and joined in
`Examples.SuspensionStatic.cached_reference_type_mismatch`. Its conclusion
contains the actual finite execution of that same expression, the returned
integer atom, and its static atom type's inequality with boolean. The result
is scoped to this source-specific core; no global preservation/type-safety
claim is assumed.

Additional clients distinguish expansive applicative generalization from
imperative non-generalization; reject suspension equality while permitting
reference-to-suspension equality; and exercise generic force and hygienic lazy
function types; their complete module passed in r8.

## Design and statement checks

Static environments reuse Mathlib.Finmap so shadowed schemes contribute no free
type variables. Binding status distinguishes variables from monomorphic
exception constructors. Value-pattern typing must reject binding an active
exception identifier as an ordinary variable. The separate namespace adapter
is root-owned; raw unclassified flat-name syntax is not claimed to be SML.

`Names` computes a conservative set of all environment names, including bound
names and exception-pattern lookups. It is not named or claimed to be an exact
free-variable set. Lazy-function typing must preserve ambient type variables;
a fresh term binder alone does not justify polymorphic weakening, because its
monotype can otherwise change Clos. The proved sufficient condition places
input-type variables in the persistent ambient type-variable context.

## Judgment boundary and source correspondence

The checked core provides `PatternHasType`, `PatternFieldsHaveType`,
`HasType`, `ClausesHaveType`, `FieldsHaveType`, and
`RecursiveBindingsHaveType`. Pattern bindings contain monotypes. The recursive
rule fixes the complete monotype environment from the group domain before any
RHS is checked; each RHS must satisfy Core.RecursiveRhs and is closed relative
to the original context. Duplicate group names and record labels are excluded,
and field pattern environments are disjoint. These conditions are source
restrictions, not global invariants assumed about raw machine inputs.

The source boundary omits modules, type/datatype declarations, open rows and
explicit type annotation syntax. A value binding has the source U=∅ form;
scoped variables already present in Context.ambient remain available. Record
type lists choose a representation of the finite source row; no complete
row-equivalence inference algorithm is claimed. Basis/datatype signatures and
admitted equality type names remain explicit parameters. Constructor patterns
without arguments require a named result type, preserving Rule36's restriction
rather than admitting an unapplied unary constructor as a function pattern.
Reference patterns retain the imperative payload restriction induced by the
1990 ref scheme. Exception payload types are monomorphic and imperative.

`forceFunction_type` and `force_type` quantify over every representable payload
and context, subject to the generated binder0 being allowed as a variable.
This is automatic in the root's separated even-variable/odd-exception encoding;
it is also directly discharged by the concrete exception-free counterexample.
It is not silently assumed for arbitrary flat-name contexts.

The checked lazy-function theorem transports original clause typing under
a fresh monomorphic parameter binding. Freshness includes exception-pattern
lookups and bound names. Requiring input-type variables to lie in the persistent
ambient context ensures this extension does not change the exact Clos decision,
even inside a clause where a pre-existing ordinary binding is shadowed.

## Development evidence so far

- r1: Static target exited1 after140s. Problems were reserved `variable` syntax,
  an excess termination parameter and a termination tactic invoked after all
  goals were closed. The finite-context and generalization portion elaborated.
  These are development errors, not source counterexamples or acceptance.
- r2: corrected Static plus Names target checks are queued under the shared
  focused lock. They run sequentially, with each compilation input frozen.
- The draft client now contains `cachedReference_boolean` for the exact public
  runtime term and `cached_reference_type_mismatch` connecting it to the actual
  returned integer atom. Both still await compiler confirmation.

- r2 terminated with the documented Static equation/type-ascription issues and
  only redundant termination-tactic lint in Names. No judgment rule or expected
  source conclusion was changed. Both module inputs were frozen for that run.
- The corrections are applied, and the generic static transport/lazy-function
  tranche is now persisted in Static.lean. It proves context free-variable
  stability, conservative pattern-binding support, transport of all represented
  typing judgments, and lazyFunction_type/lazyFunction_fresh_type under the
  stated ambient-variable and freshness conditions. These new proofs await
  their first compiler pass; the wording here describes intended statements,
  not accepted evidence.
- Static examples now include an arbitrary-payload force scheme instance, a lazy
  function at an open scoped input type, and a concrete comparison showing the
  generalization decision changes when that scope condition is omitted.

## Surface-grammar addition (parent-assigned requirement1 follow-up)

AppendixA printedp131 was visually rechecked: exact-dollar reservation and both
lowest-precedence productions are required. SML90 §2.4 PDF14–16 (printed4–6)
provides the inherited symbolic-identifier alphabet and occurrence
classification. The longer spelling `$+` remains an inherited symbolic
identifier; the extension reserves only `$`. SML90 §2.5 keeps longest-item
lexing, so the adapter makes no claim that adjacent `$$` becomes two dollar
tokens. Its clients start from explicit prelexed sequences.

Grammar.lean is a source-specific derivation/embedding layer. Identifier tokens
carry the inherited membership proof, exact-dollar exclusion and preclassified
Var/Con/ExCon role. Atomic/application/full expression categories and
atomic/higher/full pattern categories place dollar only at the full level.
Already delimited inherited atomic/full phrases have opaque parameter types
and explicit Core embeddings. They cannot consume an arbitrary token span;
lexing and the internal recognition of those phrases are outside this adapter.
The layer does not claim complete parsing or elaboration of Standard ML.

Expected connected cases are `$f x` → delay(apply(f,x)), `f ($x)` →
apply(f,delay(x)), `$C x` → suspended(constructor(C,x)), and `C ($x)` →
constructor(C,suspended(x)). The generic leading-dollar inversion theorems
exclude the wrong outer application/constructor trees. The exact-reservation
client admits `$` in its inherited alphabet, excludes it from extension
identifiers, and retains `$+`. All are drafted and awaiting focused checking.

- Static r3 ended before compiling Static: Names still needed arithmetic after
  simplifying several mutual-recursion measures. The correction separates the
  simplification pass from the arithmetic pass; already-solved option helper
  obligations retain only simplification. It changes no traversal definition.
- Grammar r1 took50s and reported only the accidentally reserved Lean binder
  `prefix`. It has been renamed without changing any grammar rule or statement.
- Parent approved and the draft now includes Signature.ScopedIn: any free
  variables in supplied primitive/constructor schemes must be in ambient scope.
  Both concrete signatures discharge this obligation. Context extension retains
  it. This prevents the source closure calculation from overlooking an open
  signature's variables; no arbitrary raw-signature source claim is made.

- r4: Names passed (697 jobs,8.8s). Its API and definitions are stable and are
  available to the dynamic derived-form worker. The generic grammar was blocked
  only by mutual-inductive structural-recursion inference, now replaced by an
  explicit token-length decrease using the atomic argument's nonempty witness.
- Static r4 reached the new transport proofs. Remaining errors were a reserved
  Lean binder `scoped`, the renamed Finset.notMem_union API, implicit constructor
  parameter counts, and one dependent recursive proof now expressed as ordinary
  list induction. The earlier attribute/scheme/Clos/context/typing definitions,
  substitution identity and force proofs had no new local errors. No acceptance
  follows from that partial feedback; the full module still must pass.
- Machine worker r5 checked all17 actual runtime cases, including the exact
  integer0 result and shared-reference/cache counts for SUSP-STAT-001. The static
  half and combined theorem are still pending.

## Public statement review before the next focused pass

The r5 inputs retain the intended conclusions. This pass is queued under the
shared lock; it checks the grammar client, the static module, and (only if that
module succeeds) the connected static/runtime client. No current claim of
static completion or project acceptance follows from being queued.

| Public claim | Intended mathematical content and boundary |
| --- | --- |
| `Scheme.Instantiates` | One simultaneous replacement fixes all unquantified variables; quantified equality and imperative attributes impose independent conditions. It does not recursively substitute inside a replacement. |
| `mem_generalize`, `generalize_delay` | The 1990 Clos decision is the actual quantified-variable set, with the ambient/context variables excluded. A delay uses all remaining type variables, including imperative ones. |
| `Signature.ScopedIn` | The source context must account for free variables in the externally supplied basis/datatype schemes. The concrete machine and empty signatures are closed; their clients prove this condition. Raw signatures without this condition are not claimed to represent an entire source basis. |
| `PatternHasType.bound_names` | Every variable introduced by the pattern lies in the conservative syntactic name set. That set also contains exception-constructor lookup names and bound names; it is not an exact free-variable analysis. |
| `HasType.weaken` and its mutual companions | Adding an unused term binding preserves the same typing conclusion when the binding is fresh in the finite context and syntax and its type variables already belong to persistent ambient scope. This premise keeps Clos unchanged even below later shadowing. |
| `forceFunction_type`, `force_type` | Every representable payload is admitted without equality/imperative restriction. The fixed generated binder0 must be allowed as a variable in the context; arbitrary exception-classified raw contexts are not silently accepted. |
| `lazyFunction_type`, `lazyFunction_fresh_type` | The book's expansion has input→suspension-result type when the original nonempty clauses have suspension-result type and the freshness/scope conditions hold. These are typing theorems; they do not erase the captured extra parameter binding from arbitrary returned runtime closures. |
| `expression_dollar_iff`, `pattern_dollar_iff` | A leading dollar in the explicit prelexed sequence forces the outer delay/suspended AST constructor and consumes the whole following full category. Opaque inherited phrases are already delimited tokens with specified embeddings. |

The concrete cached-reference calculation uses one imperative variable with no
equality requirement. The identity function has type α→α, so reference creation
requires this α to be imperative. The delay makes the enclosing expression
non-expansive, and closing its otherwise empty context quantifies α. Both int
and bool are closed imperative instantiations. Consequently the first force
can produce an int→int reference and accept a constant-integer function, while
the second force can give the very same suspension binding the bool→bool
reference instance. The final application is therefore assigned bool. The
already checked machine result is integer0. The proposed combined theorem
mentions the exact shared `cachedReference` expression and its actual finite
execution; it does not assume a global source preservation theorem.

The attribute/Clos example for an expansive expression with an applicative
variable is a calculation of the closure operation, not a claim that reference
allocation at that applicative monotype is well typed. The typed counterexample
uses the imperative variable and discharges the reference rule's side condition.
The open-input lazy-function case quantifies over both attribute bits and
actually places the variable in ambient scope. A companion case computes the
different closure sets when this scope premise is omitted.

All source statements above refer to the audited official 1990 Definition
§§4.4, 4.7–4.8 and the corresponding core rules, plus thesis Appendix A's static
changes. In particular they do not replace the published closure rule with the
later blanket value restriction, and they make no full Standard ML elaboration
or global type-safety claim.

- r5 terminated with the same statements: Grammar's decrease was solved by
  simplification and only the unnecessarySimpa linter rejected the redundant
  proof suffix. Static's remaining diagnostics were exclusively termination
  measures in the dependent weakening proofs. The attribute, instantiation,
  Clos, context, judgment, force and finite-domain proofs produced no local
  errors in that pass. The final static client was skipped as intended because
  its prerequisite module did not succeed.
- The weakening proof now requests structural recursion on the supplied typing
  derivation, which is the proof's actual induction argument. This replaces
  proxy syntax-size measures whose dependent indices were not identified in
  the generated termination goals. No typing rule, theorem premise, result,
  or expected concrete conclusion is changed; compiler confirmation is pending.
- The grammar boundary now explicitly reserves its ordinary constructor tags
  for datatype constructors. Source reference forms (including the special
  `ref` constructor) must use the already-delimited inherited categories;
  these tags do not secretly denote allocation. The exception constructor
  production's Nat is an environment identifier, not a generated exception
  identity. The concrete f/x/C dollar-precedence cases are unchanged.

- r6 finished at2026-11-02 19:23:35 UTC with exit1 and every tracked input
  unchanged. The pinned compiler rejected structural recursion in both
  weakening groups because it could not eliminate the direct recursive calls
  in this tactic form. Grammar.lean passed (101s); its first example pass found
  only five failures to synthesize Decidable for the opaque base.identifier
  projection. The static client was again correctly skipped after its module
  prerequisite failed. Detailed terminal data and hashes are recorded in
  active-validation/suspension-static-r6.json and its matching log.
- After checkpoint015 preserved those exact draft bytes, the next correction
  explicitly retains an equation between each original measured syntax index
  and the index refined by dependent case analysis. Substituting those local
  equations before the existing size calculation is proof bookkeeping, not an
  added source premise. Both mutual groups retain their original public typing
  transport statements. The grammar client now unfolds its concrete finite
  identifier predicate for membership proofs; its lexicon, roles, derivations,
  and expected ASTs are unchanged. These corrections await r7.

- r7 finished at2026-11-02 19:40:59 UTC, with tracked inputs unchanged=True.
  Applications.Suspensions.Static passed (745 jobs; module40s), including every
  mutual context-transport proof and both hygienic lazy-function typing
  theorems. The explicit syntax-index equations resolved the termination
  bookkeeping without changing the statements. Examples.SuspensionGrammar
  passed (504 jobs; client51s), so all dollar-precedence and exact-reservation
  clients are now checked. No proposed module split was needed or performed.
- The first complete Static client pass found exactly two remaining goals in
  the expansive Clos calculation cases: equality of a type variable to its
  displayed record must imply equality of its imperative flag. The next edit
  applies congrArg TyVar.imperative to those equalities. The lexicon, programs,
  typing rules, theorem statements and expected results are unchanged. All
  other Static client declarations, including the exact cachedReference
  Boolean-type/runtime-integer connection and the open-input lazy-function
  specialization, reported no local errors; the whole client still awaits its
  successful r8 check before those results are marked checked.
- The stable green Static source hash is
  bf876df55c0686f49e3cc16fdee3912ce2faac238e0e0ca2ba42af42fc365659.
  Names remains at its earlier green hash
  267803f09543b11acc9d1c305be76fb675351e001d0588dd8d290b17d590b31c.
  Grammar's source/client hashes are respectively
  258f4248a4bd5235b5e2a5c0e82e6c274794910abc5e7934974424e71fc10939 and
  3d5f484433881aa91ed27cfa58c191f8da040cd8afd40047b8b3ff08fcdf2920.
  Full command, target status and hash evidence remain in the r7 JSON/log.

## Completed focused handoff

r8 ran the single remaining target Examples.SuspensionStatic through the pinned
offline Nix shell with LEAN_NUM_THREADS=1, under the shared focused-build lock.
It ended at2026-11-02 19:50:57 UTC with exit0 (775 jobs; client104s), and all
tracked input hashes were unchanged. Its terminal evidence is
active-validation/suspension-static-r8.json and the matching log. The final
Static client hash is
5b095742ee31199f46c8045ef2bab6f116fe5b3e61e238a34841672e6dcb8bdf.
The core and Grammar hashes listed above remain unchanged.

The retained public contracts include the following:

- Type-variable equality and imperative attributes, simultaneous
  attribute-preserving scheme instantiation, the exact non-expansive/expansive
  Clos partition, and the suspension non-expansiveness/equality exclusions.
- Concrete pattern/expression/ordered-clause/record/recursive-binding typing
  judgments for the stated source fragment. The recursive monotype domain is
  checked; closure uses the original context; variable patterns cannot create
  a hole in an active exception identifier's classification.
- Conservative syntactic name support and a computable fresh-name choice,
  including exception-pattern lookup dependencies. Context transport retains
  the explicit ambient-type-variable and freshness assumptions needed for the
  same closure calculation.
- `forceFunction_type`, `force_type`, `lazyFunction_type`, and
  `lazyFunction_fresh_type`, with the stated fixed-force-name condition and
  hygienic open-input specialization. The force scheme has an arbitrary-payload
  instantiation case; the lazy-function case uses a genuinely open input type
  with either combination of type-variable attributes.
- The exact reserved dollar word and leading-dollar inversion at both full
  expression and pattern levels. Checked clients distinguish `$f x` from
  `f ($x)` and `$C x` from `C ($x)`, reject the wrong outer ASTs, and retain the
  distinct longer symbolic identifier `$+`.
- The connected SUSP-STAT-001 static/runtime theorem, using the shared runtime
  expression unchanged. The concrete primitive signature is closed and its
  ScopedIn condition is separately checked; the expression uses no primitive
  calls. The runtime witness also retains its independently checked shared
  reference/cache observations in Examples.SuspensionMachine.

No declaration or expected conclusion was weakened to obtain green. No new
axiom, sorry/admit proof hole, resource-limit override or linter suppression was
added to these files. The prototype's explicit source boundaries remain in
force: it is not a complete Standard ML elaborator/parser, arbitrary raw
signatures or name classifications are not asserted to be source-valid, and
no global runtime store-typing/preservation theorem is assumed. Ordinary
datatype-constructor grammar tokens do not represent the special ref allocator.

The source footprint is unchanged: Applications/Suspensions/{Static,Names,Grammar}.lean
and Examples/{SuspensionStatic,SuspensionGrammar}.lean. The conditional proposal
to split a separate hygiene module was not needed and was not performed.
Parent still owns the public entrypoint, commit, exact-candidate build/proof
audit, independent reviews and durability checkpoint. These focused results
do not constitute that broader acceptance.
