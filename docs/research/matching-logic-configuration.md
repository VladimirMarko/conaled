# Two-sort configuration patterns

Issue [#503](https://github.com/VladimirMarko/conaled/issues/503) implements the
bounded experiment from the [accepted study](matching-logic-bounded-fragment.md).
The native relation client remains independent of the pattern language.

## Source and adequacy

The reference is Grigore Roșu, *Matching Logic*, LMCS 13(4:28), published
2017-12-20, DOI `10.23638/LMCS-13(4:28)2017`:
[journal record](https://lmcs.episciences.org/4153) and
[61-page PDF](https://lmcs.episciences.org/4153/pdf). The PDF retrieved again for
this implementation has SHA-256
`d32b87b3c0354aa31bf9c6388185f1e7a49edf77cd5ddacb810bee2886f296a3`, matching the
accepted study. The 65-page author draft is not the pinned source.

Definitions 2.1–2.3 give sorted patterns and powerset semantics. Assumption 5.1
and Sections 5.1–5.3 give definedness, whole-pattern equality and membership.
Corollary 5.23 treats term substitution. Figure 5, printed page 53, supplies
the selected rules; Theorem 11.2 on page 55 proves soundness and completeness
of the paper's full system. This implementation proves soundness of a subset.
It neither imports nor reconstructs that completeness theorem.

The embedding account is sort preserving. `SortCode.nat/cfg` select two source
sorts; `Pattern.zero` is the nullary zero symbol. `Symbol` contains the unary
successor, run, done, step and all four cross-sort definedness symbols. Each
`Pattern.app` is the corresponding one-argument source application. Negation,
conjunction and existential binding map to their source constructors.
Disjunction, implication, equivalence, universal quantification, top and bottom
are definitions over those constructors in `Syntax.lean`.

A finite context lists the sorts of the free names in scope. Map each typed
variable position to a distinct source variable of its listed sort. When
entering a binder, select a fresh source name of the bound sort, map `here` to
it, and map `there v` to the old name of `v`. The paper's countable stock of
variables supplies such fresh names for every finite pattern. This is the
paper-level binding-convention account; there is no second named AST or
claimed machine-checked translation of the whole paper syntax.

The semantic correspondence is checked on the selected constructors: `eval`
uses singleton variables, the supplied constant set, existential union of
symbol images, complement, intersection and union over all values of a bound
variable. The evaluation equations are definitional. `eval_rename` proves the
valuation pullback law for any sorted renaming, including its lifted binder
case. `eval_agree` proves independence from variables absent according to
`Occurs`. Thus changing the fresh naming environment preserves the indicated
meaning. `eval_subst_singleton` and `eval_substOne` prove element substitution
with the exact singleton premise; `eval_subst_congr` separately proves
congruence for equal replacement sets, without claiming those sets are
selected elements. Lifted substitution weakens replacements under binders,
preventing capture without a hidden freshness assumption.

The new Lean results are these generic semantic and soundness theorems and
the configuration specializations below. The native constructors, arithmetic
exclusions and label selectors are local model facts, not new consequences
attributed to the paper's bare selected rule fragment.

## Modules and mathematical boundaries

| Module | Contract |
| --- | --- |
| [Configuration](../../Applications/MatchingLogic/Configuration.lean) | Native configurations, labelled steps, exact outcome sets, safety, traces and selector |
| [Syntax](../../Applications/MatchingLogic/Syntax.lean) | Fixed signature, typed contexts, renaming and capture-avoiding substitution |
| [Semantics](../../Applications/MatchingLogic/Semantics.lean) | Set evaluation, valuation agreement, substitution and definedness equations |
| [Rules](../../Applications/MatchingLogic/Rules.lean) | Derivation data and selected-rule soundness |
| [ConfigurationModel](../../Applications/MatchingLogic/ConfigurationModel.lean) | Concrete interpretation, exact symbolic results and numbered inference |
| [Examples](../../Examples/MatchingLogic.lean) | Public positive, binding-sensitive and rejecting consumers |

`Model.Carrier : SortCode → Type u` uses one arbitrary universe and requires
both carriers to be nonempty. A valuation assigns one carrier element to each
typed variable; an interpretation returns a set of elements of the pattern's
sort. Constants and unary symbols may be genuinely set valued. Only the
specified definedness symbols must send every element to the full target
carrier. This is the element-level law underlying the paper's variable
definedness assumption. In the concrete model it follows by definition, rather
than by assuming a conclusion about arbitrary evaluated patterns.

`ceil` is full exactly for a nonempty denotation; `floor` is full exactly for
the full input carrier. `equal` uses the floor of pointwise equivalence, so its
predicate tests equality of entire denotation sets. `member` uses definedness
of the intersection with a singleton variable. The `mem_eval_*` theorems state
these equations for every output element, including across sorts.
`Valid` quantifies over every valuation and requires the full carrier.

The selected derivation constructors are specification axioms, propositional
tautology instances, modus ponens, universal generalization, Functional
Substitution, Equality Introduction and Equality Elimination. Propositional
tautologies are represented by a small propositional schema with a proof for
all truth assignments, then instantiated with patterns. There is no constructor
that admits an arbitrary semantically valid matching pattern as a derivation.

`Derives.sound` assumes global validity of each specification axiom. It does
not generalize a premise valid under only one assignment or unrestricted local
hypotheses. Functional Substitution retains the existence of a singleton
witness as its antecedent. Equality Elimination uses equality of replacement
sets and capture-safe substitution, so it needs no singleton restriction.
The fresh witness in functionality is represented by a new context entry;
the original pattern is weakened and cannot mention that entry.

## Independent outcome contract and inference

`Cfg` has `run n` and `done n` for every natural `n`. Both keep labels send
`run n` to `done n`; bump sends it to `done (n+1)`. Done configurations have no
successor. These definitions precede and do not consult patterns. `outcomes`
forgets the label, `post` extends it by union over an input set, and `Safe c B`
is inclusion of the whole outcome set in the same supplied `B`.

The native and symbolic theorems establish exactly
`outcomes (run n) = {done n, done (n+1)}` and empty outcomes for `done n`.
The existential pattern over all natural inputs denotes exactly the terminal
family. `done (n+2)` is excluded. `safety_iff` connects the symbolic and native
clients for the same `B`, using exact outcome equality rather than just a
forward simulation. `boundary_outcomes` also recovers this fiber through the
existing relational semantic-boundary interface. No institution registration
is needed to prove these results.

The specification has two explicit axiom schemas: the outcome equality at a
natural variable and functionality of zero. `axioms_valid` checks both in the
independently defined configuration model. The numbered report inference is
actual `Derives` data:

1. `inferenceGeneralized` generalizes the outcome axiom.
2. `inferenceAtZero` combines it with the zero-functionality axiom and applies
   Functional Substitution by modus ponens.
3. `inferenceSymmetry` combines that equality with Equality Introduction and
   applies Equality Elimination in an equality context to obtain the reversed
   equality between the concrete result family and the initial step pattern.

`inference_valid` and the public `derivation_sound` use `Derives.sound` on this
value. They do not replace the derivation by a direct set calculation.
The independent `initial_exact` calculation identifies its two outcomes.
Constructor injectivity/disjointness and natural arithmetic prove the later
exclusion result in this model; no such axioms have been smuggled into the
selected derivation system.

## Substitution and observation controls

The public cross-sort example substitutes a natural pattern under a
configuration binder into a negated equality. `bound_variable_matters` proves
that assigning `run 0` and `done 0` to that bound variable gives different
body denotations. The example therefore exercises binding, negation and
capture avoidance, not merely a closed or unused binder. Other examples use
renaming and free-variable valuation agreement directly.

The universally quantified assertion that every configuration variable has a
singleton witness is valid. Replacing that variable by the initial step
pattern gives an empty functionality predicate, although the step pattern is
nonempty and has two outcomes. `unrestricted_result_is_substitution` identifies
the rejected conclusion with the actual substitution operation. Separately,
the terminal step's empty denotation is also not a singleton. These are
mathematical obstructions to dropping functionality, not encoding failures.

`Trace` retains a label and its correctness proof. `keepA n` and `keepB n` are
distinct data with equal forgotten outcome evidence; `no_recovery` proves that
no inverse recovers both original traces. `select` chooses keepA for the
unchanged result and bump for the successor. Its proofs establish a chosen
witness and correct forgetting, not recovery of a previously selected keepB.
The enriched relation on `(output,label)` forgets to the exact outcome set.
The safety client does not need this enrichment. No equality of logical proofs
is presented as a higher identity or selected path.

## Reuse and next decisions

The implementation reuses native sets, relations and the existing whole-fiber
semantic boundary. The binder, substitution and rule machinery is shared
within this symbolic client, including the negated cross-sort example and the
actual inference. There is not yet a second independent symbolic application
reusing it. That is insufficient evidence to expand the fixed signature,
mandate a common AST or migrate native clients. Keep the native interface;
select a second consumer under #290 before generalizing the syntax. Any later
shared-interface decision belongs with #235/#288 and needs a concrete recovery
contract and proof reuse.

General set semantics is classical and can use infinite carriers. This work
claims no quantified-pattern decision procedure, proof search, arbitrary
witness extraction, completeness, reachability engine, K or Wasm integration,
physical realization, runtime bound or measured author improvement. The trace
selector is a concrete data construction; there is no generic selection theorem
for arbitrary matching models. No resource budget was raised. The
[attempt record](matching-logic-configuration-attempts.md) retains encoding
repairs separately from the proved counterexamples.
