# Joint admission of conversion-changing extensions

Paper construction for [#338](https://github.com/VladimirMarko/conaled/issues/338),
under [#288](https://github.com/VladimirMarko/conaled/issues/288). Two arithmetic
packages below admit a common independent meaning and preserve a selected
indexed value. Their union has a terminating, confluent conversion procedure
on the frozen first-order index language. A separate union control shows why
individual admission is insufficient.

The original #338 paper assessment below uses repository baseline
`b8731310f05efdac29f994706fbc1f32eb77de20`. The bounded formalization in
[#345](https://github.com/VladimirMarko/conaled/issues/345) now supplies the
following checked results. Higher-order source results remain literature
comparisons, not claims about this first-order implementation.

## Checked conversion and elaboration

[CertifiedIndexConversion](../../SquareKit/CertifiedIndexConversion.lean)
defines independent arithmetic `meaning`, substitution, the context-closed
three-rule `Step`, and its generated equivalence `Converts`. All index
expressions are single-sorted Nat expressions; dependent uses are explicit
`Fin (meaning ρ index + 1)` fibers. This does not encode unrestricted dependent
contexts or lambda terms.

`step_subst` and `meaning_subst` establish the substitution boundary.
`step_meaning` admits all three rules simultaneously in the arithmetic model.
`terminating` proves well-foundedness of the reverse step relation with the
paper's natural measure; `reduces_normalize` constructs reduction to the
normalizer's output, and `normalize_normal` proves irreducibility.
`step_normalize` proves invariance under every contextual step, yielding
`confluence` and `conversion_iff`. These theorems cover open expressions,
including double's duplication of an argument, rather than only numerals.

`produce` returns a finite certificate containing a common normal form.
`check` independently recomputes both normal forms and compares them with the
certificate. It is a normalization certificate, not a serialized rewrite tree
or a faster checker that trusts cached normalization. `check_sound`,
`produce_checked`, and `produce_complete` establish its bounded contract.
`elaborate` obtains an explicit equality transport from an accepted certificate;
`elaborate_value` proves that it keeps the original finite value. No equality
oracle or arbitrary-theory search is involved.

The [checked examples](../../Examples/CertifiedIndexConversion.lean) retain the
explicit A₀-then-B proof recipe and prove it agrees with the conversion route.
They check the selected value after both substitutions, the open duplicated
peak, commutativity valid semantically but absent from generated conversion,
and rejection of the old zero-add model. The separate P/Q control proves the
union's nonjoinable peak and distinguishes distinct-meaning rejection from a
collapsed common model. The paper argument for individual P/Q confluence
below is not a separate formalization of those two packages.

Kernel-checked cases and executable `#eval` calls exercise producer success,
checker success, forged-certificate rejection, and a semantic equation outside
conversion. Rejecting a pair here means absence of *generated conversion*;
it does not refute arithmetic equality. Outside this grammar the implementation
has no decision-procedure claim. Finite checking, evaluation of an expression,
and general proof search remain separate operations.

The explicit author route supplies a conversion derivation and casts the
selected section. The admitted route supplies a normalization certificate and
its check, then uses the same interpretation to derive that cast. Recurring
arithmetic proof steps disappear for this grammar, at the setup cost of syntax,
normalization, well-foundedness, and soundness/completeness proofs. Adding a
rule requires revisiting semantic admission, normalization invariance and
termination; the existing theorem does not certify a new union. No measured
productivity comparison is claimed.

## Frozen packages, client and meaning

The old signature contains `Nat`, `z : Nat`, `s : Nat → Nat`,
`add : Nat → Nat → Nat`, `double : Nat → Nat`, a family `V : Nat → Type`, and
`last : (n : Nat) → V n`. The dependent client will use `last` at an index
that contains both add and double. These operation names are present before
admission; they do not acquire new declarations during this experiment.

The two equation packages are

```text
A₀: add z y       = y
Aₛ: add (s x) y   = s (add x y)
B:  double x      = add x x.
```

The intended setting is independently specified: Nat denotes natural numbers,
z is 0, s is successor, add is mathematical addition, and double is `n ↦ 2n`.
`V n` denotes `Fin(n+1)` and `last n` selects n. This meaning fixes which
inhabitant the client returns, not merely whether its type is inhabited.
Both packages hold simultaneously in this interpretation.

With `n : Nat`, let `e n = double (add z n)`. The shared client must turn

```text
last (e n) : V (e n)
```

into a term at `V (add n n)` retaining the selected value 2n. It must still do
so after substituting `n := s m` and then `m := s z`; the final result is 4 in
`Fin 5`. The source recipe and its output are retained, rather than replaced
by an unrelated existence proof for `Fin 5`.

The specification's equality is extensional equality of these set-valued
meanings. Transport in the indexed family is the induced equality transport;
it preserves the underlying natural-number value. Proofs of the arithmetic
identifications have no separate semantic observation in this client. A
higher setting that observes identity paths would require compatibility of
those paths and their transport, which the following set model does not prove.

## Explicit equality route

Treat A₀, Aₛ and B as named equality proofs with typed boundaries. Congruence
and composition give a selected proof

```text
q n : e n = add n n
q n = congrArg double (A₀ n) ; B n.
```

The semicolon means path composition in the displayed order. The client is
`transport V (q n) (last (e n))`. Its interpretation is 2n in `Fin(2n+1)`:
A₀ and B identify the two indices, and equality transport in Fin does not
change the represented number. This derives the observed selected result from
the original section.

Substitute a well-typed term u for n in each step of q, and the result is
exactly the same proof recipe q u. Substitution into the client changes both
V's index and its selected input section. The two substitutions specified
above yield `q (s (s z))` by either route. In the set interpretation this
transports the value 4 unchanged; no new witness is chosen.

The explicit route needs identity/equality elimination and congruence in its
chosen source calculus. It need not turn every semantic equation into a
judgmental reduction. Finite, explicitly annotated certificates containing
rule identifiers, typed substitutions, congruence and composition can be
checked by structural recursion in this bounded fragment. This does not
promise a total algorithm to find a certificate for every true equation.
Nor does it identify the source identity type with Lean's equality: a Lean
model may validate the source transport with a set-theoretic equality proof,
but that is an interpretation theorem.

## Conversion route and joint checks

Orient all three equations left to right and allow their congruence closure
as conversion of indices. The client then checks at `V (add n n)` by conversion
without an explicit transport in its surface term. Its meaning remains the
same selected value, since each rewrite preserves the independent index
meaning and the interpretation of V respects equal indices.

**Source boundary.** In Saillard's λΠ-modulo framework, product compatibility
supports typing metatheory. Confluence of `HRS(βΓ)` entails product compatibility
(Theorem 6.3). A typed λΠ-pattern rule whose free variables are exactly its
well-formed local context is permanently well typed (Theorem 6.4).
Subject reduction is conditional on the admitted well-formed global context;
confluence alone does not supply that context. Normalization adds a separate
condition for deciding conversion by normal forms. See
[*Rewriting Modulo β in the λΠ-Calculus Modulo*, §§2.5, 6.3–6.4](https://arxiv.org/pdf/1507.08055).

**Paper verification for the frozen fragment.** Our index grammar contains
variables and fully applied z, s, add and double. It contains no binders or
higher-order application. V and dependent context declarations are formed over
these indices; their conversions are generated by index conversion. This is
a bounded λΠ-style use of conversion, not a claimed implementation or
metatheorem for the whole λΠ-modulo framework.

Each rule is typed at Nat: A₀ has context `y : Nat`; Aₛ has
`x : Nat, y : Nat`; B has `x : Nat`. Every variable of the context occurs on
the left, and no new variable appears on the right. Substitution of Nat terms
therefore preserves the rule boundary. Rewriting inside V preserves its
well-formedness, and conversion changes a term's assigned fiber without
changing its independently interpreted value. There are no Π-headed rewrite
rules in this fragment; equality of Π-shaped types, if surrounding dependent
binders are included, compares their domains and codomains structurally.
We do not infer product compatibility for a future, unrestricted rule set.

The three left sides are linear. Their nonvariable roots are add/add/double;
the two add cases have distinct constructors z and s. There is no overlap of
a left side at a proper nonvariable subterm of another left side. Thus there
are no nontrivial critical overlaps. Disjoint reductions commute. For nested
reductions at variable occurrences, applying an outer rule may duplicate the
inner redex (B), keep it, or remove surrounding constructors; reducing all
residual copies joins the peak. This covers the mixed interaction that can
be hidden by checking the packages separately:

```text
double (add z n) → add (add z n) (add z n) →* add n n
                → double n              →  add n n.
```

The same residual argument covers nested B/B and A/B interactions. The
variable-substitution fact is essential: a check of only ground numerals
would miss this duplicated argument.

For termination on open first-order index expressions, use a strictly
monotone natural-number interpretation, assigning arbitrary natural values
to variables:

```text
|z| = 0               |s x| = |x| + 1
|add x y| = 2|x|+|y|+1
|double x| = 4|x|+2.
```

A₀ decreases `|y|+1` to `|y|`; Aₛ decreases `2|x|+|y|+3` to
`2|x|+|y|+2`; B decreases `4|x|+2` to `3|x|+1`. Contexts preserve strict
inequality, so each rewrite decreases the measure, also under substitution.
The local peak argument plus termination gives confluence by well-founded
induction on this measure. Normalizing both sides therefore decides the
congruence generated by these three equations in this index grammar. This
is not a decision procedure for all semantic arithmetic equality: for example
`add x y` and `add y x` can be distinct normal forms with equal meanings.

The measure does **not** prove termination for a future calculus with arbitrary
lambda terms, β-reduction, new type-level rules or additional constants.
Nor does first-order confluence certify confluence of such a union. Saillard's
higher-order criteria must then be instantiated, including mixed β/rewrite
peaks. For example, even in a simple extension admitting beta-redex arguments,
`double ((λx.x) n)` duplicates the β-redex on expansion; both residual copies
must be reduced to join the peak. This example is a local check, not a proof
that every possible higher-order interaction is safe.

## Joint interpretation and proof reuse

In the frozen setting, both packages hold by the natural-number equations and
`2x = x+x`. Induction on a rewrite/equality derivation proves equality of
interpreted indices. Interpretation of V then validates dependent conversion
or explicit transport. The selected last value at either index is the same
natural number. Thus the common model is supplied before using normalization
as a procedure; a normalizer does not itself define our intended semantics.

The two routes differ in author obligations. Explicit transport exposes q and
its use at the dependent fiber. Conversion hides that transport in the type
checking rule. A proof-producing frontend can recover q by recording each
rewrite and lifting it through its index context, then translating the
conversion step into the explicit route. In this fragment it needs the three
primitive equality proofs and the substitution/congruence rules, not a new
semantic proof of the final client. The #345 implementation above supplies this bounded conversion-to-explicit-transport
route using common-normal-form certificates. A serialized rule-by-rule proof
translator remains outside its delivery.

The shared client requires preservation of its typing judgment, meaning and
selected dependent value. Its requirements do not include all-model expansion
or reflection of every target judgment. Those broader claims have different
answers:

| Claim | Result for the frozen admission policy |
| --- | --- |
| Retain old derivations | Yes at the syntactic level: every old rule remains available. This alone would not establish soundness of a bad extension. |
| Interpret the new derivations in the intended setting | Yes, by the joint model and rulewise interpretation argument above. |
| Expand every old model without changing old operations | No. The old signature imposed no laws on add/double. On standard Nat with `add x y = 0`, A₀ already fails at y = 1. |
| Reflect all new equations about old syntax | No. `add z y = y` is a new law about existing operation symbols and fails in that old model. |
| Preserve selected dependent data | Yes for this Fin/last client and its specified substitutions. An arbitrary identity-path observation is outside its setting contract. |
| Decide all semantic equality | No. Normal forms decide the generated rewrite congruence only. |

One can change the admission policy: start with old models already carrying
proofs of A₀, Aₛ and B, then promote those same laws to conversion. Their
set-valued interpretations remain models. That is a different base theory;
it does not repair all-model expansion for the original unconstrained base.
At a syntax level it also does not prove that judgmental equality was
previously derivable. An explicit-transport translation is needed to compare
typing derivations between those presentations. For higher witnesses, equality
of endpoints alone may fail to identify the resulting transports.

## Nonconfluent union and what it does not imply

Take a separate single-sorted signature with constants a,b,c and unary f.
Package P has `f(a) → b`; package Q has `f(a) → c`. Each is terminating and
confluent on its own. Their union terminates but has the unjoinable peak
`b ← f(a) → c` with distinct irreducible b and c. A normal-form equality
checker that compares the literal normal forms b and c rejects a derivable
equation: `b = f(a) = c` is a finite conversion certificate. Hence such a
checker is incomplete. The counterexample does not establish inconsistency
of every interpretation or impossibility of certificate checking.

There are two semantic policies. If the specification fixes b and c to
distinct meanings, no common sound interpretation can admit both equations:
transitivity forces their meanings equal. If the specification identifies
them, for example in a singleton carrier, both packages have a common model
despite this rewrite presentation being nonconfluent. Even the latter system
has a finite, directly checkable certificate for `b = c`; one could also
choose a different presentation orienting that equality. Logical consistency,
confluence of a presentation and completeness of a chosen checker are separate.

In a dependent extension, promoting new equations between types requires
checking the corresponding type rules too. Collapsing indices may identify
fibers whose old selected operations disagree. The arithmetic positive example
avoids that failure by giving the shared interpretation of V and last, rather
than merely observing that its rewrite system terminates.

## Checking, evaluation and proposed next experiment

Conversion checking asks whether two specified expressions are equal under
the setting's conversion rules. Our bounded normalization procedure answers
that question. Evaluation executes a specified program or computes an index;
termination of index normalization is not termination of every program in a
larger language. Certificate checking validates a supplied finite derivation;
its termination here follows from the finite syntax and decidable primitive
checks. Proof search attempts to find such a derivation and can fail to
terminate even when checking a supplied derivation is straightforward.

Bauer and Petković Komel explicitly permit nontermination in their extensible
equality algorithm while proving soundness; user-defined theories need not
have decidable equality. Their algorithm combines computation and
extensionality rules for standard type theories. This supports keeping proof
production and trusted validation separate, rather than assuming every
parameterized setting comes with normalization. See
[*An extensible equality checking algorithm for dependent type theories*,
Introduction](https://arxiv.org/html/2103.07397v4).

The current [rule interpretation transport](../../SquareKit/GuardedRuleInterpretation.lean)
composes source-rule derivations at a fixed signature and preserves the existing
judgment language. It does not automatically admit new conversion principles
or prove that a new conversion checker is sound. The
[independent calculus](reference-dependent-calculus.md) and
[finitary-theory study](finitary-type-theories.md) supply useful typed-boundary
requirements; neither is a blanket admission theorem for rewriting extensions.

A bounded successor under #288/#235 should encode this index grammar and the
two packages, record normalization certificates, and elaborate the dependent
client to explicit transport. Its checked examples should include n = 2,
the two substitutions, the duplicated mixed peak, the P/Q failure, and a
semantic equality outside generated conversion. It must retain the source
selected value and reject the old `add = 0` model as an expansion. This is a
specific consumer for conversion certificates, not authorization for the
separate general executable proof-translator follow-up noted on #339.

This route costs certificate syntax, typed congruence/substitution proofs and
an elaboration boundary. Automatic conversion can reduce client transport
bookkeeping, but each union requires renewed admission evidence. Extending
to a full λΠ-modulo implementation adds β interactions, product compatibility,
subject reduction and, if promised, normalization/type-checking decidability.
Those are scoped future obligations, not assumptions hidden behind the word
“conversion.” No author-productivity improvement has been measured here.
