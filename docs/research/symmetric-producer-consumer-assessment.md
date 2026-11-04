# Symmetric producer/consumer syntax and its contracts

Assessment for [#270](https://github.com/VladimirMarko/conaled/issues/270), against
repository base `50cdd4b3cf78e04c245f0d90a3d252ed91aaa2a6` and the issue requirements
updated 2026-10-30. The recommendation is to retain the current direct Lean and
#203 proof interfaces. An optional consumer presentation is worth a later author
experiment, but the evidence does not justify selecting a universal calculus,
changing object logic, or choosing one evaluation strategy.

This is research, not a new Lean implementation. All proposed judgments,
translations and worked examples below are **paper-only**. References to existing
checked declarations describe their current source contracts; this change has
not rerun their builds. It adds no formal claims to the library.

## Source results and logical commitments

[Binder, Jabs, Skupin and Ostermann, arXiv:2211.13004v1](https://arxiv.org/html/2211.13004v1),
§3, use `Γ ⊢ e :prd T`, `Γ ⊢ e :con T`, and `Γ ⊢ c :cmd`.
Contexts contain oriented variables; cut pairs opposite orientations at the same
type. Data/codata polarity determines constructor versus destructor organization;
CBV/CBN is a separate type attribute. The simply typed presentation does not
supply dependent typing. §§5–6 add μ binders, strategy-sensitive substitution,
and shifts. Under polar evaluation (CBV data, CBN codata), Theorem 5.2 gives
reduction compatibility modulo eta; binders must avoid free-variable capture.
Changing polarity alone cannot preserve that strategy: evaluation changes require
shifts. The reported Coq proofs cover Theorems 3.1–4.3; later extensions have a
different evidence boundary.

The source's §1 function example, with `Ω : A → Nat` divergent, distinguishes
`(λf.5)(λx.Ω x)` from `(λf.5) Ω`: CBV returns 5 for the former and diverges for
the latter; CBN returns 5 for both. Unrestricted function eta therefore fails
in that CBV language. The data eta obstruction is dual under CBN (§§1, 2.3).
 [Binder et al., §§1–6](https://arxiv.org/html/2211.13004v1)

[Curien and Herbelin, *The Duality of Computation*, corrected July 2012 version,
§§2–5](https://pauillac.inria.fr/~herbelin/articles/icfp-CuHer00-duality%2Berrata6.pdf),
make the logical change explicit. Their term, context and command judgments are
`Γ ⊢ v:A | Δ`, `Γ | E:A ⊢ Δ`, and `c:(Γ ⊢ Δ)` in a classical implicational
sequent calculus. At `⟨μα.c | μ̃x.d⟩`, the two substitutions compete; selecting
which side substitutes distinguishes the evaluation disciplines. This is a
control calculus, not merely renamed intuitionistic introduction/elimination.

[Wadler, *Call-by-Value is Dual to Call-by-Name*, §§1–3](https://homepages.inf.ed.ac.uk/wadler/papers/dual/dual.pdf),
also explicitly uses classical sequents, with terms, coterms and statements,
and De Morgan duality. Its connection between control and classical principles
is a reason to classify the logic before importing a syntax. A multi-conclusion
classical interpretation and unrestricted continuation capture cannot silently
inherit #203's intuitionistic proof contract.

Our inference: a consumer need not mean a refutation. An observer returning a
number, a function `A → R`, a linear endpoint and a proof of `A → False` have
different types and laws. Only the last has the stated constructive refutation
meaning. Even a CPS value `(A → R) → R` is not generally recoverable as an `A`;
choosing an empty answer type does not provide double-negation elimination.
Lean's host logic does not automatically add such an object-language rule.

## Matched task: the established conjunction client

The actual [#203 client](../../Examples/CurryHoward.lean) is
`swap : Proof [and atom truth] (and truth atom)`. It has one atom, not an
arbitrary family of atomic propositions. The ordinary client
`ordinarySwap {A B} (p : A × B) := (p.2,p.1)` is more polymorphic. Compare the
same instance, `A = Nat`, `B = Unit`, rather than attributing that polymorphism
to the encoded proof fragment.

For a conservative paper presentation fix the grammar
`A ::= atom | 1 | A × A | A → A`. Ordinary assumptions `Γ` admit weakening,
exchange and contraction. Define producers by the existing pure natural-deduction
terms. Define a consumer judgment `Γ | A ⊢ K : R` as an ordinary term of type
`R` in `Γ,x:A`, with `x` designated as its input. A command `⟨t|K⟩ : R` plugs
`t : A` into that input by capture-avoiding substitution. This is a presentation
of intuitionistic syntax, with a named result `R`; it has no free-standing
classical μ rule or multiple alternative conclusions.

The matched paper terms are:

```text
Γ = p : atom × 1;   R = 1 × atom
ordinary: Γ ⊢ (snd p, fst p) : R
consumer: ∅ | atom × 1 ⊢ split(x,u).return (u,x) : R
command:  Γ ⊢ ⟨p | split(x,u).return (u,x)⟩ : R
```

Here `split(x,u).return v` abbreviates elimination of the designated pair input
followed by construction of `v`; `return` is ordinary result production, not
an effect operation. In the environment `p=(7,())`, each denotes `((),7)`.
The result is exactly the existing checked `swap` task. The symmetric-looking
presentation exposes a use site but supplies no new proof power.

Interpret the atom by a set `X`, truth by a singleton, products by cartesian
products and arrows by total functions. Producers denote
`⟦Γ⟧ → ⟦A⟧`, consumers denote `⟦Γ⟧ × ⟦A⟧ → ⟦R⟧`, and cut denotes
`ρ ↦ ⟦K⟧(ρ,⟦t⟧ρ)`. Meaning is specified without an evaluator.
The proposed equality is pointwise equality of these functions, keeping syntax
identity and directed reduction separate. At the categorical level the matching
capabilities are terminal objects, products and exponentials, with the required
laws. These equations do not prove normalization, operational reflection or
full abstraction.

[#203](curry-howard-implementation.md) already separates tree equality,
`Detour`, `Term.Step`, and semantic equality. Its `two_models` and `composed`
clients supply the current interpretation route; its backend adapter asks for
a broader full-source signature than this fragment mathematically needs.
The proposed presentation must recover those contracts, not introduce a new
normalizer or claim that semantic eta is equality of compiler trees. In the
total function interpretation `λx.f x` and `f` agree extensionally; the divergent
`Ω` above has no interpretation as a total producer in this model. A partial
or effectful extension needs a new semantic domain and an adequacy theorem
before the example can justify any operational optimization there.

## Matched task: indexed construction and observation

The second task comes from [#256's vector client](../../Examples/EquationTranspose.lean),
which is independent of the Curry–Howard atom grammar. Fix `n : Nat`,
`h : Nat`, `t : Fin n → Nat`, and `i : Fin (n+1)`. The ordinary term is
`(Fin.cases h t) i : Nat`. A paper consumer presentation is:

```text
producer: cons_n(h,t) : Vec_nplus1
consumer: at_nplus1(i,k) : Consumer Vec_nplus1 R
command:  ⟨cons_n(h,t) | at_nplus1(i,k)⟩ : R
meaning:  k (Fin.cases h t i), where k : Nat → R
Vec_nplus1 means Fin (n+1) → Nat
```

This display introduces notation only. The direct observation is recovered by
`R=Nat`, `k=id`; at the checked `n=1,h=7,t=(fun _ => 11)` inputs the two indices
return 7 and 11 respectively. The continuation is an ordinary function, not
negation. The index excludes lookup at length zero. The producer's constructor
fields and the observer's argument occupy different variable blocks; existing
`transpose_preserves` swaps the blocks and preserves the interpreted cell.
A proposed consumer view must preserve both blocks and their types, including
the impossible empty lookup, rather than erase indices into one base type.

A stronger acceptance discriminator is already available in
[the parser transposition client](../../Applications/Languages/Transposition.lean).
For `p : Parser P`, the nullable observation has result
`ULift (Decision (P []))`; derivatives have `Parser (derivative P a)`, and a
snapshot has `WitnessTrie P n`. At fixed `P`, a paper consumer of a parser can
have meaning `p ↦ k (p.nullable)` with
`k : Decision (P []) → R`, retaining the decision itself. The trivial `ULift`
wrapper in the cell interface changes no selected witness. For nullable epsilon
star, the existing result selects the empty list of empty parses. A singleton
empty-parse list is a different witness even though both erase to acceptance.
A Boolean-result view therefore cannot stand in for the exact observation.

For concatenation, `recovered_snapshot` gives the same selected parse decision
as `(Parser.concat p q).parse w` when `w.length ≤ n`. A consumer view must retain
that bound, the language index and the selected witness, as well as the unchanged
right operand in the derivative equation. Neither equation transposition nor
the paper consumer notation proves that arbitrary recursive source definitions
can be transformed into productive infinite codata.

## Binders, extensions and incompatible contracts

The conservative consumer presentation has a designated input binder in addition
to ordinary binders. Implementing it needs renaming, lifting, simultaneous
substitution, substitution composition, and an interpretation substitution law.
The existing #203 capture test, substituting free `z` into `λy.x`, must continue
to return 7 rather than 99 at its recorded inputs. Fresh names alone are not
a proof of substitution compatibility. New continuation binders require their
own scope discipline; an arbitrary μ extension is outside this proposal.

An internal dependent version also needs well-formed telescopes, substitution
in types, dependent result transport and coherence of equality transports.
Externally fixing `n` or `P` in the displayed examples does not implement those
laws. A consumer whose answer family depends on the produced value cannot be
modeled by one fixed `A → R` without retaining the dependency, for example through
a specified dependent function or pair. #271 owns the dependent continuation
and index-changing design gate. Witness-bearing outputs stay in data-bearing
types; proof irrelevance cannot recover erased choices.

[#145's assessment](codata-elaboration-termination-contracts.md) separates
termination, productivity, causality and conversion. Its finite-observation
contracts and the constant-sheaf stream counterexample prohibit inferring final
coalgebra preservation from finite-limit or finite-prefix preservation. A new
observer needs compatibility with the chosen equality; adding an observer that
distinguishes formerly equal implementations changes the observation contract.
A new semantic type needs its own interpretation and admissibility laws. Adding
constructors needs the new constructor/observer equations. None of these actions
alone preserves normalization or productivity.

[#212](linear-session-experiment.md) already provides a different symmetric use
case: typed cut connects dual endpoints, with no weakening or contraction,
disjoint residual resources, and exchange. Additive alternatives share a context
because only one executes. Its finite protocol completion and independent trace
refinement are more informative than a function's returned value. A proposed
adapter must retain the remaining endpoint and selected communication trace.
Encoding endpoints as freely duplicable consumers would violate `no_duplicate`;
using #203's `duplicate` in that context is not a syntax improvement. This task
therefore reuses #212 as a mismatch test and proposes no replacement session core.

## Fit, author effort and recommendation

| Task or requirement | Fit of an explicit consumer view | Obligation or mismatch |
|---|---|---|
| #203 swap | Same constructive product argument | More result/input naming than direct projections; no demonstrated reuse gain |
| #203 binder client | Can expose substitution sites | Must hide lifted variables and preserve the existing capture test |
| #256 vector lookup | Makes constructor/observer pairing visible | Keep both parameter blocks and `Fin n`; simple atoms lose the contract |
| #256 parser observations | Useful named observer boundary | Keep language/word/depth indices and exact decisions; Boolean erasure fails |
| #212 communication | Cut is already useful | Linear resources and traces cannot inherit cartesian structural rules |
| Effectful eta optimization | Evaluation discipline matters | Needs a partial/effect interpretation and operational correctness, not total-function equality |
| #116 multiple surfaces | Optional syntax can share meaning | Elaboration fidelity, typing, substitution and coherence between views remain to be proved |
| #145 codata | Observers can specify finite questions | Delivery, finality and transport require separate hypotheses |

For the swap task a direct author supplies a pair and two projections. The
current encoded author supplies named proof rules and one typed hypothesis;
substitution certificates and interpretation proofs are provided by the library.
The paper consumer author additionally names an input, answer type, cut and
continuation where applicable. A compiler could hide that bookkeeping, but this
assessment contains no implemented elaborator or author trial establishing that
it does. For indexed observers the direct interfaces already infer much of the
result family. Requiring every client to construct commands would add obligations
without a measured benefit.

The design benefit to investigate is reusable treatment of use sites and verified
presentation changes. The present evidence rejects wholesale replacement and
does not yet justify an implementation ticket for a new calculus. Keep
`ordinarySwap`, `Proof`, direct parser/trie observations and session clients.
#116 can compare a consumer surface with ordinary named syntax on the same tasks;
#235 owns any subsequent interface and preservation-family expansion. This
recommendation does not rank sequent approaches below the current architecture
on mathematical grounds; the dependent and effectful interpretation obligations
remain open in both approaches.

Before selecting a prototype, require a written specification choosing (1) the
object logic and structural rules, (2) a producer/consumer grammar and answer
types, (3) denotation and equality independent of execution, (4) scope and
substitution laws, and (5) the exact translations and preservation scope.
A bounded candidate could target only the #203 pure fragment, interpret consumers
as designated-hole terms, and prove typing, denotation and substitution
compatibility while retaining direct clients. Acceptance would compare swap,
free-variable capture, and duplication with the existing implementation, and
explicitly reject session duplication and unsupported dependent observers.
Only a later dependency-aware candidate may claim the full #256 contract.
This is a conditional experiment specification, not a selected prototype or
permission to weaken indexed acceptance into untyped examples.

## Evidence limits and completion boundary

The external comparison read Binder et al. v1, Curien–Herbelin's corrected
article and Wadler's 2003 article. It covers the relevant classical/control
foundations, not an exhaustive survey of focusing, dependent sequent calculi,
games or categorical control models. Their suitability remains research under
#235. Source claims above are distinguished from the proposed conservative
presentation and from repository declarations. No external proof artifact was
executed, no operational equivalence of the proposed surface was proved, and no
human or agent author trial was run.

Documentation validation checks local links, declaration references and whitespace.
Independent Standards and Spec review and the coordinator's recovered-intent
assessment apply to the committed candidate. The issue's implementation follow-up
condition is answered negatively: retain the current interfaces until the listed
logic and interpretation choices, plus an author-benefit test, justify one.
