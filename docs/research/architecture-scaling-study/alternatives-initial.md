# Alternatives and semantic coverage: independent initial assessment

This is an interim assessment for #362 against baseline
`5867d02ecfc290b7a3b7505cc94acbb98f4f49ff`, prepared on 2026-11-08.
I received the common brief with fresh conversation context, read no other
initial assessment, and had no prior involvement supplied in that context.
This independence does not establish diversity of models or training. Evidence
below consists of primary-paper inspection and pinned local source inspection.
I ran no Lean compilation, proof audit, benchmark, or new formalization.

Retain the existing implementation as a tested reference while changing the
next research tasks. Give effect interaction and relational hiding priority
over another arithmetic selected-packet example. Keep equivalence-invariant
internal languages eligible to replace the dependent authoring core. There is
insufficient evidence to select that replacement now, but there is also
insufficient evidence to make the current local-certificate organization a
requirement for its competitors. Release of #358–#361 and a final architectural
choice remain pending the incoming Agda evidence or an explicit owner scope
change, as required by the [brief](brief.md).

## Requirements independent of the implementation

An acceptable architecture must support a reusable dependent argument whose
assumptions identify admissible settings, an interpretation of that argument,
and comparisons that preserve its selected dependent data. These are separate
obligations. Expressing all three as records does not derive any laws between
them. A setting must be able to supply its own identity and observations without
silently importing Lean equality as its semantic identity.

Extension admission must distinguish adding operations, adding equations,
and choosing interactions. Separate models of two theories do not automatically
supply a joint model. Hiding must preserve the declared observation without
choosing an arbitrary solution from a relation. A compiler may inspect syntax,
but a semantic observer must obey its own invariance contract.

The comparison should count model setup, each new constructor, each additional
setting, each interaction law, and repairs after a change. A theorem covering
arbitrarily large syntax establishes mathematical reuse; it does not establish
low marginal agent effort. None of the inspected papers measures agent effort.

## Different kinds of alternative

| Formulation | Potential role | Requirement it directly addresses | Obligation still separate |
|---|---|---|---|
| Comprehension categories and local universes | Semantic core and derived coherence mechanism | Stable dependent interpretation from weakly stable model structure | Comparison between models and preservation of selected sections |
| Nominal abstraction | Replacement for binding representation | Alpha-equivalence, freshness, substitution and induction | Dependent semantic adequacy and higher identities |
| Bialgebras and distributive laws | Replacement organization for construction/observation compatibility | Derive compositional behavior from a uniform law | Independent meaning, dependent interpretation, extension interactions |
| Algebraic theories with sums and tensors | Alternative extension-composition core | State explicitly which operations commute | Models of the chosen joint theory and nonalgebraic effects |
| Quasi-Borel spaces | Model capability | Higher-order continuous probability | General dependent/higher type theory and compiler adequacy |
| Decorated corelations and black-box functors | Alternative representation and semantic construction for open systems | Compositional relational hiding | Retained internal witnesses when observers demand them |
| Univalent internal languages | Candidate replacement for the authoring/transport core | Invariance under equivalence built into internal identity | Checked hosting, admissible models, modalities and executable realization |

These candidates are not mutually exclusive. Nominal syntax and local-universe
models can coexist; probability can challenge either. Counting each as a
competing complete language would conceal the different problems they solve.

## Primary-source findings and limits

Lumsdaine and Warren's [local-universes paper, arXiv:1411.1736v2](https://arxiv.org/html/1411.1736v2)
proves a coherence construction for full comprehension categories. Its LF
condition requires finite products and specified dependent exponentials along
display maps. Weakly stable identity types, dependent products and sums lift to
strictly stable choices (Lemmas 3.4.2.4, 3.4.3.2 and 3.4.4.2). Section 4.1
explicitly excludes general type-equality rules from the lifting. This is a
possible source of derived substitution laws, not a proof that arbitrary
modalities or model comparisons lift. Its advantage should be tested on a weak
model; requiring the competitor to first implement every incumbent strict field
would charge it for the work the theorem is intended to eliminate.

Gabbay and Pitts' [2002 binding paper](https://www.cl.cam.ac.uk/~amp12/papers/newaas/newaas-jv.pdf)
uses finite-support permutation structure, freshness and name abstraction to
represent syntax modulo alpha-renaming with induction and recursion principles.
It offers a different source representation, not merely different notation for
indices. Its source theorem concerns binding datatypes. It does not establish
interpretation of this project's dependent judgments or identification of
semantic paths with syntactic renaming. A fair comparison must count support
and equivariance obligations alongside any index arithmetic it removes.

Turi and Plotkin's [1997 bialgebraic paper](https://homepages.inf.ed.ac.uk/gdp/publications/Math_Op_Sem.pdf)
relates distributive laws of a monad over a comonad to liftings (Theorem 7.1).
The syntax/behavior applications require the appropriate free monad, cofree
comonad and natural rule format; the resulting bialgebra compatibility is a
single structured condition. This could replace repeated constructor/observer
proofs when those hypotheses hold. It does not identify behavioral equivalence
with an independently requested denotation automatically. A dependent version
must explain families and selected sections; failure to find one in this paper
is missing evidence, not impossibility.

Hyland, Plotkin and Power's [2006 sum-and-tensor paper](https://www.dpmms.cam.ac.uk/~jmeh1/Research/Publications/2006/hpp06.pdf)
is an additional candidate beyond the brief's seed list. It combines effects
through Lawvere theories: sum and tensor encode different interaction choices,
with tensor imposing commutation. The paper develops countable enriched
Lawvere theories under its enrichment assumptions and derives familiar effect
transformers. For a bounded comparison, use ordinary finitary theories over
Set before claiming the enriched generalization. Its lesson for architecture
is that the combination operator is part of the specification. It does not
license arbitrary dependent or higher extensions merely because their
operations can be listed together.

Heunen, Kammar, Staton and Yang's [probability paper, arXiv:1701.02547v4](https://arxiv.org/pdf/1701.02547v4)
constructs the cartesian closed category of quasi-Borel spaces and a probability
monad. Standard measurable spaces do not supply that cartesian closed
structure. Random functions therefore form a semantic test that plain
first-order measurable kernels miss. The paper's conclusions are about this
category and its probability structure; cartesian closure alone does not give
all dependent products or higher identity semantics required by the brief.
A successful QBS test establishes a model capability, not architectural victory.

Fong's [decorated corelations, TAC 33(22), 2018](https://doi.org/10.70930/tac/ylfv3uq9)
assume finite colimits, a factorization system whose right class is stable
under pushout, and suitable lax symmetric monoidal decorating data. These
hypotheses construct hypergraph categories and functors. Fong and Sarazola's
[arXiv:1812.03601v1](https://arxiv.org/pdf/1812.03601v1), Theorems 3.21 and 7.3,
organizes this construction functorially and gives a steady-state semantics
into semialgebraic relations. Internal solutions are hidden while boundary
relations compose. That is directly relevant to interpretation beyond decoding
functions. This construction intentionally forgets internal distinctions;
retaining a selected solution would require a stronger contract than the
black-box relation alone.

Ahrens, Kapulkin and Shulman's [arXiv:1303.0584v2](https://arxiv.org/pdf/1303.0584v2)
provides another candidate outside the seeds: univalent categories and Rezk
completion. The setting is univalent foundations; hom-types are sets, while
object identity corresponds to isomorphism for univalent categories. It derives
invariance under equivalence and a universal completion. It does not replace
all higher coherence by this one theorem. The architectural opportunity is to
make some transport obligations consequences of internal identity principles.
This could justify a different authoring core even if a Lean embedding costs
more initially. Host migration is neither necessary by definition nor
authorized here; a checked object language is a candidate route.

All primary links above were accessed on 2026-11-08. The arXiv suffixes pin the
inspected revisions. The nominal and effect papers are the named journal-era
author PDFs; the Turi–Plotkin source is the author-hosted LICS 1997 paper,
sections 5–7. These access-date pins do not claim immutable PDF bytes.

## Discriminating tests with independent expected results

The following are proposed tests, not completed experiments or claims about
currently missing features throughout the repository.

1. **Extension interactions with observable failure.** Start with an operation
   `u : X → X` whose separate theory has no equations, and a constant `c : X`.
   On the independently fixed carrier `Bool`, interpret `u` as negation and
   `c` as false. Both theories have models; their sum has that joint model.
   A commuting tensor requires `u(c) = c`, which this interpretation violates.
   Expected outcome: sum admission succeeds and this tensor interpretation is
   rejected, with the mixed law exposed. Rejection of this model does not imply
   the tensor theory has no models. Add an independently specified state/read
   observer afterward so the comparison cannot stop at propositional record
   consistency. The incumbent loses if separate admission silently authorizes
   the tensor or if every interaction requires bespoke whole-language proofs
   where a theory construction derives the same result.

2. **Relational hiding without unique solvability.** Fix the meaning of a finite
   open constraint network as all boundary assignments extendable to a solution.
   Compose networks by equating their shared boundary and existentially hiding
   it. Include an inconsistent component, a component with multiple internal
   solutions, and renaming of internal nodes. Expected outcome: inconsistency
   gives the empty relation, multiple solutions remain a relation, renaming is
   invisible, and composition is relational composition. A later observer of
   solution multiplicity must fail to factor through this boundary relation.
   Compare a direct local-square account with the corelation/functor account
   against that same specification. Requiring a chosen internal solution, or
   accepting the multiplicity observer without changing the contract, fails.
   This can favor replacing the open-system core even while retaining other
   library interfaces.

3. **A higher-order probability observer that sees correlation.** Compare a
   sampled constant function `f(x) = Z`, where one standard normal `Z` is sampled
   once, with a function that performs a fresh standard-normal draw on each call.
   The types must distinguish a distribution over functions from a function
   returning distributions. A client invokes the same returned callable twice
   and tests equality of its results. Expected probability is one in the shared
   sample case and zero for independent draws, while each single-call marginal
   is standard normal. These are mathematical expectations from the specified
   random variables, not outputs of a local run. An encoding that represents
   only marginal kernels and identifies the programs fails. A QBS model may
   supply the required function-space structure; it does not by itself prove
   that a compiler preserves the distinction.

4. **Selected action across changes of context.** Use a one-object groupoid
   with automorphism group `C₂` and its dependent family given by the nontrivial
   action on a two-element fiber. Select the nonidentity loop and a fiber
   element. Pull the family back along two separately specified functors and
   compare iterated with composite pullback. Expected action of the selected
   loop swaps the fiber elements; substituting identity leaves them fixed.
   Retaining only endpoints or the existence of a loop is therefore rejected.
   Reuse the same abstract dependent transport-composition argument in a
   set-family setting, where identity action is trivial, and in this groupoid
   setting, where the chosen action is nontrivial. The theorem is shared; the
   nontrivial-action assertion is a property of the second model, not a law
   falsely imposed on both.
   Add a nonidentity natural comparison between presentations to test transport
   beyond strict equality of maps. Use a weak comprehension presentation for
   the local-universes competitor. The incumbent loses if its source argument
   must be rewritten for that presentation while the competitor derives the
   same selected action. This test probes witness-sensitive dependence; it does
   not establish all higher identity levels or synthetic geometry.

5. **Binding maintenance with an unchanged semantic theorem.** Present the
   previous dependent argument with explicit named binders and then add a
   constructor binding two dependent variables. Freeze its intended substitution
   theorem and selected-action observation first. Compare the current binding
   machinery with nominal abstraction, charging both for all generic setup.
   Vary nesting and independent constructor additions separately. Passing means
   capture avoidance, equivariance and the unchanged interpretation theorem
   survive; deleting dependence or replacing binders by a closed example fails.
   The nominal alternative wins only if its reusable principles reduce recurring
   obligations without moving them into unmeasured model setup.

For agent trials, give matched agents the same mathematical specification,
validation budget and existing helper inventory. Record completion, failed
attempts, repairs, checked declarations and resource use; separate initial
infrastructure from marginal clients. Repeat after changing one constructor
law and one observation contract. No asymptotic effort estimate follows from
this proposed design or from a finite successful sample.

## What supports retaining the current approach

Pinned source inspection supplies a stronger reason than sunk cost.
[`compiled_image`](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/Examples/DependentPairSharedClient.lean)
connects native compilation, exact target quotation and execution against a
selected source meaning for its bounded proof fragment. The same file rejects
a wrong selected component with the same index. The
[compositional trial](https://github.com/VladimirMarko/conaled/blob/5867d02ecfc290b7a3b7505cc94acbb98f4f49ff/Examples/IncrementalDependentCompositionalTrial.lean)
derives execution for arbitrary schedules and actual code substitution, with
`substituted_code_is_actual` linking syntactic substitution to the generated
program. These are inspectable theorem statements and proof bodies; their
previous checking is reported repository evidence, not re-executed here.

The explicit limit is also in the source: interpretation covers generated
arithmetic indices followed by a pair and observation. Native proof provenance
and target quotation are useful guarantees that any replacement should recover.
They do not test open-system hiding, mixed extension laws, probability on
functions, or equivalence-invariant authoring. Existing relational architecture
is acknowledged by ADR 0002; the proposed hiding test is not a claim that the
repository permits only functions. No ADR change is proposed by this report.

## Orbifolds and the remaining decision

Myers' [arXiv:2205.15887v1](https://arxiv.org/pdf/2205.15887v1), sections 2–4,
uses synthetic differential cohesive homotopy type theory. Its assumptions
include the specified smooth-real axioms, Kock–Lawvere behavior, crisp context
restrictions and a modality preserving crisp pullbacks. Its internal orbifold
criterion combines microlinearity with properly finite identity types. These
are legitimate conditional mathematical assumptions. A concrete semantic
interpretation must validate the relevant assumptions, and comparison with a
classical presentation requires its own theorem. A numerical implementation
requires a further realization contract.

The `C₂` test above isolates isotropy and dependent action without pretending to
cover those synthetic hypotheses. The reported completed Agda development
could supply much stronger evidence for an internal-language alternative.
Its current artifact is unavailable, so this assessment makes no claims about
its rankings, coverage, assumptions beyond the owner's statement, or classical
comparison results. I did not use either historical orbifold archive as proof
evidence.

The smallest useful correction is to freeze the extension-interaction and
relational-hiding specifications before commissioning another implementation.
Allow competitors to derive their guarantees through their own universal
constructions. The consequential uncertainty is whether model setup and
cross-model comparison dominate total author effort once the examples leave
the prepared arithmetic fragment. If they do, a comprehension or univalent
internal-language core could outperform local certificates despite larger
initial cost. If the current approach supplies the missing clients with
reusable laws and comparable maintenance effort, retaining it would have new,
independent support. The present evidence cannot decide between those outcomes.
