# Selected witnesses across state and exception interpretations

For [#296](https://github.com/VladimirMarko/conaled/issues/296), a finite paper
experiment supports retaining a direct semantic contract and investigating a
handler adapter only for a concrete additional consumer. Changing exception
policy can preserve a captured witness while changing final state. Recomputing
that witness inside the handler can destroy its identity, even when the same
existential proposition remains true.

The inspected local baseline is
`701023ce73ff297604fb21f2b6caada9e727c10c`; this report is prepared from integration
revision `a272379ff0abfb9d5b033340e77885266b065a79`. It reuses the D3 question in
[external discovery](external-discovery-assessment.md), the retained primary
bibliography, and the existing #196/#254/#278/#285 reports. All new constructions
and reductions below are paper arguments. No new Lean claim, external
formalization replay, operational adequacy theorem or author trial is reported.

## Subsequent checked work

[#373](state-exception-checked-comparison.md) constructs both policy meanings,
scoped interpretation and selected-witness controls in Lean, with an existing
measurement-record client. #381 owns the further case where the observation is
produced during protected computation. The calculations below retain their
original paper scope; they are not a full effect framework or runtime adequacy
theorem.

## Freeze the argument and its meaning

Let state `S = Bool`, exception set `E = {fault}`, and returned data

```text
W := { n : Nat // n < 2 }
w(false) := (0, proof that 0 < 2)
w(true)  := (1, proof that 1 < 2).
```

The proofs certify the selected natural; they do not choose it. The pure source
argument reads an initial Boolean and produces that particular certified value.
The independent client specification is: return exactly `w(s₀)` for initial
state `s₀`. Final state is a separate observation, not part of witness equality.
Both the value and its fixed result type `W` are retained. There is no change of
index here; a dependent consumer would require its own transported result fiber.

Wrap that argument in a tentative state update which fails:

```text
P := get >>= λs₀.
       let chosen := w(s₀)
       catch (put true >> throw fault) (λ_. return chosen).
```

The handler closes over data constructed before the failing computation. It
must not silently replace `chosen` by any other inhabitant of `W`. We distinguish
an observation of the selected natural from mere truth of `∃ n, n < 2` and from
an observation of the final state. None of these means “the implementation is
fast” or “a physical write was undone.” The state is a mathematical Boolean cell.

## Two denotations, with scoped catch defined separately

Use these total set-level computation carriers:

```text
Keep A := S → ((A + E) × S)
Undo A := S → ((A × S) + E).
```

`Keep` retains state on both success and failure. `Undo` has no state component
in an exception result. Both return an ordinary successful value paired with
the current state. `get` returns the current state without changing it, and
`put t` changes it to `t`. In `Keep`, `throw e s = (inr e,s)`; in `Undo`,
`throw e s = inr e`. Sequencing runs the continuation on the resulting state
only after success; an exception skips it. These clauses fix return, bind and
primitive operations, rather than deriving meaning from a runtime interpreter.

The two catch operations are:

```text
catchKeep m h s₀ =
  case m s₀ of (inl a,s₁) => (inl a,s₁)
              (inr e,s₁) => h e s₁
catchUndo m h s₀ =
  case m s₀ of inl (a,s₁) => inl (a,s₁)
              inr e      => h e s₀.
```

Catch is scoped: it takes a computation and a handler, and its entry state is
fixed before evaluating the protected computation. It is not merely a nullary
algebraic operation named `catch`. These definitions are total, so this finite
example needs neither a divergence model nor a termination assumption on an
external action.

For every `s₀`, direct substitution gives

```text
PKeep s₀ = (inl (w(s₀)), true)
PUndo s₀ = inl (w(s₀), s₀).
```

Thus the explicit transferred result in both interpretations is the same
`w(s₀)`, with its bound certificate. At `s₀ = false`, final states differ.
A cross-interpretation relation that compares successful `W` values exactly
relates these two outcomes; a relation demanding identical final states does
not. This is a result for `P`, not an unrestricted translation between the two
monads preserving every operation and catch.

The direct proof decomposes into the pure construction of `w`, the clauses for
put/throw, the selected catch clause, and the captured return. Reusing the pure
argument is immediate. Reusing an effectful proof requires the chosen catch law
to remain a premise. No existential elimination supplies the returned data.

## Primary results and applicable hypotheses

[Hyland–Plotkin–Power, *Combining Effects: Sum and Tensor*](https://www.pure.ed.ac.uk/ws/portalfiles/portal/17919624/Hyland_Plotkin_ET_AL_2006_Combining_Effects_Sum_and_Tensor.pdf),
2006 peer-reviewed manuscript, §§3–5: Corollary 3 assumes binary sums, an object
`E` and a monad `T`, and identifies the exception sum with `T(-+E)`.
Definition 5 adds cross-operation commutation for tensor. Theorem 9 concerns
countable Lawvere V-theories and target V-categories with countable cotensors.
For ordinary state, Theorem 10 assumes a countable state theory, another
countable theory and a locally countably presentable category; the induced
monad is `T(S×-)^S`. The enriched Theorem 11 has corresponding V-category
hypotheses. Here `Set`, one Boolean cell and one exception fit the ordinary
case. Sum yields `Keep`, tensor yields `Undo`, up to product/sum ordering.
These results concern algebraic effect combinations; they do not select our
scoped catch policy or prove witness preservation. The manuscript numbering
is used because another retained copy numbers the tensor results differently.

[Plotkin–Pretnar, *Handling Algebraic Effects*](https://homepages.inf.ed.ac.uk/gdp/publications/handling-algebraic-effects.pdf),
LMCS 9(4:23), 2013, §§4.2–4.3: Definition 4.2 requires each model to satisfy all
chosen theory equations. Proposition 4.3 constructs the free-model adjunction
for their signatures, whose operation-result arities are countable.
Definition 4.5 requires handler clauses to be total and to form such a model
at every environment. Given a correct handler and a defined return clause,
handling uses the unique homomorphism extending that clause. These hypotheses
justify equation-respecting interpretation, not arbitrary code called a handler.
The present finite operation signature fits the countable-arity condition.
We use this model-checking discipline, not a claimed port of their full calculus,
recursion extension or operational semantics.

[Delaware et al., *Modular Monadic Meta-Theory*](https://skeuchel.org/files/papers/2013-icfp-modular-monadic-metatheory.pdf),
ICFP 2013, §§5–6 and Figures 7–11: feature soundness and effect soundness have
separate premises. The state/error effect theorem starts from a computation
typing derivation and a well-formed store, then concludes a typed returned value
or an exception with the stated store conditions. Its catch case requires one
of two state/catch interaction laws, implemented by separate proof algebras.
The remaining cases can be reused. The applicable transformer orders are
`ET E (ST S I)` and `ST S (ET E I)`. These are our two carrier shapes.
This is a type-soundness result under the feature, store and effect laws; it
does not equate results across transformer orders or preserve a chosen realizer.
We use the laws as comparison obligations, not the language theorem without its
typing infrastructure.

The retained bibliography also leads to [Cohen et al., EffHOL,
v1](https://arxiv.org/html/2506.09458v1), §V, Theorem 5. Its premise is a HOL
derivation; its translated computation and specification live in the prescribed
EffHOL translation, including the logical modality's rules. We recovered and
inspected this primary statement. No modality instance for our `Keep`/`Undo`
pair is constructed here, so that theorem is not invoked to justify them.
The selected alternative is the handler account above; neither arbitrary monads
nor the notation `W` establish an EffHOL instance. No CBPV correspondence theorem
is used from a secondary summary.

## Handler presentation of the frozen task

Use finite trees for return, Boolean read, Boolean write and exception raise,
quotiented only by the chosen effect equations. Read has two branches; write
has one continuation; raise has none. A direct fold interprets return, read,
write and raise by the clauses above. For a fixed result set, the carrier
`Keep A` or `Undo A` with these operations satisfies the single-cell state
laws and the exception theory. This gives two models of the sum theory.
The `Undo` model also satisfies the tensor interaction below; `Keep` does not.
An inductive fold of a finite tree agrees with direct monadic sequencing by
those clauses. This is a paper specialization of the free-model interpretation
principle, not a checked implementation of free models in Lean.

For `P`, interpret its protected finite tree and then apply the appropriate
scoped catch function. Both functions respect extensional equality of the
interpreted computation, since their defining case analyses depend only on
that function's result. They reproduce the two displayed results. A generic
handler adapter must additionally encode that scope and entry state; a fold of
operation symbols alone does not recover the rollback policy.

In particular, we do not identify scoped rollback catch with a homomorphism
that leaves every combined state operation unchanged. Replacing an aborting
exception by a successful result changes which state is observable. The
handler's target algebra and return map must be justified for that exact use.
Applying the free-model theorem without those checks would skip the central
obligation of this example.

Compared with the direct route, the benefit would be one shared expression and
reused interpretation proofs for many clients. The new preparation is the
finite effect presentation, both models, scoped handling representation and
compatibility with selected-value observation. For this one expression, direct
case analysis is smaller. The experiment establishes mathematical fit, not a
measured authoring advantage of either interface.

## Equations that hold, and the law that changes

Both interpretations satisfy monad unit/associativity and the ordinary
single-cell equations, written with `>>` for sequencing:

```text
put s >> put t = put t
put s >> get = put s >> return s
get >>= (λs. put s) = return ()
get >>= (λs. get >>= λt. k s t) = get >>= (λs. k s s).
```

They also satisfy aborting bind, `throw e >>= k = throw e`, and their catch
clauses recover `catch (throw e) h = h e` and
`catch (return a) h = return a`. These are paper checks by expanding the
specified functions. They do not impose a relation between state and exceptions
beyond the selected combination.

For tensor, commuting write with a nullary exception requires

```text
put t >> throw e = throw e.
```

`Undo` satisfies it: both sides return `inr e` for every starting state.
`Keep` fails at initial `false` and `t = true`: the two results are
`(inr e,true)` and `(inr e,false)`. Read also commutes with a constant exception
in `Undo`, since all read branches abort identically. With the single-cell
state equations, these supply the cross-equations with this exception theory.
A sum does not demand them. Thus rejecting `Keep` as a tensor model is an
established mismatch in this paper instance, not absence of a construction.

The scoped laws distinguish the policies more finely:

```text
Keep: put s >> catch m h = catch (put s >> m) h
Undo: put s >> catch m h = catch (put s >> m) (λe. put s >> h e).
```

Both follow by the success/exception cases in their definitions. The first is
false for `Undo`: start in `false`, choose `s = true`, `m = throw fault`, and
`h = λ_. get`. The left returns `true`, but the right handler starts in `false`.
The second is false for `Keep` in general: choose `s = false`,
`m = put true >> throw fault`, and `h = λ_. get`. Its left returns `true`, while
the right explicitly resets to `false`. A reusable proof must select the law
matching its interpretation. Having individually lawful state and exception
operations does not select that law.

## Changed witness and changed proof

Now alter the client to read inside the handler:

```text
Q := catch (put true >> throw fault)
           (λ_. get >>= λs. return (w(s))).
```

At initial `false`, `QKeep` returns `w(true)` and `QUndo` returns `w(false)`.
Both values certify `n < 2`; their selected naturals are 1 and 0. Therefore
propositional validity alone cannot certify the desired cross-interpretation
witness equality. This also rejects the proposed rewrite moving the initial
read of `P` into its handler for `Keep`, even though it agrees for this particular
`Undo` example. Such agreement does not establish a general read-motion law.

For the original `P`, exact witness preservation succeeds precisely because the
value is captured before the effect change. A handler permitted to ignore that
captured value and return an arbitrary certified natural is outside its contract.
The same distinction protects a selected parser alternative: a Boolean success
observation would hide the replacement of one successful witness by another.

The observations and evidence levels remain separate:

| Claim | Result of this paper experiment |
|---|---|
| Existence of a natural below two | True under both policies, too weak for selected data |
| Returned data of `P` | Exactly `w(s₀)` in both, with its bound certificate |
| Returned data of `Q` from false | Different, despite satisfying the same proposition |
| Final-state equality for `P` | Fails from false; a witness-only relation deliberately forgets it |
| Equation-preserving model/handler | Requires the chosen sum/tensor and scoped-catch laws above |
| Operational adequacy | Not claimed; no runtime or reduction-to-denotation proof supplied |
| Resource or physical rollback guarantee | Not claimed; no cost, interference, crash or storage model supplied |

## Local reuse, decisions and residual work

[#196's interaction contracts](external-interaction-contracts.md) already
separate observable effects, returned results, interference and recovery.
Our Boolean rollback is not evidence that those external actions can be undone.
A concrete adapter would have to relate its real observations to the selected
contract, including failed attempts and missing replies.

[#254](language-extension-metatheory.md) already separates constructor admission,
model validity and interaction laws. This experiment uses that discipline for
an effect change rather than repeating a general language-extension survey.
[#278's assessed evidence](construction-observation-research-assessment.md)
and the [observation-extension contracts](observation-extension-contracts.md)
retain exact parser witnesses separately from recognition. [#285](higher-order-extensional-comparison.md)
retains independent meaning and distinguishes strong cost observations from
weaker result equality. None of these completed studies is reopened, and this
paper adds no new general observation or higher-order infrastructure.

**Adopt** the explicit selected-data and effect-law ledger for effectful
proof-producing clients. Retain ordinary direct proofs and APIs. This is a
contract recommendation, not adoption of a universal effect representation.
**Investigate** a bounded handler specialization when #196/#235 selects an
actual witness-producing client whose effect policy changes; #36/#200 should
coordinate its proof interpretation with the theory-extension programme.
The successor must retain `P` and `Q`, show both catch-law cases, reject tensor
commutation for `Keep`, and connect its selected output to independent meaning.

**Defer** a general handler implementation, CBPV migration and EffHOL instance.
Promotion requires a second client demonstrating reusable interpretation or
proof structure beyond the direct case split, and an explicit inventory of
scope, model and modality obligations. EffHOL work additionally needs an admitted
modality and a translated derivation retaining the selected realizer; the soundness
theorem alone is not that instance. No architecture is rejected merely because
an adapter into today's syntax is absent.

Preparation costs are qualitative: the direct route needs two semantics and
small case proofs; a handler route additionally needs equation admission,
scoping and fold/interpretation evidence; a general realizability route adds its
logical modality and proof translation. No elapsed-time or source-size benefit
was measured. No immediate formalization is needed to resolve the paper question;
existing interfaces and Mathlib structures should be reused if the conditional
successor is promoted. New formal claims would require the usual checked
success/failure cases and build/proof audit.

This is a bounded comparison, not exhaustive effect discovery. It omits
divergence, nondeterminism, higher identity, indexed state, concurrency, operational
adequacy and performance. The next client may require different equations.
#107 remains paused, #108's theorem unselected/unprepared, #260 inactive, and
#305/#306 outside this assignment. No universal AST, global subtyping or new
kernel axiom follows from this report.

## Checked successor

[#373's bounded implementation](state-exception-checked-comparison.md) now checks
these carrier meanings, scoped laws, selected-witness controls and an existing
measurement-record client. The original report above remains the paper-stage
record; the successor states the checked scope and remaining external-event
obligation separately.
