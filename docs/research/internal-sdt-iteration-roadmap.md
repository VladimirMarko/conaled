# Internal iteration and complete families: proof roadmap

This primary-source roadmap was prepared from the accepted assembly/program-lift
prerequisites at integration `fecec8579a3715ecf9efb5153a64d856256a9cce`. It guides
[#387](https://github.com/VladimirMarko/conaled/issues/387) and
[#388](https://github.com/VladimirMarko/conaled/issues/388); it supplies no new
Lean-checked iteration or completeness theorem. P1 classification was not assumed
in this assessment. The task graph now uses all-context completeness in #387
and requires its exponential equivalence in #388.

Primary source: van Oosten–Simpson, *Axioms and (counter)examples in synthetic domain theory*, APAL 104 (2000), 233–278, DOI 10.1016/S0168-0072(00)00014-2, [publisher-version PDF](https://www.pure.ed.ac.uk/ws/portalfiles/portal/12306183/1_s2.0_S0168007200000142_main.pdf). Retrieved PDF SHA-256 `066a36aa48fc38b5105637e8b77ef0b34de9e61751010492b922946b1ce9c2e2`. Printed page p is PDF zero-based page p−232.

## Verified source locators

| Locator | Fact needed |
|---|---|
| pp.238–239, Theorem 1.4 | F consists of descending Σ-sequences; coalgebra removes the head conditionally. I is the least lift subalgebra, with Jibladze's impredicative characterization. |
| p.241, Theorem 1.5 | From initial σ:LI→I derive strict algebra ρ=σμL(σ⁻¹) and successor s=ση. Strict means monad algebra; successor is arbitrary. |
| p.244, Definition 1.11 and Theorem 1.13 | Completeness is invertibility of restriction X^F→X^I. For complete strict X, extend its iteration map uniquely and evaluate at infinity. |
| p.245; p.250 after Axiom 3; p.254 Proposition 1.31 | Exponential/retract closure; decidable-object completeness; lift completeness requires Axioms 1–3 and Σ's N-existential closure. |
| pp.265–268, §3, Theorem 3.2 | Assembly F has carrier N∪{∞}, finite n realized by indices with domain [0,n), infinity by total indices. I has carrier N with the same finite realizers. |
| pp.268–269, Theorem 3.3 | I differs from the initial-chain colimit I₀, whose realizers additionally carry a finite bound. |

These source claims concern the stated model and its internal structure. They are not checked theorems about the present Lean category.

The later [cut-continuity proposal](assembly-cut-continuity-roadmap.md) supplies
explicit candidate recursion-theorem arguments and a uniform extension program
for the N/L(N) obligations below. It remains unformalized; its existence does not
change the checked status of completeness or iteration. [#386's lifting monads](assembly-lifting-monad.md)
now discharge P2. [The checked P3 construction](internal-cut-iteration.md)
discharges #387, including uniform tracking and conditional selection. The
proposed P3 steps below are retained as the source-based design rationale;
#388–#389 retain their construction obligations.

## Proposed direct #387 construction

The following is a proof roadmap inferred from the accepted code and explicit index semantics, not a claim of completed formal proofs.

Use `W(e)={m | ((Denumerable.ofNat Code e).eval m).Dom}`. Define a finite-length assembly and a finite-or-infinite-length assembly with the realizers above, in the same carrier universe as P0 (lifting Nat carriers with ULift if a uniform larger universe is required). The carrier being Nat does not make the finite-length assembly `encoded Nat`: its realizers expose positive observations of a cut, not its final length.

1. Construct recursive index transformations for empty/full cuts, shift `W(e)↦{k | k+1∈W(e)}`, and predecessor guarded by membership of zero. Prove equalities of domains, not equality of returned enumeration values. The cut realizers constrain definedness only. Account explicitly for P0's `run e = eval e 0` and any accepted #385 presentation comparison.
2. Give I its functor-algebra structure `none↦0`, `some n↦n+1`. Its tracker emits a program that waits for the lifted input, then enumerates the prefixed cut. For any tracked algebra `a:L A→A`, define the underlying fold by finite recursion, but **prove** it tracked independently: a recursion-theorem program R on a cut index e applies a's tracker to code for “wait for e(0), then evaluate R on shift(e).” Induct on the finite cut length to show that R returns a realizer of the fold. At length zero the inner program diverges, but its code realizes bottom, so a's tracker must still return. This is the essential nontrivial tracking lemma; structural recursion on an externally known n alone does not prove it.
3. Prove the unique arrow h:I→A satisfying `h∘σ=a∘Lh`, using the constructed tracker and induction on the underlying finite length. From this actual initial algebra and #386's monad laws, derive `(I,ρ,s)` initial among strict monad algebras with an arbitrary endomap. Do not substitute a theorem about initial *monad* algebras, which is a different universal property.
4. Give F its coalgebra `0↦none`, `n+1↦some n`, `∞↦some ∞`. For `c:A→L A`, generate a cut enumerator: membership of k succeeds precisely after k+1 successful unfoldings using c's tracker and the lift evaluator. The underlying map records termination length or infinity; the tracker does not decide which. Establish the coalgebra equation and uniqueness by all finite membership observations. Constant full enumeration realizes infinity. Inclusion I→F uses the same realizer, successor prefixes a true observation, and successor fixes infinity.
5. For a complete strict algebra `(X,a)` and admitted endomap g, initiality supplies the unique iteration arrow h satisfying the algebra equation and `h∘s=g∘h`. Let H extend h. Prove `H∘s_F=g∘H` by extension uniqueness, then `g(H∞)=H∞`. For selected transport, require an admitted algebra morphism t intertwining endomaps; compare t∘h and then t∘H by the two uniqueness results. A random fixed-point witness is insufficient. Boolean negation remains a negative control: computability of g alone does not give a complete strict algebra structure on its carrier.

This direct construction can establish the category-level universal properties without first importing Eff's impredicative internal logic. Reconstructing the full Eff interpretation instead would require substantially different additional infrastructure (logic, power objects/quantification, and comparison with assemblies). Nothing in P0 establishes that infrastructure. The direct route is a feasible candidate plan, not a proof of the required tracking lemmas.

## Completeness contract and task-order risk

A bijection of ordinary hom sets `Hom(F,X)→Hom(I,X)` at global points is too weak for the intended uniform result. It does not itself give a tracked inverse on function assemblies. The reconciled
contract requires restriction bijectivity for **every context Γ**,
`Hom(Γ×F,X)→Hom(Γ×I,X)`, before exponentials are available. Once function
assemblies exist, prove equivalence with an exponential restriction
**isomorphism**, including the trackability of its inverse.

The all-context formulation states the strong contract using products; it is
not permission to assume concrete completeness. #388 must construct it for N and L(N). Ordinary initiality for each algebra likewise does not automatically prove a tracked family of folds: preserve tracker parameters explicitly if #387 promises a parameterized selector.

The preflight found a sequencing ambiguity without a forced model change:
#388 owns exponentials while #387 cited an exponential definition of completeness.
The reconciled tasks use the all-context formulation for #387's conditional theorem
and require #388 to prove the equivalence once function assemblies exist. Moving
generic exponentials to an earlier independent substep was an alternative; it is
not required to state this strong contract. Concrete completeness must still be
proved. P4's complete-family proof remains after #387, and P5's concrete state
algebra remains after P4 as corrected by STD371-001.

## #388 proof obligations and reusable construction plan

1. **Function assembly:** carrier `Hom A B`, with e realizing f when `(ofNat Code e).eval` tracks f. P0 `Hom.has_code` proves inhabitation. Evaluation uses universal partial evaluation. Currying a tracker on paired realizers uses the computable code constructor `Code.curry`; prove evaluation, curry/uncurry and uniqueness before using exponential notation. Function carriers contain tracked maps, not all underlying functions. P0's products still need the chosen categorical packaging and terminal object required by the selected Mathlib closed-category API.
2. **The missing recursion-theoretic lemma:** obtain a finite-observation/continuity result for trackers acting on cut indices, with its uniform code transformation. This should justify constancy of maps I→encoded Nat and uniqueness of extension into lifted Nat. Mathlib's Rice theorem about total decidable semantic predicates is not by itself that result. No Rice–Shapiro theorem was found in the inspected computability files. This is a substantive proof obligation, not a renamed continuity assumption.
3. **N and L(N):** construct extension trackers, not just underlying extensions. For N the expected map is constant along the cut coordinate. For L(N), investigate enumerating all finite-cut observations accessible from a given F realizer and dovetailing their defined results; prove value compatibility, equality at finite cuts, and uniqueness at infinity using the preceding lemma. This is a proposed direct computational proof. Alternatively, reconstruct the halting-dominance hypotheses and the specific internal reasoning needed to apply Proposition 1.31. The latter route cannot treat host classical logic as the internal logic of assemblies. Neither route is already discharged by #385's partial-map classifier.
4. **Closure:** prove retract closure by extending into the ambient object and composing with the retraction. Prove exponential closure by transpose/extend/transpose, using uniform completeness. A theorem asserting merely that every individual extension has some tracker does not give a tracker uniformly from source-function realizers unless that extra argument is supplied.
5. **Uniform family:** construct `D=(L N)^N`, so its elements are uniformly tracked partial sequences. They are not arbitrary external sequences of partial values. For context Γ with admitted capacity map n:Γ→N, construct tracked `e:Γ×D→D`, filtering a defined value v at coordinate k by decidable `v<n(γ)+k+1`. Compile the test after waiting for the value; never decide the outer partial domain. Prove idempotence and construct the fixed subassembly with inherited realizers.
6. **Dependent certificate identification:** construct both directions between that fixed subassembly and the intended uniformly realizable family of bounded certificates, including canonical trace reconstruction and variable-bound witnesses. Merely identifying carrier sets with `∀k,Option(Cert n k)` would admit untracked sequences. Prove evaluation/reassembly and the bound-preserving maps uniformly; only then can #389 build its algebra and countdown functional.
7. **Generalized contexts:** for h:Γ×I→X over Γ, forget bounds, extend in D uniformly, and compare H with e∘⟨projection,H⟩ by uniqueness. The equality gives a factorization through X with inherited realizers. Prove factorization uniqueness and pullback/repeated-substitution compatibility. This avoids asserting completeness of every slice object. If the implementation instead uses dependent section objects to parameterize initiality, those objects and their trackers are additional prerequisites; CCC alone is not a blanket local-cartesian-closure theorem.

The direct computational proof of L(N) completeness would establish the required bounded result independently of the source's general complete-implies-well-complete theorem. Acceptance must state which theorem was actually proved; do not advertise the latter from the former. The desired actual N/L(N) instance is mandatory in either route.

## Pinned Mathlib inventory

Revision inspected: `56a005855ea17e0b0958f73ec801ae140b0a1679`, as in the manifest. Relevant exact facilities:

- `Computability/Partrec.lean`: `Nat.Partrec` constructors and `Partrec.bind`, `Partrec.rfind`, `Partrec.rfindOpt`; closure for recursive evaluator/search programs.
- `Computability/PartrecCode.lean`: `Code.smn`, `Code.exists_code`, `Code.eval_part`, `Code.primrec₂_curry`, `Code.fixed_point₂`; also `evaln_sound`, `evaln_complete`, `primrec_evaln`, `eval_eq_rfindOpt` for finite observation and dovetailing. `fixed_point₂` is a program-index recursion theorem, not the SDT selected fixed-point theorem.
- `Computability/Halting.lean`: `ComputablePred.rice`/`rice₂`; inspect their total decidability hypotheses before proposing reuse for cut-tracker continuity.
- `CategoryTheory/Endofunctor/Algebra.lean`: endofunctor algebra/coalgebra categories, `Algebra.Initial.str_isIso`, `Coalgebra.Terminal.str_isIso` (Lambek lemmas). Instances still require actual assembly structures/universal proofs.
- `CategoryTheory/Monad/Basic.lean`, `Monad/Algebra.lean`: monad and Eilenberg–Moore algebra/hom structures for strict algebras. No checked initial-strict-algebra-with-successor theorem was identified in this inventory.
- `CategoryTheory/Monoidal/Closed/Basic.lean` and `Closed/Cartesian.lean` under Monoidal: `MonoidalClosed.curry`, `uncurry`, their inverse/naturality laws. The pinned Cartesian file says the old separate CartesianClosed API is deprecated; use CartesianMonoidalCategory plus MonoidalClosed when registering the assembly construction.
- `CategoryTheory/ObjectProperty/Local.lean`: `MorphismProperty.isLocal` is hom-precomposition bijectivity and has limit closure. Apply it, if useful, to the family of context products with I→F. `ObjectProperty/Orthogonal.lean` instead concerns vanishing morphisms in categories with zero morphisms; it is not the SDT orthogonality API.
- `CategoryTheory/Comma/Over/Basic.lean`, `Comma/Over/Pullback.lean`, `CategoryTheory/Retract.lean`: reusable categorical packaging; no assembly instances or slice completeness follow merely by importing them.

## Implementation disposition

P3 now has a [checked implementation](internal-cut-iteration.md), including
all-context conditional selection. Continue with #388's concrete completeness,
tracked function assemblies and exponential equivalence. The cut-observer
continuity roadmap remains unformalized. No effective-topos theorem has been
imported wholesale; any future source/category mismatch must still expose its
missing prerequisite before claiming the concrete provider complete.
